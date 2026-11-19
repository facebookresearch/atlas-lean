/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Elasticity.PrismaticMembers
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Spring compliance sensitivity on a constrained design interval

## i. Overview

A bar of length `L > 0` and axial rigidity `EA` (a force) is fixed at `x = 0` and loaded at
`x = L` by the end force `F`, positive along the outward normal `+x`, with no distributed load.
This is the fixed-traction problem `Elasticity.PrismaticMembers.IsFixedTractionSolution` at zero
load: by the existence and uniqueness results of that module its solution is `u x = F * x / EA`,
with `u 0 = 0` and `EA * u' L = F`. As a spring the bar has the effective stiffness `k = EA / L`
(force per length) and the tip displacement `u_tip = u L = F / k` (a length).

For a fixed end force and a design stiffness `k` in the feasible interval `[kmin, kmax]` with
`0 < kmin ≤ kmax`, the compliance is the work of the end force, `J = F * u_tip = F² / k` (an
energy). Its scalar adjoint `p = F / k` solves the adjoint equation `k * p = ∂J/∂u_tip = F`, and
`dJ/dk = -p * u_tip = -F² / k²` (energy per stiffness, a squared length) at every `k > 0`, so
the derivative exists on an open positive neighborhood even at an endpoint of the interval.
Restricted to the feasible interval the derivative is taken within `[kmin, kmax]`. At an
endpoint of a nondegenerate interval the feasible directions are one-sided, and a degenerate
interval has none but zero. For `F ≠ 0` the derivative never vanishes: an endpoint satisfies a
one-sided first-order condition, not stationarity, and no unconstrained optimum exists. The
dimension identities of section F record the units of `k`, `u_tip` and `p`, `J`, and `dJ/dk`
in the ISQ dimensions of `PhyslibExt.Units.EngineeringQuantities`.

Model inputs:

* a clamped/traction-end bar (not a fixed-fixed bar), small-strain linear elastic with constant
  rigidity; the end force is fixed and the stiffness `k` is the design variable;
* `J` is the load work on the tip displacement; no PDE adjoint, dynamic adjoint or constrained
  minimizer existence is claimed.

## ii. Key results

- `Statistics.DesignSensitivity.isFixedTractionSolution_zero_load`,
  `Statistics.DesignSensitivity.eqOn_zero_load_of_isFixedTractionSolution`: the zero-load bar and
  its solution `F * x / EA`.
- `Statistics.DesignSensitivity.tip_eq_of_isFixedTractionSolution`: the tip displacement is
  `F / k` with `k = EA / L`, and its load work is the compliance.
- `Statistics.DesignSensitivity.stiffness_mul_adjointDisplacement`: the adjoint equation
  `k * p = F`.
- `Statistics.DesignSensitivity.hasDerivAt_compliance`,
  `Statistics.DesignSensitivity.neg_adjointDisplacement_mul_tipDisplacement`,
  `Statistics.DesignSensitivity.hasDerivWithinAt_compliance_Icc`: `dJ/dk = -p * u_tip = -F² / k²`
  on `k > 0` and within the feasible interval.
- `Statistics.DesignSensitivity.feasibleDirections_left`,
  `Statistics.DesignSensitivity.feasibleDirections_right`,
  `Statistics.DesignSensitivity.feasibleDirections_interior`,
  `Statistics.DesignSensitivity.feasibleDirections_self`: feasible directions at the endpoints,
  in the interior and for a degenerate interval.
- `Statistics.DesignSensitivity.deriv_compliance_ne_zero`,
  `Statistics.DesignSensitivity.compliance_upper_endpoint`: no stationary point for `F ≠ 0`; the
  one-sided first-order condition at the upper endpoint.

## iii. Table of contents

- A. The bar under a tip force: zero distributed load
- B. Spring stiffness, tip displacement, load work and the adjoint
- C. Sensitivity of the compliance
- D. Feasible directions
- E. Endpoints: one-sided conditions, not stationarity
- F. Units

## iv. References

- J. M. Gere and B. J. Goodno, *Mechanics of Materials*, 8th edition, 2013 (axially loaded
  bars; the bar as a spring of stiffness `EA / L`).
- M. P. Bendsøe and O. Sigmund, *Topology Optimization: Theory, Methods and Applications*,
  2003, chapter 1 (compliance, adjoint sensitivity, self-adjointness of compliance).
-/

@[expose] public section

namespace Statistics.DesignSensitivity

open Elasticity.PrismaticMembers

/-! ## A. The bar under a tip force: zero distributed load -/

/-- At zero distributed load the constructed fixed-traction displacement is `F * x / EA`. -/
lemma fixedTractionDisplacement_zero_load (EA L F x : ℝ) :
    fixedTractionDisplacement EA L F (fun _ => 0) x = F * x / EA := by
  rw [fixedTractionDisplacement_const, fixedFreeDisplacement]
  ring

/-- `u x = F * x / EA` solves the fixed-traction problem with zero distributed load: `u 0 = 0`,
`u'' = 0` and `EA * u' L = F`. -/
lemma isFixedTractionSolution_zero_load {EA L F : ℝ} (hL : 0 < L) (hEA : EA ≠ 0) :
    IsFixedTractionSolution EA L F (fun _ => 0) (fun x => F * x / EA) := by
  have h := isFixedTractionSolution_fixedTractionDisplacement (P := F) (f := fun _ => (0 : ℝ))
    hL hEA continuousOn_const
  rwa [show fixedTractionDisplacement EA L F (fun _ => 0) = fun x => F * x / EA from
    funext (fixedTractionDisplacement_zero_load EA L F)] at h

/-- Every solution of the fixed-traction problem with zero distributed load is `F * x / EA` on
`[0, L]`. -/
lemma eqOn_zero_load_of_isFixedTractionSolution {EA L F : ℝ} {u : ℝ → ℝ} (hEA : EA ≠ 0)
    (hu : IsFixedTractionSolution EA L F (fun _ => 0) u) :
    Set.EqOn u (fun x => F * x / EA) (Set.Icc 0 L) := by
  intro x hx
  rw [hu.eqOn_fixedTractionDisplacement hEA hx, fixedTractionDisplacement_zero_load]

/-! ## B. Spring stiffness, tip displacement, load work and the adjoint -/

/-- Effective axial stiffness `k = EA / L` (force per length) of a bar of axial rigidity `EA`
and length `L`. -/
noncomputable def axialStiffness (EA L : ℝ) : ℝ :=
  EA / L

/-- Tip displacement `u_tip = F / k` (a length) of a spring of stiffness `k` under the end
force `F`. -/
noncomputable def tipDisplacement (F k : ℝ) : ℝ :=
  F / k

/-- Compliance `J = F * u_tip` (an energy): the work of the end force on the tip
displacement. -/
noncomputable def compliance (F k : ℝ) : ℝ :=
  F * tipDisplacement F k

/-- Scalar adjoint `p = F / k` (a length): the solution of the adjoint equation
`k * p = ∂J/∂u_tip = F`. -/
noncomputable def adjointDisplacement (F k : ℝ) : ℝ :=
  F / k

/-- A positive rigidity and a positive length give a positive stiffness. -/
lemma axialStiffness_pos {EA L : ℝ} (hEA : 0 < EA) (hL : 0 < L) : 0 < axialStiffness EA L := by
  unfold axialStiffness
  exact div_pos hEA hL

/-- The tip displacement of every zero-load solution is `F / k` with `k = EA / L`, and its load
work is the compliance `J = F * u_tip`. -/
lemma tip_eq_of_isFixedTractionSolution {EA L F : ℝ} {u : ℝ → ℝ} (hL : 0 < L) (hEA : EA ≠ 0)
    (hu : IsFixedTractionSolution EA L F (fun _ => 0) u) :
    u L = tipDisplacement F (axialStiffness EA L) ∧
      F * u L = compliance F (axialStiffness EA L) := by
  have hEq := eqOn_zero_load_of_isFixedTractionSolution hEA hu
  have hLmem : L ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt hL, le_rfl⟩
  have huL : u L = F * L / EA := hEq hLmem
  have hLne : L ≠ 0 := ne_of_gt hL
  have htip : F * L / EA = tipDisplacement F (axialStiffness EA L) := by
    unfold tipDisplacement axialStiffness
    field_simp
  constructor
  · exact huL.trans htip
  · rw [huL]
    unfold compliance
    rw [← htip]

/-- The scalar adjoint solves the adjoint equation `k * p = F`. -/
lemma stiffness_mul_adjointDisplacement {k : ℝ} (hk : k ≠ 0) (F : ℝ) :
    k * adjointDisplacement F k = F := by
  unfold adjointDisplacement
  field_simp

/-! ## C. Sensitivity of the compliance -/

/-- Adjoint sensitivity on the open half-line: at every `k > 0`, `dJ/dk = -p * u_tip`. -/
lemma hasDerivAt_compliance {k : ℝ} (hk : 0 < k) (F : ℝ) :
    HasDerivAt (compliance F) (-(adjointDisplacement F k * tipDisplacement F k)) k := by
  have hk' : k ≠ 0 := ne_of_gt hk
  have hdiv : HasDerivAt (fun k => F / k) ((0 * k - F * 1) / k ^ 2) k :=
    (hasDerivAt_const k F).div (hasDerivAt_id' k) hk'
  have hmul := hdiv.const_mul F
  have hderiv : F * ((0 * k - F * 1) / k ^ 2)
      = -(adjointDisplacement F k * tipDisplacement F k) := by
    unfold adjointDisplacement tipDisplacement
    field_simp
    ring
  rw [hderiv] at hmul
  exact hmul

/-- The adjoint expression is `-p * u_tip = -F² / k²`. -/
lemma neg_adjointDisplacement_mul_tipDisplacement (F k : ℝ) :
    -(adjointDisplacement F k * tipDisplacement F k) = -F ^ 2 / k ^ 2 := by
  unfold adjointDisplacement tipDisplacement
  by_cases hk : k = 0
  · simp [hk]
  · field_simp

/-- Restricted to the feasible interval `[kmin, kmax]` with `0 < kmin`, the compliance has the
derivative `-F² / k²` within the interval at every feasible `k`, endpoints included. -/
lemma hasDerivWithinAt_compliance_Icc {kmin kmax k : ℝ} (hkmin : 0 < kmin)
    (hk : k ∈ Set.Icc kmin kmax) (F : ℝ) :
    HasDerivWithinAt (compliance F) (-F ^ 2 / k ^ 2) (Set.Icc kmin kmax) k := by
  have hkpos : 0 < k := lt_of_lt_of_le hkmin hk.1
  have h : HasDerivWithinAt (compliance F) (-(adjointDisplacement F k * tipDisplacement F k))
      (Set.Icc kmin kmax) k :=
    (hasDerivAt_compliance hkpos F).hasDerivWithinAt
  rwa [neg_adjointDisplacement_mul_tipDisplacement] at h

/-! ## D. Feasible directions -/

/-- Feasible directions at the design `k` for the interval `[kmin, kmax]`: the `d` with
`k + t * d ∈ [kmin, kmax]` for every step `0 < t ≤ ε`, for some `ε > 0`. -/
def feasibleDirections (kmin kmax k : ℝ) : Set ℝ :=
  {d | ∃ ε > 0, ∀ t ∈ Set.Ioc (0 : ℝ) ε, k + t * d ∈ Set.Icc kmin kmax}

/-- At the lower endpoint of a nondegenerate interval the feasible directions are `d ≥ 0`. -/
lemma feasibleDirections_left {kmin kmax : ℝ} (h : kmin < kmax) :
    feasibleDirections kmin kmax kmin = Set.Ici 0 := by
  ext d
  simp only [feasibleDirections, Set.mem_ofPred_eq, Set.mem_Ici]
  constructor
  · rintro ⟨ε, hε, ht⟩
    by_contra hd
    have hlt : d < 0 := lt_of_not_ge hd
    have hmem := ht (ε / 2) ⟨by linarith, by linarith⟩
    simp only [Set.mem_Icc] at hmem
    have hmul : (ε / 2) * d < 0 := mul_neg_of_pos_of_neg (by linarith) hlt
    linarith
  · intro hd
    by_cases hd0 : d = 0
    · subst hd0
      exact ⟨1, by norm_num, fun t _ => ⟨by simp, by simpa using le_of_lt h⟩⟩
    · have hdpos : 0 < d := lt_of_le_of_ne hd (fun heq => hd0 heq.symm)
      have hsub : 0 < kmax - kmin := sub_pos.mpr h
      refine ⟨(kmax - kmin) / d, div_pos hsub hdpos, fun t ht => ?_⟩
      obtain ⟨ht0, htε⟩ := ht
      have htd : t * d ≤ kmax - kmin := by
        have hle := mul_le_mul_of_nonneg_right htε (le_of_lt hdpos)
        rwa [div_mul_cancel₀ _ (ne_of_gt hdpos)] at hle
      have hnn : 0 ≤ t * d := mul_nonneg (le_of_lt ht0) (le_of_lt hdpos)
      refine ⟨by linarith, by linarith⟩

/-- At the upper endpoint of a nondegenerate interval the feasible directions are `d ≤ 0`. -/
lemma feasibleDirections_right {kmin kmax : ℝ} (h : kmin < kmax) :
    feasibleDirections kmin kmax kmax = Set.Iic 0 := by
  ext d
  simp only [feasibleDirections, Set.mem_ofPred_eq, Set.mem_Iic]
  constructor
  · rintro ⟨ε, hε, ht⟩
    by_contra hd
    have hlt : 0 < d := lt_of_not_ge hd
    have hmem := ht (ε / 2) ⟨by linarith, by linarith⟩
    simp only [Set.mem_Icc] at hmem
    have hmul : 0 < (ε / 2) * d := mul_pos (by linarith) hlt
    linarith
  · intro hd
    by_cases hd0 : d = 0
    · subst hd0
      exact ⟨1, by norm_num, fun t _ => ⟨by simpa using le_of_lt h, by simp⟩⟩
    · have hdneg : d < 0 := lt_of_le_of_ne hd hd0
      have hneg : 0 < -d := neg_pos.mpr hdneg
      have hsub : 0 < kmax - kmin := sub_pos.mpr h
      refine ⟨(kmax - kmin) / (-d), div_pos hsub hneg, fun t ht => ?_⟩
      obtain ⟨ht0, htε⟩ := ht
      have htd : t * (-d) ≤ kmax - kmin := by
        have hle := mul_le_mul_of_nonneg_right htε (le_of_lt hneg)
        rwa [div_mul_cancel₀ _ (ne_of_gt hneg)] at hle
      have hnp : t * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht0) (le_of_lt hdneg)
      have hneg' : t * (-d) = -(t * d) := by ring
      refine ⟨by linarith, by linarith⟩

/-- At an interior design every direction is feasible. -/
lemma feasibleDirections_interior {kmin kmax k : ℝ} (hk : k ∈ Set.Ioo kmin kmax) :
    feasibleDirections kmin kmax k = Set.univ := by
  ext d
  simp only [feasibleDirections, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  obtain ⟨hlo, hhi⟩ := hk
  have hg1 : 0 < k - kmin := sub_pos.mpr hlo
  have hg2 : 0 < kmax - k := sub_pos.mpr hhi
  have hmpos : 0 < min (k - kmin) (kmax - k) := lt_min hg1 hg2
  refine ⟨min (k - kmin) (kmax - k) / (|d| + 1), div_pos hmpos (by positivity), fun t ht => ?_⟩
  obtain ⟨ht0, htε⟩ := ht
  have hd1 : (0 : ℝ) < |d| + 1 := by positivity
  have hbound : |t * d| ≤ min (k - kmin) (kmax - k) := by
    have h1 : |t * d| = t * |d| := by rw [abs_mul, abs_of_pos ht0]
    have h2 : t * |d| ≤ (min (k - kmin) (kmax - k) / (|d| + 1)) * |d| :=
      mul_le_mul_of_nonneg_right htε (abs_nonneg d)
    have h3 : (min (k - kmin) (kmax - k) / (|d| + 1)) * |d|
        ≤ min (k - kmin) (kmax - k) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hd1]
      exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg d]) (le_of_lt hmpos)
    rw [h1]
    exact le_trans h2 h3
  rw [abs_le] at hbound
  have hm1 : min (k - kmin) (kmax - k) ≤ k - kmin := min_le_left _ _
  have hm2 : min (k - kmin) (kmax - k) ≤ kmax - k := min_le_right _ _
  refine ⟨by linarith, by linarith⟩

/-- A degenerate interval has no nontrivial feasible direction. -/
lemma feasibleDirections_self (k : ℝ) : feasibleDirections k k k = {0} := by
  ext d
  simp only [feasibleDirections, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ε, hε, ht⟩
    have hmem := ht (ε / 2) ⟨by linarith, by linarith⟩
    simp only [Set.mem_Icc] at hmem
    have h0 : (ε / 2) * d = 0 := by linarith [hmem.1, hmem.2]
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    exact (mul_eq_zero.mp h0).resolve_left (ne_of_gt hε2)
  · intro hd
    subst hd
    exact ⟨1, by norm_num, fun t _ => ⟨by simp, by simp⟩⟩

/-! ## E. Endpoints: one-sided conditions, not stationarity -/

/-- For `F ≠ 0` the compliance has no stationary point on `k > 0`. -/
lemma deriv_compliance_ne_zero {F k : ℝ} (hF : F ≠ 0) (hk : 0 < k) :
    deriv (compliance F) k ≠ 0 := by
  have h := (hasDerivAt_compliance hk F).deriv
  rw [neg_adjointDisplacement_mul_tipDisplacement] at h
  rw [h]
  exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hF)) (pow_ne_zero 2 (ne_of_gt hk))

/-- At the upper endpoint of a nondegenerate feasible interval the derivative within the
interval is `-F² / kmax² < 0`, so the endpoint is not stationary; along every feasible
direction `d` the first-order change `-F² / kmax² * d` is nonnegative and vanishes only for
`d = 0`. -/
lemma compliance_upper_endpoint {F kmin kmax : ℝ} (hF : F ≠ 0) (hkmin : 0 < kmin)
    (hlt : kmin < kmax) :
    HasDerivWithinAt (compliance F) (-F ^ 2 / kmax ^ 2) (Set.Icc kmin kmax) kmax ∧
      -F ^ 2 / kmax ^ 2 < 0 ∧
      ∀ d ∈ feasibleDirections kmin kmax kmax,
        0 ≤ -F ^ 2 / kmax ^ 2 * d ∧ (-F ^ 2 / kmax ^ 2 * d = 0 → d = 0) := by
  have hkmax : 0 < kmax := lt_trans hkmin hlt
  have hmem : kmax ∈ Set.Icc kmin kmax := ⟨le_of_lt hlt, le_rfl⟩
  have hderiv := hasDerivWithinAt_compliance_Icc hkmin hmem F
  have hF2 : 0 < F ^ 2 := by positivity
  have hk2 : 0 < kmax ^ 2 := by positivity
  have hneg : -F ^ 2 / kmax ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) hk2
  refine ⟨hderiv, hneg, fun d hd => ?_⟩
  rw [feasibleDirections_right hlt, Set.mem_Iic] at hd
  have hne : -F ^ 2 / kmax ^ 2 ≠ 0 := ne_of_lt hneg
  constructor
  · exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt hneg) hd
  · intro hzero
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h hne
    · exact h

/-! ## F. Units -/

section Units

open Dimension Units.QuantityDimensions Units.EngineeringQuantities

/-- Units of the effective stiffness `k = EA / L`: an axial rigidity (a force) over a length is
the translational stiffness dimension `M T⁻²`. -/
lemma axialStiffness_dimension : forceDim / single .length = translationalStiffnessDim := by
  decide

/-- Units of the tip displacement `u_tip = F / k` and of the adjoint `p = F / k`: a force over a
translational stiffness is a length. -/
lemma tipDisplacement_dimension : forceDim / translationalStiffnessDim = single .length := by
  decide

/-- Units of the compliance `J = F * u_tip`: a force times a length is an energy (the identity
`forceDim_mul_length`, read for the load work). -/
lemma compliance_dimension : forceDim * single .length = energyDim :=
  forceDim_mul_length

/-- Units of the sensitivity `dJ/dk = -F² / k²`: an energy per translational stiffness is a
squared length. -/
lemma complianceSensitivity_dimension :
    energyDim / translationalStiffnessDim = single .length ^ (2 : ℕ) := by
  decide

end Units

end Statistics.DesignSensitivity

end
