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
# Spring compliance: sensitivity on a constrained design interval and error composition

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

Sections G to I bound errors in the compliance `J(F, k) = F² / k` itself, read as a quantity of
interest. The admissible parameters `|F| ≤ Fmax`, `k ≥ kmin` with `kmin > 0` form a convex set,
so with two admissible points `(F, k)` and `(Fhat, khat)` the coordinate path
`(F, k) → (Fhat, k) → (Fhat, khat)` stays in it. The named intermediate compliance `J(Fhat, k)`
splits the error into a force step, bounded through the difference of squares by
`(2 Fmax / kmin) |F - Fhat|`, and a stiffness step, bounded through the difference of inverse
stiffnesses by `(Fmax² / kmin²) |k - khat|`; the triangle inequality adds them. Model,
discretization, algebraic solver and floating-point arithmetic terms enter the same finite
triangle inequality only as supplied bounds between named values of the same compliance. A
residual `k u - F` of a trial tip displacement `u` bounds the state error, and for `F ≠ 0` the
compliance error, only through a stability constant: for `k ≥ kmin > 0` it bounds the state error
by `|k u - F| / kmin` and the compliance error by `|F| |k u - F| / kmin`, while over all `k > 0`
no constant turns the residual into a bound on the state error, nor, for `F ≠ 0`, into a bound on
the compliance error. The state-error half holds for every `F`; at `F = 0` the compliance error
`J - F u` vanishes, so its half needs `F ≠ 0`.

Model inputs:

* a clamped/traction-end bar (not a fixed-fixed bar), small-strain linear elastic with constant
  rigidity; the end force is fixed and the stiffness `k` is the design variable;
* `J` is the load work on the tip displacement; no PDE adjoint, dynamic adjoint or constrained
  minimizer existence is claimed;
* the error bounds are deterministic, not covariance or credibility statements, and each supplied
  error term carries its own provenance.

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
- `Statistics.DesignSensitivity.compliance_eq_sq_div`,
  `Statistics.DesignSensitivity.abs_compliance_sub_force_le`,
  `Statistics.DesignSensitivity.abs_compliance_sub_stiffness_le`: `J = F² / k` and the force and
  stiffness steps of the compliance error.
- `Statistics.DesignSensitivity.abs_compliance_sub_compliance_le`,
  `Statistics.DesignSensitivity.abs_compliance_sub_computed_le`: the compliance error between two
  admissible parameter points, and its composition with supplied model, discretization, solver
  and arithmetic terms.
- `Statistics.DesignSensitivity.abs_sub_le_residual_div`: a residual bounds the state and
  compliance errors with the stability constant `1 / kmin`.
- `Statistics.DesignSensitivity.not_exists_residual_state_error_bound`,
  `Statistics.DesignSensitivity.not_exists_residual_compliance_error_bound`,
  `Statistics.DesignSensitivity.not_exists_residual_error_bound`: without a lower stiffness bound
  no constant turns the residual into a bound on the state error, for any `F`, nor on the
  compliance error, for `F ≠ 0`; the last lemma states both halves for `F ≠ 0`.

## iii. Table of contents

- A. The bar under a tip force: zero distributed load
- B. Spring stiffness, tip displacement, load work and the adjoint
- C. Sensitivity of the compliance
- D. Feasible directions
- E. Endpoints: one-sided conditions, not stationarity
- F. Units
- G. Compliance error: one-parameter steps
- H. Compliance error: composition
- I. Residuals and the stability constant

## iv. References

- J. M. Gere and B. J. Goodno, *Mechanics of Materials*, 8th edition, 2013 (axially loaded
  bars; the bar as a spring of stiffness `EA / L`).
- M. P. Bendsøe and O. Sigmund, *Topology Optimization: Theory, Methods and Applications*,
  2003, chapter 1 (compliance, adjoint sensitivity, self-adjointness of compliance).
- W. L. Oberkampf and C. J. Roy, *Verification and Validation in Scientific Computing*,
  Cambridge University Press, 2010, chapters 7 and 8 (round-off, iterative and discretization
  errors in a numerical solution).
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

/-! ## G. Compliance error: one-parameter steps -/

/-- The compliance is `J(F, k) = F² / k`, for every `k` (both sides are `0` at `k = 0`). -/
lemma compliance_eq_sq_div (F k : ℝ) : compliance F k = F ^ 2 / k := by
  unfold compliance tipDisplacement
  ring

/-- **Force step.** For forces `|F|, |Fhat| ≤ Fmax` at a stiffness `k ≥ kmin > 0`, the difference
of squares gives `|J(F, k) - J(Fhat, k)| ≤ (2 Fmax / kmin) |F - Fhat|`. -/
lemma abs_compliance_sub_force_le {Fmax kmin F Fhat k : ℝ} (hkmin : 0 < kmin)
    (hF : |F| ≤ Fmax) (hFhat : |Fhat| ≤ Fmax) (hk : kmin ≤ k) :
    |compliance F k - compliance Fhat k| ≤ (2 * Fmax / kmin) * |F - Fhat| := by
  have hkpos : 0 < k := lt_of_lt_of_le hkmin hk
  have hkne : k ≠ 0 := ne_of_gt hkpos
  have hFmax : 0 ≤ Fmax := le_trans (abs_nonneg F) hF
  have hsum : |F + Fhat| ≤ 2 * Fmax := by
    calc |F + Fhat| ≤ |F| + |Fhat| := abs_add_le _ _
      _ ≤ Fmax + Fmax := add_le_add hF hFhat
      _ = 2 * Fmax := by ring
  have hid : F ^ 2 / k - Fhat ^ 2 / k = (F - Fhat) * (F + Fhat) / k := by ring
  have h1 : |F + Fhat| / k ≤ (2 * Fmax) / k := by
    rw [div_le_iff₀ hkpos, div_mul_cancel₀ _ hkne]
    exact hsum
  have h2 : (2 * Fmax) / k ≤ (2 * Fmax) / kmin := by
    rw [div_le_iff₀ hkpos, div_mul_eq_mul_div, le_div_iff₀ hkmin]
    exact mul_le_mul_of_nonneg_left hk (mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hFmax)
  have hstep : |F + Fhat| / k ≤ 2 * Fmax / kmin := le_trans h1 h2
  rw [compliance_eq_sq_div, compliance_eq_sq_div, hid, abs_div, abs_mul,
    abs_of_pos hkpos]
  calc |F - Fhat| * |F + Fhat| / k
      = |F - Fhat| * (|F + Fhat| / k) := by ring
    _ ≤ |F - Fhat| * (2 * Fmax / kmin) :=
        mul_le_mul_of_nonneg_left hstep (abs_nonneg (F - Fhat))
    _ = 2 * Fmax / kmin * |F - Fhat| := by ring

/-- **Stiffness step.** For a force `|Fhat| ≤ Fmax` and stiffnesses `k, khat ≥ kmin > 0`, the
inverse-stiffness difference gives `|J(Fhat, k) - J(Fhat, khat)| ≤ (Fmax² / kmin²) |k - khat|`. -/
lemma abs_compliance_sub_stiffness_le {Fmax kmin Fhat k khat : ℝ} (hkmin : 0 < kmin)
    (hFhat : |Fhat| ≤ Fmax) (hk : kmin ≤ k) (hkhat : kmin ≤ khat) :
    |compliance Fhat k - compliance Fhat khat| ≤ (Fmax ^ 2 / kmin ^ 2) * |k - khat| := by
  have hkpos : 0 < k := lt_of_lt_of_le hkmin hk
  have hkhatpos : 0 < khat := lt_of_lt_of_le hkmin hkhat
  have hkne : k ≠ 0 := ne_of_gt hkpos
  have hkhatne : khat ≠ 0 := ne_of_gt hkhatpos
  have hsq : Fhat ^ 2 ≤ Fmax ^ 2 := by
    calc Fhat ^ 2 = |Fhat| ^ 2 := (sq_abs Fhat).symm
      _ ≤ Fmax ^ 2 := pow_le_pow_left₀ (abs_nonneg Fhat) hFhat 2
  have hkkpos : (0:ℝ) < k * khat := mul_pos hkpos hkhatpos
  have hkmin2 : (0:ℝ) < kmin ^ 2 := pow_pos hkmin 2
  have hkk : kmin ^ 2 ≤ k * khat := by
    calc kmin ^ 2 = kmin * kmin := by ring
      _ ≤ k * khat := mul_le_mul hk hkhat hkmin.le (le_trans hkmin.le hk)
  have hid : Fhat ^ 2 / k - Fhat ^ 2 / khat = Fhat ^ 2 * (khat - k) / (k * khat) := by
    field_simp
  have h1 : Fhat ^ 2 / (k * khat) ≤ Fmax ^ 2 / (k * khat) := by
    rw [div_le_iff₀ hkkpos, div_mul_cancel₀ _ (ne_of_gt hkkpos)]
    exact hsq
  have h2 : Fmax ^ 2 / (k * khat) ≤ Fmax ^ 2 / kmin ^ 2 := by
    rw [div_le_iff₀ hkkpos, div_mul_eq_mul_div, le_div_iff₀ hkmin2]
    exact mul_le_mul_of_nonneg_left hkk (sq_nonneg Fmax)
  have hbound : Fhat ^ 2 / (k * khat) ≤ Fmax ^ 2 / kmin ^ 2 := le_trans h1 h2
  rw [compliance_eq_sq_div, compliance_eq_sq_div, hid, abs_div, abs_mul,
    abs_of_pos hkkpos, abs_sq Fhat, abs_sub_comm khat k]
  calc Fhat ^ 2 * |k - khat| / (k * khat)
      = |k - khat| * (Fhat ^ 2 / (k * khat)) := by ring
    _ ≤ |k - khat| * (Fmax ^ 2 / kmin ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (abs_nonneg (k - khat))
    _ = Fmax ^ 2 / kmin ^ 2 * |k - khat| := by ring

/-! ## H. Compliance error: composition -/

/-- **Compliance error between two admissible parameter points.** For `|F|, |Fhat| ≤ Fmax` and
`k, khat ≥ kmin > 0`, through the intermediate compliance `J(Fhat, k)`,
`|J(F, k) - J(Fhat, khat)| ≤ (2 Fmax / kmin) |F - Fhat| + (Fmax² / kmin²) |k - khat|`. -/
lemma abs_compliance_sub_compliance_le {Fmax kmin F Fhat k khat : ℝ} (hkmin : 0 < kmin)
    (hF : |F| ≤ Fmax) (hFhat : |Fhat| ≤ Fmax) (hk : kmin ≤ k) (hkhat : kmin ≤ khat) :
    |compliance F k - compliance Fhat khat| ≤
      (2 * Fmax / kmin) * |F - Fhat| + (Fmax ^ 2 / kmin ^ 2) * |k - khat| := by
  have hforce := abs_compliance_sub_force_le hkmin hF hFhat hk
  have hstiff := abs_compliance_sub_stiffness_le hkmin hFhat hk hkhat
  calc |compliance F k - compliance Fhat khat|
      = |(compliance F k - compliance Fhat k) +
        (compliance Fhat k - compliance Fhat khat)| := by
        congr 1
        ring
    _ ≤ |compliance F k - compliance Fhat k| + |compliance Fhat k - compliance Fhat khat| :=
        abs_add_le _ _
    _ ≤ (2 * Fmax / kmin) * |F - Fhat| + (Fmax ^ 2 / kmin ^ 2) * |k - khat| :=
        add_le_add hforce hstiff

/-- **Composition with supplied terms.** The compliance `J(Fhat, khat)` at the estimated inputs,
the compliance `Jmodel` of the analysis model, its discretization `Jdisc`, the algebraic solver
output `Jsolve` and the computed value `Jcomp` are successive values of the same compliance;
with the supplied bounds `eModel`, `eDisc`, `eSolve`, `eArith` on their successive differences,
`|J(F, k) - Jcomp|` is at most the parameter bound plus the four supplied terms. -/
lemma abs_compliance_sub_computed_le {Fmax kmin F Fhat k khat Jmodel Jdisc Jsolve Jcomp eModel
    eDisc eSolve eArith : ℝ} (hkmin : 0 < kmin) (hF : |F| ≤ Fmax) (hFhat : |Fhat| ≤ Fmax)
    (hk : kmin ≤ k) (hkhat : kmin ≤ khat) (hmodel : |compliance Fhat khat - Jmodel| ≤ eModel)
    (hdisc : |Jmodel - Jdisc| ≤ eDisc) (hsolve : |Jdisc - Jsolve| ≤ eSolve)
    (harith : |Jsolve - Jcomp| ≤ eArith) :
    |compliance F k - Jcomp| ≤
      (2 * Fmax / kmin) * |F - Fhat| + (Fmax ^ 2 / kmin ^ 2) * |k - khat| + eModel + eDisc +
        eSolve + eArith := by
  have h0 := abs_compliance_sub_compliance_le hkmin hF hFhat hk hkhat
  have t1 : |compliance F k - Jcomp|
      ≤ |compliance F k - compliance Fhat khat| + |compliance Fhat khat - Jcomp| := by
    calc |compliance F k - Jcomp|
        = |(compliance F k - compliance Fhat khat) + (compliance Fhat khat - Jcomp)| := by
          congr 1
          ring
      _ ≤ _ := abs_add_le _ _
  have t2 : |compliance Fhat khat - Jcomp|
      ≤ |compliance Fhat khat - Jmodel| + |Jmodel - Jcomp| := by
    calc |compliance Fhat khat - Jcomp|
        = |(compliance Fhat khat - Jmodel) + (Jmodel - Jcomp)| := by
          congr 1
          ring
      _ ≤ _ := abs_add_le _ _
  have t3 : |Jmodel - Jcomp| ≤ |Jmodel - Jdisc| + |Jdisc - Jcomp| := by
    calc |Jmodel - Jcomp| = |(Jmodel - Jdisc) + (Jdisc - Jcomp)| := by
          congr 1
          ring
      _ ≤ _ := abs_add_le _ _
  have t4 : |Jdisc - Jcomp| ≤ |Jdisc - Jsolve| + |Jsolve - Jcomp| := by
    calc |Jdisc - Jcomp| = |(Jdisc - Jsolve) + (Jsolve - Jcomp)| := by
          congr 1
          ring
      _ ≤ _ := abs_add_le _ _
  linarith

/-! ## I. Residuals and the stability constant -/

/-- **A residual with a stability constant.** For a stiffness `k ≥ kmin > 0` and a trial tip
displacement `u`, the residual `k u - F` of the equilibrium `k u_tip = F` bounds the state error
by `|k u - F| / kmin` and the compliance error `J - F u` by `|F| |k u - F| / kmin`. -/
lemma abs_sub_le_residual_div {kmin k F u : ℝ} (hkmin : 0 < kmin) (hk : kmin ≤ k) :
    |tipDisplacement F k - u| ≤ |k * u - F| / kmin ∧
      |compliance F k - F * u| ≤ |F| * |k * u - F| / kmin := by
  have hkpos : 0 < k := lt_of_lt_of_le hkmin hk
  have hkne : k ≠ 0 := ne_of_gt hkpos
  have hstate : |tipDisplacement F k - u| ≤ |k * u - F| / kmin := by
    have hid : tipDisplacement F k - u = -(k * u - F) / k := by
      unfold tipDisplacement
      field_simp
      ring
    rw [hid, abs_div, abs_neg, abs_of_pos hkpos, div_le_iff₀ hkpos, div_mul_eq_mul_div,
      le_div_iff₀ hkmin]
    exact mul_le_mul_of_nonneg_left hk (abs_nonneg (k * u - F))
  refine ⟨hstate, ?_⟩
  have hid2 : compliance F k - F * u = F * (tipDisplacement F k - u) := by
    unfold compliance
    ring
  rw [hid2, abs_mul]
  calc |F| * |tipDisplacement F k - u|
      ≤ |F| * (|k * u - F| / kmin) := mul_le_mul_of_nonneg_left hstate (abs_nonneg F)
    _ = |F| * |k * u - F| / kmin := by ring

/-- **A bare residual is not a state error.** For every end force `F`, over all stiffnesses
`k > 0`, with no lower bound, no constant `C` makes `C |k u - F|` a bound on the state error: the
trial `u = F / k + 1` has residual `k` and state error `1`. -/
lemma not_exists_residual_state_error_bound (F : ℝ) :
    ¬ ∃ C : ℝ, ∀ k u : ℝ, 0 < k → |tipDisplacement F k - u| ≤ C * |k * u - F| := by
  rintro ⟨C, hC⟩
  have key : ∀ k : ℝ, 0 < k → (1:ℝ) ≤ C * k := by
    intro k hk
    have h := hC k (F / k + 1) hk
    have e1 : tipDisplacement F k - (F / k + 1) = -1 := by
      unfold tipDisplacement
      ring
    have e2 : k * (F / k + 1) - F = k := by
      have hkne : k ≠ 0 := ne_of_gt hk
      field_simp
      ring
    rw [e1, abs_neg, abs_one, e2, abs_of_pos hk] at h
    exact h
  have hC1 : (1:ℝ) ≤ C := by
    have h := key 1 one_pos
    rwa [mul_one] at h
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC1
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have h2C : (0:ℝ) < 2 * C := by linarith
  have h2Cne : (2:ℝ) * C ≠ 0 := mul_ne_zero two_ne_zero hCne
  have hsmall := key (1 / (2 * C)) (div_pos one_pos h2C)
  have hval : C * (1 / (2 * C)) = 1 / 2 := by
    rw [mul_one_div, div_eq_iff h2Cne]
    ring
  rw [hval] at hsmall
  norm_num at hsmall

/-- **A bare residual is not a compliance error.** For an end force `F ≠ 0`, over all stiffnesses
`k > 0`, with no lower bound, no constant `C` makes `C |k u - F|` a bound on the compliance error:
the trial `u = F / k + 1` has residual `k` and compliance error `|F|`. At `F = 0` the compliance
error `J - F u` vanishes, so the force must be nonzero. -/
lemma not_exists_residual_compliance_error_bound {F : ℝ} (hF : F ≠ 0) :
    ¬ ∃ C : ℝ, ∀ k u : ℝ, 0 < k → |compliance F k - F * u| ≤ C * |k * u - F| := by
  rintro ⟨C, hC⟩
  have key : ∀ k : ℝ, 0 < k → |F| ≤ C * k := by
    intro k hk
    have h := hC k (F / k + 1) hk
    have e1 : compliance F k - F * (F / k + 1) = -F := by
      unfold compliance tipDisplacement
      ring
    have e2 : k * (F / k + 1) - F = k := by
      have hkne : k ≠ 0 := ne_of_gt hk
      field_simp
      ring
    rw [e1, abs_neg, e2, abs_of_pos hk] at h
    exact h
  have hFpos : 0 < |F| := abs_pos.mpr hF
  have hC1 : |F| ≤ C := by
    have h := key 1 one_pos
    rwa [mul_one] at h
  have hCpos : 0 < C := lt_of_lt_of_le hFpos hC1
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have h2C : (0:ℝ) < 2 * C := by linarith
  have h2Cne : (2:ℝ) * C ≠ 0 := mul_ne_zero two_ne_zero hCne
  have hsmall := key (|F| / (2 * C)) (div_pos hFpos h2C)
  have hval2 : C * (|F| / (2 * C)) = |F| / 2 := by
    rw [← mul_div_assoc, div_eq_div_iff h2Cne two_ne_zero]
    ring
  rw [hval2] at hsmall
  linarith

/-- **A bare residual is not an error.** Over all stiffnesses `k > 0`, with no lower bound, no
constant `C` makes `C |k u - F|` a bound on the state error, and for `F ≠ 0` none makes it a
bound on the compliance error: the trial `u = F / k + 1` has residual `k`, state error `1` and
compliance error `|F|`. This combines `not_exists_residual_state_error_bound`, which holds for
every `F`, and `not_exists_residual_compliance_error_bound`. -/
lemma not_exists_residual_error_bound {F : ℝ} (hF : F ≠ 0) :
    (¬ ∃ C : ℝ, ∀ k u : ℝ, 0 < k → |tipDisplacement F k - u| ≤ C * |k * u - F|) ∧
      ¬ ∃ C : ℝ, ∀ k u : ℝ, 0 < k → |compliance F k - F * u| ≤ C * |k * u - F| := by
  exact ⟨not_exists_residual_state_error_bound F, not_exists_residual_compliance_error_bound hF⟩

end Statistics.DesignSensitivity

end
