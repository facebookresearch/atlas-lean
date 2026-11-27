/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import PhyslibExt.EarthScience.BlackbodyFlux
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Enclosure radiation: black power conservation, gray radiosity and parallel plates

## i. Overview

A closed enclosure of finitely many diffuse black surfaces `i : ι` with areas `A i > 0`, view
factors `F i j ≥ 0` (fraction of the radiation leaving `i` that arrives at `j`), unit row sums and
area reciprocity `A i * F i j = A j * F j i`. Surface temperatures `T i ≥ 0` are absolute and
`σ > 0` is the Stefan-Boltzmann constant; the law `σ T⁴` is an adopted input.

The net power leaving surface `i` is `P i = ∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4)` (watts);
it includes the area, and the net flux is `P i / A i` (watts per square metre). Positive `P i`
is a net outflow. Results: total power cancels, an isothermal neighbourhood exchanges nothing,
a hottest surface has nonnegative outflow, and `P i` is emission minus absorption of the
Lambertian blackbody flux.

Gray surfaces: with emissivities `0 < ε i ≤ 1` (absorptivity `ε i`, reflectivity `1 - ε i`) the
radiosities `J` solve `J i = ε i * σ * T i ^ 4 + (1 - ε i) * ∑ j, F i j * J j`. The system matrix
`1 - diag (1 - ε) * F` is strictly row diagonally dominant because every `ε i > 0`, so
`det_ne_zero_of_sum_row_lt_diag` makes the solution exist and be unique. The gray net power
`∑ j, A i * F i j * (J i - J j)` is radiosity minus irradiation times area and emission minus
absorption; the gray powers sum to zero; with every `ε i = 1` the radiosity is `σ T⁴` and the
gray power is `netPower`. With every `ε i = 0` each constant radiosity solves the equations.

Parallel plates, in the infinite-plane idealization: two gray plates of equal area `A` that see
only each other, with no radiation escaping through the edges, have view factors
`F 0 1 = F 1 0 = 1` and `F 0 0 = F 1 1 = 0`. These are the view factors of infinite parallel
planes, the limit of a vanishing gap-to-size ratio. Finite plates at a positive gap lose part of
their radiation through the edges and have `F 0 1 < 1`, so the parallel-plate results are exact
for the idealization and only an approximation for finite plates. Solving the two radiosity rows
of the idealization gives the net power leaving plate `0` as
`σ A (T 0⁴ - T 1⁴) / (1 / ε 0 + 1 / ε 1 - 1)`, a power through the area `A` (the flux is the power
divided by `A`). The two powers sum to zero, swapping the temperatures reverses the sign, equal
temperatures exchange nothing and different temperatures exchange a nonzero power. These view
factors satisfy reciprocity only for equal areas.

## ii. Key results

- `HeatTransfer.EnclosureRadiation.sum_netPower_eq_zero`: the net powers of all surfaces
  in a black enclosure sum to zero.
- `HeatTransfer.EnclosureRadiation.netPower_eq_emitted_sub_absorbed`: net power is emitted
  hemispheric blackbody power minus absorbed power from every other surface.
- `HeatTransfer.EnclosureRadiation.netPower_nonneg_of_hottest`: a hottest surface has
  nonnegative net outflow.
- `HeatTransfer.EnclosureRadiation.existsUnique_isRadiosity`: the gray radiosities exist and are
  unique when every emissivity is positive.
- `HeatTransfer.EnclosureRadiation.sum_grayNetPower_eq_zero`: the gray net powers sum to zero.
- `HeatTransfer.EnclosureRadiation.isRadiosity_iff_of_emissivity_eq_one`,
  `HeatTransfer.EnclosureRadiation.grayNetPower_blackbody`: the black limit.
- `HeatTransfer.EnclosureRadiation.grayNetPower_parallelPlates`: in the infinite-plane
  idealization (unit view factors, no edge loss), the net power of two equal-area parallel gray
  plates is `parallelPlatePower`; for finite plates it is an approximation.
- `HeatTransfer.EnclosureRadiation.parallelPlatePower_swap`,
  `HeatTransfer.EnclosureRadiation.parallelPlatePower_self`,
  `HeatTransfer.EnclosureRadiation.parallelPlatePower_ne_zero`: sign reversal, zero exchange at
  equal temperature and nonzero exchange at different temperatures.

## iii. Table of contents

- A. Enclosure data and net power
- B. Conservation and sign results
- C. Gray enclosures: radiosity
- D. Gray net power: conservation and the black limit
- E. Equal-area parallel gray plates: the infinite-plane idealization

## iv. References

- The view-factor enclosure theory for diffuse black surfaces is classical radiative
  heat transfer (e.g. Incropera and DeWitt, *Fundamentals of Heat and Mass Transfer*,
  the enclosure-theory chapter); the hemispheric blackbody flux `σ T⁴` is
  `PhyslibExt.EarthScience.BlackbodyFlux`.
- Radiosity of opaque, diffuse, gray surfaces and the radiosity network: the same chapter of
  Incropera and DeWitt; M. F. Modest, *Radiative Heat Transfer*, the chapter on exchange between
  gray, diffuse surfaces.
- Exchange between two large (in the limit, infinite) parallel gray planes,
  `q = A σ (T₁⁴ - T₂⁴) / (1 / ε₁ + 1 / ε₂ - 1)` with `F₁₂ = 1`: the same chapter of Incropera and
  DeWitt, whose view factors for finite aligned parallel rectangles and coaxial parallel disks are
  below one at every positive gap.

## A. Enclosure data and net power
-/

@[expose] public section

namespace HeatTransfer.EnclosureRadiation

variable {ι : Type*} [Fintype ι]

/-- Diffuse black enclosure data on the finite surface set `ι`: areas `A i > 0`, view factors
`F i j ≥ 0`, unit row sums `∑ j, F i j = 1` (closure: an opening must be an explicit node) and
area reciprocity `A i * F i j = A j * F j i`. -/
structure IsBlackEnclosure (A : ι → ℝ) (F : ι → ι → ℝ) : Prop where
  area_pos : ∀ i, 0 < A i
  viewFactor_nonneg : ∀ i j, 0 ≤ F i j
  rowSum_eq_one : ∀ i, ∑ j, F i j = 1
  reciprocity : ∀ i j, A i * F i j = A j * F j i

/-- Net radiative power leaving surface `i`:
`P i = ∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4)`. Positive values are a net outflow. -/
def netPower (σ : ℝ) (A : ι → ℝ) (F : ι → ι → ℝ) (T : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4)

/-- Net radiative flux leaving surface `i`: the net power per unit area, `P i / A i`. -/
noncomputable def netFlux (σ : ℝ) (A : ι → ℝ) (F : ι → ι → ℝ) (T : ι → ℝ) (i : ι) : ℝ :=
  netPower σ A F T i / A i

/-- The net flux is the power with the area removed:
`P i / A i = ∑ j, F i j * σ * (T i ^ 4 - T j ^ 4)` for `A i > 0`. -/
lemma netFlux_eq {σ : ℝ} {A : ι → ℝ} {F : ι → ι → ℝ} {T : ι → ℝ} {i : ι} (hA : 0 < A i) :
    netFlux σ A F T i = ∑ j, F i j * σ * (T i ^ 4 - T j ^ 4) := by
  unfold netFlux netPower
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have hA' : A i ≠ 0 := ne_of_gt hA
  field_simp

/-- Emission minus absorption: in a black enclosure with `σ > 0` and absolute temperatures
`T ≥ 0`, the net power of surface `i` is its area times the hemispheric integral of its
Lambertian intensity `σ T i ^ 4 / π`, minus the power `A j * F j i` times the same integral for
`T j`, arriving from every surface `j` and absorbed. -/
lemma netPower_eq_emitted_sub_absorbed {σ : ℝ} {A : ι → ℝ} {F : ι → ι → ℝ} {T : ι → ℝ}
    (hE : IsBlackEnclosure A F) (hσ : 0 < σ) (hT : ∀ i, 0 ≤ T i) (i : ι) :
    netPower σ A F T i =
      A i * (∫ θ in (0 : ℝ)..(Real.pi / 2),
          (σ * T i ^ 4 / Real.pi) * Real.cos θ * (2 * Real.pi * Real.sin θ)) -
        ∑ j, A j * F j i * (∫ θ in (0 : ℝ)..(Real.pi / 2),
          (σ * T j ^ 4 / Real.pi) * Real.cos θ * (2 * Real.pi * Real.sin θ)) := by
  have hσ0 : 0 ≤ σ := le_of_lt hσ
  have hint : ∀ k, (∫ θ in (0 : ℝ)..(Real.pi / 2),
        (σ * T k ^ 4 / Real.pi) * Real.cos θ * (2 * Real.pi * Real.sin θ))
      = σ * T k ^ 4 :=
    fun k => EarthScience.integrated_blackbody_flux_eq hσ0 (hT k)
  simp only [hint]
  unfold netPower
  have hrow := hE.rowSum_eq_one i
  have hsplit : (∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4))
      = (∑ j, A i * F i j * σ * T i ^ 4) - ∑ j, A i * F i j * σ * T j ^ 4 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hfirst : (∑ j, A i * F i j * σ * T i ^ 4) = A i * (σ * T i ^ 4) := by
    calc (∑ j, A i * F i j * σ * T i ^ 4)
        = (∑ j, F i j) * (A i * σ * T i ^ 4) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = A i * (σ * T i ^ 4) := by
          rw [hrow, one_mul]
          ring
  have hsecond : (∑ j, A i * F i j * σ * T j ^ 4)
      = ∑ j, A j * F j i * (σ * T j ^ 4) := by
    apply Finset.sum_congr rfl
    intro j _
    have hr := hE.reciprocity i j
    calc A i * F i j * σ * T j ^ 4
        = (A i * F i j) * (σ * T j ^ 4) := by ring
      _ = (A j * F j i) * (σ * T j ^ 4) := by rw [hr]
      _ = A j * F j i * (σ * T j ^ 4) := by ring
  rw [hsplit, hfirst, hsecond]

/-! ## B. Conservation and sign results -/

/-- Power conservation: the net powers of a black enclosure sum to zero. Only reciprocity is
used; no sign condition on `σ` or `T` is needed. -/
lemma sum_netPower_eq_zero {A : ι → ℝ} {F : ι → ι → ℝ} (hE : IsBlackEnclosure A F)
    (σ : ℝ) (T : ι → ℝ) :
    ∑ i, netPower σ A F T i = 0 := by
  unfold netPower
  have hsym : ∀ i j, A j * F j i * σ * (T j ^ 4 - T i ^ 4)
      = -(A i * F i j * σ * (T i ^ 4 - T j ^ 4)) := by
    intro i j
    have hrec := hE.reciprocity i j
    rw [← hrec]
    ring
  have hcomm : (∑ i, ∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4))
      = ∑ i, ∑ j, A j * F j i * σ * (T j ^ 4 - T i ^ 4) := Finset.sum_comm
  have hneg : (∑ i, ∑ j, A j * F j i * σ * (T j ^ 4 - T i ^ 4))
      = -(∑ i, ∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact hsym i j
  have hself : (∑ i, ∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4))
      = -(∑ i, ∑ j, A i * F i j * σ * (T i ^ 4 - T j ^ 4)) := hcomm.trans hneg
  linarith

/-- Zero exchange at equal temperatures: if every surface has the temperature of surface `i`,
the net power of `i` is zero. -/
lemma netPower_eq_zero_of_temp_eq {σ : ℝ} {A : ι → ℝ} {F : ι → ι → ℝ} {T : ι → ℝ} {i : ι}
    (hT : ∀ j, T j = T i) :
    netPower σ A F T i = 0 := by
  unfold netPower
  apply Finset.sum_eq_zero
  intro j _
  rw [hT j, sub_self, mul_zero]

/-- A hottest surface has nonnegative net outflow: with `σ > 0`, absolute temperatures `T ≥ 0`
and `T j ≤ T k` for every `j`, the net power of `k` is `≥ 0`. -/
lemma netPower_nonneg_of_hottest {σ : ℝ} {A : ι → ℝ} {F : ι → ι → ℝ} {T : ι → ℝ}
    (hE : IsBlackEnclosure A F) (hσ : 0 < σ) (hT : ∀ i, 0 ≤ T i) {k : ι}
    (hk : ∀ j, T j ≤ T k) :
    0 ≤ netPower σ A F T k := by
  unfold netPower
  apply Finset.sum_nonneg
  intro j _
  have hA : 0 ≤ A k := le_of_lt (hE.area_pos k)
  have hF : 0 ≤ F k j := hE.viewFactor_nonneg k j
  have hs : 0 ≤ σ := le_of_lt hσ
  have hpow : T j ^ 4 ≤ T k ^ 4 := pow_le_pow_left₀ (hT j) (hk j) 4
  have hsub : 0 ≤ T k ^ 4 - T j ^ 4 := sub_nonneg.mpr hpow
  exact mul_nonneg (mul_nonneg (mul_nonneg hA hF) hs) hsub


/-! ## C. Gray enclosures: radiosity -/

open scoped Matrix

/-- The radiosity equations of a diffuse-gray enclosure: surface `i` leaves with its emitted
power `ε i * σ * T i ^ 4` plus the reflected fraction `1 - ε i` of its irradiation
`∑ j, F i j * J j`, so `J i = ε i * σ * T i ^ 4 + (1 - ε i) * ∑ j, F i j * J j` (watts per
square metre). -/
def IsRadiosity (σ : ℝ) (ε : ι → ℝ) (F : ι → ι → ℝ) (T J : ι → ℝ) : Prop :=
  ∀ i, J i = ε i * σ * T i ^ 4 + (1 - ε i) * ∑ j, F i j * J j

/-- The radiosity matrix `M = 1 - diag (1 - ε) * F`, with entries
`M i j = δ i j - (1 - ε i) * F i j`. -/
def radiosityMatrix [DecidableEq ι] (ε : ι → ℝ) (F : ι → ι → ℝ) : Matrix ι ι ℝ :=
  1 - Matrix.of fun i j => (1 - ε i) * F i j

/-- Matrix form of the radiosity equations: `M *ᵥ J = ε σ T⁴`. -/
lemma radiosityMatrix_mulVec_eq_iff [DecidableEq ι] {σ : ℝ} {ε : ι → ℝ} {F : ι → ι → ℝ}
    {T J : ι → ℝ} :
    radiosityMatrix ε F *ᵥ J = (fun i => ε i * σ * T i ^ 4) ↔ IsRadiosity σ ε F T J := by
  have hfac : ∀ i : ι, (∑ j, (1 - ε i) * F i j * J j)
      = (1 - ε i) * ∑ j, F i j * J j := by
    intro i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hentry : ∀ i : ι, (radiosityMatrix ε F *ᵥ J) i
      = J i - (1 - ε i) * ∑ j, F i j * J j := by
    intro i
    unfold radiosityMatrix
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    change _ - ∑ j, (1 - ε i) * F i j * J j = _
    rw [hfac i]
  constructor
  · intro h i
    have hi := congrFun h i
    rw [hentry i] at hi
    linear_combination hi
  · intro h
    funext i
    rw [hentry i]
    linear_combination h i

/-- Strict row diagonal dominance: for the view factors of an enclosure and emissivities
`0 < ε i ≤ 1`, row `k` of the radiosity matrix has off-diagonal mass
`(1 - ε k) * (1 - F k k)`, strictly below the diagonal entry `1 - (1 - ε k) * F k k`. -/
lemma radiosityMatrix_sum_row_lt_diag [DecidableEq ι] {A : ι → ℝ} {F : ι → ι → ℝ}
    {ε : ι → ℝ} (hE : IsBlackEnclosure A F) (hε : ∀ i, 0 < ε i) (hε₁ : ∀ i, ε i ≤ 1)
    (k : ι) :
    ∑ j ∈ Finset.univ.erase k, ‖radiosityMatrix ε F k j‖ < ‖radiosityMatrix ε F k k‖ := by
  have h1e_nonneg : 0 ≤ 1 - ε k := by
    have := hε₁ k
    linarith
  have hFkk_le : F k k ≤ 1 := by
    have h := Finset.single_le_sum (fun j _ => hE.viewFactor_nonneg k j)
      (Finset.mem_univ k)
    rw [hE.rowSum_eq_one k] at h
    exact h
  have hdiag_nonneg : 0 ≤ 1 - (1 - ε k) * F k k := by
    have h1e_le : 1 - ε k ≤ 1 := by
      have := hε k
      linarith
    have hF_nonneg := hE.viewFactor_nonneg k k
    have hprod : (1 - ε k) * F k k ≤ 1 := by
      calc (1 - ε k) * F k k ≤ 1 * F k k :=
            mul_le_mul_of_nonneg_right h1e_le hF_nonneg
        _ = F k k := one_mul _
        _ ≤ 1 := hFkk_le
    linarith
  have hM : ∀ i j : ι, radiosityMatrix ε F i j
      = (if i = j then (1 : ℝ) else 0) - (1 - ε i) * F i j := by
    intro i j
    simp [radiosityMatrix, Matrix.one_apply]
  have hoff : ∀ j ∈ Finset.univ.erase k,
      ‖radiosityMatrix ε F k j‖ = (1 - ε k) * F k j := by
    intro j hj
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    have hkj : k ≠ j := fun h => hjk h.symm
    rw [hM k j, ite_eq_right hkj, zero_sub, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (mul_nonneg h1e_nonneg (hE.viewFactor_nonneg k j))]
  have hdiag : ‖radiosityMatrix ε F k k‖ = 1 - (1 - ε k) * F k k := by
    rw [hM k k, ite_eq_left rfl, Real.norm_eq_abs, abs_of_nonneg hdiag_nonneg]
  rw [hdiag]
  have hsum : ∑ j ∈ Finset.univ.erase k, ‖radiosityMatrix ε F k j‖
      = (1 - ε k) * (1 - F k k) := by
    have hcongr : ∑ j ∈ Finset.univ.erase k, ‖radiosityMatrix ε F k j‖
        = ∑ j ∈ Finset.univ.erase k, (1 - ε k) * F k j :=
      Finset.sum_congr rfl (fun j hj => hoff j hj)
    rw [hcongr, ← Finset.mul_sum]
    congr 1
    have hrow := hE.rowSum_eq_one k
    have hadd := Finset.add_sum_erase Finset.univ (fun j => F k j) (Finset.mem_univ k)
    linarith
  rw [hsum]
  have hεpos := hε k
  have hdiff : (1 - (1 - ε k) * F k k) - (1 - ε k) * (1 - F k k) = ε k := by
    ring
  linarith

/-- The radiosity matrix is invertible: `det_ne_zero_of_sum_row_lt_diag` applied to the strict
row diagonal dominance. -/
lemma radiosityMatrix_det_ne_zero [DecidableEq ι] {A : ι → ℝ} {F : ι → ι → ℝ} {ε : ι → ℝ}
    (hE : IsBlackEnclosure A F) (hε : ∀ i, 0 < ε i) (hε₁ : ∀ i, ε i ≤ 1) :
    (radiosityMatrix ε F).det ≠ 0 := by
  exact det_ne_zero_of_sum_row_lt_diag
    (fun k => radiosityMatrix_sum_row_lt_diag hE hε hε₁ k)

/-- Existence and uniqueness of the gray radiosities: in an enclosure whose surfaces all have
emissivity `0 < ε i ≤ 1`, the radiosity equations have exactly one solution, for every
temperature field and every `σ`. -/
lemma existsUnique_isRadiosity {A : ι → ℝ} {F : ι → ι → ℝ} {ε : ι → ℝ}
    (hE : IsBlackEnclosure A F) (hε : ∀ i, 0 < ε i) (hε₁ : ∀ i, ε i ≤ 1) (σ : ℝ)
    (T : ι → ℝ) :
    ∃! J, IsRadiosity σ ε F T J := by
  classical
  have hdet : (radiosityMatrix ε F).det ≠ 0 :=
    radiosityMatrix_det_ne_zero hE hε hε₁
  have hU : IsUnit (radiosityMatrix ε F).det := isUnit_iff_ne_zero.mpr hdet
  have hleft : (radiosityMatrix ε F)⁻¹ * radiosityMatrix ε F = 1 :=
    Matrix.nonsing_inv_mul _ hU
  have hright : radiosityMatrix ε F * (radiosityMatrix ε F)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hU
  have hex : ∃! J, radiosityMatrix ε F *ᵥ J = (fun i => ε i * σ * T i ^ 4) := by
    refine ⟨(radiosityMatrix ε F)⁻¹ *ᵥ (fun i => ε i * σ * T i ^ 4), ?_, ?_⟩
    · change radiosityMatrix ε F *ᵥ _ = _
      rw [Matrix.mulVec_mulVec, hright, Matrix.one_mulVec]
    · intro J hJ
      have h1 : (radiosityMatrix ε F)⁻¹ *ᵥ (radiosityMatrix ε F *ᵥ J)
          = (radiosityMatrix ε F)⁻¹ *ᵥ (fun i => ε i * σ * T i ^ 4) := by
        rw [hJ]
      rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] at h1
      exact h1
  obtain ⟨J0, hJ0, huniq⟩ := hex
  refine ⟨J0, radiosityMatrix_mulVec_eq_iff.mp hJ0, ?_⟩
  intro J hJ
  apply huniq
  exact radiosityMatrix_mulVec_eq_iff.mpr hJ

/-! ## D. Gray net power: conservation and the black limit -/

/-- Net radiative power leaving gray surface `i` with radiosities `J`:
`q i = ∑ j, A i * F i j * (J i - J j)` (watts), the black `netPower` with `σ * T ^ 4` replaced
by the radiosity. Positive values are a net outflow. -/
def grayNetPower (A : ι → ℝ) (F : ι → ι → ℝ) (J : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, A i * F i j * (J i - J j)

/-- Radiosity minus irradiation: in an enclosure, `q i = A i * (J i - ∑ j, F i j * J j)`. -/
lemma grayNetPower_eq_radiosity_sub_irradiation {A : ι → ℝ} {F : ι → ι → ℝ}
    (hE : IsBlackEnclosure A F) (J : ι → ℝ) (i : ι) :
    grayNetPower A F J i = A i * (J i - ∑ j, F i j * J j) := by
  unfold grayNetPower
  have h1 : ∀ j : ι, A i * F i j * (J i - J j)
      = A i * (F i j * J i) - A i * (F i j * J j) := fun j => by ring
  simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hrow : (∑ j, F i j * J i) = J i := by
    rw [← Finset.sum_mul, hE.rowSum_eq_one, one_mul]
  rw [hrow]
  ring

/-- Emission minus absorption: for a radiosity solution in an enclosure, the net power of gray
surface `i` is `A i * ε i * (σ * T i ^ 4 - ∑ j, F i j * J j)`, emitted power minus the absorbed
fraction `ε i` of the irradiation. -/
lemma grayNetPower_eq_emitted_sub_absorbed {A : ι → ℝ} {F : ι → ι → ℝ} {ε : ι → ℝ} {σ : ℝ}
    {T J : ι → ℝ} (hE : IsBlackEnclosure A F) (hJ : IsRadiosity σ ε F T J) (i : ι) :
    grayNetPower A F J i = A i * ε i * (σ * T i ^ 4 - ∑ j, F i j * J j) := by
  rw [grayNetPower_eq_radiosity_sub_irradiation hE J i, hJ i]
  ring

/-- Power conservation: the gray net powers of an enclosure sum to zero, for every radiosity
field. Only reciprocity is used. -/
lemma sum_grayNetPower_eq_zero {A : ι → ℝ} {F : ι → ι → ℝ} (hE : IsBlackEnclosure A F)
    (J : ι → ℝ) :
    ∑ i, grayNetPower A F J i = 0 := by
  unfold grayNetPower
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  have hrec : ∀ i j : ι, A i * F i j * J j = A j * F j i * J j := by
    intro i j
    rw [hE.reciprocity i j]
  have hswap : (∑ i, ∑ j, A i * F i j * J j) = ∑ i, ∑ j, A j * F j i * J j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hrec]
  rw [hswap]
  exact Finset.sum_comm

/-- Black limit, radiosities: with every emissivity one, `J` solves the radiosity equations
exactly when it is the blackbody emissive power, `J i = σ * T i ^ 4`. -/
lemma isRadiosity_iff_of_emissivity_eq_one {σ : ℝ} {ε : ι → ℝ} {F : ι → ι → ℝ}
    {T J : ι → ℝ} (hε : ∀ i, ε i = 1) :
    IsRadiosity σ ε F T J ↔ ∀ i, J i = σ * T i ^ 4 := by
  simp [IsRadiosity, hε]

/-- Black limit, power: at the blackbody radiosities `J i = σ * T i ^ 4` the gray net power is
the black `netPower`. -/
lemma grayNetPower_blackbody (σ : ℝ) (A : ι → ℝ) (F : ι → ι → ℝ) (T : ι → ℝ) (i : ι) :
    grayNetPower A F (fun j => σ * T j ^ 4) i = netPower σ A F T i := by
  unfold grayNetPower netPower
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Reflectors only: with every emissivity zero, each constant radiosity solves the equations of
an enclosure, whatever the temperatures. -/
lemma isRadiosity_const_of_emissivity_eq_zero {A : ι → ℝ} {F : ι → ι → ℝ} {ε : ι → ℝ}
    (hE : IsBlackEnclosure A F) (hε : ∀ i, ε i = 0) (σ : ℝ) (T : ι → ℝ) (c : ℝ) :
    IsRadiosity σ ε F T (fun _ => c) := by
  intro i
  simp only [hε i, zero_mul, zero_add, sub_zero, one_mul]
  rw [← Finset.sum_mul, hE.rowSum_eq_one, one_mul]

/-- Hence a nonempty reflector-only enclosure has no unique radiosity: positive emissivity
cannot be dropped from `existsUnique_isRadiosity`. -/
lemma not_existsUnique_isRadiosity_of_emissivity_eq_zero [Nonempty ι] {A : ι → ℝ}
    {F : ι → ι → ℝ} {ε : ι → ℝ} (hE : IsBlackEnclosure A F) (hε : ∀ i, ε i = 0) (σ : ℝ)
    (T : ι → ℝ) :
    ¬ ∃! J, IsRadiosity σ ε F T J := by
  intro h
  obtain ⟨J, -, huniq⟩ := h
  have h0 := isRadiosity_const_of_emissivity_eq_zero hE hε σ T 0
  have h1 := isRadiosity_const_of_emissivity_eq_zero hE hε σ T 1
  have e0 := huniq _ h0
  have e1 := huniq _ h1
  have h01 : (fun _ : ι => (0 : ℝ)) = fun _ => (1 : ℝ) := e0.trans e1.symm
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hcontra := congrFun h01 i
  norm_num at hcontra

/-! ## E. Equal-area parallel gray plates: the infinite-plane idealization

Every result of this section concerns two plates that see only each other: the view factors
`parallelPlateViewFactor` are those of infinite parallel planes, with no radiation escaping
through the edges. The results are exact for this idealization. Finite plates at a positive gap
have `F 0 1 < 1`, so applying the results to them is an approximation.
-/

/-- View factors of two equal-area parallel plates in the infinite-plane idealization: all
radiation leaving one plate reaches the other, `F 0 1 = F 1 0 = 1`, and a flat plate does not
see itself, `F 0 0 = F 1 1 = 0`. These are the view factors of infinite parallel planes, the limit
of a vanishing gap-to-size ratio with no loss through the edges; finite plates at a positive gap
have `F 0 1 < 1`, and using these view factors for them is an approximation. -/
def parallelPlateViewFactor : Fin 2 → Fin 2 → ℝ :=
  ![![0, 1], ![1, 0]]

/-- Net radiative power from plate 1 to plate 2 of two equal-area parallel gray plates in the
infinite-plane idealization (`parallelPlateViewFactor`), with emissivities `ε₁, ε₂`, absolute
temperatures `T₁, T₂` and plate area `A`: `σ * A * (T₁ ^ 4 - T₂ ^ 4) / (1 / ε₁ + 1 / ε₂ - 1)`
(watts). Positive values are a net outflow from plate 1. It is the power through the area `A`,
not a flux. For finite plates, whose view factor is below one, it is an approximation. -/
noncomputable def parallelPlatePower (σ A ε₁ ε₂ T₁ T₂ : ℝ) : ℝ :=
  σ * A * (T₁ ^ 4 - T₂ ^ 4) / (1 / ε₁ + 1 / ε₂ - 1)

/-- With the idealized view factors, equal-area parallel plates form an enclosure: positive areas,
nonnegative view factors with unit row sums (no radiation leaves through the edges), and
reciprocity `A * F 0 1 = A * F 1 0`, which holds because the areas are equal. -/
lemma isBlackEnclosure_parallelPlates {A : ℝ} (hA : 0 < A) :
    IsBlackEnclosure (fun _ : Fin 2 => A) parallelPlateViewFactor := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact hA
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [parallelPlateViewFactor]
  · intro i
    fin_cases i <;> simp [parallelPlateViewFactor, Fin.sum_univ_two]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [parallelPlateViewFactor]

/-- Unequal areas need other view factors: for `A₀ ≠ A₁` the view factors
`F 0 1 = F 1 0 = 1` violate reciprocity, so the parallel-plate formula is not a general
two-surface enclosure formula. -/
lemma not_isBlackEnclosure_parallelPlates_of_area_ne {A₀ A₁ : ℝ} (h : A₀ ≠ A₁) :
    ¬ IsBlackEnclosure ![A₀, A₁] parallelPlateViewFactor := by
  intro hE
  have hrec := hE.reciprocity 0 1
  simp [parallelPlateViewFactor] at hrec
  exact h (by linarith)

/-- The radiosities of two parallel gray plates in the infinite-plane idealization, with
emissivities `0 < ε i ≤ 1`, exist and are unique, for every temperature field and every `σ`. -/
lemma existsUnique_isRadiosity_parallelPlates {ε : Fin 2 → ℝ} (hε : ∀ i, 0 < ε i)
    (hε₁ : ∀ i, ε i ≤ 1) (σ : ℝ) (T : Fin 2 → ℝ) :
    ∃! J, IsRadiosity σ ε parallelPlateViewFactor T J := by
  exact existsUnique_isRadiosity (isBlackEnclosure_parallelPlates one_pos) hε hε₁ σ T

/-- The parallel-plate formula from the radiosity equations of the infinite-plane idealization:
for emissivities `0 < ε i ≤ 1` and radiosities `J` of the two plates with the view factors
`parallelPlateViewFactor`, the net power leaving plate `0` is
`σ * A * (T 0 ^ 4 - T 1 ^ 4) / (1 / ε 0 + 1 / ε 1 - 1)`. The identity is exact for the
idealization; for finite plates, whose view factor is below one, the formula is an
approximation. -/
lemma grayNetPower_parallelPlates {A σ : ℝ} {ε T J : Fin 2 → ℝ} (hε : ∀ i, 0 < ε i)
    (hε₁ : ∀ i, ε i ≤ 1) (hJ : IsRadiosity σ ε parallelPlateViewFactor T J) :
    grayNetPower (fun _ : Fin 2 => A) parallelPlateViewFactor J 0 =
      parallelPlatePower σ A (ε 0) (ε 1) (T 0) (T 1) := by
  have s0 : ∑ j, parallelPlateViewFactor 0 j * J j = J 1 := by
    rw [Fin.sum_univ_two]
    simp [parallelPlateViewFactor]
  have s1 : ∑ j, parallelPlateViewFactor 1 j * J j = J 0 := by
    rw [Fin.sum_univ_two]
    simp [parallelPlateViewFactor]
  have h0 : J 0 = ε 0 * σ * T 0 ^ 4 + (1 - ε 0) * J 1 := by
    have h := hJ 0
    rw [s0] at h
    exact h
  have h1 : J 1 = ε 1 * σ * T 1 ^ 4 + (1 - ε 1) * J 0 := by
    have h := hJ 1
    rw [s1] at h
    exact h
  have hq : grayNetPower (fun _ : Fin 2 => A) parallelPlateViewFactor J 0
      = A * (J 0 - J 1) := by
    unfold grayNetPower
    rw [Fin.sum_univ_two]
    simp [parallelPlateViewFactor]
  have hd : (ε 0 + ε 1 - ε 0 * ε 1) * (J 0 - J 1)
      = ε 0 * ε 1 * σ * (T 0 ^ 4 - T 1 ^ 4) := by
    linear_combination (ε 1) * h0 - (ε 0) * h1
  have e0 : ε 0 ≠ 0 := ne_of_gt (hε 0)
  have e1 : ε 1 ≠ 0 := ne_of_gt (hε 1)
  have hε0pos : 0 < ε 0 := hε 0
  have hε1pos : 0 < ε 1 := hε 1
  have hD : (0 : ℝ) < 1 / ε 0 + 1 / ε 1 - 1 := by
    have g0 : (1 : ℝ) ≤ 1 / ε 0 := one_le_one_div (hε 0) (hε₁ 0)
    have g1 : (0 : ℝ) < 1 / ε 1 := by positivity
    linarith
  have hD' : (1 / ε 0 + 1 / ε 1 - 1) ≠ 0 := ne_of_gt hD
  rw [hq]
  unfold parallelPlatePower
  rw [eq_div_iff hD']
  field_simp
  linear_combination A * hd

/-- Conservation in the idealization: with no radiation escaping through the edges, the power
leaving plate `0` arrives at plate `1`; for every radiosity field the two net powers sum to
zero. -/
lemma grayNetPower_parallelPlates_add_eq_zero (A : ℝ) (J : Fin 2 → ℝ) :
    grayNetPower (fun _ : Fin 2 => A) parallelPlateViewFactor J 0 +
      grayNetPower (fun _ : Fin 2 => A) parallelPlateViewFactor J 1 = 0 := by
  have q0 : grayNetPower (fun _ : Fin 2 => A) parallelPlateViewFactor J 0
      = A * (J 0 - J 1) := by
    unfold grayNetPower
    rw [Fin.sum_univ_two]
    simp [parallelPlateViewFactor]
  have q1 : grayNetPower (fun _ : Fin 2 => A) parallelPlateViewFactor J 1
      = A * (J 1 - J 0) := by
    unfold grayNetPower
    rw [Fin.sum_univ_two]
    simp [parallelPlateViewFactor]
  rw [q0, q1]
  ring

/-- Reciprocity: the formula read from plate 2 is the negative of the formula read from plate 1.
-/
lemma parallelPlatePower_comm (σ A ε₁ ε₂ T₁ T₂ : ℝ) :
    parallelPlatePower σ A ε₂ ε₁ T₂ T₁ = -parallelPlatePower σ A ε₁ ε₂ T₁ T₂ := by
  unfold parallelPlatePower
  ring

/-- Sign reversal: swapping the two plate temperatures, with the emissivities kept, reverses the
net power. -/
lemma parallelPlatePower_swap (σ A ε₁ ε₂ T₁ T₂ : ℝ) :
    parallelPlatePower σ A ε₁ ε₂ T₂ T₁ = -parallelPlatePower σ A ε₁ ε₂ T₁ T₂ := by
  unfold parallelPlatePower
  ring

/-- Zero exchange at equal temperature. -/
lemma parallelPlatePower_self (σ A ε₁ ε₂ T : ℝ) : parallelPlatePower σ A ε₁ ε₂ T T = 0 := by
  unfold parallelPlatePower
  ring

/-- Equilibrium from the radiosity equations of the idealization: plates at equal temperature
exchange no net power. -/
lemma grayNetPower_parallelPlates_eq_zero_of_temp_eq {A σ : ℝ} {ε T J : Fin 2 → ℝ}
    (hε : ∀ i, 0 < ε i) (hε₁ : ∀ i, ε i ≤ 1) (hJ : IsRadiosity σ ε parallelPlateViewFactor T J)
    (hT : T 0 = T 1) :
    grayNetPower (fun _ : Fin 2 => A) parallelPlateViewFactor J 0 = 0 := by
  rw [grayNetPower_parallelPlates hε hε₁ hJ, hT]
  exact parallelPlatePower_self σ A (ε 0) (ε 1) (T 1)

/-- The hotter plate loses power: with `σ > 0`, `A > 0`, emissivities in `(0, 1]` and absolute
temperatures `0 ≤ T₂ < T₁`, the net power from plate 1 is positive. -/
lemma parallelPlatePower_pos {σ A ε₁ ε₂ T₁ T₂ : ℝ} (hσ : 0 < σ) (hA : 0 < A) (hε₁ : 0 < ε₁)
    (hε₁' : ε₁ ≤ 1) (hε₂ : 0 < ε₂) (hε₂' : ε₂ ≤ 1) (hT₂ : 0 ≤ T₂) (hT : T₂ < T₁) :
    0 < parallelPlatePower σ A ε₁ ε₂ T₁ T₂ := by
  have hpow : T₂ ^ 4 < T₁ ^ 4 := pow_lt_pow_left₀ hT hT₂ (by norm_num)
  have hsub : (0 : ℝ) < T₁ ^ 4 - T₂ ^ 4 := sub_pos.mpr hpow
  have hnum : (0 : ℝ) < σ * A * (T₁ ^ 4 - T₂ ^ 4) := by positivity
  have hden : (0 : ℝ) < 1 / ε₁ + 1 / ε₂ - 1 := by
    have g1 : (1 : ℝ) ≤ 1 / ε₁ := one_le_one_div hε₁ hε₁'
    have g2 : (1 : ℝ) ≤ 1 / ε₂ := one_le_one_div hε₂ hε₂'
    linarith
  unfold parallelPlatePower
  exact div_pos hnum hden

/-- Different temperatures exchange a nonzero power: with `σ > 0`, `A > 0`, emissivities in
`(0, 1]` and absolute temperatures `T₁ ≠ T₂`, the net power is nonzero. -/
lemma parallelPlatePower_ne_zero {σ A ε₁ ε₂ T₁ T₂ : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (hε₁ : 0 < ε₁) (hε₁' : ε₁ ≤ 1) (hε₂ : 0 < ε₂) (hε₂' : ε₂ ≤ 1) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (hT : T₁ ≠ T₂) :
    parallelPlatePower σ A ε₁ ε₂ T₁ T₂ ≠ 0 := by
  have hpow : T₁ ^ 4 ≠ T₂ ^ 4 := by
    rcases lt_or_gt_of_ne hT with h | h
    · exact ne_of_lt (pow_lt_pow_left₀ h hT₁ (by norm_num))
    · exact ne_of_gt (pow_lt_pow_left₀ h hT₂ (by norm_num))
  have hnum : σ * A * (T₁ ^ 4 - T₂ ^ 4) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ne_of_gt hσ) (ne_of_gt hA)) (sub_ne_zero.mpr hpow)
  have hden : (1 / ε₁ + 1 / ε₂ - 1) ≠ 0 := by
    have g1 : (1 : ℝ) ≤ 1 / ε₁ := one_le_one_div hε₁ hε₁'
    have g2 : (1 : ℝ) ≤ 1 / ε₂ := one_le_one_div hε₂ hε₂'
    have hpos : (0 : ℝ) < 1 / ε₁ + 1 / ε₂ - 1 := by linarith
    exact ne_of_gt hpos
  unfold parallelPlatePower
  exact div_ne_zero hnum hden

/-- Power, not flux: dividing the net power by the plate area `A > 0` gives the net flux
`σ * (T₁ ^ 4 - T₂ ^ 4) / (1 / ε₁ + 1 / ε₂ - 1)` (watts per square metre). -/
lemma parallelPlatePower_div_area {σ A ε₁ ε₂ T₁ T₂ : ℝ} (hA : 0 < A) :
    parallelPlatePower σ A ε₁ ε₂ T₁ T₂ / A = σ * (T₁ ^ 4 - T₂ ^ 4) / (1 / ε₁ + 1 / ε₂ - 1) := by
  have hA' : A ≠ 0 := ne_of_gt hA
  unfold parallelPlatePower
  field_simp

end HeatTransfer.EnclosureRadiation
