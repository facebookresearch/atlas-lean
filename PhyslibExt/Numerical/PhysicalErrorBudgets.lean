/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.ODE.FiniteElement1D
public import PhyslibExt.Elasticity.PrismaticMembers

/-!
# Physical bar pullback of the one-dimensional P1 error estimates

## i. Overview

A bar of length `L > 0` and constant axial rigidity `EA > 0`, fixed at both ends, carries the
uniform axial load `q`. Its displacement `axialDisplacement EA L q x = q * x * (L - x) / (2 * EA)`
(the fixed-fixed bar of `PhyslibExt.Elasticity.PrismaticMembers`) is the amplitude
`α = q * L ^ 2 / (2 * EA)` times the unit profile `û ξ = ξ * (1 - ξ)` at `ξ = x / L`, and `û` is
a classical solution of the unit problem `-û'' = 2`, `û 0 = û 1 = 0`, of
`MathlibExt.Analysis.ODE.FiniteElement1D`.

For a partition `P` of `[0, 1]`, the physical P1 reconstruction is `u_h x = α * (I_P û) (x / L)`,
where `I_P = interp P` is the existing nodal interpolant, which is also the P1 Galerkin solution
of the unit problem. The error `e = u - u_h` is `α` times the unit error `ê = û - I_P û` at
`x / L`, so changing variables gives

* `∫₀ᴸ EA (e')² = (EA / L) α² ∫₀¹ (ê')²` and `∫₀ᴸ e² = L α² ∫₀¹ ê²`,

with derivatives in the convention of the finite element module (`deriv` takes junk values at
the finitely many nodes, which no integral sees). The existing mesh estimates then bound both
physical quantities. Both the coordinate factor (`1 / L` in the strain, `L` in `dx`) and the
amplitude `α` are kept.

The normalization is inverted, `û ξ = α⁻¹ * u (L * ξ)`, only when `α ≠ 0`, that is `q ≠ 0`. The
zero load is treated directly: the physical solution, its reconstruction and the error are zero,
and the inverse map does not recover `û`.

Two uniform cells: the unit error vanishes at the nodes and is `1 / 16` at `ξ = 1 / 4`, with
`∫₀¹ (ê')² = 1 / 12` and `∫₀¹ ê² = 1 / 480`; physically `e (L / 4) = α / 16`, the energy is
`(EA / L) α² / 12` and the squared `L²` error is `L α² / 480`. For `EA = 2`, `L = 3`, `q = 4`:
`α = 9`, `e (3 / 4) = 9 / 16`, energy `9 / 2`, squared `L²` error `81 / 160`.

Model inputs: small-strain linear elastic bar with constant `EA`, both ends fixed, uniform load.
Non-goals: no second assembled finite element carrier, no variable `EA`, no claim that zero nodal
error means zero reconstructed error, and no empirical adequacy or system safety claim.

## ii. Key results

- `unitProfile_isClassicalSolution`, `axialDisplacement_eq_barAmplitude_mul`,
  `isFixedFixedSolution_barAmplitude_mul`, `physicalP1_zero_and_length`,
  `physicalP1_eq_galerkin`: the pullback, the physical load and the Dirichlet values.
- `barAmplitude_ne_zero_iff`, `unitProfile_eq_inv_barAmplitude_mul`, `zero_load`,
  `zero_load_inverse_ne`: inverse normalization only for `α ≠ 0`, and the zero-load branch.
- `physicalError_eq`, `integral_energy_physicalError`, `integral_sq_physicalError`: the two
  scaling identities.
- `integral_energy_physicalError_le_mesh`, `integral_sq_physicalError_le_mesh`: the physical
  instances of the existing mesh estimates.
- `twoCells`, `unitError_twoCells`, `physicalError_twoCells`: the two-cell record; the nonunit
  numeric fixture is in `PhyslibExtTest.Numerical.PhysicalErrorBudgetsTest`.

## iii. Table of contents

- A. Amplitude, unit profile and the physical reconstruction
- B. Inverse normalization and the zero load
- C. Scaling of the two error integrals
- D. The mesh estimates in physical form
- E. Two uniform cells

## iv. References

- S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, chapters 0 to 2 (the one-dimensional P1 method and its error estimates).
- T. J. R. Hughes, *The Finite Element Method: Linear Static and Dynamic Finite Element
  Analysis*, Dover, 2000, chapter 1 (the one-dimensional bar model problem).
- J. M. Gere and B. J. Goodno, *Mechanics of Materials*, 8th ed., 2013 (statically indeterminate
  bars under distributed axial loads).
-/

@[expose] public section

namespace PhysicalErrorBudgets

open MeasureTheory MathlibExt.Analysis.Integration MathlibExt.Analysis.ODE.FiniteElement1D
  Elasticity.PrismaticMembers

/-! ## A. Amplitude, unit profile and the physical reconstruction -/

/-- The amplitude `α = q * L ^ 2 / (2 * EA)` of the uniform-load fixed-fixed bar. -/
noncomputable def barAmplitude (EA L q : ℝ) : ℝ :=
  q * L ^ 2 / (2 * EA)

/-- The unit profile `û ξ = ξ * (1 - ξ)`. -/
def unitProfile (ξ : ℝ) : ℝ :=
  ξ * (1 - ξ)

/-- The unit error `ê = û - I_P û` of the existing nodal interpolant on a partition `P` of
`[0, 1]`. -/
noncomputable def unitError (P : Partition (0 : ℝ) 1) (ξ : ℝ) : ℝ :=
  unitProfile ξ - interp P unitProfile ξ

/-- The physical P1 reconstruction `u_h x = α * (I_P û) (x / L)`. -/
noncomputable def physicalP1 (P : Partition (0 : ℝ) 1) (EA L q x : ℝ) : ℝ :=
  barAmplitude EA L q * interp P unitProfile (x / L)

/-- The physical error `e x = u x - u_h x` of the reconstruction against the exact
displacement. -/
noncomputable def physicalError (P : Partition (0 : ℝ) 1) (EA L q x : ℝ) : ℝ :=
  axialDisplacement EA L q x - physicalP1 P EA L q x

/-- The derivative of the unit profile: `û' x = 1 - 2 * x`. -/
private lemma hasDerivAt_unitProfile (x : ℝ) : HasDerivAt unitProfile (1 - 2 * x) x := by
  have h : HasDerivAt (fun ξ : ℝ => ξ * (1 - ξ)) (1 * (1 - x) + x * -1) x :=
    (hasDerivAt_id' x).mul ((hasDerivAt_id' x).const_sub 1)
  exact h.congr_deriv (by ring)

/-- The derivative of the unit profile, as a function. -/
private lemma deriv_unitProfile : deriv unitProfile = fun x => 1 - 2 * x :=
  funext fun x => (hasDerivAt_unitProfile x).deriv

/-- The unit profile is `C²`. -/
private lemma contDiff_unitProfile : ContDiff ℝ 2 unitProfile := by
  unfold unitProfile
  fun_prop

/-- The unit profile is a classical solution of `-û'' = 2` with `û 0 = û 1 = 0`. -/
lemma unitProfile_isClassicalSolution : IsClassicalSolution (fun _ => 2) unitProfile := by
  refine ⟨contDiff_unitProfile, continuous_const, by simp [unitProfile], by simp [unitProfile],
    fun x _ => ?_⟩
  rw [deriv_unitProfile]
  have h : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-(2 * 1)) x :=
    ((hasDerivAt_id' x).const_mul 2).const_sub 1
  rw [h.deriv]
  norm_num

/-- Coordinate and amplitude pullback: `u x = α * û (x / L)` at every `x`. -/
lemma axialDisplacement_eq_barAmplitude_mul {L : ℝ} (hL : L ≠ 0) (EA q x : ℝ) :
    axialDisplacement EA L q x = barAmplitude EA L q * unitProfile (x / L) := by
  unfold axialDisplacement barAmplitude unitProfile
  rcases eq_or_ne EA 0 with h | h
  · simp [h]
  · field_simp

/-- The physical load is `q` and both ends are fixed: the pulled-back profile solves the
fixed-fixed bar problem `-(EA * u'') = q`, `u 0 = u L = 0`. -/
lemma isFixedFixedSolution_barAmplitude_mul {EA L : ℝ} (hL : 0 < L) (hEA : 0 < EA) (q : ℝ) :
    IsFixedFixedSolution EA L (fun _ => q)
      (fun x => barAmplitude EA L q * unitProfile (x / L)) := by
  have h : (fun x => barAmplitude EA L q * unitProfile (x / L)) = axialDisplacement EA L q :=
    funext fun x => (axialDisplacement_eq_barAmplitude_mul hL.ne' EA q x).symm
  rw [h]
  exact isFixedFixedSolution_axialDisplacement hL hEA q

/-- Both Dirichlet values of the reconstruction: `u_h 0 = 0` and `u_h L = 0`. -/
lemma physicalP1_zero_and_length (P : Partition (0 : ℝ) 1) {L : ℝ} (hL : L ≠ 0) (EA q : ℝ) :
    physicalP1 P EA L q 0 = 0 ∧ physicalP1 P EA L q L = 0 := by
  have hnode : ∀ j, interp P unitProfile (P.points j) = unitProfile (P.points j) :=
    fun j => p1_points P _ j
  have h0 : interp P unitProfile 0 = unitProfile 0 := by simpa [P.first] using hnode 0
  have h1 : interp P unitProfile 1 = unitProfile 1 := by simpa [P.last] using hnode (Fin.last P.n)
  constructor
  · simp [physicalP1, h0, unitProfile]
  · simp [physicalP1, div_self hL, h1, unitProfile]

/-- The reconstruction is the amplitude times the Galerkin solution of the unit problem. -/
lemma physicalP1_eq_galerkin (P : Partition (0 : ℝ) 1) {c : Fin (P.n + 1) → ℝ}
    (hc : IsGalerkinSolution P (fun _ => 2) c) (EA L q x : ℝ) :
    physicalP1 P EA L q x = barAmplitude EA L q * p1 P c (x / L) := by
  rw [physicalP1, p1_eq_interp_of_isGalerkinSolution P unitProfile_isClassicalSolution hc]

/-! ## B. Inverse normalization and the zero load -/

/-- For `EA ≠ 0` and `L ≠ 0`, the amplitude is nonzero exactly for a nonzero load. -/
lemma barAmplitude_ne_zero_iff {EA L : ℝ} (hEA : EA ≠ 0) (hL : L ≠ 0) (q : ℝ) :
    barAmplitude EA L q ≠ 0 ↔ q ≠ 0 := by
  unfold barAmplitude
  constructor
  · intro h hq
    apply h
    simp [hq]
  · intro hq
    exact div_ne_zero (mul_ne_zero hq (pow_ne_zero 2 hL)) (mul_ne_zero two_ne_zero hEA)

/-- Inverse normalization, only for `α ≠ 0`: `û ξ = α⁻¹ * u (L * ξ)`. -/
lemma unitProfile_eq_inv_barAmplitude_mul {EA L q : ℝ} (hL : L ≠ 0)
    (hα : barAmplitude EA L q ≠ 0) (ξ : ℝ) :
    unitProfile ξ = (barAmplitude EA L q)⁻¹ * axialDisplacement EA L q (L * ξ) := by
  rw [axialDisplacement_eq_barAmplitude_mul hL, mul_div_cancel_left₀ ξ hL,
    inv_mul_cancel_left₀ hα]

/-- Zero load, treated directly: the amplitude, the physical solution, its reconstruction and
the error are all zero. -/
lemma zero_load (P : Partition (0 : ℝ) 1) (EA L : ℝ) :
    barAmplitude EA L 0 = 0 ∧ (∀ x, axialDisplacement EA L 0 x = 0) ∧
      (∀ x, physicalP1 P EA L 0 x = 0) ∧ ∀ x, physicalError P EA L 0 x = 0 := by
  refine ⟨by simp [barAmplitude], fun x => by simp [axialDisplacement],
    fun x => by simp [physicalP1, barAmplitude], fun x => ?_⟩
  simp [physicalError, physicalP1, barAmplitude, axialDisplacement]

/-- At zero load the inverse amplitude map does not recover the unit profile: at `ξ = 1 / 2` it
gives `0`, while `û (1 / 2) = 1 / 4`. -/
lemma zero_load_inverse_ne (EA L : ℝ) :
    (barAmplitude EA L 0)⁻¹ * axialDisplacement EA L 0 (L * (1 / 2)) ≠ unitProfile (1 / 2) := by
  norm_num [barAmplitude, axialDisplacement, unitProfile]

/-! ## C. Scaling of the two error integrals -/

/-- The physical error is the amplitude times the unit error at `x / L`, at every `x`. -/
lemma physicalError_eq (P : Partition (0 : ℝ) 1) {L : ℝ} (hL : L ≠ 0) (EA q x : ℝ) :
    physicalError P EA L q x = barAmplitude EA L q * unitError P (x / L) := by
  rw [physicalError, axialDisplacement_eq_barAmplitude_mul hL, physicalP1, unitError]
  ring

/-- Energy scaling: `∫₀ᴸ EA (e')² = (EA / L) α² ∫₀¹ (ê')²`. -/
lemma integral_energy_physicalError (P : Partition (0 : ℝ) 1) {L : ℝ} (hL : 0 < L) (EA q : ℝ) :
    ∫ x in (0 : ℝ)..L, EA * deriv (physicalError P EA L q) x ^ 2 =
      EA / L * barAmplitude EA L q ^ 2 * ∫ ξ in (0 : ℝ)..1, deriv (unitError P) ξ ^ 2 := by
  have hL0 := hL.ne'
  have hs : physicalError P EA L q = fun x => barAmplitude EA L q * unitError P (L⁻¹ * x) := by
    funext x
    rw [physicalError_eq P hL0, div_eq_inv_mul]
  have hd : ∀ x, deriv (physicalError P EA L q) x =
      barAmplitude EA L q * (L⁻¹ * deriv (unitError P) (L⁻¹ * x)) := by
    intro x
    rw [hs, deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul]
  have hi : ∫ x in (0 : ℝ)..L, EA * deriv (physicalError P EA L q) x ^ 2 =
      ∫ x in (0 : ℝ)..L, EA * barAmplitude EA L q ^ 2 * L⁻¹ ^ 2 *
        deriv (unitError P) (L⁻¹ * x) ^ 2 := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [hd]
    ring
  rw [hi, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun ξ => deriv (unitError P) ξ ^ 2)
      (inv_ne_zero hL0), mul_zero, inv_mul_cancel₀ hL0, inv_inv, smul_eq_mul]
  field_simp

/-- `L²` scaling: `∫₀ᴸ e² = L α² ∫₀¹ ê²`. -/
lemma integral_sq_physicalError (P : Partition (0 : ℝ) 1) {L : ℝ} (hL : 0 < L) (EA q : ℝ) :
    ∫ x in (0 : ℝ)..L, physicalError P EA L q x ^ 2 =
      L * barAmplitude EA L q ^ 2 * ∫ ξ in (0 : ℝ)..1, unitError P ξ ^ 2 := by
  have hL0 := hL.ne'
  have hi : ∫ x in (0 : ℝ)..L, physicalError P EA L q x ^ 2 =
      ∫ x in (0 : ℝ)..L, barAmplitude EA L q ^ 2 * unitError P (L⁻¹ * x) ^ 2 := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [physicalError_eq P hL0, div_eq_inv_mul]
    ring
  rw [hi, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun ξ => unitError P ξ ^ 2) (inv_ne_zero hL0),
    mul_zero, inv_mul_cancel₀ hL0, inv_inv, smul_eq_mul]
  ring

/-! ## D. The mesh estimates in physical form -/

/-- The existing energy estimate `‖ê‖²_a ≤ (h / π)² ‖2‖²_{L²}` in physical form:
`∫₀ᴸ EA (e')² ≤ (EA / L) α² (4 (h / π)²)`, with `h` the mesh size of `P`. -/
lemma integral_energy_physicalError_le_mesh (P : Partition (0 : ℝ) 1) {EA L : ℝ} (hL : 0 < L)
    (hEA : 0 < EA) (q : ℝ) :
    ∫ x in (0 : ℝ)..L, EA * deriv (physicalError P EA L q) x ^ 2 ≤
      EA / L * barAmplitude EA L q ^ 2 * (4 * (P.mesh / Real.pi) ^ 2) := by
  rw [integral_energy_physicalError P hL EA q]
  have hc := isGalerkinSolution_nodal P unitProfile_isClassicalSolution
  have hb := energy_sub_galerkin_le_mesh P unitProfile_isClassicalSolution hc
  have h1 : ∫ ξ in (0 : ℝ)..1, deriv (unitError P) ξ ^ 2 =
      energy (unitProfile - p1 P fun j => unitProfile (P.points j))
        (unitProfile - p1 P fun j => unitProfile (P.points j)) := by
    unfold energy
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [sq]
    rfl
  have h2 : ∫ x in (0 : ℝ)..1, (fun _ : ℝ => (2 : ℝ)) x ^ 2 = 4 := by norm_num
  have hk : 0 ≤ EA / L * barAmplitude EA L q ^ 2 :=
    mul_nonneg (div_nonneg hEA.le hL.le) (sq_nonneg _)
  rw [h1]
  calc _ ≤ EA / L * barAmplitude EA L q ^ 2 *
        ((P.mesh / Real.pi) ^ 2 * ∫ x in (0 : ℝ)..1, (fun _ : ℝ => (2 : ℝ)) x ^ 2) :=
        mul_le_mul_of_nonneg_left hb hk
    _ = _ := by rw [h2]; ring

/-- The existing `L²` estimate `‖ê‖²_{L²} ≤ (h / π)⁴ ‖2‖²_{L²}` in physical form:
`∫₀ᴸ e² ≤ L α² (4 (h / π)⁴)`. -/
lemma integral_sq_physicalError_le_mesh (P : Partition (0 : ℝ) 1) {L : ℝ} (hL : 0 < L)
    (EA q : ℝ) :
    ∫ x in (0 : ℝ)..L, physicalError P EA L q x ^ 2 ≤
      L * barAmplitude EA L q ^ 2 * (4 * (P.mesh / Real.pi) ^ 4) := by
  rw [integral_sq_physicalError P hL EA q]
  have hc := isGalerkinSolution_nodal P unitProfile_isClassicalSolution
  have hb := integral_sq_sub_galerkin_le_mesh P unitProfile_isClassicalSolution hc
  have h2 : ∫ x in (0 : ℝ)..1, (fun _ : ℝ => (2 : ℝ)) x ^ 2 = 4 := by norm_num
  have hk : 0 ≤ L * barAmplitude EA L q ^ 2 := mul_nonneg hL.le (sq_nonneg _)
  calc _ ≤ L * barAmplitude EA L q ^ 2 *
        ((P.mesh / Real.pi) ^ 4 * ∫ x in (0 : ℝ)..1, (fun _ : ℝ => (2 : ℝ)) x ^ 2) :=
        mul_le_mul_of_nonneg_left hb hk
    _ = _ := by rw [h2]; ring

/-! ## E. Two uniform cells -/

/-- The partition `0 < 1 / 2 < 1` of `[0, 1]` into two uniform cells. -/
noncomputable def twoCells : Partition (0 : ℝ) 1 where
  n := 2
  points := ![0, 1 / 2, 1]
  ordered := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  first := rfl
  last := by simp

/-- Inside the `i`-th element, the unit error has derivative `1 - 2 x - slopeᵢ`, with `slopeᵢ`
the slope of the interpolant there. -/
private lemma hasDerivAt_unitError (P : Partition (0 : ℝ) 1) (i : Fin P.n) {x : ℝ}
    (hx : x ∈ Set.Ioo (P.points i.castSucc) (P.points i.succ)) :
    HasDerivAt (unitError P)
      (1 - 2 * x - elementSlope P (fun j => unitProfile (P.points j)) i) x :=
  (hasDerivAt_unitProfile x).sub (hasDerivAt_p1 P _ i hx)

/-- The integral of a polynomial of degree at most four over `[a, b]`. -/
private lemma integral_poly4 (a b c0 c1 c2 c3 c4 : ℝ) :
    ∫ x in a..b, (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4) =
      c0 * (b - a) + c1 * (b ^ 2 - a ^ 2) / 2 + c2 * (b ^ 3 - a ^ 3) / 3 +
        c3 * (b ^ 4 - a ^ 4) / 4 + c4 * (b ^ 5 - a ^ 5) / 5 := by
  have hG : ∀ x ∈ Set.uIcc a b, HasDerivAt
      (fun x => c0 * x + c1 * x ^ 2 / 2 + c2 * x ^ 3 / 3 + c3 * x ^ 4 / 4 + c4 * x ^ 5 / 5)
      (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4) x := by
    intro x _
    have h := (((((hasDerivAt_id' x).const_mul c0).add
      (((hasDerivAt_pow 2 x).const_mul c1).div_const 2)).add
      (((hasDerivAt_pow 3 x).const_mul c2).div_const 3)).add
      (((hasDerivAt_pow 4 x).const_mul c3).div_const 4)).add
      (((hasDerivAt_pow 5 x).const_mul c4).div_const 5)
    convert h using 1
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG
    ((by fun_prop : Continuous fun x : ℝ =>
      c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4).intervalIntegrable _ _)]
  ring

/-- Two cells, unit problem: the error vanishes at the nodes but is `1 / 16` at `ξ = 1 / 4`;
`∫₀¹ (ê')² = 1 / 12` and `∫₀¹ ê² = 1 / 480`. -/
lemma unitError_twoCells :
    (∀ j, unitError twoCells (twoCells.points j) = 0) ∧ unitError twoCells (1 / 4) = 1 / 16 ∧
      ∫ ξ in (0 : ℝ)..1, deriv (unitError twoCells) ξ ^ 2 = 1 / 12 ∧
      ∫ ξ in (0 : ℝ)..1, unitError twoCells ξ ^ 2 = 1 / 480 := by
  have hp0 : twoCells.points 0 = 0 := rfl
  have hp1 : twoCells.points 1 = 1 / 2 := rfl
  have hp2 : twoCells.points 2 = 1 := rfl
  have hs0 :
      elementSlope twoCells (fun j => unitProfile (twoCells.points j)) (0 : Fin 2) = 1 / 2 := by
    simp only [elementSlope, width]
    change (unitProfile (twoCells.points 1) - unitProfile (twoCells.points 0)) /
      (twoCells.points 1 - twoCells.points 0) = 1 / 2
    rw [hp0, hp1]
    norm_num [unitProfile]
  have hs1 :
      elementSlope twoCells (fun j => unitProfile (twoCells.points j)) (1 : Fin 2) = -1 / 2 := by
    simp only [elementSlope, width]
    change (unitProfile (twoCells.points 2) - unitProfile (twoCells.points 1)) /
      (twoCells.points 2 - twoCells.points 1) = -1 / 2
    rw [hp1, hp2]
    norm_num [unitProfile]
  have hlin0 : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), unitError twoCells x = x / 2 - x ^ 2 := by
    intro x hx
    have h := p1_eq_of_mem_Icc twoCells (fun j => unitProfile (twoCells.points j)) (0 : Fin 2)
      (x := x) (by
        change x ∈ Set.Icc (twoCells.points 0) (twoCells.points 1); rw [hp0, hp1]; exact hx)
    rw [unitError, interp, h, hs0]
    change unitProfile x - (unitProfile (twoCells.points 0) + 1 / 2 * (x - twoCells.points 0)) = _
    rw [hp0]
    simp [unitProfile]
    ring
  have hlin1 : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1, unitError twoCells x = 3 / 2 * x - x ^ 2 - 1 / 2 := by
    intro x hx
    have h := p1_eq_of_mem_Icc twoCells (fun j => unitProfile (twoCells.points j)) (1 : Fin 2)
      (x := x) (by
        change x ∈ Set.Icc (twoCells.points 1) (twoCells.points 2); rw [hp1, hp2]; exact hx)
    rw [unitError, interp, h, hs1]
    change unitProfile x - (unitProfile (twoCells.points 1) + -1 / 2 * (x - twoCells.points 1)) = _
    rw [hp1]
    simp [unitProfile]
    ring
  have hd0 : Set.EqOn (fun x : ℝ => (1 / 2 - 2 * x) ^ 2) (fun x => deriv (unitError twoCells) x ^ 2)
      (Set.uIoo 0 (1 / 2)) := by
    intro x hx
    rw [Set.uIoo_of_le (by norm_num)] at hx
    have h := hasDerivAt_unitError twoCells (0 : Fin 2) (x := x)
      (by change x ∈ Set.Ioo (twoCells.points 0) (twoCells.points 1); rw [hp0, hp1]; exact hx)
    simp only
    rw [h.deriv, hs0]
    ring
  have hd1 : Set.EqOn (fun x : ℝ => (3 / 2 - 2 * x) ^ 2) (fun x => deriv (unitError twoCells) x ^ 2)
      (Set.uIoo (1 / 2) 1) := by
    intro x hx
    rw [Set.uIoo_of_le (by norm_num)] at hx
    have h := hasDerivAt_unitError twoCells (1 : Fin 2) (x := x)
      (by change x ∈ Set.Ioo (twoCells.points 1) (twoCells.points 2); rw [hp1, hp2]; exact hx)
    simp only
    rw [h.deriv, hs1]
    ring
  refine ⟨fun j => ?_, ?_, ?_, ?_⟩
  · rw [unitError, interp, p1_points]
    simp
  · rw [hlin0 _ ⟨by norm_num, by norm_num⟩]
    norm_num
  · have hc0 : Continuous fun x : ℝ => (1 / 2 - 2 * x) ^ 2 := by fun_prop
    have hc1 : Continuous fun x : ℝ => (3 / 2 - 2 * x) ^ 2 := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hc0.intervalIntegrable 0 (1 / 2)).congr_uIoo hd0)
      ((hc1.intervalIntegrable (1 / 2) 1).congr_uIoo hd1),
      ← intervalIntegral.integral_congr_uIoo hd0, ← intervalIntegral.integral_congr_uIoo hd1]
    have e0 : ∫ x in (0 : ℝ)..(1 / 2), (1 / 2 - 2 * x) ^ 2 =
        ∫ x in (0 : ℝ)..(1 / 2), ((1 / 4) + (-2) * x + 4 * x ^ 2 + 0 * x ^ 3 + 0 * x ^ 4) :=
      intervalIntegral.integral_congr fun x _ => by ring
    have e1 : ∫ x in (1 / 2 : ℝ)..1, (3 / 2 - 2 * x) ^ 2 =
        ∫ x in (1 / 2 : ℝ)..1, ((9 / 4) + (-6) * x + 4 * x ^ 2 + 0 * x ^ 3 + 0 * x ^ 4) :=
      intervalIntegral.integral_congr fun x _ => by ring
    rw [e0, e1, integral_poly4, integral_poly4]
    norm_num
  · have hc : Continuous fun x => unitError twoCells x ^ 2 :=
      ((contDiff_unitProfile.continuous).sub (continuous_p1 twoCells _)).pow 2
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (1 / 2))
      (hc.intervalIntegrable (1 / 2) 1)]
    have e0 : ∫ x in (0 : ℝ)..(1 / 2), unitError twoCells x ^ 2 =
        ∫ x in (0 : ℝ)..(1 / 2), (0 + 0 * x + (1 / 4) * x ^ 2 + (-1) * x ^ 3 + 1 * x ^ 4) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hx
      rw [hlin0 x hx]
      ring
    have e1 : ∫ x in (1 / 2 : ℝ)..1, unitError twoCells x ^ 2 =
        ∫ x in (1 / 2 : ℝ)..1,
          ((1 / 4) + (-3 / 2) * x + (13 / 4) * x ^ 2 + (-3) * x ^ 3 + 1 * x ^ 4)
          := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hx
      rw [hlin1 x hx]
      ring
    rw [e0, e1, integral_poly4, integral_poly4]
    norm_num

/-- Two cells, physical bar: `e (L / 4) = α / 16`, energy `(EA / L) α² / 12` and squared `L²`
error `L α² / 480`. -/
lemma physicalError_twoCells {L : ℝ} (hL : 0 < L) (EA q : ℝ) :
    physicalError twoCells EA L q (L / 4) = barAmplitude EA L q / 16 ∧
      ∫ x in (0 : ℝ)..L, EA * deriv (physicalError twoCells EA L q) x ^ 2 =
        EA / L * barAmplitude EA L q ^ 2 / 12 ∧
      ∫ x in (0 : ℝ)..L, physicalError twoCells EA L q x ^ 2 =
        L * barAmplitude EA L q ^ 2 / 480 := by
  obtain ⟨-, h4, hE, hS⟩ := unitError_twoCells
  refine ⟨?_, ?_, ?_⟩
  · rw [physicalError_eq twoCells hL.ne', show L / 4 / L = 1 / 4 by field_simp [hL.ne'], h4]
    ring
  · rw [integral_energy_physicalError twoCells hL EA q, hE]
    ring
  · rw [integral_sq_physicalError twoCells hL EA q, hS]
    ring

end PhysicalErrorBudgets

end
