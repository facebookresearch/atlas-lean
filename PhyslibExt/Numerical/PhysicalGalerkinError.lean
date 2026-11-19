/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Numerical.PhysicalErrorBudgets

/-!
# Bar solve residual to reconstructed displacement error

For the two-cell physical P1 bar of `PhyslibExt.Numerical.PhysicalErrorBudgets` (length `L > 0`,
constant axial rigidity `EA > 0`, both ends fixed, uniform load `q`, the uniform partition
`twoCells` of `[0, 1]` pulled back by `x / L`), the Galerkin solve has a single unknown: the
coefficient of the hat `φ (x / L)` of the interior node `x = L / 2`. An approximate value of that
coefficient is bound to the residual it leaves in the same one-equation system, and the
coefficient error is carried through the same hat reconstruction to the displacement.

## i. Overview

* Reduction. The pulled-back interior hat has the physical stiffness
  `K = ∫₀ᴸ EA (φ (x / L))'² = 4 * EA / L`, the assembled unit entry `stiffness twoCells 1 1 = 4`
  scaled by `EA / L`, and the consistent load `F = ∫₀ᴸ q φ (x / L) = q * L / 2`. The physical
  reconstruction is `u_h = c * φ (x / L)` with the interior coefficient
  `c = u_h (L / 2) = q * L ^ 2 / (8 * EA)`, and `K * c = F`.
* Residual. An approximate coefficient `c̃` leaves the residual `r = F - K * c̃` of the same
  system; then `c - c̃ = r / K = L * r / (4 * EA)`, so `|c - c̃| ≤ L * |r| / (4 * EA)`, with
  equality.
* Transport. Reconstructing `c̃` through the same hat, `ũ_h = c̃ * φ (x / L)`, the displacement
  error is `u_h - ũ_h = (c - c̃) * φ (x / L)`. It is at most `L * |r| / (4 * EA)` on `[0, L]`, its
  energy is `∫₀ᴸ EA ((u_h - ũ_h)')² = K * (c - c̃) ^ 2 = L * r ^ 2 / (4 * EA)`, and its squared
  `L²` norm is `L * (c - c̃) ^ 2 / 3`: the hat contributes the factors `1`, `K` and `L / 3`.

Signs: `r > 0` means the approximate coefficient is too small (`c̃ < c`). Derivatives follow the
convention of the finite element module (`deriv` takes junk values at the mesh nodes, which no
integral sees).

Model inputs: small-strain linear elastic bar with constant `EA`, both ends fixed, uniform load,
the fixed two-cell partition. Non-goals: no new linear solver, no generic Céa or a posteriori
theorem, no assumed physical coercivity. The approximate reconstruction is not a Galerkin
solution, so no exact-Galerkin error theorem is applied to it; its distance to the exact
displacement is not bounded here.

## ii. Key results

- `twoCellStiffness`, `twoCellLoad`, `twoCellCoeff`, `twoCellResidual`, `twoCellReconstruction`:
  the one-unknown system, its residual and the hat reconstruction.
- `twoCells_interior_system`, `twoCellStiffness_eq_stiffness`, `integral_energy_hat`,
  `integral_load_hat`: `K` and `F` from the assembled unit system and from the pulled-back hat.
- `physicalP1_eq_twoCellReconstruction`, `twoCellCoeff_eq`, `twoCellStiffness_mul_twoCellCoeff`:
  one interior coefficient, its closed form and the reduced solve `K * c = F`.
- `twoCellCoeff_sub_eq`, `abs_twoCellCoeff_sub_le`: the coefficient error from the residual.
- `twoCellReconstruction_zero_and_length`, `physicalP1_sub_twoCellReconstruction`,
  `abs_physicalP1_sub_twoCellReconstruction_le`, `integral_energy_reconstruction_error`,
  `integral_sq_reconstruction_error`: the Dirichlet values of the hat reconstruction and the
  transported displacement error, pointwise, in energy and in `L²`.
- The nonzero-residual fixture, the three reconstruction factors and the excluded zero rigidity
  are in `PhyslibExtTest.Numerical.PhysicalGalerkinErrorTest`.

## iii. Table of contents

- A. The interior hat: stiffness, load and coefficient
- B. Residual and coefficient error
- C. Transport through the hat reconstruction

## iv. References

- T. J. R. Hughes, *The Finite Element Method: Linear Static and Dynamic Finite Element
  Analysis*, Dover, 2000, chapter 1 (the one-dimensional bar, element stiffness `EA / h` and
  consistent load `q h / 2`).
- S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, chapters 0 to 2.
- `PhyslibExt.Numerical.PhysicalErrorBudgets` and `MathlibExt.Analysis.ODE.FiniteElement1D`.
-/

@[expose] public section

namespace PhysicalGalerkinError

open MeasureTheory MathlibExt.Analysis.ODE.FiniteElement1D PhysicalErrorBudgets

/-! ## A. The interior hat: stiffness, load and coefficient -/

/-- The physical stiffness `K = 4 * EA / L` of the interior node of the two-cell bar. -/
noncomputable def twoCellStiffness (EA L : ℝ) : ℝ :=
  4 * EA / L

/-- The physical consistent load `F = q * L / 2` of the interior node under the uniform load
`q`. -/
noncomputable def twoCellLoad (L q : ℝ) : ℝ :=
  q * L / 2

/-- The interior coefficient `c = u_h (L / 2)` of the physical two-cell reconstruction. -/
noncomputable def twoCellCoeff (EA L q : ℝ) : ℝ :=
  physicalP1 twoCells EA L q (L / 2)

/-- The residual `F - K * c` that an approximate interior coefficient `c` leaves in the same
system. -/
noncomputable def twoCellResidual (EA L q c : ℝ) : ℝ :=
  twoCellLoad L q - twoCellStiffness EA L * c

/-- The reconstruction `c * φ (x / L)` of an interior coefficient `c` through the hat `φ` of the
interior node of `twoCells`. -/
noncomputable def twoCellReconstruction (L c x : ℝ) : ℝ :=
  c * hat twoCells 1 (x / L)

/-- The left end of `twoCells` is `0`. -/
private lemma points_zero : twoCells.points 0 = 0 := rfl

/-- The interior node of `twoCells` is `1 / 2`. -/
private lemma points_one : twoCells.points 1 = 1 / 2 := rfl

/-- The right end of `twoCells` is `1`. -/
private lemma points_two : twoCells.points 2 = 1 := rfl

/-- The assembled unit entry at the interior node: `1 / h + 1 / h = 4` with `h = 1 / 2`. -/
private lemma stiffness_twoCells_one : stiffness twoCells 1 1 = 4 := by
  have h := stiffness_succ_succ twoCells (i := (0 : Fin 2)) (j := (1 : Fin 2)) rfl
  have hw0 : width twoCells (0 : Fin 2) = 1 / 2 := by
    simp only [width]
    change twoCells.points 1 - twoCells.points 0 = 1 / 2
    rw [points_zero, points_one]
    norm_num
  have hw1 : width twoCells (1 : Fin 2) = 1 / 2 := by
    simp only [width]
    change twoCells.points 2 - twoCells.points 1 = 1 / 2
    rw [points_one, points_two]
    norm_num
  rw [hw0, hw1] at h
  have h' : stiffness twoCells 1 1 = (1 / 2)⁻¹ + (1 / 2)⁻¹ := h
  rw [h']
  norm_num

/-- The nodal vector of the interior hat: `1` at the interior node, `0` at both ends. -/
private noncomputable def interiorNodal : Fin (twoCells.n + 1) → ℝ := Pi.single 1 1

/-- The interior hat is the P1 function of its nodal vector. -/
private lemma hat_eq_p1 : hat twoCells 1 = p1 twoCells interiorNodal := rfl

/-- The nodal vector of the interior hat vanishes at the left end. -/
private lemma interiorNodal_zero : interiorNodal 0 = 0 := Pi.single_eq_of_ne (by decide) _

/-- The nodal vector of the interior hat is `1` at the interior node. -/
private lemma interiorNodal_one : interiorNodal 1 = 1 := Pi.single_eq_same _ _

/-- The nodal vector of the interior hat vanishes at the right end. -/
private lemma interiorNodal_two : interiorNodal 2 = 0 := Pi.single_eq_of_ne (by decide) _

/-- On the left element the interior hat is `2 x`. -/
private lemma hat_left {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    hat twoCells 1 x = 2 * x := by
  have h := p1_eq_of_mem_Icc twoCells interiorNodal (0 : Fin 2) (x := x) (by
    change x ∈ Set.Icc (twoCells.points 0) (twoCells.points 1)
    rw [points_zero, points_one]
    exact hx)
  rw [hat_eq_p1, h]
  simp only [elementSlope, width]
  change interiorNodal 0 + (interiorNodal 1 - interiorNodal 0) /
      (twoCells.points 1 - twoCells.points 0) * (x - twoCells.points 0) = 2 * x
  rw [interiorNodal_zero, interiorNodal_one, points_zero, points_one]
  ring

/-- On the right element the interior hat is `2 - 2 x`. -/
private lemma hat_right {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 1) :
    hat twoCells 1 x = 2 - 2 * x := by
  have h := p1_eq_of_mem_Icc twoCells interiorNodal (1 : Fin 2) (x := x) (by
    change x ∈ Set.Icc (twoCells.points 1) (twoCells.points 2)
    rw [points_one, points_two]
    exact hx)
  rw [hat_eq_p1, h]
  simp only [elementSlope, width]
  change interiorNodal 1 + (interiorNodal 2 - interiorNodal 1) /
      (twoCells.points 2 - twoCells.points 1) * (x - twoCells.points 1) = 2 - 2 * x
  rw [interiorNodal_one, interiorNodal_two, points_one, points_two]
  ring

/-- The interior hat is `1` at the interior node. -/
private lemma hat_half : hat twoCells 1 (1 / 2) = 1 := by
  rw [hat_left ⟨by norm_num, le_rfl⟩]
  norm_num

/-- On `[0, 1]` the interior hat lies in `[0, 1]`. -/
private lemma hat_mem_unit {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ hat twoCells 1 x ∧ hat twoCells 1 x ≤ 1 := by
  rcases le_total x (1 / 2) with h | h
  · rw [hat_left ⟨hx.1, h⟩]
    constructor <;> linarith [hx.1]
  · rw [hat_right ⟨h, hx.2⟩]
    constructor <;> linarith [hx.2]

/-- The integral of a polynomial of degree at most two over `[a, b]`. -/
private lemma integral_quad (a b c0 c1 c2 : ℝ) :
    ∫ x in a..b, (c0 + c1 * x + c2 * x ^ 2) =
      c0 * (b - a) + c1 * (b ^ 2 - a ^ 2) / 2 + c2 * (b ^ 3 - a ^ 3) / 3 := by
  have hG : ∀ x ∈ Set.uIcc a b, HasDerivAt
      (fun x => c0 * x + c1 * x ^ 2 / 2 + c2 * x ^ 3 / 3) (c0 + c1 * x + c2 * x ^ 2) x := by
    intro x _
    have h := (((hasDerivAt_id' x).const_mul c0).add
      (((hasDerivAt_pow 2 x).const_mul c1).div_const 2)).add
      (((hasDerivAt_pow 3 x).const_mul c2).div_const 3)
    convert h using 1
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG
    ((by fun_prop : Continuous fun x : ℝ => c0 + c1 * x + c2 * x ^ 2).intervalIntegrable _ _)]
  ring

/-- The interior hat is continuous. -/
private lemma continuous_hat : Continuous (hat twoCells 1) :=
  continuous_p1 twoCells _

/-- `∫₀¹ φ = 1 / 2`. -/
private lemma integral_hat : ∫ x in (0 : ℝ)..1, hat twoCells 1 x = 1 / 2 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_hat.intervalIntegrable 0 (1 / 2)) (continuous_hat.intervalIntegrable (1 / 2) 1)]
  have e0 : ∫ x in (0 : ℝ)..(1 / 2), hat twoCells 1 x =
      ∫ x in (0 : ℝ)..(1 / 2), (0 + 2 * x + 0 * x ^ 2) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hx
    rw [hat_left hx]
    ring
  have e1 : ∫ x in (1 / 2 : ℝ)..1, hat twoCells 1 x =
      ∫ x in (1 / 2 : ℝ)..1, (2 + (-2) * x + 0 * x ^ 2) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hx
    rw [hat_right hx]
    ring
  rw [e0, e1, integral_quad, integral_quad]
  norm_num

/-- `∫₀¹ φ² = 1 / 3`. -/
private lemma integral_hat_sq : ∫ x in (0 : ℝ)..1, hat twoCells 1 x ^ 2 = 1 / 3 := by
  have hc : Continuous fun x => hat twoCells 1 x ^ 2 := continuous_hat.pow 2
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (1 / 2)) (hc.intervalIntegrable (1 / 2) 1)]
  have e0 : ∫ x in (0 : ℝ)..(1 / 2), hat twoCells 1 x ^ 2 =
      ∫ x in (0 : ℝ)..(1 / 2), (0 + 0 * x + 4 * x ^ 2) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hx
    rw [hat_left hx]
    ring
  have e1 : ∫ x in (1 / 2 : ℝ)..1, hat twoCells 1 x ^ 2 =
      ∫ x in (1 / 2 : ℝ)..1, (4 + (-8) * x + 4 * x ^ 2) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hx
    rw [hat_right hx]
    ring
  rw [e0, e1, integral_quad, integral_quad]
  norm_num

/-- `∫₀¹ (φ')² = 4`, the assembled unit entry, by `energy_hat_hat`. -/
private lemma integral_deriv_hat_sq :
    ∫ x in (0 : ℝ)..1, deriv (hat twoCells 1) x ^ 2 = 4 := by
  have h := energy_hat_hat twoCells 1 1
  rw [energy, stiffness_twoCells_one] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [sq]

/-- The nodal interpolant of the unit profile is a quarter of the interior hat. -/
private lemma interp_unitProfile_apply (y : ℝ) :
    interp twoCells unitProfile y = 1 / 4 * hat twoCells 1 y := by
  have hv : (fun j => unitProfile (twoCells.points j)) = (1 / 4 : ℝ) • interiorNodal := by
    funext j
    change Fin 3 at j
    fin_cases j
    · change unitProfile (twoCells.points 0) = (1 / 4 : ℝ) * interiorNodal 0
      rw [points_zero, interiorNodal_zero]
      norm_num [unitProfile]
    · change unitProfile (twoCells.points 1) = (1 / 4 : ℝ) * interiorNodal 1
      rw [points_one, interiorNodal_one]
      norm_num [unitProfile]
    · change unitProfile (twoCells.points 2) = (1 / 4 : ℝ) * interiorNodal 2
      rw [points_two, interiorNodal_two]
      norm_num [unitProfile]
  have h := congrFun ((p1Map twoCells).map_smul (1 / 4 : ℝ) interiorNodal) y
  rw [interp, hv]
  exact h

/-- The interior coefficient is a quarter of the amplitude. -/
private lemma twoCellCoeff_eq_barAmplitude {L : ℝ} (hL : L ≠ 0) (EA q : ℝ) :
    twoCellCoeff EA L q = barAmplitude EA L q / 4 := by
  unfold twoCellCoeff physicalP1
  rw [interp_unitProfile_apply, show L / 2 / L = 1 / 2 by field_simp, hat_half]
  ring

/-- The unit two-cell system at the interior node: the assembled stiffness entry is
`1 / h + 1 / h = 4` with `h = 1 / 2`, and the load of `-û'' = 2` is `∫₀¹ 2 φ = 1`. -/
lemma twoCells_interior_system :
    stiffness twoCells 1 1 = 4 ∧ load twoCells (fun _ => 2) 1 = 1 := by
  refine ⟨stiffness_twoCells_one, ?_⟩
  rw [load, intervalIntegral.integral_const_mul, integral_hat]
  norm_num

/-- The physical stiffness is the assembled unit entry scaled by `EA / L`. -/
lemma twoCellStiffness_eq_stiffness (EA L : ℝ) :
    twoCellStiffness EA L = EA / L * stiffness twoCells 1 1 := by
  rw [stiffness_twoCells_one, twoCellStiffness]
  ring

/-- The physical stiffness is the energy of the pulled-back interior hat:
`∫₀ᴸ EA (φ (x / L))'² = 4 * EA / L`. -/
lemma integral_energy_hat (EA : ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ x in (0 : ℝ)..L, EA * deriv (fun x => hat twoCells 1 (x / L)) x ^ 2 =
      twoCellStiffness EA L := by
  have hL0 := hL.ne'
  have hs : (fun x => hat twoCells 1 (x / L)) = fun x => hat twoCells 1 (L⁻¹ * x) := by
    funext x
    rw [div_eq_inv_mul]
  have hd : ∀ x, deriv (fun x => hat twoCells 1 (x / L)) x =
      L⁻¹ * deriv (hat twoCells 1) (L⁻¹ * x) := by
    intro x
    rw [hs, deriv_comp_mul_left, smul_eq_mul]
  have hi : ∫ x in (0 : ℝ)..L, EA * deriv (fun x => hat twoCells 1 (x / L)) x ^ 2 =
      ∫ x in (0 : ℝ)..L, EA * L⁻¹ ^ 2 * deriv (hat twoCells 1) (L⁻¹ * x) ^ 2 := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [hd]
    ring
  rw [hi, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun ξ => deriv (hat twoCells 1) ξ ^ 2)
      (inv_ne_zero hL0), mul_zero, inv_mul_cancel₀ hL0, inv_inv, smul_eq_mul,
    integral_deriv_hat_sq, twoCellStiffness]
  field_simp

/-- The physical load is the consistent load of the pulled-back interior hat:
`∫₀ᴸ q φ (x / L) = q * L / 2`. -/
lemma integral_load_hat {L : ℝ} (hL : 0 < L) (q : ℝ) :
    ∫ x in (0 : ℝ)..L, q * hat twoCells 1 (x / L) = twoCellLoad L q := by
  have hL0 := hL.ne'
  have hi : ∫ x in (0 : ℝ)..L, q * hat twoCells 1 (x / L) =
      ∫ x in (0 : ℝ)..L, q * hat twoCells 1 (L⁻¹ * x) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [div_eq_inv_mul]
  rw [hi, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun ξ => hat twoCells 1 ξ) (inv_ne_zero hL0),
    mul_zero, inv_mul_cancel₀ hL0, inv_inv, smul_eq_mul, integral_hat, twoCellLoad]
  ring

/-- One interior coefficient: the physical two-cell reconstruction is the hat reconstruction of
its value at `L / 2`. -/
lemma physicalP1_eq_twoCellReconstruction {L : ℝ} (hL : L ≠ 0) (EA q x : ℝ) :
    physicalP1 twoCells EA L q x = twoCellReconstruction L (twoCellCoeff EA L q) x := by
  rw [twoCellReconstruction, twoCellCoeff_eq_barAmplitude hL, physicalP1,
    interp_unitProfile_apply]
  ring

/-- The interior coefficient in closed form: `c = α / 4 = q * L ^ 2 / (8 * EA)`. -/
lemma twoCellCoeff_eq {L : ℝ} (hL : L ≠ 0) (EA q : ℝ) :
    twoCellCoeff EA L q = q * L ^ 2 / (8 * EA) := by
  rw [twoCellCoeff_eq_barAmplitude hL, barAmplitude]
  ring

/-- The reduced solve: the interior coefficient solves `K * c = F`. -/
lemma twoCellStiffness_mul_twoCellCoeff {EA L : ℝ} (hEA : EA ≠ 0) (hL : L ≠ 0) (q : ℝ) :
    twoCellStiffness EA L * twoCellCoeff EA L q = twoCellLoad L q := by
  rw [twoCellCoeff_eq hL, twoCellStiffness, twoCellLoad]
  field_simp
  ring

/-! ## B. Residual and coefficient error -/

/-- The coefficient error is the residual over the stiffness: `c - c̃ = L * r / (4 * EA)`. -/
lemma twoCellCoeff_sub_eq {EA L : ℝ} (hEA : EA ≠ 0) (hL : L ≠ 0) (q c : ℝ) :
    twoCellCoeff EA L q - c = L * twoCellResidual EA L q c / (4 * EA) := by
  rw [twoCellResidual, ← twoCellStiffness_mul_twoCellCoeff hEA hL q, twoCellStiffness]
  field_simp

/-- The residual bound on the coefficient error: `|c - c̃| ≤ L * |r| / (4 * EA)` for the physical
bar `0 < EA`, `0 < L`. -/
lemma abs_twoCellCoeff_sub_le {EA L : ℝ} (hEA : 0 < EA) (hL : 0 < L) (q c : ℝ) :
    |twoCellCoeff EA L q - c| ≤ L * |twoCellResidual EA L q c| / (4 * EA) := by
  rw [twoCellCoeff_sub_eq hEA.ne' hL.ne', abs_div, abs_mul, abs_of_pos hL,
    abs_of_pos (by positivity : (0 : ℝ) < 4 * EA)]

/-! ## C. Transport through the hat reconstruction -/

/-- Every hat reconstruction keeps the homogeneous Dirichlet values: `ũ_h 0 = 0` and
`ũ_h L = 0`. -/
lemma twoCellReconstruction_zero_and_length {L : ℝ} (hL : L ≠ 0) (c : ℝ) :
    twoCellReconstruction L c 0 = 0 ∧ twoCellReconstruction L c L = 0 := by
  refine ⟨?_, ?_⟩
  · rw [twoCellReconstruction, zero_div, hat_left ⟨le_rfl, by norm_num⟩]
    ring
  · rw [twoCellReconstruction, div_self hL, hat_right ⟨by norm_num, le_rfl⟩]
    ring

/-- The displacement error of the approximate reconstruction is the coefficient error times the
hat: `u_h - ũ_h = (c - c̃) * φ (x / L)`. -/
lemma physicalP1_sub_twoCellReconstruction {L : ℝ} (hL : L ≠ 0) (EA q c x : ℝ) :
    physicalP1 twoCells EA L q x - twoCellReconstruction L c x =
      (twoCellCoeff EA L q - c) * hat twoCells 1 (x / L) := by
  rw [physicalP1_eq_twoCellReconstruction hL, twoCellReconstruction, twoCellReconstruction]
  ring

/-- On the bar `[0, L]` the displacement error is at most `L * |r| / (4 * EA)`, since
`0 ≤ φ ≤ 1` on `[0, 1]`. -/
lemma abs_physicalP1_sub_twoCellReconstruction_le {EA L : ℝ} (hEA : 0 < EA) (hL : 0 < L)
    (q c : ℝ) {x : ℝ} (hx : x ∈ Set.Icc 0 L) :
    |physicalP1 twoCells EA L q x - twoCellReconstruction L c x| ≤
      L * |twoCellResidual EA L q c| / (4 * EA) := by
  rw [physicalP1_sub_twoCellReconstruction hL.ne', abs_mul]
  have hb := hat_mem_unit (x := x / L) ⟨div_nonneg hx.1 hL.le, (div_le_one hL).mpr hx.2⟩
  rw [abs_of_nonneg hb.1]
  calc |twoCellCoeff EA L q - c| * hat twoCells 1 (x / L)
      ≤ |twoCellCoeff EA L q - c| * 1 := mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _)
    _ ≤ L * |twoCellResidual EA L q c| / (4 * EA) := by
      rw [mul_one]
      exact abs_twoCellCoeff_sub_le hEA hL q c

/-- The energy of the displacement error carries the factor `K`:
`∫₀ᴸ EA ((u_h - ũ_h)')² = K * (c - c̃) ^ 2 = L * r ^ 2 / (4 * EA)`. -/
lemma integral_energy_reconstruction_error {EA L : ℝ} (hEA : 0 < EA) (hL : 0 < L) (q c : ℝ) :
    ∫ x in (0 : ℝ)..L,
        EA * deriv (fun x => physicalP1 twoCells EA L q x - twoCellReconstruction L c x) x ^ 2 =
      twoCellStiffness EA L * (twoCellCoeff EA L q - c) ^ 2 ∧
    twoCellStiffness EA L * (twoCellCoeff EA L q - c) ^ 2 =
      L * twoCellResidual EA L q c ^ 2 / (4 * EA) := by
  have hfun : (fun x => physicalP1 twoCells EA L q x - twoCellReconstruction L c x) =
      fun x => (twoCellCoeff EA L q - c) * hat twoCells 1 (x / L) :=
    funext fun x => physicalP1_sub_twoCellReconstruction hL.ne' EA q c x
  refine ⟨?_, ?_⟩
  · have hi : ∫ x in (0 : ℝ)..L,
        EA * deriv (fun x => physicalP1 twoCells EA L q x - twoCellReconstruction L c x) x ^ 2 =
        ∫ x in (0 : ℝ)..L, (twoCellCoeff EA L q - c) ^ 2 *
          (EA * deriv (fun x => hat twoCells 1 (x / L)) x ^ 2) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [hfun, deriv_const_mul_field]
      ring
    rw [hi, intervalIntegral.integral_const_mul, integral_energy_hat EA hL]
    ring
  · rw [twoCellCoeff_sub_eq hEA.ne' hL.ne', twoCellStiffness]
    field_simp

/-- The squared `L²` norm of the displacement error carries the factor `L / 3`:
`∫₀ᴸ (u_h - ũ_h)² = L * (c - c̃) ^ 2 / 3`. -/
lemma integral_sq_reconstruction_error {L : ℝ} (hL : 0 < L) (EA q c : ℝ) :
    ∫ x in (0 : ℝ)..L, (physicalP1 twoCells EA L q x - twoCellReconstruction L c x) ^ 2 =
      L * (twoCellCoeff EA L q - c) ^ 2 / 3 := by
  have hL0 := hL.ne'
  have hi : ∫ x in (0 : ℝ)..L, (physicalP1 twoCells EA L q x - twoCellReconstruction L c x) ^ 2 =
      ∫ x in (0 : ℝ)..L, (twoCellCoeff EA L q - c) ^ 2 * hat twoCells 1 (L⁻¹ * x) ^ 2 := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [physicalP1_sub_twoCellReconstruction hL0, div_eq_inv_mul]
    ring
  rw [hi, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun ξ => hat twoCells 1 ξ ^ 2) (inv_ne_zero hL0),
    mul_zero, inv_mul_cancel₀ hL0, inv_inv, smul_eq_mul, integral_hat_sq]
  ring

end PhysicalGalerkinError
