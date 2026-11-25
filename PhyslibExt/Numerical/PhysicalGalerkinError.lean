/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Numerical.PhysicalErrorBudgets

/-!
# Two-cell bar: solve residual, load quadrature and reconstructed displacement error

For the two-cell physical P1 bar of `PhyslibExt.Numerical.PhysicalErrorBudgets` (length `L > 0`,
constant axial rigidity `EA > 0`, both ends fixed, the uniform partition `twoCells` of `[0, 1]`
pulled back by `x / L`), the Galerkin solve has a single unknown: the coefficient of the hat
`φ (x / L)` of the interior node `x = L / 2`. Under a uniform load `q`, an approximate value of
that coefficient is bound to the residual it leaves in the same one-equation system, and the
coefficient error is carried through the same hat reconstruction to the displacement. Under the
quadratic load `Q * (x / L) ^ 2`, the interior load is computed exactly and by the composite
midpoint rule, and the quadrature error is composed with the residual and the reconstructed
discretization error.

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
* Quadratic load. `û ξ = (ξ - ξ ^ 4) / 12` solves `-û'' = ξ ^ 2`, `û 0 = û 1 = 0`, and
  `u x = β * û (x / L)` with `β = Q * L ^ 2 / EA` solves the bar problem under `Q * (x / L) ^ 2`.
  The load shape differs from the uniform one, so `β = 2 α` for the amplitude
  `α = Q * L ^ 2 / (2 * EA)` of the uniform load `Q`.
* Quadrature. The interior load is `∫₀¹ ξ ^ 2 φ = 7 / 48` exactly and `5 / 32` by the composite
  midpoint rule (each cell contributes its width times `ξ ^ 2 φ` at its midpoint); the physical
  loads are `Q * L` times these. The coefficients `F / K` are `7 β / 192 = u (L / 2)` and
  `5 β / 128`, so the coefficient error is `|β| / 384`; through the hat its squared energy norm is
  `(4 * EA / L) * (β / 384) ^ 2` and its squared `L²` norm `(L / 3) * (β / 384) ^ 2`.
* Composition. For an approximate coefficient `c` of the midpoint system with residual
  `r = F_mid - K * c`, the energy and `L²` norms of `u - c * φ (x / L)` are at most the norm of the
  reconstructed discretization error of the exact-load coefficient, plus the quadrature term
  `|β| / 384` and the algebraic term `L * |r| / (4 * EA)`, each times the hat factor `√K` (energy)
  or `√(L / 3)` (`L²`).

Signs: `r > 0` means the approximate coefficient is too small (`c̃ < c`). For `Q > 0` the
quadratic load points toward increasing `x`. The midpoint coefficient differs from the exact-load
one by `β / 384`, which has the sign of `Q`: it is too large for `Q > 0` and too small for
`Q < 0`. `Q` may have either sign, and the zero load is treated directly, without the inverse
amplitude map.
Derivatives follow the convention of the finite element module (`deriv` takes junk values at the
mesh nodes, which no integral sees).

Model inputs: small-strain linear elastic bar with constant `EA`, both ends fixed, uniform or
quadratic load, the fixed two-cell partition. Non-goals: no new linear solver, no generic Céa or a
posteriori theorem, no assumed physical coercivity. An approximate reconstruction is not a
Galerkin solution, so no exact-Galerkin error theorem is applied to it. The exact-load coefficient
of the quadratic load is nodally exact; this removes neither the quadrature error nor the error
between the nodes.

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
- `quadProfile`, `midpointLoad`, `quadProfile_isClassicalSolution`, `load_quad_twoCells`,
  `midpointLoad_quad_twoCells`, `quad_defects_twoCells`: the normalized quadratic-load problem,
  its exact and midpoint interior loads and their defects.
- `quadAmplitude`, `quadDisplacement`, `quadLoad`, `physMidpointLoad`, `quadAmplitude_eq_two_mul`,
  `isFixedFixedSolution_quadDisplacement`, `quadAmplitude_ne_zero_iff`,
  `quadProfile_eq_inv_quadAmplitude_mul`, `quad_zero_load`, `quad_physical_loads`: the physical
  quadratic load, its inverse map for `Q ≠ 0`, the direct zero load and the physical loads.
- `quadCoeff`, `quadMidpointCoeff`, `quadCoeff_eq`, `quadMidpointCoeff_eq`,
  `quadMidpointCoeff_sub_quadCoeff`, `integral_energy_quadrature_error`,
  `integral_sq_quadrature_error`: the two coefficients and the reconstructed quadrature error.
- `quadMidpointResidual`, `quadMidpointCoeff_sub_eq`, `sqrt_energy_quad_error_le`,
  `sqrt_sq_quad_error_le`: the residual of the midpoint system and the composed norm bounds.
- `nodal_exactness_not_enough`: the exact-load coefficient is nodally exact, the midpoint
  coefficient is not, and the error between the nodes remains.
- The nonzero-residual fixture, the three reconstruction factors, the excluded zero rigidity and
  the nonunit quadratic-load fixture are in `PhyslibExtTest.Numerical.PhysicalGalerkinErrorTest`.

## iii. Table of contents

- A. The interior hat: stiffness, load and coefficient
- B. Residual and coefficient error
- C. Transport through the hat reconstruction
- D. The normalized quadratic-load problem
- E. The physical quadratic load
- F. Coefficients and the reconstructed quadrature error
- G. Composition with the residual and the discretization error
- H. Nodal exactness and the remaining errors

## iv. References

- T. J. R. Hughes, *The Finite Element Method: Linear Static and Dynamic Finite Element
  Analysis*, Dover, 2000, chapter 1 (the one-dimensional bar, element stiffness `EA / h` and
  consistent load `q h / 2`) and chapter 3 (numerical integration of element arrays).
- S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, chapters 0 to 2.
- G. Strang and G. J. Fix, *An Analysis of the Finite Element Method*, 2nd ed.,
  Wellesley-Cambridge Press, 2008, chapter 4 (the effect of numerical integration).
- `PhyslibExt.Numerical.PhysicalErrorBudgets` and `MathlibExt.Analysis.ODE.FiniteElement1D`.
-/

@[expose] public section

namespace PhysicalGalerkinError

open MeasureTheory MathlibExt.Analysis.Integration MathlibExt.Analysis.ODE.FiniteElement1D
  PhysicalErrorBudgets Elasticity.PrismaticMembers

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

/-! ## D. The normalized quadratic-load problem -/

/-- The unit profile `û ξ = (ξ - ξ ^ 4) / 12` of the quadratic load `ξ ^ 2`. -/
noncomputable def quadProfile (ξ : ℝ) : ℝ :=
  (ξ - ξ ^ 4) / 12

/-- The composite midpoint rule for the load vector of `P`: each element contributes its width
times `f * φⱼ` at its midpoint. -/
noncomputable def midpointLoad (P : Partition (0 : ℝ) 1) (f : ℝ → ℝ) (j : Fin (P.n + 1)) : ℝ :=
  ∑ i, width P i * (f ((P.points i.castSucc + P.points i.succ) / 2) *
    hat P j ((P.points i.castSucc + P.points i.succ) / 2))

/-- The unit profile is a classical solution of `-û'' = ξ ^ 2` with `û 0 = û 1 = 0`. -/
lemma quadProfile_isClassicalSolution : IsClassicalSolution (fun ξ => ξ ^ 2) quadProfile := by
  have hd1 : ∀ x : ℝ, HasDerivAt quadProfile ((1 - 4 * x ^ 3) / 12) x := by
    intro x
    have h := ((hasDerivAt_id' x).sub (hasDerivAt_pow 4 x)).div_const 12
    exact h.congr_deriv (by norm_num)
  have hderiv : deriv quadProfile = fun x => (1 - 4 * x ^ 3) / 12 :=
    funext fun x => (hd1 x).deriv
  have hd2 : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (1 - 4 * x ^ 3) / 12) (-x ^ 2) x := by
    intro x
    have h := (((hasDerivAt_pow 3 x).const_mul 4).const_sub 1).div_const 12
    convert h using 1
    norm_num
    ring
  refine ⟨?_, by fun_prop, by norm_num [quadProfile], by norm_num [quadProfile], fun x _ => ?_⟩
  · unfold quadProfile
    fun_prop
  · rw [hderiv, (hd2 x).deriv]
    ring

/-- The integral of a polynomial of degree at most three over `[a, b]`. -/
private lemma integral_cubic (a b c0 c1 c2 c3 : ℝ) :
    ∫ x in a..b, (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3) =
      c0 * (b - a) + c1 * (b ^ 2 - a ^ 2) / 2 + c2 * (b ^ 3 - a ^ 3) / 3 +
        c3 * (b ^ 4 - a ^ 4) / 4 := by
  have hG : ∀ x ∈ Set.uIcc a b, HasDerivAt
      (fun x => c0 * x + c1 * x ^ 2 / 2 + c2 * x ^ 3 / 3 + c3 * x ^ 4 / 4)
      (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3) x := by
    intro x _
    have h := ((((hasDerivAt_id' x).const_mul c0).add
      (((hasDerivAt_pow 2 x).const_mul c1).div_const 2)).add
      (((hasDerivAt_pow 3 x).const_mul c2).div_const 3)).add
      (((hasDerivAt_pow 4 x).const_mul c3).div_const 4)
    convert h using 1
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG
    ((by fun_prop : Continuous fun x : ℝ =>
      c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3).intervalIntegrable _ _)]
  ring

/-- The exact interior load of the quadratic load on two cells: `∫₀¹ ξ ^ 2 φ = 7 / 48`. -/
lemma load_quad_twoCells : load twoCells (fun ξ => ξ ^ 2) 1 = 7 / 48 := by
  have hc : Continuous fun x : ℝ => x ^ 2 * hat twoCells 1 x :=
    (continuous_pow 2).mul continuous_hat
  change ∫ x in (0 : ℝ)..1, x ^ 2 * hat twoCells 1 x = 7 / 48
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (1 / 2))
    (hc.intervalIntegrable (1 / 2) 1)]
  have e0 : ∫ x in (0 : ℝ)..(1 / 2), x ^ 2 * hat twoCells 1 x =
      ∫ x in (0 : ℝ)..(1 / 2), (0 + 0 * x + 0 * x ^ 2 + 2 * x ^ 3) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hx
    rw [hat_left hx]
    ring
  have e1 : ∫ x in (1 / 2 : ℝ)..1, x ^ 2 * hat twoCells 1 x =
      ∫ x in (1 / 2 : ℝ)..1, (0 + 0 * x + 2 * x ^ 2 + (-2) * x ^ 3) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hx
    rw [hat_right hx]
    ring
  rw [e0, e1, integral_cubic, integral_cubic]
  norm_num

/-- The composite midpoint interior load on two cells:
`(1 / 2) (1 / 4) ^ 2 φ (1 / 4) + (1 / 2) (3 / 4) ^ 2 φ (3 / 4) = 5 / 32`. -/
lemma midpointLoad_quad_twoCells : midpointLoad twoCells (fun ξ => ξ ^ 2) 1 = 5 / 32 := by
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
  have hm0 : (twoCells.points (Fin.castSucc (0 : Fin 2)) +
      twoCells.points (Fin.succ (0 : Fin 2))) / 2 = 1 / 4 := by
    change (twoCells.points 0 + twoCells.points 1) / 2 = 1 / 4
    rw [points_zero, points_one]
    norm_num
  have hm1 : (twoCells.points (Fin.castSucc (1 : Fin 2)) +
      twoCells.points (Fin.succ (1 : Fin 2))) / 2 = 3 / 4 := by
    change (twoCells.points 1 + twoCells.points 2) / 2 = 3 / 4
    rw [points_one, points_two]
    norm_num
  have hsum : midpointLoad twoCells (fun ξ => ξ ^ 2) 1 =
      width twoCells (0 : Fin 2) * (((twoCells.points (Fin.castSucc (0 : Fin 2)) +
        twoCells.points (Fin.succ (0 : Fin 2))) / 2) ^ 2 *
        hat twoCells 1 ((twoCells.points (Fin.castSucc (0 : Fin 2)) +
          twoCells.points (Fin.succ (0 : Fin 2))) / 2)) +
      width twoCells (1 : Fin 2) * (((twoCells.points (Fin.castSucc (1 : Fin 2)) +
        twoCells.points (Fin.succ (1 : Fin 2))) / 2) ^ 2 *
        hat twoCells 1 ((twoCells.points (Fin.castSucc (1 : Fin 2)) +
          twoCells.points (Fin.succ (1 : Fin 2))) / 2)) :=
    Fin.sum_univ_two _
  rw [hsum, hw0, hw1, hm0, hm1, hat_left ⟨by norm_num, by norm_num⟩,
    hat_right ⟨by norm_num, by norm_num⟩]
  norm_num

/-- The load defect `1 / 96` and the coefficient defect `1 / 384` (division by the unit
stiffness `4`); the exact-load coefficient `7 / 192` is the nodal value `û (1 / 2)`. -/
lemma quad_defects_twoCells :
    midpointLoad twoCells (fun ξ => ξ ^ 2) 1 - load twoCells (fun ξ => ξ ^ 2) 1 = 1 / 96 ∧
      midpointLoad twoCells (fun ξ => ξ ^ 2) 1 / stiffness twoCells 1 1 -
          load twoCells (fun ξ => ξ ^ 2) 1 / stiffness twoCells 1 1 = 1 / 384 ∧
      load twoCells (fun ξ => ξ ^ 2) 1 / stiffness twoCells 1 1 = quadProfile (1 / 2) := by
  rw [load_quad_twoCells, midpointLoad_quad_twoCells, stiffness_twoCells_one]
  norm_num [quadProfile]

/-! ## E. The physical quadratic load -/

/-- The amplitude `β = Q * L ^ 2 / EA` of the quadratic load `Q * (x / L) ^ 2`. -/
noncomputable def quadAmplitude (EA L Q : ℝ) : ℝ :=
  Q * L ^ 2 / EA

/-- The physical displacement `u x = β * û (x / L)` under the quadratic load. -/
noncomputable def quadDisplacement (EA L Q x : ℝ) : ℝ :=
  quadAmplitude EA L Q * quadProfile (x / L)

/-- The exact consistent load `∫₀ᴸ Q (x / L) ^ 2 φ (x / L)` of the interior node. -/
noncomputable def quadLoad (L Q : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, Q * (x / L) ^ 2 * hat twoCells 1 (x / L)

/-- The composite midpoint rule on the physical two-cell mesh of `[0, L]` at the interior node:
cells of width `L / 2` with midpoints `L / 4` and `3 * L / 4`, the load `q` times the pulled-back
hat `φ (x / L)` at each midpoint. -/
noncomputable def physMidpointLoad (L : ℝ) (q : ℝ → ℝ) : ℝ :=
  L / 2 * (q (L / 4) * hat twoCells 1 (L / 4 / L)) +
    L / 2 * (q (3 * L / 4) * hat twoCells 1 (3 * L / 4 / L))

/-- The quadratic-load amplitude is twice the uniform-load amplitude of the same `Q`:
`β = 2 α`. -/
lemma quadAmplitude_eq_two_mul (EA L Q : ℝ) :
    quadAmplitude EA L Q = 2 * barAmplitude EA L Q := by
  unfold quadAmplitude barAmplitude
  ring

/-- The physical forcing: `u = β * û (x / L)` solves the fixed-fixed bar problem
`-(EA * u'') = Q * (x / L) ^ 2`, `u 0 = u L = 0`. -/
lemma isFixedFixedSolution_quadDisplacement {EA L : ℝ} (hL : 0 < L) (hEA : 0 < EA) (Q : ℝ) :
    IsFixedFixedSolution EA L (fun x => Q * (x / L) ^ 2) (quadDisplacement EA L Q) := by
  have hL0 := hL.ne'
  have hEA0 := hEA.ne'
  set β := quadAmplitude EA L Q with hβ
  have hpoly : quadDisplacement EA L Q =
      fun x => β / (12 * L) * x + (-(β / (12 * L ^ 4))) * x ^ 4 := by
    funext x
    unfold quadDisplacement quadProfile
    rw [← hβ]
    field_simp
    ring
  have hcd : ContDiff ℝ 2 (quadDisplacement EA L Q) := by
    rw [hpoly]
    fun_prop
  have hd1 : ∀ x : ℝ, HasDerivAt (fun x => β / (12 * L) * x + (-(β / (12 * L ^ 4))) * x ^ 4)
      (β / (12 * L) + 4 * (-(β / (12 * L ^ 4))) * x ^ 3) x := by
    intro x
    have h := ((hasDerivAt_id' x).const_mul (β / (12 * L))).add
      ((hasDerivAt_pow 4 x).const_mul (-(β / (12 * L ^ 4))))
    convert h using 1
    norm_num
    ring
  have hd2 : ∀ x : ℝ, HasDerivAt (fun x => β / (12 * L) + 4 * (-(β / (12 * L ^ 4))) * x ^ 3)
      (12 * (-(β / (12 * L ^ 4))) * x ^ 2) x := by
    intro x
    have h := ((hasDerivAt_pow 3 x).const_mul (4 * (-(β / (12 * L ^ 4))))).const_add
      (β / (12 * L))
    convert h using 1
    norm_num
    ring
  refine ⟨hcd.contDiffOn, fun x hx => ?_, by simp [quadDisplacement, quadProfile], ?_⟩
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hL) hcd.contDiffAt hx,
      iteratedDeriv_succ, iteratedDeriv_one, hpoly,
      show deriv (fun x => β / (12 * L) * x + (-(β / (12 * L ^ 4))) * x ^ 4) =
        fun x => β / (12 * L) + 4 * (-(β / (12 * L ^ 4))) * x ^ 3 from
        funext fun x => (hd1 x).deriv, (hd2 x).deriv, hβ, quadAmplitude]
    field_simp
  · simp [quadDisplacement, quadProfile, div_self hL0]

/-- For `EA ≠ 0` and `L ≠ 0` the amplitude is nonzero exactly for a nonzero load. -/
lemma quadAmplitude_ne_zero_iff {EA L : ℝ} (hEA : EA ≠ 0) (hL : L ≠ 0) (Q : ℝ) :
    quadAmplitude EA L Q ≠ 0 ↔ Q ≠ 0 := by
  unfold quadAmplitude
  constructor
  · intro h hq
    apply h
    simp [hq]
  · intro hq
    exact div_ne_zero (mul_ne_zero hq (pow_ne_zero 2 hL)) hEA

/-- Inverse normalization, only for `β ≠ 0`: `û ξ = β⁻¹ * u (L * ξ)`. -/
lemma quadProfile_eq_inv_quadAmplitude_mul {EA L Q : ℝ} (hL : L ≠ 0)
    (hβ : quadAmplitude EA L Q ≠ 0) (ξ : ℝ) :
    quadProfile ξ = (quadAmplitude EA L Q)⁻¹ * quadDisplacement EA L Q (L * ξ) := by
  rw [quadDisplacement, mul_div_cancel_left₀ ξ hL, inv_mul_cancel_left₀ hβ]

/-- Zero load, treated directly: the amplitude, the displacement and both interior loads
vanish. -/
lemma quad_zero_load (EA L : ℝ) :
    quadAmplitude EA L 0 = 0 ∧ (∀ x, quadDisplacement EA L 0 x = 0) ∧ quadLoad L 0 = 0 ∧
      physMidpointLoad L (fun x => 0 * (x / L) ^ 2) = 0 := by
  refine ⟨by simp [quadAmplitude], fun x => by simp [quadDisplacement, quadAmplitude], ?_, ?_⟩
  · simp [quadLoad]
  · simp [physMidpointLoad]

/-- The physical loads are `Q * L` times the normalized ones, exact and midpoint. -/
lemma quad_physical_loads {L : ℝ} (hL : 0 < L) (Q : ℝ) :
    quadLoad L Q = Q * L * load twoCells (fun ξ => ξ ^ 2) 1 ∧
      physMidpointLoad L (fun x => Q * (x / L) ^ 2) =
        Q * L * midpointLoad twoCells (fun ξ => ξ ^ 2) 1 := by
  have hL0 := hL.ne'
  constructor
  · have hi : ∫ x in (0 : ℝ)..L, Q * (x / L) ^ 2 * hat twoCells 1 (x / L) =
        ∫ x in (0 : ℝ)..L, Q * ((fun ξ => ξ ^ 2 * hat twoCells 1 ξ) (L⁻¹ * x)) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [div_eq_inv_mul]
      ring
    rw [quadLoad, hi, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun ξ => ξ ^ 2 * hat twoCells 1 ξ)
        (inv_ne_zero hL0), mul_zero, inv_mul_cancel₀ hL0, inv_inv, smul_eq_mul, load]
    ring
  · rw [midpointLoad_quad_twoCells, physMidpointLoad, show L / 4 / L = 1 / 4 by field_simp,
      show 3 * L / 4 / L = 3 / 4 by field_simp, hat_left ⟨by norm_num, by norm_num⟩,
      hat_right ⟨by norm_num, by norm_num⟩]
    ring

/-! ## F. Coefficients and the reconstructed quadrature error -/

/-- The exact-load interior coefficient `F / K`. -/
noncomputable def quadCoeff (EA L Q : ℝ) : ℝ :=
  quadLoad L Q / twoCellStiffness EA L

/-- The midpoint-quadrature interior coefficient `F_mid / K`. -/
noncomputable def quadMidpointCoeff (EA L Q : ℝ) : ℝ :=
  physMidpointLoad L (fun x => Q * (x / L) ^ 2) / twoCellStiffness EA L

/-- The residual `F_mid - K * c` that an approximate interior coefficient `c` leaves in the
midpoint system. -/
noncomputable def quadMidpointResidual (EA L Q c : ℝ) : ℝ :=
  physMidpointLoad L (fun x => Q * (x / L) ^ 2) - twoCellStiffness EA L * c

/-- The exact-load coefficient is `7 β / 192`, the nodal value `u (L / 2)`. -/
lemma quadCoeff_eq {EA L : ℝ} (hEA : EA ≠ 0) (hL : 0 < L) (Q : ℝ) :
    quadCoeff EA L Q = 7 * quadAmplitude EA L Q / 192 ∧
      quadCoeff EA L Q = quadDisplacement EA L Q (L / 2) := by
  have hL0 := hL.ne'
  have hq := (quad_physical_loads hL Q).1
  rw [load_quad_twoCells] at hq
  constructor
  · rw [quadCoeff, hq, twoCellStiffness, quadAmplitude]
    field_simp
    ring
  · rw [quadCoeff, hq, twoCellStiffness, quadDisplacement, quadAmplitude, quadProfile,
      show L / 2 / L = 1 / 2 by field_simp]
    field_simp
    ring

/-- The midpoint coefficient is `5 β / 128`. -/
lemma quadMidpointCoeff_eq {EA L : ℝ} (hEA : EA ≠ 0) (hL : L ≠ 0) (Q : ℝ) :
    quadMidpointCoeff EA L Q = 5 * quadAmplitude EA L Q / 128 := by
  have hm : physMidpointLoad L (fun x => Q * (x / L) ^ 2) = Q * L * (5 / 32) := by
    rw [physMidpointLoad, show L / 4 / L = 1 / 4 by field_simp,
      show 3 * L / 4 / L = 3 / 4 by field_simp, hat_left ⟨by norm_num, by norm_num⟩,
      hat_right ⟨by norm_num, by norm_num⟩]
    field_simp
    ring
  rw [quadMidpointCoeff, hm, twoCellStiffness, quadAmplitude]
  field_simp
  ring

/-- The midpoint coefficient differs from the exact-load coefficient by `β / 384` (midpoint
minus exact; for `EA > 0` it has the sign of `Q`); the physical coefficient error is
`|β| / 384`. -/
lemma quadMidpointCoeff_sub_quadCoeff {EA L : ℝ} (hEA : EA ≠ 0) (hL : 0 < L) (Q : ℝ) :
    quadMidpointCoeff EA L Q - quadCoeff EA L Q = quadAmplitude EA L Q / 384 ∧
      |quadCoeff EA L Q - quadMidpointCoeff EA L Q| = |quadAmplitude EA L Q| / 384 := by
  rw [quadMidpointCoeff_eq hEA hL.ne', (quadCoeff_eq hEA hL Q).1]
  constructor
  · ring
  · rw [show 7 * quadAmplitude EA L Q / 192 - 5 * quadAmplitude EA L Q / 128 =
      -(quadAmplitude EA L Q / 384) by ring, abs_neg, abs_div]
    norm_num

/-- The reconstructed coefficient error has squared energy norm
`(4 * EA / L) * (β / 384) ^ 2`. -/
lemma integral_energy_quadrature_error {EA L : ℝ} (hEA : 0 < EA) (hL : 0 < L) (Q : ℝ) :
    ∫ x in (0 : ℝ)..L, EA * deriv (fun x => twoCellReconstruction L (quadCoeff EA L Q) x -
        twoCellReconstruction L (quadMidpointCoeff EA L Q) x) x ^ 2 =
      4 * EA / L * (quadAmplitude EA L Q / 384) ^ 2 := by
  set c₁ := quadCoeff EA L Q
  set c₂ := quadMidpointCoeff EA L Q
  have hfun : (fun x => twoCellReconstruction L c₁ x - twoCellReconstruction L c₂ x) =
      fun x => (c₁ - c₂) * hat twoCells 1 (x / L) := by
    funext x
    simp only [twoCellReconstruction]
    ring
  have hi : ∫ x in (0 : ℝ)..L, EA * deriv (fun x => (c₁ - c₂) * hat twoCells 1 (x / L)) x ^ 2 =
      ∫ x in (0 : ℝ)..L, (c₁ - c₂) ^ 2 *
        (EA * deriv (fun x => hat twoCells 1 (x / L)) x ^ 2) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [deriv_const_mul_field]
    ring
  have hd := (quadMidpointCoeff_sub_quadCoeff hEA.ne' hL Q).1
  have hsq : (c₁ - c₂) ^ 2 = (quadAmplitude EA L Q / 384) ^ 2 := by
    rw [show c₁ - c₂ = -(c₂ - c₁) by ring, hd, neg_sq]
  rw [hfun, hi, intervalIntegral.integral_const_mul, integral_energy_hat EA hL, hsq,
    twoCellStiffness]
  ring

/-- `∫₀ᴸ (c φ (x / L)) ^ 2 = L * c ^ 2 / 3`: the `L²` factor `L / 3` of the hat. -/
private lemma integral_sq_twoCellReconstruction {L : ℝ} (hL : 0 < L) (c : ℝ) :
    ∫ x in (0 : ℝ)..L, twoCellReconstruction L c x ^ 2 = L * c ^ 2 / 3 := by
  have hL0 := hL.ne'
  have hi : ∫ x in (0 : ℝ)..L, twoCellReconstruction L c x ^ 2 =
      ∫ x in (0 : ℝ)..L, c ^ 2 * hat twoCells 1 (L⁻¹ * x) ^ 2 := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [twoCellReconstruction, div_eq_inv_mul]
    ring
  rw [hi, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun ξ => hat twoCells 1 ξ ^ 2) (inv_ne_zero hL0),
    mul_zero, inv_mul_cancel₀ hL0, inv_inv, smul_eq_mul, integral_hat_sq]
  ring

/-- The reconstructed coefficient error has squared `L²` norm `(L / 3) * (β / 384) ^ 2`. -/
lemma integral_sq_quadrature_error {EA L : ℝ} (hEA : EA ≠ 0) (hL : 0 < L) (Q : ℝ) :
    ∫ x in (0 : ℝ)..L, (twoCellReconstruction L (quadCoeff EA L Q) x -
        twoCellReconstruction L (quadMidpointCoeff EA L Q) x) ^ 2 =
      L / 3 * (quadAmplitude EA L Q / 384) ^ 2 := by
  have hfun : (fun x => (twoCellReconstruction L (quadCoeff EA L Q) x -
      twoCellReconstruction L (quadMidpointCoeff EA L Q) x) ^ 2) =
      fun x => twoCellReconstruction L (quadCoeff EA L Q - quadMidpointCoeff EA L Q) x ^ 2 := by
    funext x
    simp only [twoCellReconstruction]
    ring
  have hd := (quadMidpointCoeff_sub_quadCoeff hEA hL Q).1
  have hsq : (quadCoeff EA L Q - quadMidpointCoeff EA L Q) ^ 2 =
      (quadAmplitude EA L Q / 384) ^ 2 := by
    rw [show quadCoeff EA L Q - quadMidpointCoeff EA L Q =
      -(quadMidpointCoeff EA L Q - quadCoeff EA L Q) by ring, hd, neg_sq]
  rw [hfun, integral_sq_twoCellReconstruction hL, hsq]
  ring

/-! ## G. Composition with the residual and the discretization error -/

/-- The residual identity of the midpoint system: `c_mid - c = L * r / (4 * EA)`. -/
lemma quadMidpointCoeff_sub_eq {EA L : ℝ} (hEA : EA ≠ 0) (hL : L ≠ 0) (Q c : ℝ) :
    quadMidpointCoeff EA L Q - c = L * quadMidpointResidual EA L Q c / (4 * EA) := by
  unfold quadMidpointCoeff quadMidpointResidual twoCellStiffness
  field_simp

/-- A quadratic `S t = A - 2 t B + t ^ 2 C` that is nonnegative for every `t` satisfies the
triangle inequality `√(S c) ≤ √(S c₀) + √C |c - c₀|`. -/
private lemma sqrt_quadratic_le {A B C : ℝ} (hC : 0 ≤ C)
    (hS : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C) (c c₀ : ℝ) :
    √(A - 2 * c * B + c ^ 2 * C) ≤ √(A - 2 * c₀ * B + c₀ ^ 2 * C) + √C * |c - c₀| := by
  set S₀ := A - 2 * c₀ * B + c₀ ^ 2 * C with hS₀
  have hS0 : 0 ≤ S₀ := hS c₀
  have hdisc : (c₀ * C - B) ^ 2 ≤ C * S₀ := by
    have h := discrim_le_zero (a := C) (b := 2 * (c₀ * C - B)) (c := S₀) (fun s => by
      have := hS (c₀ + s)
      simp only [hS₀]
      nlinarith [this])
    unfold discrim at h
    nlinarith [h]
  have hD : |c₀ * C - B| ≤ √C * √S₀ := by
    rw [← Real.sqrt_mul hC, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hdisc
  have hexp : A - 2 * c * B + c ^ 2 * C =
      S₀ + 2 * (c - c₀) * (c₀ * C - B) + (c - c₀) ^ 2 * C := by
    simp only [hS₀]
    ring
  have hcross : 2 * (c - c₀) * (c₀ * C - B) ≤ 2 * |c - c₀| * (√C * √S₀) := by
    have h1 : (c - c₀) * (c₀ * C - B) ≤ |c - c₀| * |c₀ * C - B| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h2 : |c - c₀| * |c₀ * C - B| ≤ |c - c₀| * (√C * √S₀) :=
      mul_le_mul_of_nonneg_left hD (abs_nonneg _)
    linarith
  have hsq : (√S₀ + √C * |c - c₀|) ^ 2 =
      S₀ + 2 * |c - c₀| * (√C * √S₀) + (c - c₀) ^ 2 * C := by
    have e1 : √S₀ ^ 2 = S₀ := Real.sq_sqrt hS0
    have e2 : √C ^ 2 = C := Real.sq_sqrt hC
    have e3 : |c - c₀| ^ 2 = (c - c₀) ^ 2 := sq_abs _
    nlinarith [e1, e2, e3]
  have hle : A - 2 * c * B + c ^ 2 * C ≤ (√S₀ + √C * |c - c₀|) ^ 2 := by
    rw [hexp, hsq]
    linarith
  calc √(A - 2 * c * B + c ^ 2 * C) ≤ √((√S₀ + √C * |c - c₀|) ^ 2) := Real.sqrt_le_sqrt hle
    _ = √S₀ + √C * |c - c₀| := Real.sqrt_sq (by positivity)

/-- `∫ₐᵇ EA (u' + k) ^ 2 = ∫ₐᵇ EA u' ^ 2 + 2 EA k (u b - u a) + EA k ^ 2 (b - a)` for a `C¹`
function `u` and a constant `k`. -/
private lemma integral_energy_shift {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (EA k a b : ℝ) :
    ∫ x in a..b, EA * (deriv u x + k) ^ 2 =
      (∫ x in a..b, EA * deriv u x ^ 2) + 2 * EA * k * (u b - u a) + EA * k ^ 2 * (b - a) := by
  have hdc : Continuous (deriv u) := hu.continuous_deriv le_rfl
  have hdu : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hftc : ∫ x in a..b, deriv u x = u b - u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (hdu x).hasDerivAt)
      (hdc.intervalIntegrable _ _)
  have hi1 : IntervalIntegrable (fun x => EA * deriv u x ^ 2) MeasureTheory.volume a b :=
    (continuous_const.mul (hdc.pow 2)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => 2 * EA * k * deriv u x) MeasureTheory.volume a b :=
    (continuous_const.mul hdc).intervalIntegrable _ _
  have e : (fun x => EA * (deriv u x + k) ^ 2) =
      fun x => (EA * deriv u x ^ 2 + 2 * EA * k * deriv u x) + EA * k ^ 2 := by
    funext x
    ring
  have h2 : ∫ x in a..b, 2 * EA * k * deriv u x = 2 * EA * k * (u b - u a) := by
    rw [intervalIntegral.integral_const_mul, hftc]
  rw [e, intervalIntegral.integral_add (hi1.add hi2) intervalIntegrable_const,
    intervalIntegral.integral_add hi1 hi2, h2, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Energy of `u - c φ (x / L)` for a `C¹` function `u`: a quadratic in `c` with the
coefficients `∫₀ᴸ EA u' ^ 2`, `K (u (L / 2) - (u 0 + u L) / 2)` and `K`. -/
private lemma integral_energy_sub_twoCellReconstruction {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (EA : ℝ) {L : ℝ} (hL : 0 < L) (c : ℝ) :
    ∫ x in (0 : ℝ)..L, EA * deriv (fun x => u x - twoCellReconstruction L c x) x ^ 2 =
      (∫ x in (0 : ℝ)..L, EA * deriv u x ^ 2) -
        2 * c * (twoCellStiffness EA L * (u (L / 2) - (u 0 + u L) / 2)) +
        c ^ 2 * twoCellStiffness EA L := by
  have hL0 := hL.ne'
  have hdc : Continuous (deriv u) := hu.continuous_deriv le_rfl
  have hdu : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hleft : ∀ x ∈ Set.Ioo (0 : ℝ) (L / 2),
      deriv (fun x => u x - twoCellReconstruction L c x) x = deriv u x + -(2 * c / L) := by
    intro x hx
    have hrec : HasDerivAt (fun y => twoCellReconstruction L c y) (2 * c / L) x := by
      have hlin : HasDerivAt (fun y : ℝ => c * (2 * (y / L))) (2 * c / L) x := by
        have h := (((hasDerivAt_id x).div_const L).const_mul 2).const_mul c
        exact h.congr_deriv (by ring)
      refine hlin.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      simp only [twoCellReconstruction]
      rw [hat_left ⟨div_nonneg hy.1.le hL.le, by
        rw [div_le_iff₀ hL]; linarith [hy.2]⟩]
    have h : HasDerivAt (fun x => u x - twoCellReconstruction L c x) (deriv u x - 2 * c / L) x :=
      (hdu x).hasDerivAt.sub hrec
    rw [h.deriv]
    ring
  have hright : ∀ x ∈ Set.Ioo (L / 2) L,
      deriv (fun x => u x - twoCellReconstruction L c x) x = deriv u x + 2 * c / L := by
    intro x hx
    have hrec : HasDerivAt (fun y => twoCellReconstruction L c y) (-(2 * c / L)) x := by
      have hlin : HasDerivAt (fun y : ℝ => c * (2 - 2 * (y / L))) (-(2 * c / L)) x := by
        have h := ((((hasDerivAt_id x).div_const L).const_mul 2).const_sub 2).const_mul c
        exact h.congr_deriv (by ring)
      refine hlin.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      simp only [twoCellReconstruction]
      rw [hat_right ⟨by rw [le_div_iff₀ hL]; linarith [hy.1],
        (div_le_one hL).mpr hy.2.le⟩]
    have h : HasDerivAt (fun x => u x - twoCellReconstruction L c x)
        (deriv u x - -(2 * c / L)) x := (hdu x).hasDerivAt.sub hrec
    rw [h.deriv]
    ring
  have hL2 : (0 : ℝ) ≤ L / 2 := by positivity
  have hL2' : L / 2 ≤ L := by linarith
  have heq0 : Set.EqOn (fun x => EA * (deriv u x + -(2 * c / L)) ^ 2)
      (fun x => EA * deriv (fun x => u x - twoCellReconstruction L c x) x ^ 2)
      (Set.uIoo 0 (L / 2)) := by
    intro x hx
    rw [Set.uIoo_of_le hL2] at hx
    simp only [hleft x hx]
  have heq1 : Set.EqOn (fun x => EA * (deriv u x + 2 * c / L) ^ 2)
      (fun x => EA * deriv (fun x => u x - twoCellReconstruction L c x) x ^ 2)
      (Set.uIoo (L / 2) L) := by
    intro x hx
    rw [Set.uIoo_of_le hL2'] at hx
    simp only [hright x hx]
  have hc0 : Continuous fun x => EA * (deriv u x + -(2 * c / L)) ^ 2 := by fun_prop
  have hc1 : Continuous fun x => EA * (deriv u x + 2 * c / L) ^ 2 := by fun_prop
  have hcu : Continuous fun x => EA * deriv u x ^ 2 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hc0.intervalIntegrable 0 (L / 2)).congr_uIoo heq0)
      ((hc1.intervalIntegrable (L / 2) L).congr_uIoo heq1),
    ← intervalIntegral.integral_congr_uIoo heq0, ← intervalIntegral.integral_congr_uIoo heq1,
    integral_energy_shift hu, integral_energy_shift hu,
    ← intervalIntegral.integral_add_adjacent_intervals (hcu.intervalIntegrable 0 (L / 2))
      (hcu.intervalIntegrable (L / 2) L), twoCellStiffness]
  field_simp
  ring

/-- `∫₀ᴸ (u - c φ (x / L)) ^ 2` for a continuous `u`: a quadratic in `c` with the coefficients
`∫₀ᴸ u ^ 2`, `∫₀ᴸ u φ (x / L)` and `L / 3`. -/
private lemma integral_sq_sub_twoCellReconstruction {u : ℝ → ℝ} (hu : Continuous u) {L : ℝ}
    (hL : 0 < L) (c : ℝ) :
    ∫ x in (0 : ℝ)..L, (u x - twoCellReconstruction L c x) ^ 2 =
      (∫ x in (0 : ℝ)..L, u x ^ 2) - 2 * c * (∫ x in (0 : ℝ)..L, u x * hat twoCells 1 (x / L)) +
        c ^ 2 * (L / 3) := by
  have hφ : Continuous fun x => hat twoCells 1 (x / L) :=
    continuous_hat.comp (continuous_id.div_const L)
  have h1 := integral_sq_twoCellReconstruction hL 1
  simp only [twoCellReconstruction, one_mul, one_pow, mul_one] at h1
  have hi1 : IntervalIntegrable (fun x => u x ^ 2) MeasureTheory.volume 0 L :=
    (hu.pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => 2 * c * (u x * hat twoCells 1 (x / L)))
      MeasureTheory.volume 0 L := (continuous_const.mul (hu.mul hφ)).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun x => c ^ 2 * hat twoCells 1 (x / L) ^ 2)
      MeasureTheory.volume 0 L := (continuous_const.mul (hφ.pow 2)).intervalIntegrable _ _
  have e : (fun x => (u x - twoCellReconstruction L c x) ^ 2) =
      fun x => (u x ^ 2 - 2 * c * (u x * hat twoCells 1 (x / L))) +
        c ^ 2 * hat twoCells 1 (x / L) ^ 2 := by
    funext x
    simp only [twoCellReconstruction]
    ring
  rw [e, intervalIntegral.integral_add (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h1]

/-- Composed energy-norm bound: the energy error of the reconstruction `c φ (x / L)` of an
approximate midpoint coefficient is at most the reconstructed discretization error of the
exact-load coefficient, plus the quadrature term `√K * |β| / 384`, plus the algebraic term
`√K * L * |r| / (4 * EA)`. -/
lemma sqrt_energy_quad_error_le {EA L : ℝ} (hEA : 0 < EA) (hL : 0 < L) (Q c : ℝ) :
    √(∫ x in (0 : ℝ)..L,
        EA * deriv (fun x => quadDisplacement EA L Q x - twoCellReconstruction L c x) x ^ 2) ≤
      √(∫ x in (0 : ℝ)..L, EA * deriv (fun x => quadDisplacement EA L Q x -
          twoCellReconstruction L (quadCoeff EA L Q) x) x ^ 2) +
        √(twoCellStiffness EA L) * (|quadAmplitude EA L Q| / 384) +
        √(twoCellStiffness EA L) * (L * |quadMidpointResidual EA L Q c| / (4 * EA)) := by
  have hL0 := hL.ne'
  have hEA0 := hEA.ne'
  set u := quadDisplacement EA L Q with hu
  have huc : ContDiff ℝ 1 u := by
    change ContDiff ℝ 1 (fun x => quadAmplitude EA L Q * ((x / L - (x / L) ^ 4) / 12))
    fun_prop
  have hu0 : u 0 = 0 := by simp [hu, quadDisplacement, quadProfile]
  have huL : u L = 0 := by simp [hu, quadDisplacement, quadProfile, div_self hL0]
  have hK : 0 ≤ twoCellStiffness EA L := by
    rw [twoCellStiffness]
    positivity
  set A := ∫ x in (0 : ℝ)..L, EA * deriv u x ^ 2
  set B := twoCellStiffness EA L * (u (L / 2) - (u 0 + u L) / 2)
  have hE : ∀ t, ∫ x in (0 : ℝ)..L, EA * deriv (fun x => u x - twoCellReconstruction L t x) x ^ 2 =
      A - 2 * t * B + t ^ 2 * twoCellStiffness EA L := fun t =>
    integral_energy_sub_twoCellReconstruction huc EA hL t
  have hS : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * twoCellStiffness EA L := by
    intro t
    rw [← hE t]
    exact intervalIntegral.integral_nonneg hL.le fun x _ => by positivity
  have hmain := sqrt_quadratic_le hK hS c (quadCoeff EA L Q)
  rw [← hE c, ← hE (quadCoeff EA L Q)] at hmain
  have hres := quadMidpointCoeff_sub_eq hEA0 hL0 Q c
  have hq := (quadMidpointCoeff_sub_quadCoeff hEA0 hL Q).2
  have htri : |c - quadCoeff EA L Q| ≤
      |quadAmplitude EA L Q| / 384 + L * |quadMidpointResidual EA L Q c| / (4 * EA) := by
    have h1 : |c - quadCoeff EA L Q| ≤
        |quadCoeff EA L Q - quadMidpointCoeff EA L Q| + |quadMidpointCoeff EA L Q - c| := by
      rw [abs_sub_comm c]
      exact abs_sub_le _ _ _
    have h2 : |quadMidpointCoeff EA L Q - c| = L * |quadMidpointResidual EA L Q c| / (4 * EA) := by
      rw [hres, abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by positivity : (0 : ℝ) < 4 * EA)]
    linarith [h1, h2, hq]
  calc _ ≤ _ := hmain
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left htri (Real.sqrt_nonneg (twoCellStiffness EA L))
      linarith

/-- Composed `L²` bound: the `L²` error of the reconstruction `c φ (x / L)` of an approximate
midpoint coefficient is at most the reconstructed discretization error of the exact-load
coefficient, plus `√(L / 3) * |β| / 384`, plus `√(L / 3) * L * |r| / (4 * EA)`. -/
lemma sqrt_sq_quad_error_le {EA L : ℝ} (hEA : 0 < EA) (hL : 0 < L) (Q c : ℝ) :
    √(∫ x in (0 : ℝ)..L, (quadDisplacement EA L Q x - twoCellReconstruction L c x) ^ 2) ≤
      √(∫ x in (0 : ℝ)..L,
          (quadDisplacement EA L Q x - twoCellReconstruction L (quadCoeff EA L Q) x) ^ 2) +
        √(L / 3) * (|quadAmplitude EA L Q| / 384) +
        √(L / 3) * (L * |quadMidpointResidual EA L Q c| / (4 * EA)) := by
  have hL0 := hL.ne'
  have hEA0 := hEA.ne'
  set u := quadDisplacement EA L Q with hu
  have huc : Continuous u := by
    change Continuous (fun x => quadAmplitude EA L Q * ((x / L - (x / L) ^ 4) / 12))
    fun_prop
  set A := ∫ x in (0 : ℝ)..L, u x ^ 2
  set B := ∫ x in (0 : ℝ)..L, u x * hat twoCells 1 (x / L)
  have hC : (0 : ℝ) ≤ L / 3 := by positivity
  have hE : ∀ t, ∫ x in (0 : ℝ)..L, (u x - twoCellReconstruction L t x) ^ 2 =
      A - 2 * t * B + t ^ 2 * (L / 3) := fun t => integral_sq_sub_twoCellReconstruction huc hL t
  have hS : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * (L / 3) := by
    intro t
    rw [← hE t]
    exact intervalIntegral.integral_nonneg hL.le fun x _ => by positivity
  have hmain := sqrt_quadratic_le hC hS c (quadCoeff EA L Q)
  rw [← hE c, ← hE (quadCoeff EA L Q)] at hmain
  have hres := quadMidpointCoeff_sub_eq hEA0 hL0 Q c
  have hq := (quadMidpointCoeff_sub_quadCoeff hEA0 hL Q).2
  have htri : |c - quadCoeff EA L Q| ≤
      |quadAmplitude EA L Q| / 384 + L * |quadMidpointResidual EA L Q c| / (4 * EA) := by
    have h1 : |c - quadCoeff EA L Q| ≤
        |quadCoeff EA L Q - quadMidpointCoeff EA L Q| + |quadMidpointCoeff EA L Q - c| := by
      rw [abs_sub_comm c]
      exact abs_sub_le _ _ _
    have h2 : |quadMidpointCoeff EA L Q - c| = L * |quadMidpointResidual EA L Q c| / (4 * EA) := by
      rw [hres, abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by positivity : (0 : ℝ) < 4 * EA)]
    linarith [h1, h2, hq]
  calc _ ≤ _ := hmain
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left htri (Real.sqrt_nonneg (L / 3))
      linarith

/-! ## H. Nodal exactness and the remaining errors -/

/-- Nodal exactness of the exact-load coefficient removes neither the quadrature error nor the
off-node error: for `Q ≠ 0` the exact-load coefficient equals `u (L / 2)`, the midpoint
coefficient does not, and at `x = L / 4` the exact-load reconstruction differs from `u` by
`7 β / 3072 ≠ 0` (`u` minus the reconstruction). -/
lemma nodal_exactness_not_enough {EA L Q : ℝ} (hEA : 0 < EA) (hL : 0 < L) (hQ : Q ≠ 0) :
    quadCoeff EA L Q = quadDisplacement EA L Q (L / 2) ∧
      quadMidpointCoeff EA L Q ≠ quadDisplacement EA L Q (L / 2) ∧
      quadDisplacement EA L Q (L / 4) - twoCellReconstruction L (quadCoeff EA L Q) (L / 4) =
        7 * quadAmplitude EA L Q / 3072 ∧
      7 * quadAmplitude EA L Q / 3072 ≠ 0 := by
  have hL0 := hL.ne'
  have hβ : quadAmplitude EA L Q ≠ 0 := (quadAmplitude_ne_zero_iff hEA.ne' hL0 Q).mpr hQ
  have hc := quadCoeff_eq hEA.ne' hL Q
  have hm := quadMidpointCoeff_eq hEA.ne' hL0 Q
  refine ⟨hc.2, ?_, ?_, ?_⟩
  · rw [hm, ← hc.2, hc.1]
    intro h
    apply hβ
    linarith
  · rw [hc.1, twoCellReconstruction, quadDisplacement, quadProfile,
      show L / 4 / L = 1 / 4 by field_simp, hat_left ⟨by norm_num, by norm_num⟩]
    ring
  · intro h
    apply hβ
    linarith

end PhysicalGalerkinError
