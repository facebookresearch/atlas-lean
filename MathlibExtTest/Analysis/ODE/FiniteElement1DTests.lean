/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.FiniteElement1D
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Tests for the one-dimensional P1 finite element method

* The uniform mesh `xⱼ = j / n` is a `Partition 0 1` (non-vacuity of the mesh), with element
  length and mesh size `1 / n`; its stiffness matrix is `n · tridiag(-1, 2, -1)` in the interior.
* Worked example (non-vacuity of `IsClassicalSolution` and `IsGalerkinSolution`): `-u'' = 1`
  with `u = x (1 - x) / 2`. On the two-element mesh the Galerkin system is the single equation
  `4 c₁ = 1 / 2`, solved by `c = (0, 1 / 8, 0)`, the nodal values of `u`; the load entry is
  `∫₀¹ φ₁ = 1 / 2`.
* The exact energy error on that mesh is `‖u - u_h‖_a² = 1 / 48 = h² / 12`, below the proved
  bound `(h / π)² ‖f‖² = 1 / (4π²)`; the `L²` bound gives `‖u - u_h‖² ≤ 1 / (16 π⁴)`.
* Boundary behavior: outside `[0, 1]` a P1 function is constant (equal to the end values).
-/

namespace MathlibExtTest.Analysis.ODE.FiniteElement1DTests

open MathlibExt.Analysis.ODE.FiniteElement1D MathlibExt.Analysis.Integration

/-- The uniform mesh `xⱼ = j / n` of `[0, 1]` with `n ≥ 1` elements. -/
noncomputable abbrev uniformMesh (n : ℕ) (hn : 0 < n) : Partition (0 : ℝ) 1 where
  n := n
  points j := (j : ℝ) / n
  ordered a b hab := by
    have h : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast hab
    exact div_lt_div_of_pos_right h (by exact_mod_cast hn)
  first := by simp
  last := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [this]

/-- The nodes of the uniform mesh. -/
@[simp]
theorem uniformMesh_points (n : ℕ) (hn : 0 < n) (j : Fin (n + 1)) :
    (uniformMesh n hn).points j = (j : ℝ) / n := rfl

/-- Every element of the uniform mesh has length `1 / n`. -/
theorem width_uniformMesh (n : ℕ) (hn : 0 < n) (i : Fin n) :
    width (uniformMesh n hn) i = 1 / n := by
  simp only [width, uniformMesh, Fin.val_succ, Fin.val_castSucc]
  push_cast
  ring

/-- The mesh size of the uniform mesh is `1 / n`. -/
theorem mesh_uniformMesh (n : ℕ) (hn : 0 < n) : (uniformMesh n hn).mesh = 1 / n := by
  refine le_antisymm ?_ ?_
  · have hne : (uniformMesh n hn).n ≠ 0 := hn.ne'
    unfold Partition.mesh
    simp only [hne, ↓reduceDIte]
    refine Finset.sup'_le _ _ fun i _ => ?_
    exact (width_uniformMesh n hn i).le
  · have h := width_le_mesh (uniformMesh n hn) (⟨0, hn⟩ : Fin n)
    rwa [width_uniformMesh] at h

/-- Off-diagonal stiffness entries of the uniform mesh: `K_{i, i+1} = -n`. -/
example (n : ℕ) (hn : 0 < n) (i : Fin n) :
    stiffness (uniformMesh n hn) i.castSucc i.succ = -n := by
  rw [stiffness_castSucc_succ, width_uniformMesh]
  simp

/-- Interior diagonal stiffness entries of the uniform mesh: `K_{jj} = 2 n`. -/
example (n : ℕ) (hn : 0 < n) (i j : Fin n) (hij : i.succ = j.castSucc) :
    stiffness (uniformMesh n hn) i.succ i.succ = 2 * n := by
  rw [stiffness_succ_succ _ hij, width_uniformMesh, width_uniformMesh]
  simp only [one_div, inv_inv]
  ring

/-- Tridiagonality on the uniform mesh with four elements. -/
example : stiffness (uniformMesh 4 (by norm_num)) 0 3 = 0 :=
  stiffness_eq_zero _ (by decide)

/-! ### The worked example `-u'' = 1`, `u = x (1 - x) / 2` -/

/-- The exact solution `u(x) = x (1 - x) / 2` of `-u'' = 1`, `u(0) = u(1) = 0`. -/
noncomputable def exampleSol (x : ℝ) : ℝ := x * (1 - x) / 2

/-- The two-element uniform mesh `0 < 1/2 < 1`. -/
noncomputable abbrev mesh2 : Partition (0 : ℝ) 1 := uniformMesh 2 (by norm_num)

/-- `u'(x) = (1 - 2x) / 2`. -/
theorem hasDerivAt_exampleSol (x : ℝ) : HasDerivAt exampleSol ((1 - 2 * x) / 2) x := by
  unfold exampleSol
  have h := ((hasDerivAt_id' x).mul ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x))).div_const
    2
  convert h using 1
  simp only [Pi.sub_apply]
  ring

/-- `deriv u = fun x => (1 - 2x) / 2`. -/
theorem deriv_exampleSol : deriv exampleSol = fun x => (1 - 2 * x) / 2 :=
  funext fun x => (hasDerivAt_exampleSol x).deriv

/-- `u'' = -1`. -/
theorem deriv_deriv_exampleSol (x : ℝ) : deriv (deriv exampleSol) x = -1 := by
  rw [deriv_exampleSol]
  have h := (((hasDerivAt_id' x).const_mul (2 : ℝ)).const_sub 1).div_const 2
  convert h.deriv using 1
  norm_num

/-- Non-vacuity of `IsClassicalSolution`: `u = x (1 - x) / 2` solves `-u'' = 1`. -/
theorem isClassicalSolution_example : IsClassicalSolution (fun _ => 1) exampleSol where
  contDiff := by
    unfold exampleSol
    fun_prop
  zero_left := by simp [exampleSol]
  zero_right := by simp [exampleSol]
  eq x _ := by rw [deriv_deriv_exampleSol]; norm_num

/-- The Galerkin solution on the two-element mesh is `c = (0, 1/8, 0)` (non-vacuity of
`IsGalerkinSolution`): it is the vector of nodal values of `u`. -/
theorem isGalerkinSolution_example :
    IsGalerkinSolution mesh2 (fun _ => 1) ![0, 1 / 8, 0] := by
  have h := isGalerkinSolution_nodal mesh2 isClassicalSolution_example
  convert h using 1
  funext j
  fin_cases j <;> norm_num [exampleSol]

/-- The interior diagonal stiffness entry of the two-element mesh is `4`. -/
theorem stiffness_mesh2_one_one : stiffness mesh2 1 1 = 4 := by
  have h := stiffness_succ_succ mesh2 (i := (0 : Fin 2)) (j := 1) rfl
  rw [width_uniformMesh, width_uniformMesh] at h
  norm_num at h
  exact h

/-- The Galerkin equation at the interior node reads `4 · (1/8) = 1/2`, so the load entry is
`∫₀¹ φ₁ = 1 / 2`. -/
example : load mesh2 (fun _ => 1) 1 = 1 / 2 := by
  have h := isGalerkinSolution_example.2.2 1 (by decide) (by decide)
  rw [← h, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have h10 : stiffness mesh2 1 0 * 0 = 0 := mul_zero _
  have h12 : stiffness mesh2 1 2 * 0 = 0 := mul_zero _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, h10, h12, stiffness_mesh2_one_one]
  norm_num

/-- The exact energy error on the two-element mesh is `1 / 48 = h² / 12`. -/
theorem energy_error_mesh2 :
    energy (exampleSol - p1 mesh2 ![0, 1 / 8, 0]) (exampleSol - p1 mesh2 ![0, 1 / 8, 0]) =
      1 / 48 := by
  rw [energy_sub_p1_self mesh2 isClassicalSolution_example.contDiff, Fin.sum_univ_two,
    deriv_exampleSol]
  simp only [elementSlope, width_uniformMesh]
  norm_num [mesh2, uniformMesh]
  have e1 : ∀ x : ℝ, ((1 - 2 * x) / 2 - 1 / 4) ^ 2 = (1 / 4 - x) ^ 2 := fun x => by ring
  have e2 : ∀ x : ℝ, ((1 - 2 * x) / 2 + 1 / 4) ^ 2 = (3 / 4 - x) ^ 2 := fun x => by ring
  simp only [e1, e2]
  rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ 2),
    intervalIntegral.integral_comp_sub_left (fun x => x ^ 2)]
  norm_num [integral_pow]

/-- The proved energy bound applies on the two-element mesh: `‖u - u_h‖_a² ≤ 1 / (4π²)`. -/
example :
    energy (exampleSol - p1 mesh2 ![0, 1 / 8, 0]) (exampleSol - p1 mesh2 ![0, 1 / 8, 0]) ≤
      1 / (4 * Real.pi ^ 2) := by
  have h := energy_sub_galerkin_le_mesh mesh2 isClassicalSolution_example
    isGalerkinSolution_example
  rw [mesh_uniformMesh] at h
  norm_num at h
  calc _ ≤ (1 / 2 / Real.pi) ^ 2 := h
    _ = 1 / (4 * Real.pi ^ 2) := by field_simp; norm_num

/-- The bound is consistent with the exact error: `1 / 48 ≤ 1 / (4π²)` since `π² < 12`. -/
example : (1 : ℝ) / 48 ≤ 1 / (4 * Real.pi ^ 2) := by
  have hpi := Real.pi_lt_d2
  have hpos := Real.pi_pos
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

/-- The `L²` bound on the two-element mesh: `‖u - u_h‖² ≤ (1 / (2π))⁴`. -/
example :
    ∫ x in (0 : ℝ)..1, (exampleSol x - p1 mesh2 ![0, 1 / 8, 0] x) ^ 2 ≤
      (1 / 2 / Real.pi) ^ 4 := by
  have h := integral_sq_sub_galerkin_le_mesh mesh2 isClassicalSolution_example
    isGalerkinSolution_example
  rw [mesh_uniformMesh] at h
  norm_num at h
  exact h

/-! ### Boundary behavior -/

/-- Left of `0` a P1 function equals its first nodal value. -/
example (d : Fin 3 → ℝ) : p1 mesh2 d (-1) = d 0 := by
  simp only [p1, ramp, Fin.sum_univ_two]
  norm_num [mesh2, uniformMesh]

/-- Right of `1` a P1 function equals its last nodal value. -/
example (d : Fin 3 → ℝ) : p1 mesh2 d 2 = d 2 := by
  simp only [p1, ramp, Fin.sum_univ_two, elementSlope, width_uniformMesh]
  norm_num [mesh2, uniformMesh]

/-- The P1 function interpolates its nodal values (here the middle node `1 / 2`). -/
example : p1 mesh2 ![0, 1 / 8, 0] (1 / 2) = 1 / 8 := by
  have h := p1_points mesh2 ![0, 1 / 8, 0] 1
  norm_num [mesh2, uniformMesh] at h
  exact h

#print axioms energy_sub_galerkin_le_mesh
#print axioms integral_sq_sub_galerkin_le_mesh

end MathlibExtTest.Analysis.ODE.FiniteElement1DTests
