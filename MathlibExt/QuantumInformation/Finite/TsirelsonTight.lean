/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Source: B. S. Cirel'son/Tsirelson, "Quantum generalizations of Bell's inequality",
  Letters in Mathematical Physics 4(2) (1980), 93-100, DOI 10.1007/BF00417500.
Proof: standard 4x4 CHSH observables (Pauli-type block matrices with
  `s = 1/√2` coefficients); the vector `[s, 0, 0, s]` is an eigenvector of the
  CHSH operator with eigenvalue `2√2`. Every explicit matrix product,
  self-adjointness, commutation, and involution identity below was checked
  entry by entry against the archive candidate before retention.
-/
module

public import Mathlib.Algebra.Star.CHSH
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Matrix

namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

private noncomputable def s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

private noncomputable def u : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

private theorem sqrt2_pos : 0 < Real.sqrt 2 :=
  Real.sqrt_pos.mpr (by norm_num)

private theorem sqrt2_ne : Real.sqrt 2 ≠ 0 :=
  ne_of_gt sqrt2_pos

private theorem sqrt2_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rwa [pow_two] at h

private theorem s_ne_zero : s ≠ 0 := by
  unfold s
  intro h
  have h' : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = (((0 : ℝ)) : ℂ)) := by
    rw [h, Complex.ofReal_zero]
  have h2 : (Real.sqrt 2)⁻¹ = 0 := Complex.ofReal_inj.mp h'
  exact inv_ne_zero sqrt2_ne h2

private theorem u_mul_s : u * s = 1 := by
  unfold u s
  rw [← Complex.ofReal_mul]
  have h : Real.sqrt 2 * (Real.sqrt 2)⁻¹ = 1 := mul_inv_cancel₀ sqrt2_ne
  rw [h, Complex.ofReal_one]

private theorem u_mul_self : u * u = 2 := by
  unfold u
  rw [← Complex.ofReal_mul, sqrt2_mul_self]
  simp

private theorem s_mul_self : s * s = 1 / 2 := by
  unfold s
  rw [← Complex.ofReal_mul]
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 2⁻¹ := by
    rw [← mul_inv, sqrt2_mul_self]
  rw [h, Complex.ofReal_inv]
  have h2 : (((2 : ℝ)) : ℂ) = 2 := by simp
  rw [h2, div_eq_mul_inv, one_mul]

@[simp]
private theorem s_star : star s = s := by
  unfold s
  simp

private def A₀ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

private def A₁ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

private noncomputable def B₀ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![s, s, 0, 0; s, -s, 0, 0; 0, 0, s, s; 0, 0, s, -s]

private noncomputable def B₁ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![s, -s, 0, 0; -s, -s, 0, 0; 0, 0, s, -s; 0, 0, -s, -s]

private noncomputable def v : Fin 4 → ℂ := ![s, 0, 0, s]

private theorem A₀_inv : A₀ ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, A₀]

private theorem A₁_inv : A₁ ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, A₁]

private theorem B₀_inv : B₀ ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, B₀] <;>
    linear_combination 2 * s_mul_self

private theorem B₁_inv : B₁ ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, B₁] <;>
    linear_combination 2 * s_mul_self

private theorem A₀_sa : star A₀ = A₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply, A₀]

private theorem A₁_sa : star A₁ = A₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply, A₁]

private theorem B₀_sa : star B₀ = B₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply, B₀]

private theorem B₁_sa : star B₁ = B₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply, B₁]

private theorem A₀B₀_comm : A₀ * B₀ = B₀ * A₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, A₀, B₀]

private theorem A₀B₁_comm : A₀ * B₁ = B₁ * A₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, A₀, B₁]

private theorem A₁B₀_comm : A₁ * B₀ = B₀ * A₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, A₁, B₀]

private theorem A₁B₁_comm : A₁ * B₁ = B₁ * A₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, A₁, B₁]

private theorem B₀_mulVec_v : B₀ *ᵥ v = ![1 / 2, 1 / 2, 1 / 2, -1 / 2] := by
  ext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, B₀, v, s_mul_self, neg_div]

private theorem B₁_mulVec_v : B₁ *ᵥ v = ![1 / 2, -1 / 2, -1 / 2, -1 / 2] := by
  ext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, B₁, v, s_mul_self, neg_div]

private theorem A₀B₀_mulVec_v : (A₀ * B₀) *ᵥ v = ![1 / 2, 1 / 2, -1 / 2, 1 / 2] := by
  rw [← Matrix.mulVec_mulVec, B₀_mulVec_v]
  ext k
  fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, A₀] <;> ring

private theorem A₀B₁_mulVec_v : (A₀ * B₁) *ᵥ v = ![1 / 2, -1 / 2, 1 / 2, 1 / 2] := by
  rw [← Matrix.mulVec_mulVec, B₁_mulVec_v]
  ext k
  fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, A₀] <;> ring

private theorem A₁B₀_mulVec_v : (A₁ * B₀) *ᵥ v = ![1 / 2, -1 / 2, 1 / 2, 1 / 2] := by
  rw [← Matrix.mulVec_mulVec, B₀_mulVec_v]
  ext k
  fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, A₁]

private theorem A₁B₁_mulVec_v : (A₁ * B₁) *ᵥ v = ![-1 / 2, -1 / 2, 1 / 2, -1 / 2] := by
  rw [← Matrix.mulVec_mulVec, B₁_mulVec_v]
  ext k
  fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, A₁]

private theorem chsh_mulVec_v :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) *ᵥ v = ![2, 0, 0, 2] := by
  have hAdd : (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) *ᵥ v =
      ((A₀ * B₀) *ᵥ v + (A₀ * B₁) *ᵥ v + (A₁ * B₀) *ᵥ v - (A₁ * B₁) *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.add_mulVec]
  rw [hAdd, A₀B₀_mulVec_v, A₀B₁_mulVec_v, A₁B₀_mulVec_v, A₁B₁_mulVec_v]
  ext k
  fin_cases k <;> simp <;> ring

private theorem v_ne_zero : v ≠ 0 := by
  intro h
  have h0 : v 0 = (0 : Fin 4 → ℂ) 0 := by rw [h]
  simp [v, s_ne_zero] at h0

private theorem mu_eq : ((↑(2 * Real.sqrt 2) : ℂ)) = 2 * u := by
  unfold u
  rw [Complex.ofReal_mul]
  simp

private theorem mu_mul_s : ((↑(2 * Real.sqrt 2) : ℂ)) * s = 2 := by
  rw [mu_eq, mul_assoc, u_mul_s, mul_one]

private theorem mu_smul_s : ((↑(2 * Real.sqrt 2) : ℂ)) • s = 2 := by
  rw [smul_eq_mul]
  exact mu_mul_s

private theorem two_eq : (2 : ℂ) = 2 * ((Real.sqrt 2 : ℝ) : ℂ) * s := by
  have h := mu_mul_s
  push_cast at h
  exact h.symm

/--
**Tsirelson's bound is attained.** There exist $4 \times 4$ complex matrices $A_0, A_1, B_0, B_1$
such that each of them is Hermitian and squares to the identity matrix, each $A_i$ commutes with
each $B_j$, and the CHSH operator $A_0 B_0 + A_0 B_1 + A_1 B_0 - A_1 B_1$ has $2\sqrt{2}$ as an
eigenvalue.

This shows that the upper bound $2\sqrt{2}$ in Tsirelson's inequality for CHSH tuples is sharp.

Source: B. S. Cirel'son/Tsirelson, "Quantum generalizations of Bell's inequality", Lett. Math. Phys.
4 (1980), 93-100, DOI 10.1007/BF00417500.
-/
public theorem tsirelson_bound_tight :
    ∃ (A₀ A₁ B₀ B₁ : Matrix (Fin 4) (Fin 4) ℂ),
      IsCHSHTuple A₀ A₁ B₀ B₁ ∧
        Module.End.HasEigenvalue
          (Matrix.toLin' (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁))
          ((↑(2 * Real.sqrt 2) : ℂ)) := by
  refine ⟨A₀, A₁, B₀, B₁,
    ⟨A₀_inv, A₁_inv, B₀_inv, B₁_inv, A₀_sa, A₁_sa, B₀_sa, B₁_sa,
     A₀B₀_comm, A₀B₁_comm, A₁B₀_comm, A₁B₁_comm⟩, ?_⟩
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
  refine ⟨?_, v_ne_zero⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, chsh_mulVec_v]
  ext k
  fin_cases k <;> simp [v, mu_mul_s, smul_eq_mul, -Complex.ofReal_mul]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight
