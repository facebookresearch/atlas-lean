/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero.lean`
and
`P2M/Sol/S_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.Algebra.Quaternion
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

/-!
# Splitting quaternion algebras with isotropic norm form

If the norm form `x₀² - a * x₁² - b * x₂² + a * b * x₃²` of a quaternion
algebra `ℍ[K, a, b]` over a field of characteristic not two is isotropic,
then the algebra splits: it is isomorphic to the `2 × 2` matrix algebra.
The proof exhibits explicit matrices for the quaternion units and checks
that the induced map is injective, hence an isomorphism by dimension
count.
-/

@[expose] public section

open scoped Quaternion

namespace QuaternionSplitAux

variable {K : Type} [Field K]

private theorem exists_sq_sub_of_sq (h2 : (2 : K) ≠ 0) {a : K} (b : K) {c : K} (hc : c ≠ 0)
    (hca : c ^ 2 = a) :
    ∃ s t : K, s ^ 2 - a * t ^ 2 = b := by
  refine ⟨(b + 1) / 2, (1 - b) / (2 * c), ?_⟩
  rw [← hca]
  field_simp
  ring

private theorem exists_sq_sub_of_isotropic (h2 : (2 : K) ≠ 0) {a b : K} (ha : a ≠ 0)
    (x₀ x₁ x₂ x₃ : K) (hx : ¬ (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0))
    (h0 : x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0) :
    ∃ s t : K, s ^ 2 - a * t ^ 2 = b := by
  by_cases hD : x₂ ^ 2 - a * x₃ ^ 2 = 0
  · by_cases hx₃ : x₃ = 0
    · have hx₂ : x₂ = 0 := by
        rw [hx₃] at hD; simpa using hD
      have hx₁ : x₁ ≠ 0 := by
        intro hx₁
        apply hx
        rw [hx₁, hx₂, hx₃] at h0
        have : x₀ = 0 := by simpa using h0
        exact ⟨this, hx₁, hx₂, hx₃⟩
      have h0' : x₀ ^ 2 = a * x₁ ^ 2 := by
        rw [hx₂, hx₃] at h0; linear_combination h0
      refine exists_sq_sub_of_sq h2 b (c := x₀ / x₁) ?_ ?_
      · intro hc
        rw [div_eq_zero_iff] at hc
        rcases hc with hc | hc
        · rw [hc] at h0'
          have : a * x₁ ^ 2 = 0 := by simpa using h0'.symm
          rcases mul_eq_zero.mp this with h | h
          · exact ha h
          · exact hx₁ (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
        · exact hx₁ hc
      · field_simp
        linear_combination h0'
    · refine exists_sq_sub_of_sq h2 b (c := x₂ / x₃) ?_ ?_
      · intro hc
        rw [div_eq_zero_iff] at hc
        rcases hc with hc | hc
        · rw [hc] at hD
          have : a * x₃ ^ 2 = 0 := by simpa using hD
          rcases mul_eq_zero.mp this with h | h
          · exact ha h
          · exact hx₃ (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
        · exact hx₃ hc
      · field_simp
        linear_combination hD
  · refine ⟨(x₀ * x₂ - a * x₁ * x₃) / (x₂ ^ 2 - a * x₃ ^ 2),
      (x₀ * x₃ - x₁ * x₂) / (x₂ ^ 2 - a * x₃ ^ 2), ?_⟩
    field_simp
    linear_combination (x₂ ^ 2 - a * x₃ ^ 2) * h0

private def matI (a : K) : Matrix (Fin 2) (Fin 2) K := !![0, a; 1, 0]

private def matJ (a s t : K) : Matrix (Fin 2) (Fin 2) K := !![s, -(a * t); t, -s]

private def basisM (a b s t : K) (hst : s ^ 2 - a * t ^ 2 = b) :
    QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) K) a 0 b where
  i := matI a
  j := matJ a s t
  k := matI a * matJ a s t
  i_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matI, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
  j_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matJ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, ← hst] <;> ring
  i_mul_j := rfl
  j_mul_i := by
    rw [zero_smul, zero_sub]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matI, matJ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply] <;> ring

private theorem lift_apply (a b s t : K) (hst : s ^ 2 - a * t ^ 2 = b)
    (x : QuaternionAlgebra K a 0 b) :
    (basisM a b s t hst).lift x =
      !![x.re + x.imJ * s + x.imK * (a * t), x.imI * a - x.imJ * (a * t) - x.imK * (a * s);
         x.imI + x.imJ * t + x.imK * s, x.re - x.imJ * s - x.imK * (a * t)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QuaternionAlgebra.Basis.lift, basisM, matI, matJ,
      Matrix.add_apply, Matrix.smul_apply, Algebra.algebraMap_eq_smul_one] <;> ring

private theorem lift_injective (h2 : (2 : K) ≠ 0) (a b s t : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hst : s ^ 2 - a * t ^ 2 = b) :
    Function.Injective (basisM a b s t hst).liftHom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  change (basisM a b s t hst).lift x = 0 at hx
  rw [lift_apply] at hx
  have e11 := congrFun (congrFun hx 0) 0
  have e12 := congrFun (congrFun hx 0) 1
  have e21 := congrFun (congrFun hx 1) 0
  have e22 := congrFun (congrFun hx 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.zero_apply] at e11 e12 e21 e22
  have hre : x.re = 0 := by
    have : (2 : K) * x.re = 0 := by linear_combination e11 + e22
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h2
    · exact h
  have himI : x.imI = 0 := by
    have : (2 : K) * a * x.imI = 0 := by linear_combination e12 + a * e21
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h h2
      · exact absurd h ha
    · exact h
  have eq1 : x.imJ * s + x.imK * (a * t) = 0 := by linear_combination e11 - hre
  have eq2 : x.imJ * t + x.imK * s = 0 := by linear_combination e21 - himI
  have himJ : x.imJ = 0 := by
    have : x.imJ * b = 0 := by linear_combination s * eq1 - (a * t) * eq2 - x.imJ * hst
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hb
  have himK : x.imK = 0 := by
    have : x.imK * b = 0 := by
      linear_combination (-(t)) * eq1 + s * eq2 - x.imK * hst + 0 * himJ + (t * s - s * t) * himJ
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hb
  ext <;> simp [hre, himI, himJ, himK]

private noncomputable def algEquivMatrix (h2 : (2 : K) ≠ 0) (a b s t : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hst : s ^ 2 - a * t ^ 2 = b) : ℍ[K, a, b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  AlgEquiv.ofBijective (basisM a b s t hst).liftHom (by
    have hinj := lift_injective h2 a b s t ha hb hst
    refine ⟨hinj, ?_⟩
    have hrank : Module.finrank K ℍ[K, a, b] = Module.finrank K (Matrix (Fin 2) (Fin 2) K) := by
      rw [QuaternionAlgebra.finrank_eq_four, Module.finrank_matrix, Fintype.card_fin]
      norm_num
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
      (f := (basisM a b s t hst).liftHom.toLinearMap)).mp hinj)

end QuaternionSplitAux

namespace QuaternionAlgebra

/-- If the norm form of a quaternion algebra over a field of characteristic
not two is isotropic, then the algebra splits: it is isomorphic to the
`2 × 2` matrix algebra. -/
theorem nonempty_algEquiv_matrix_of_normForm_eq_zero
    (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (x₀ x₁ x₂ x₃ : K) (hx : ¬ (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0))
    (h0 : x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0) :
    Nonempty (ℍ[K, a, b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨s, t, hst⟩ :=
    QuaternionSplitAux.exists_sq_sub_of_isotropic h2 ha x₀ x₁ x₂ x₃ hx h0
  exact ⟨QuaternionSplitAux.algEquivMatrix h2 a b s t ha hb hst⟩

end QuaternionAlgebra
