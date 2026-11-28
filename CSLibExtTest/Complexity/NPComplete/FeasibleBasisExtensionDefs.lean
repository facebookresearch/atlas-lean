/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.FeasibleBasisExtensionDefs

namespace MetaMathlibExt.Complexity.NPComplete.FeasibleBasisExtension

open Matrix
open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : FeasibleBasisExtensionInstance) :
    feasibleBasisExtensionDec (bitEncode i) = true ↔
      WellFormed i ∧ FeasibleBasisExtensionFeasible i := by
  simp [feasibleBasisExtensionDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : feasibleBasisExtensionDec [true] = false := by
  have h : bitDecode (α := FeasibleBasisExtensionInstance) [true] = none := rfl
  simp [feasibleBasisExtensionDec, h]

/-- `A = [[1, 0, -1], [0, 1, -1]]` and `a = (1, 1)`, with the prescribed columns `S` (integers
`p - q` written as pairs `(p, q)`). -/
private abbrev inst (S : List ℕ) : FeasibleBasisExtensionInstance :=
  (2, 3, [[(1, 0), (0, 0), (0, 1)], [(0, 0), (1, 0), (0, 1)]], [(1, 0), (1, 0)], S)

/-- The first two columns. -/
private def σ₀₁ (S : List ℕ) : Fin (inst S).1 → Fin (inst S).2.1 := fun k =>
  ⟨k.val, by have := k.isLt; simp only [inst] at this ⊢; omega⟩

/-- The first two columns form the identity matrix. -/
private theorem submatrix_σ₀₁ (S : List ℕ) : (matA (inst S)).submatrix id (σ₀₁ S) = 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [matA, intVal, σ₀₁]

/-- Columns `0` and `1` form a basis containing `S = {0}`, the identity, with `B⁻¹ a = (1, 1)`.
-/
example : feasibleBasisExtensionDec (bitEncode (inst [0])) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, σ₀₁ [0], ?_, ?_, ?_, ?_⟩
  · intro j k h
    exact Fin.ext (by simpa [σ₀₁] using congrArg Fin.val h)
  · intro j hj
    obtain rfl : j = 0 := by simpa using hj
    exact ⟨0, rfl⟩
  · rw [submatrix_σ₀₁]
    simp
  · intro k
    rw [submatrix_σ₀₁, inv_one, Matrix.one_mulVec]
    fin_cases k <;> simp [vecA, intVal]

/-- With `S = {2}` every basis contains the column `(-1, -1)`, and then `B v = a` forces a
negative coordinate of `v = B⁻¹ a`. The basis `{0, 1}` above is feasible but misses `S`. -/
example : feasibleBasisExtensionDec (bitEncode (inst [2])) = false := by
  have h : ¬ FeasibleBasisExtensionFeasible (inst [2]) := by
    rintro ⟨σ, -, hS, hdet, hpos⟩
    have hBv : (matA (inst [2])).submatrix id σ *ᵥ
        (((matA (inst [2])).submatrix id σ)⁻¹ *ᵥ vecA (inst [2])) = vecA (inst [2]) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
        Matrix.one_mulVec]
    have e₀ := congrFun hBv 0
    have e₁ := congrFun hBv 1
    have p₀ := hpos 0
    have p₁ := hpos 1
    generalize ((matA (inst [2])).submatrix id σ)⁻¹ *ᵥ vecA (inst [2]) = v at e₀ e₁ p₀ p₁
    obtain ⟨k, hk⟩ := hS 2 (by simp)
    have two : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
    have three : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    have hk₂ : σ 0 = 2 ∨ σ 1 = 2 := by
      rcases two k with rfl | rfl
      · exact Or.inl (Fin.ext hk)
      · exact Or.inr (Fin.ext hk)
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.submatrix_apply, id] at e₀ e₁
    rcases three (σ 0) with h₀ | h₀ | h₀ <;> rcases three (σ 1) with h₁ | h₁ | h₁ <;>
      simp [h₀, h₁, matA, vecA, intVal] at hk₂ e₀ e₁ <;>
      linarith
  simpa [feasibleBasisExtensionDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.FeasibleBasisExtension
