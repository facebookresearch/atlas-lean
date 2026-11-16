/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank-one coefficient matrices

A complex matrix is in product form, `M i j = a i * b j`, exactly when all its `2 × 2`
minors vanish (`product_iff_minors`), and exactly when its rank is at most one
(`rank_le_one_iff_product`). This is the matrix fact behind the Schmidt-rank-one test
for product states; states themselves are not modeled here, and decompositions of
higher rank are not included.
-/

@[expose] public section

namespace MathlibExt.Quantum.RankOneMatrix

/-- A matrix `M : Fin m → Fin n → ℂ` is in product form, `M i j = a i * b j`, iff all its
`2 × 2` minors vanish. The reverse direction factors through a nonzero entry; the zero
matrix uses zero factors. -/
theorem product_iff_minors {m n : ℕ} (M : Fin m → Fin n → ℂ) :
    (∃ a : Fin m → ℂ, ∃ b : Fin n → ℂ, ∀ i j, M i j = a i * b j)
    ↔ ∀ i₁ i₂ j₁ j₂, M i₁ j₁ * M i₂ j₂ = M i₁ j₂ * M i₂ j₁ := by
  constructor
  · rintro ⟨a, b, hab⟩ i₁ i₂ j₁ j₂
    rw [hab, hab, hab, hab]
    ring
  · intro hmin
    by_cases h : ∀ i j, M i j = 0
    · exact ⟨fun _ => 0, fun _ => 0, fun i j => by simp [h i j]⟩
    · push Not at h
      obtain ⟨i₀, j₀, hne⟩ := h
      refine ⟨fun i => M i j₀, fun j => M i₀ j / M i₀ j₀, fun i j => ?_⟩
      have hkey : M i j * M i₀ j₀ = M i j₀ * M i₀ j := hmin i i₀ j j₀
      have h2 : M i j = M i j₀ * M i₀ j / M i₀ j₀ := by
        rw [eq_div_iff hne]
        exact hkey
      rw [h2, mul_div_assoc]

/-- A complex matrix has rank at most one iff it is in product form. The reverse
direction is Mathlib's `Matrix.rank_vecMulVec_le`; the forward direction writes every
column as a multiple of one vector spanning the column space. -/
theorem rank_le_one_iff_product {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    M.rank ≤ 1 ↔ ∃ a : Fin m → ℂ, ∃ b : Fin n → ℂ, ∀ i j, M i j = a i * b j := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := finrank_le_one_iff.mp h
    choose c hc using fun j : Fin n =>
      hv ⟨M.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩
    refine ⟨(v : Fin m → ℂ), c, fun i j => ?_⟩
    have hcol := congrArg (fun w : LinearMap.range M.mulVecLin => (w : Fin m → ℂ) i) (hc j)
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVecLin_apply,
      Matrix.mulVec_single_one, Matrix.col_apply] at hcol
    rw [← hcol, mul_comm]
  · rintro ⟨a, b, hab⟩
    have hM : M = Matrix.vecMulVec a b := by
      ext i j
      rw [hab, Matrix.vecMulVec_apply]
    rw [hM]
    exact Matrix.rank_vecMulVec_le a b

end MathlibExt.Quantum.RankOneMatrix

end
