/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.PosDef.GreedyMinima

open Matrix

variable {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ}

-- Greedy successive minima exist, and the chosen ones are greedy.
example (hY : Y.PosDef) : ∃ v, IsGreedyMinima Y v := exists_isGreedyMinima hY

example (hY : Y.PosDef) : IsGreedyMinima Y hY.greedyMinVec := hY.isGreedyMinima_greedyMinVec

-- `0 < λ₁ ≤ ⋯ ≤ λ_g` for the chosen minima.
example (hY : Y.PosDef) (i j : Fin g) (hij : i ≤ j) :
    0 < hY.succMin i ∧ hY.succMin i ≤ hY.succMin j :=
  ⟨hY.succMin_pos i, hY.monotone_succMin hij⟩

-- Property (b) in the form `y ∉ span {v i | i ≤ k} → λ_{k+1} ≤ Q(y)`.
example {v : Fin g → Fin g → ℤ} (hv : IsGreedyMinima Y v) (k : Fin g) (hk : k.val + 1 < g)
    (y : Fin g → ℤ) (hy : (Int.cast ∘ y : Fin g → ℝ) ∉
      Submodule.span ℝ ((fun i ↦ (Int.cast ∘ v i : Fin g → ℝ)) '' {i | i ≤ k})) :
    (Int.cast ∘ v ⟨k + 1, hk⟩ : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ v ⟨k + 1, hk⟩) ≤
      (Int.cast ∘ y : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ y) :=
  hv.le_of_notMem_span_Iic k hk y hy

-- The downstream pattern: some `v i`, `i ≤ k`, has a nonzero coordinate of index `≥ k`, and
-- its value of `Q` is at most `λ_k`.
example (hY : Y.PosDef) (k : Fin g) :
    ∃ i ≤ k, ∃ j, k ≤ j ∧ hY.greedyMinVec i j ≠ 0 ∧ hY.succMin i ≤ hY.succMin k := by
  obtain ⟨i, hik, j, hkj, hne⟩ := hY.isGreedyMinima_greedyMinVec.exists_le_le_ne_zero k
  exact ⟨i, hik, j, hkj, hne, hY.monotone_succMin hik⟩

-- `λ₁` is the minimum of `Q` on the nonzero integral vectors.
example (hY : Y.PosDef) (hg : 0 < g) (y : Fin g → ℤ) (hy : y ≠ 0) :
    hY.succMin ⟨0, hg⟩ ≤ (Int.cast ∘ y : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ y) :=
  (hY.isGreedyMinima_greedyMinVec.isLeast hg).2 ⟨y, hy, rfl⟩

-- The greedy vectors form a basis of `ℝ^g`.
example {v : Fin g → Fin g → ℤ} (hv : IsGreedyMinima Y v) :
    LinearIndependent ℝ (fun i ↦ (Int.cast ∘ v i : Fin g → ℝ)) ∧
      Submodule.span ℝ (Set.range fun i ↦ (Int.cast ∘ v i : Fin g → ℝ)) = ⊤ :=
  ⟨hv.linearIndependent, hv.span_eq_top⟩

-- Finitely many integral vectors have bounded value of `Q`.
example (hY : Y.PosDef) :
    {z : Fin g → ℤ | (Int.cast ∘ z : Fin g → ℝ) ⬝ᵥ Y *ᵥ (Int.cast ∘ z) ≤ 1}.Finite :=
  hY.finite_setOf_le 1
