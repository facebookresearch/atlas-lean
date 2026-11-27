/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

@[expose] public section

open CategoryTheory

namespace SimplexCategory

theorem δ_comp_subinterval {n : ℕ} (j l : ℕ) (hjl : j + l ≤ n)
    (i : Fin (l + 2)) :
    δ i ≫ subinterval j (l + 1) (n := n + 1) (by omega) =
      subinterval j l (n := n) hjl ≫
        δ (⟨j + i.val, by omega⟩ : Fin (n + 2)) := by
  ext k
  have hk : k.val < l + 1 := k.isLt
  change
    (i.succAbove k).val + j =
      ((⟨j + i.val, by omega⟩ : Fin (n + 2)).succAbove
        (⟨k.val + j, by omega⟩ : Fin (n + 1))).val
  by_cases h : k.val < i.val
  · have h1 : k.castSucc < i := h
    simp [Fin.succAbove, h, h1, Nat.add_comm]
  · have h1 : ¬ k.castSucc < i := h
    simp [Fin.succAbove, h, h1, Nat.add_assoc, Nat.add_comm]

end SimplexCategory
