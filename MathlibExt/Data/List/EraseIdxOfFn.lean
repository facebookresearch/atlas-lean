/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Data.List.OfFn

/-!
# Erasing entries from lists defined by finite tuples

This file relates `List.eraseIdx` on `List.ofFn v` to `Fin.removeNth` on the
tuple `v`. It also records the ordered two-deletion formula used when a pair
`i < j` is encoded by `i : Fin (n + 1)` and `j ∈ Finset.Ici i`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace List

variable {α : Type u}

/-- Erasing the entry indexed by `i` from `List.ofFn v` gives the list of the
tuple obtained by removing that entry from `v`. -/
theorem eraseIdx_ofFn {n : ℕ} (v : Fin (n + 1) → α) (i : Fin (n + 1)) :
    (List.ofFn v).eraseIdx i.val = List.ofFn (i.removeNth v) := by
  apply List.ext_getElem
  · rw [List.length_eraseIdx_of_lt (by simpa only [List.length_ofFn] using i.isLt)]
    simp only [List.length_ofFn, Nat.add_sub_cancel]
  · intro j _ hj₂
    rw [List.getElem_eraseIdx]
    simp only [List.getElem_ofFn, Fin.removeNth_apply]
    split_ifs with hj
    · rw [Fin.succAbove_of_castSucc_lt i ⟨j, by simpa using hj₂⟩
        (by change j < i.val; exact hj)]
      rfl
    · rw [Fin.succAbove_of_le_castSucc i ⟨j, by simpa using hj₂⟩
        (by change i.val ≤ j; exact Nat.le_of_not_lt hj)]
      rfl

/-- If `i ≤ j`, deleting the entry `j + 1` and then the entry `i` from
`List.ofFn v` keeps the same ordered tuple as first removing `i` and then
removing `j` from the shortened tuple. -/
theorem eraseIdx_eraseIdx_ofFn {n : ℕ} (v : Fin (n + 2) → α)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    ((List.ofFn v).eraseIdx j.succ.val).eraseIdx i.val =
      List.ofFn (j.removeNth (i.castSucc.removeNth v)) := by
  rw [eraseIdx_ofFn v j.succ, eraseIdx_ofFn (j.succ.removeNth v) i]
  congr 1
  rw [Fin.removeNth_removeNth_eq_swap,
    Fin.predAbove_succ_of_le _ _ hij,
    Fin.succAbove_succ_of_le _ _ hij]

end List
