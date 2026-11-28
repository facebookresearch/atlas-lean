/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Data.Sym.SortedTuple

/-!
# Symmetric words with ties and an empty alphabet

Sorting the multiset [2,0,2] gives (0,2,2), retaining multiplicity. The empty alphabet has
one empty word and no one-letter word; both are read through the monotone-tuple equivalence.
-/

noncomputable section

namespace SymmetricTupleBoundaryTests

private def word : Sym (Fin 3) 3 :=
  ⟨(↑[2, 0, 2] : Multiset (Fin 3)), by decide⟩

private def ascending : {f : Fin 3 → Fin 3 // Monotone f} :=
  ⟨![0, 2, 2], by decide⟩

private theorem inverse_word :
    (Sym.sortedTupleEquiv 3).symm ascending = word := by
  apply Subtype.ext
  change (↑(List.ofFn (![0, 2, 2] : Fin 3 → Fin 3)) : Multiset (Fin 3)) = ↑[2, 0, 2]
  decide

example : ((Sym.sortedTupleEquiv 3) word).val = ![0, 2, 2] := by
  have h : (Sym.sortedTupleEquiv 3) word = ascending := by
    rw [← inverse_word]
    exact (Sym.sortedTupleEquiv 3).apply_symm_apply ascending
  exact congrArg Subtype.val h

example : ((Sym.sortedTupleEquiv (α := Fin 0) 0)
    (⟨0, rfl⟩ : Sym (Fin 0) 0)).val = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

example : Fintype.card (Sym (Fin 0) 0) = 1 := by
  rw [Fintype.card_congr (Sym.sortedTupleEquiv (α := Fin 0) 0), Sym.card_monotone_fin]
  decide

example : Fintype.card (Sym (Fin 0) 1) = 0 := by
  rw [Fintype.card_congr (Sym.sortedTupleEquiv (α := Fin 0) 1), Sym.card_monotone_fin]
  decide

end SymmetricTupleBoundaryTests
