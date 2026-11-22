/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.PrimrecList

/-!
# Tests for the primitive recursive list helpers

* `memB` and `dedupB` on small lists, by `decide`.
* `iterate_closed` for a round that adds the successors below 5, starting from `[0]`.
* Primitive recursiveness of `List.all` with a parameter-dependent test, and a `ComputablePred`
  obtained from a correct primitive recursive test.
-/

@[expose] public section

namespace Cslib.Decidability.PrimrecListTests

example : memB [3, 1, 4] 4 = true := by decide
example : memB [3, 1, 4] 2 = false := by decide
example : dedupB [1, 2, 1, 3, 2] = [1, 3, 2] := by decide
example : ∀ x, x ∈ dedupB [1, 2, 1] ↔ x ∈ [1, 2, 1] := fun _ => mem_dedupB

/-- `0` together with the successors below `5` of the numbers found. -/
def addSucc (G : List ℕ) : List ℕ :=
  0 :: (G.map (· + 1)).filter (· < 5)

example : addSucc (addSucc^[[0, 1, 2, 3, 4].length] []) ⊆ addSucc^[[0, 1, 2, 3, 4].length] [] :=
  iterate_closed (fun G G' h x hx => by
      simp only [addSucc, List.mem_cons, List.mem_filter, List.mem_map] at hx ⊢
      rcases hx with rfl | ⟨⟨y, hy, rfl⟩, hlt⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨y, h hy, rfl⟩, hlt⟩)
    [0, 1, 2, 3, 4] fun G x hx => by
      simp only [addSucc, List.mem_cons, List.mem_filter, List.mem_map, decide_eq_true_eq] at hx
      rcases hx with rfl | ⟨-, hlt⟩
      · simp
      · simp only [List.mem_cons, List.not_mem_nil, or_false]; omega

example : Primrec fun p : ℕ × List ℕ => p.2.all (fun x => decide (x < p.1)) :=
  primrec_list_all (Primrec.nat_lt.decide.comp₂ Primrec₂.right (Primrec.fst.comp₂ Primrec₂.left))
    Primrec.snd

example : ComputablePred fun l : List ℕ => 3 ∈ l :=
  computablePred_of_primrec_bool (primrec_memB.comp Primrec.id (Primrec.const 3))
    fun _ => memB_iff

end Cslib.Decidability.PrimrecListTests
