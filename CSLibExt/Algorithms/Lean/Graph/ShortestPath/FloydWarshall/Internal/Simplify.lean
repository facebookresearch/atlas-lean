/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Internal.Paths

/-!
# Weighted path simplification

An internal loop-erasure dichotomy: a weighted path either contains a simple negative cycle or
can be shortened to a duplicate-free path of no greater weight.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloydWarshall.Internal

def SimplifiesPath {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (source target : Fin n) (original simplified : List (Fin n)) : Prop :=
  IsWeightedPath weight source target simplified ∧ simplified.Nodup ∧
    pathWeight weight simplified ≤ pathWeight weight original ∧
    ∀ vertex ∈ simplified, vertex ∈ original

lemma negativeCycle_or_simplifies {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    {source target : Fin n} {path : List (Fin n)}
    (hpath : IsWeightedPath weight source target path) :
    HasNegativeCycle weight ∨
      ∃ simplified, SimplifiesPath weight source target path simplified := by
  induction hpath using List.IsChainFromTo.head_induction_on with
  | h_refl =>
      right
      refine ⟨[_], weightedPath_singleton weight _, by simp, ?_, by simp⟩
      exact le_rfl
  | @h_head first second last rest hedge chain induction =>
      rcases induction with hnegative | ⟨simplified, hsimple, hnodup, hweight, hsubset⟩
      · exact Or.inl hnegative
      · by_cases hfirst : first ∈ simplified
        · let index := simplified.idxOf first
          have hindex : index < simplified.length :=
            List.idxOf_lt_length_iff.mpr hfirst
          have hget : simplified[index] = first :=
            List.getElem_idxOf (x := first) hindex
          let cycleTail := simplified.take (index + 1)
          let tailPart := simplified.drop index
          have hprefix : IsWeightedPath weight second first cycleTail := by
            change List.IsChainFromTo (fun left right => weight left right ≠ ⊤)
              cycleTail second first
            simpa [cycleTail, hget] using hsimple.take hindex
          have hsuffix : IsWeightedPath weight first last tailPart := by
            change List.IsChainFromTo (fun left right => weight left right ≠ ⊤)
              tailPart first last
            simpa [tailPart, hget] using hsimple.drop hindex
          let cycle := first :: cycleTail
          have hcycle : IsWeightedPath weight first first cycle := by
            exact hprefix.cons hedge
          have htake : cycleTail = simplified.take index ++ [first] := by
            dsimp only [cycleTail]
            rw [List.take_succ_eq_append_getElem hindex, hget]
          have hnotTake : first ∉ simplified.take index := by
            intro hmem
            have hlt := (List.mem_take_iff_idxOf_lt hfirst).mp hmem
            exact (Nat.lt_irrefl index) hlt
          have htakeNodup : (simplified.take index).Nodup :=
            hnodup.sublist (List.take_sublist ..)
          have hdrop : cycle.dropLast = first :: simplified.take index := by
            dsimp only [cycle]
            rw [htake]
            change ((first :: simplified.take index) ++ [first]).dropLast = _
            rw [List.dropLast_concat]
          have hcycleNodup : cycle.dropLast.Nodup := by
            rw [hdrop]
            exact List.nodup_cons.mpr ⟨hnotTake, htakeNodup⟩
          have hcycleLength : 2 ≤ cycle.length := by
            dsimp only [cycle]
            rw [htake]
            simp
          by_cases hcycleNegative : pathWeight weight cycle < 0
          · left
            exact ⟨cycle, first, hcycle, hcycleLength, hcycleNodup, hcycleNegative⟩
          · right
            have hdecomp : cycle ++ tailPart.tail = first :: simplified := by
              dsimp only [cycle, cycleTail, tailPart]
              simp only [List.cons_append]
              congr 1
              simp [List.tail_drop, List.take_append_drop]
            have hweightDecomp : pathWeight weight (first :: simplified) =
                pathWeight weight cycle + pathWeight weight tailPart := by
              rw [← hdecomp, pathWeight_append_tail weight hcycle hsuffix]
            have hcycleNonnegative : 0 ≤ pathWeight weight cycle := le_of_not_gt hcycleNegative
            have hsuffixLe : pathWeight weight tailPart ≤
                pathWeight weight (first :: simplified) :=
              (le_add_of_nonneg_left hcycleNonnegative).trans_eq hweightDecomp.symm
            have hheadLe : pathWeight weight (first :: simplified) ≤
                pathWeight weight (first :: rest) := by
              rw [pathWeight_cons_of_ne_nil weight first hsimple.ne_nil, hsimple.head_eq,
                pathWeight_cons_of_ne_nil weight first chain.ne_nil, chain.head_eq]
              exact add_le_add_right hweight _
            refine ⟨tailPart, hsuffix, hnodup.sublist (List.drop_sublist ..),
              hsuffixLe.trans hheadLe, ?_⟩
            intro vertex hvertex
            have hsimplified : vertex ∈ simplified := List.mem_of_mem_drop hvertex
            exact List.mem_cons_of_mem first (hsubset vertex hsimplified)
        · right
          have hcombined : IsWeightedPath weight first last (first :: simplified) :=
            hsimple.cons hedge
          have hcombinedWeight : pathWeight weight (first :: simplified) ≤
              pathWeight weight (first :: rest) := by
            rw [pathWeight_cons_of_ne_nil weight first hsimple.ne_nil, hsimple.head_eq,
              pathWeight_cons_of_ne_nil weight first chain.ne_nil, chain.head_eq]
            exact add_le_add_right hweight _
          refine ⟨first :: simplified, hcombined, by simp [hfirst, hnodup],
            hcombinedWeight, ?_⟩
          intro vertex hvertex
          simp only [List.mem_cons] at hvertex ⊢
          exact hvertex.imp_right (hsubset vertex)

lemma exists_nodup_weight_le_of_noNegativeCycle {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (hNoCycle : NoNegativeCycle weight)
    {source target : Fin n} {path : List (Fin n)}
    (hpath : IsWeightedPath weight source target path) :
    ∃ simplified, IsWeightedPath weight source target simplified ∧ simplified.Nodup ∧
      pathWeight weight simplified ≤ pathWeight weight path ∧
      ∀ vertex ∈ simplified, vertex ∈ path := by
  rcases negativeCycle_or_simplifies weight hpath with hnegative | ⟨simple, hsimple⟩
  · exact False.elim (hNoCycle hnegative)
  · exact ⟨simple, hsimple⟩

end Cslib.Algorithms.Lean.FloydWarshall.Internal
