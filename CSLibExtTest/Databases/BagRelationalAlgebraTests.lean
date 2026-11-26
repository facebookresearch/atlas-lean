/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Databases.BagRelationalAlgebra
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Tests for bag relational algebra

Two tuples with a common first value coalesce under projection, but grow the output
multiplicity by both counts. Natural join multiplies the counts for the agreeing pair
and rejects the pair that disagrees on the shared attribute.
-/

namespace Cslib.Databases.BagRelationalAlgebraTests

private abbrev Attr := Fin 3

private def leftTuple (b : ℕ) : Tuple.Over ℕ ({0, 1} : Finset Attr) :=
  ⟨![some 1, some b, none], by
    intro a
    fin_cases a <;> (first | change true = true ↔ _ | change false = true ↔ _) <;> decide⟩

private def rightTuple (b : ℕ) : Tuple.Over ℕ ({1, 2} : Finset Attr) :=
  ⟨![none, some b, some 5], by
    intro a
    fin_cases a <;> (first | change true = true ↔ _ | change false = true ↔ _) <;> decide⟩

private def joinedTuple (b : ℕ) : Tuple.Over ℕ (({0, 1} ∪ {1, 2}) : Finset Attr) :=
  ⟨![some 1, some b, some 5], by
    intro a
    fin_cases a <;> change true = true ↔ _ <;> decide⟩

private def firstTuple : Tuple.Over ℕ ({0} : Finset Attr) :=
  ⟨![some 1, none, none], by unfold Tuple.IsOver; decide⟩

private noncomputable def leftBag : BagRelation ℕ ({0, 1} : Finset Attr) :=
  Finsupp.single (leftTuple 2) 2 + Finsupp.single (leftTuple 3) 3

private noncomputable def rightBag : BagRelation ℕ ({1, 2} : Finset Attr) :=
  Finsupp.single (rightTuple 2) 7

private theorem first_subset : ({0} : Finset Attr) ⊆ {0, 1} := by decide

private theorem restrict_first (b : ℕ) : (leftTuple b).restrict first_subset = firstTuple := by
  apply Subtype.ext
  funext a
  fin_cases a <;> rfl

-- Projecting away the second attribute adds 2 and 3 rather than dropping the duplicate.
example : BagRelation.project first_subset leftBag = Finsupp.single firstTuple 5 := by
  simp [BagRelation.project, leftBag, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    restrict_first, ← Finsupp.single_add]

private theorem restrict_join_left (b : ℕ) :
    (joinedTuple b).restrict Finset.subset_union_left = leftTuple b := by
  apply Subtype.ext
  funext a
  fin_cases a <;> rfl

private theorem restrict_join_right (b : ℕ) :
    (joinedTuple b).restrict Finset.subset_union_right = rightTuple b := by
  apply Subtype.ext
  funext a
  fin_cases a <;> rfl

private theorem left_disagree : leftTuple 3 ≠ leftTuple 2 := fun h => by
  have hb := congrArg (fun t : Tuple.Over ℕ ({0, 1} : Finset Attr) => t.val 1) h
  change some 3 = some 2 at hb
  contradiction

private theorem right_disagree : rightTuple 3 ≠ rightTuple 2 := fun h => by
  have hb := congrArg (fun t : Tuple.Over ℕ ({1, 2} : Finset Attr) => t.val 1) h
  change some 3 = some 2 at hb
  contradiction

example : BagRelation.join leftBag rightBag (joinedTuple 2) = 14 := by
  simp [leftBag, rightBag, restrict_join_left, restrict_join_right, Finsupp.single_eq_of_ne,
    Ne.symm left_disagree]

-- The candidate assembled using the nonagreeing left tuple has no matching right restriction.
example : BagRelation.join leftBag rightBag (joinedTuple 3) = 0 := by
  simp [rightBag, restrict_join_right, Finsupp.single_eq_of_ne, right_disagree]

example : (bagRelationalAlgebra Attr ℕ).union leftBag leftBag (leftTuple 2) = 4 := by
  change BagRelation.union leftBag leftBag (leftTuple 2) = 4
  simp [leftBag, Finsupp.single_eq_of_ne, Ne.symm left_disagree]

example : BagRelation.select (Cond.eqConst 1 2) (by decide) leftBag (leftTuple 2) = 2 := by
  have hc : (Cond.eqConst (1 : Attr) 2).eval (leftTuple 2).val = true := by decide
  simp [hc, leftBag, Finsupp.single_eq_of_ne, Ne.symm left_disagree]

example : BagRelation.select (Cond.eqConst 1 2) (by decide) leftBag (leftTuple 3) = 0 := by
  have hc : ¬ (Cond.eqConst (1 : Attr) 2).eval (leftTuple 3).val = true := by decide
  simp [hc]

private def swappedTuple :
    Tuple.Over ℕ (({0, 1} : Finset Attr).map (Equiv.swap 0 2).toEmbedding) :=
  ⟨![none, some 2, some 1], by unfold Tuple.IsOver; decide⟩

example : BagRelation.rename (Equiv.swap (0 : Attr) 2) leftBag swappedTuple = 2 := by
  have h : Tuple.Over.rename (Equiv.swap 0 2) {0, 1} (leftTuple 2) = swappedTuple := by
    apply Subtype.ext
    funext a
    fin_cases a <;> rfl
  rw [← h]
  simp [leftBag, Finsupp.single_eq_of_ne, Ne.symm left_disagree]

private theorem set_isOver : IsOver ({0, 1} : Finset Attr) {(leftTuple 2).val} := by
  intro t ht
  rw [Finset.mem_singleton] at ht
  simpa only [ht] using (leftTuple 2).property

example : BagRelation.ofFinset {(leftTuple 2).val} set_isOver (leftTuple 2) = 1 := by
  simp

example : BagRelation.ofFinset {(leftTuple 2).val} set_isOver (leftTuple 3) = 0 := by
  have h : (leftTuple 3).val ≠ (leftTuple 2).val := fun h => left_disagree (Subtype.ext h)
  simp [h]

end Cslib.Databases.BagRelationalAlgebraTests
