/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.InfiniteUnionPigeonhole

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.InfiniteUnionPigeonhole`

* `bc4_finite_biUnion_infinite` on the family `f 0 = ∅`, `f 1 = ℕ` indexed by `{0, 1}`: the
  infinite member is found (instance), and it must be `f 1`.
* `bc4_finite_sUnion_infinite` on the finite family `{∅, {n | Even n}}` of subsets of `ℕ`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.InfiniteUnionPigeonhole

open _root_.StatMech.Walls

/-- The family `f 0 = ∅`, `f n = ℕ` otherwise. -/
def f (i : ℕ) : Set ℕ := if i = 0 then ∅ else Set.univ

-- Some member of the finite family is infinite; it is not `f 0`.
example : ∃ i ∈ ({0, 1} : Set ℕ), (f i).Infinite ∧ i ≠ 0 := by
  obtain ⟨i, hi, hinf⟩ := bc4_finite_biUnion_infinite (S := {0, 1}) (f := f)
    (Set.toFinite _) (by
      refine Set.infinite_univ.mono fun n _ => ?_
      simp only [Set.mem_iUnion]
      exact ⟨1, by simp, by simp [f]⟩)
  refine ⟨i, hi, hinf, fun h => ?_⟩
  subst h
  simp [f] at hinf

-- The finite family `{∅, evens}` has an infinite member.
example : ∃ t ∈ ({∅, {n | Even n}} : Set (Set ℕ)), t.Infinite :=
  bc4_finite_sUnion_infinite (Set.toFinite _) <|
    (Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n) (fun a b h => by simpa using h)
      fun n => show 2 * n ∈ {n | Even n} from even_two_mul n).mono
      (Set.subset_sUnion_of_mem (t := {n | Even n}) (by simp))

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.InfiniteUnionPigeonhole
