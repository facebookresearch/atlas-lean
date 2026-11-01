/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerIteratedCompression

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerButterflyProve3`

* `iterDownComp` with the empty list is the identity, and with `[0]` is `Down.compression 0`;
* `isLowerSet_iff_forall_downComp_eq_self` applied to the lower set `famA = {∅, {0}}`;
* `exists_iterDownComp_isLowerSet` for the non-lower family `{{0, 1}}`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyProve3

open _root_.StatMech

/-- The lower family `{∅, {0}}` on `Fin 2`. -/
def famA : Finset (Finset (Fin 2)) := {∅, {0}}

/-- The lower family `{∅, {1}}` on `Fin 2`. -/
def famB : Finset (Finset (Fin 2)) := {∅, {1}}

-- `famA` is a lower set.
theorem isLowerSet_famA : IsLowerSet (famA : Set (Finset (Fin 2))) := by
  intro a b hba ha
  simp only [famA, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha ⊢
  rcases ha with rfl | rfl
  · exact Or.inl (Finset.subset_empty.mp hba)
  · exact Finset.subset_singleton_iff.mp hba

-- `famB` is a lower set.
theorem isLowerSet_famB : IsLowerSet (famB : Set (Finset (Fin 2))) := by
  intro a b hba ha
  simp only [famB, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha ⊢
  rcases ha with rfl | rfl
  · exact Or.inl (Finset.subset_empty.mp hba)
  · exact Finset.subset_singleton_iff.mp hba

-- `iterDownComp []` is the identity.
example : iterDownComp [] famA = famA := rfl

-- `iterDownComp [i]` is one down-compression.
example : iterDownComp [0] ({{0}} : Finset (Finset (Fin 2))) = Down.compression 0 {{0}} := rfl

-- Every down-compression fixes the lower set `famA`.
example (i : Fin 2) : Down.compression i famA = famA :=
  (isLowerSet_iff_forall_downComp_eq_self famA).mp isLowerSet_famA i

-- Some iterated compression of `{{0, 1}}` is a lower set.
example : ∃ cs : List (Fin 2),
    IsLowerSet ((iterDownComp cs ({{0, 1}} : Finset (Finset (Fin 2)))) : Set (Finset (Fin 2))) :=
  exists_iterDownComp_isLowerSet _

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyProve3
