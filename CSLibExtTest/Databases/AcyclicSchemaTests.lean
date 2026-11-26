/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Databases.AcyclicSchema
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Boundary cases for acyclic database schemas

The triangle forces $A=B=C$ along two relations and $A\ne C$ on the third.
Every local row has a partner in each other relation, but none extends globally.
The other tests exercise disconnected schemes, an empty relation and the final GYO ear.
-/

namespace Cslib.Databases.AcyclicSchema.Tests

private def triangle : Fin 3 → Finset (Fin 3) := ![{0, 1}, {1, 2}, {0, 2}]

private def rows : Fin 3 → Finset (Tuple (Fin 3) ℕ) :=
  ![{![some 0, some 0, none], ![some 1, some 1, none]},
    {![none, some 0, some 0], ![none, some 1, some 1]},
    {![some 0, none, some 1], ![some 1, none, some 0]}]

private theorem typed : Expr.Conforms triangle rows := by
  unfold Expr.Conforms IsOver Tuple.IsOver
  decide

private theorem pairwise_triangle : PairwiseConsistent triangle rows := by
  unfold PairwiseConsistent
  decide

private theorem triangle_empty : fullJoin triangle rows = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro t ⟨ht, h⟩
  have hU : Finset.univ.biUnion triangle = triangle 0 ∪ triangle 1 := by decide
  have h01 : t ∈ join (rows 0) (rows 1) :=
    (mem_join_iff (typed 0) (typed 1)).mpr ⟨hU ▸ ht, h 0, h 1⟩
  have incompatible : ∀ v ∈ join (rows 0) (rows 1), v.restrict (triangle 2) ∉ rows 2 := by decide
  exact incompatible t h01 (h 2)

private theorem not_global_triangle : ¬ GloballyConsistent triangle rows := by
  intro h
  have ht : ![some 0, some 0, none] ∈ rows 0 := by decide
  change ![some 0, some 0, none] ∈ (rows 0 : Set _) at ht
  rw [← h 0, triangle_empty, Set.image_empty] at ht
  exact ht

example : ¬ HasFullReducer triangle := fun h =>
  not_global_triangle (globallyConsistent_of_hasFullReducer h typed pairwise_triangle)

example : ¬ GYOEmpties triangle := by
  intro h
  have stop : ∀ i, ¬ IsEar triangle Finset.univ i := by unfold IsEar; decide
  exact (by decide : (Finset.univ : Finset (Fin 3)) ≠ ∅) (h _ .refl stop)

-- On two schemes the full join is the existing binary join, so both ordered
-- pairwise tests give precisely the two projection equalities for global consistency.
example {A : Type*} [Fintype A] [DecidableEq A] {sch : Bool → Finset A}
    {I : Bool → Finset (Tuple A ℕ)} (hI : Expr.Conforms sch I) (hp : PairwiseConsistent sch I) :
    GloballyConsistent sch I := by
  have hu : Finset.univ.biUnion sch = sch false ∪ sch true := by
    simp [Fintype.univ_bool, Finset.union_comm]
  have hj : fullJoin sch I = (join (I false) (I true) : Set _) := by
    ext t
    rw [Finset.mem_coe, mem_join_iff (hI false) (hI true)]
    change (t.IsOver _ ∧ ∀ i, t.restrict (sch i) ∈ I i) ↔ _
    rw [hu]
    constructor
    · rintro ⟨h, hs⟩
      exact ⟨h, hs false, hs true⟩
    · rintro ⟨h, hl, hr⟩
      exact ⟨h, fun | false => hl | true => hr⟩
  intro i
  rw [hj, ← Finset.coe_image]
  cases i with
  | false => exact_mod_cast hp false true
  | true => rw [join_comm]; exact_mod_cast hp true false

-- The one-relation program is empty and works also for the empty extent.
example {A : Type*} [Fintype A] [DecidableEq A] (S : Finset A) :
    HasFullReducer (fun _ : Unit => S) := by
  refine ⟨[], fun I hI i => ?_⟩
  change Tuple.restrict S '' fullJoin (fun _ : Unit => S) I = (I i : Set _)
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu.2 i
  · intro ht
    have ho := hI i t ht
    refine ⟨t, ⟨?_, ?_⟩, ho.restrict_self⟩
    · simpa using ho
    · intro j
      rwa [Subsingleton.elim j i, ho.restrict_self]

example {N A : Type*} [DecidableEq N] [DecidableEq A] (sch : N → Finset A) (i : N) :
    EarStep sch {i} ∅ := by
  refine ⟨i, ⟨by simp, Or.inl ?_⟩, by simp⟩
  simp

-- No connectivity hypothesis: the two schemes are disjoint, yet they have a join tree,
-- and every terminal deletion run is empty. The tree edge has empty intersection label.
private def separate (i : Fin 2) : Finset (Fin 2) := {i}

example {A : Type*} [DecidableEq A] (sch : Fin 2 → Finset A) : HasJoinTree sch := by
  refine ⟨SimpleGraph.pathGraph 2, SimpleGraph.isTree_pathGraph_add_one 1, ?_⟩
  intro i j p hp k hk
  by_cases hij : i = j
  · subst j
    obtain rfl := (SimpleGraph.Walk.isPath_iff_nil.mp hp).eq_nil
    have hki : k = i := by simpa using hk
    subst k
    exact Finset.inter_subset_left
  · have hk' : k = i ∨ k = j := by omega
    rcases hk' with rfl | rfl
    · exact Finset.inter_subset_left
    · exact Finset.inter_subset_right

example : GYOEmpties separate := by
  intro F _ stop
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  apply stop i
  refine ⟨hi, Or.inl ?_⟩
  intro k hk
  simpa [separate] using (Finset.mem_erase.mp hk).1.symm

-- A semijoin against an empty extent kills a nonempty one, even with disjoint schemes.
private def oneEmpty : Fin 2 → Finset (Tuple (Fin 2) ℕ) := ![{![some 7, none]}, ∅]

example : semijoinStep separate oneEmpty (0, 1) 0 = ∅ ∧
    semijoinStep separate oneEmpty (0, 1) 1 = oneEmpty 1 := by decide

end Cslib.Databases.AcyclicSchema.Tests
