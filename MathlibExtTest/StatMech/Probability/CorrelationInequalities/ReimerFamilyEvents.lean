/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerFamilyEvents

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerCompressLib`

* `familyEvent` membership computed on `Fin 2`;
* `fmarg_eq_wprob_familyEvent` for the uniform weight;
* `reimer_wprob_familyEvent_of_isLowerSet` for the lower families `famA = {∅, {0}}`,
  `famB = {∅, {1}}` (lower-set hypotheses proved), and `reimer_wprob_familyEvent_of_isUpperSet`
  for the upper family `{S | 0 ∈ S}` with itself.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerCompressLib

open _root_.StatMech
open scoped FinsetFamily

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

/-- The upper family `{S | 0 ∈ S}` on `Fin 2`. -/
def famUp : Finset (Finset (Fin 2)) := Finset.univ.filter (fun S => 0 ∈ S)

-- `famUp` is an upper set.
theorem isUpperSet_famUp : IsUpperSet (famUp : Set (Finset (Fin 2))) := by
  intro a b hab ha
  simp only [famUp, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
  exact hab ha

/-- The uniform coordinate weight. -/
noncomputable def half : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

-- The all-closed configuration lies in `familyEvent famA`; the all-open one does not.
example : (fun _ => false) ∈ familyEvent famA ∧ (fun _ => true) ∉ familyEvent famA := by
  simp only [familyEvent, Set.mem_ofPred_eq]
  decide

-- `fmarg` is the `wprob` of the family event.
example : fmarg half famA = wprob half (familyEvent famA) := fmarg_eq_wprob_familyEvent _ _

-- Reimer for events of lower families.
example : wprob half (disjointOccurrence (familyEvent famA) (familyEvent famB))
    ≤ wprob half (familyEvent famA) * wprob half (familyEvent famB) :=
  reimer_wprob_familyEvent_of_isLowerSet half (fun _ _ => by norm_num [half])
    (fun _ => by norm_num [half]) isLowerSet_famA isLowerSet_famB

-- Reimer (here BK) for events of upper families.
example : wprob half (disjointOccurrence (familyEvent famUp) (familyEvent famUp))
    ≤ wprob half (familyEvent famUp) * wprob half (familyEvent famUp) :=
  reimer_wprob_familyEvent_of_isUpperSet half (fun _ _ => by norm_num [half])
    (fun _ => by norm_num [half]) isUpperSet_famUp isUpperSet_famUp

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerCompressLib
