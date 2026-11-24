/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Foundations.Relation.DisjunctiveWellFounded
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Relation
import Mathlib.Order.RelClasses
import Mathlib.Order.WellFounded

@[expose] public section

namespace CslibTest

/-- Forward step of the two-counter example: decrement the first counter, or
decrement the second counter alone. -/
def twoCounterStep (s s' : ℕ × ℕ) : Prop :=
  0 < s.1 ∧ 0 < s.2 ∧
    ((s'.1 + 1 = s.1) ∨ (s'.1 = s.1 ∧ s'.2 + 1 = s.2))

/-- Backward reading of the two-counter step. -/
def twoCounterR (s' s : ℕ × ℕ) : Prop :=
  twoCounterStep s s'

/-- Covering family for the two-counter example. -/
def twoCounterT (i : Fin 2) (s' s : ℕ × ℕ) : Prop :=
  if i = 0 then s'.1 < s.1 else s'.1 = s.1 ∧ s'.2 < s.2

/-- Each member of the two-counter covering family is well-founded. -/
theorem twoCounter_cover_wf : ∀ i, WellFounded (twoCounterT i) := by
  rw [Fin.forall_fin_two]
  constructor
  · have hT0 :
        twoCounterT 0 = fun s' s : ℕ × ℕ => s'.1 < s.1 := by
      unfold twoCounterT
      simp
    rw [hT0]
    show WellFounded (InvImage (· < · : ℕ → ℕ → Prop) Prod.fst)
    exact InvImage.wf _ wellFounded_lt
  · have h10 : (1 : Fin 2) ≠ 0 := by decide
    have hT1 :
        twoCounterT 1 =
          fun s' s : ℕ × ℕ => s'.1 = s.1 ∧ s'.2 < s.2 := by
      unfold twoCounterT
      simp [h10]
    rw [hT1]
    refine Subrelation.wf
      (r := InvImage (· < · : ℕ → ℕ → Prop) Prod.snd) ?_
      (InvImage.wf _ wellFounded_lt)
    intro s' s h
    exact h.2

/-- The transitive closure of the two-counter relation is covered by the
two-counter family. -/
theorem twoCounter_cover_sub :
    ∀ x y, Relation.TransGen twoCounterR x y → ∃ i, twoCounterT i x y := by
  have hT0 :
      twoCounterT 0 = fun s' s : ℕ × ℕ => s'.1 < s.1 := by
    unfold twoCounterT
    simp
  have hT1 :
      twoCounterT 1 = fun s' s : ℕ × ℕ => s'.1 = s.1 ∧ s'.2 < s.2 := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    unfold twoCounterT
    simp [h10]
  intro x y h
  induction h with
  | single h =>
    simp only [twoCounterR, twoCounterStep] at h
    rcases h with ⟨-, -, hstep | ⟨hac, hbd⟩⟩
    · exact ⟨0, by simp only [hT0]; omega⟩
    · exact ⟨1, by simp only [hT1]; omega⟩
  | tail _ h2 ih =>
    rw [Fin.exists_fin_two] at ih
    simp only [twoCounterR, twoCounterStep] at h2
    rcases h2 with ⟨-, -, hstep | ⟨hac, hbd⟩⟩
    · rcases ih with hi | hi
      · simp only [hT0] at hi
        exact ⟨0, by simp only [hT0]; omega⟩
      · simp only [hT1] at hi
        obtain ⟨hi1, hi2⟩ := hi
        exact ⟨0, by simp only [hT0]; omega⟩
    · rcases ih with hi | hi
      · simp only [hT0] at hi
        exact ⟨0, by simp only [hT0]; omega⟩
      · simp only [hT1] at hi
        obtain ⟨hi1, hi2⟩ := hi
        exact ⟨1, by simp only [hT1]; omega⟩

/-- The two-counter relation is well-founded, by the main theorem. -/
theorem twoCounter_wellFounded : WellFounded twoCounterR :=
  Cslib.wellFounded_of_transGen_subset_iUnion _ _ twoCounter_cover_wf
    twoCounter_cover_sub

/-- The two-counter step, read backwards, is well-founded, by the forward
form. -/
theorem twoCounter_wellFounded_forward :
    WellFounded (fun y x => twoCounterStep x y) := by
  apply Cslib.wellFounded_swap_of_transGen_subset_iUnion _ (fun i x y =>
    twoCounterT i y x) twoCounter_cover_wf
  intro x y h
  have h' : Relation.TransGen twoCounterR y x := Relation.transGen_swap.mpr h
  exact twoCounter_cover_sub y x h'

/-- The empty relation is well-founded, via the empty index family. -/
theorem emptyRelation_wellFounded {α : Type*} :
    WellFounded (fun _ _ : α => False) := by
  refine Cslib.wellFounded_of_transGen_subset_iUnion _
    (fun (_ : Empty) _ _ => False) ?_ ?_
  · intro i
    nomatch i
  · intro x y h
    induction h with
    | single h => exact False.elim h
    | tail _ _ ih => exact ih

/-- Successor-step relation on naturals. -/
def succR (n' n : ℕ) : Prop := n' + 1 = n

/-- The transitive closure of the successor step is bounded by `<`. -/
theorem succR_transGen_lt :
    ∀ x y, Relation.TransGen succR x y → x < y := by
  intro x y h
  induction h with
  | single h =>
    simp only [succR] at h
    omega
  | tail _ h2 ih =>
    simp only [succR] at h2
    omega

/-- The successor-step relation is well-founded, with a single index. -/
theorem succR_wellFounded : WellFounded succR := by
  refine Cslib.wellFounded_of_transGen_subset_iUnion _
    (fun (_ : Unit) (x y : ℕ) => x < y) ?_ ?_
  · intro _
    exact wellFounded_lt
  · intro x y h
    exact ⟨(), succR_transGen_lt x y h⟩

/-- Equality on `Unit` is not well-founded. -/
theorem unitEq_not_wellFounded : ¬ WellFounded (fun a b : Unit => a = b) := by
  intro h
  exact (wellFounded_iff_isEmpty_descending_chain.mp h).false
    ⟨fun _ => (), fun _ => rfl⟩

/-- No single well-founded relation covers the transitive closure of equality
on `Unit`. -/
theorem unitEq_transGen_not_covered :
    ¬ ∃ T : Unit → Unit → Prop, WellFounded T ∧
      ∀ x y, Relation.TransGen (fun a b : Unit => a = b) x y → T x y := by
  rintro ⟨T, hT, hsub⟩
  have hTT : T () () := hsub () () (Relation.TransGen.single rfl)
  exact (wellFounded_iff_isEmpty_descending_chain.mp hT).false
    ⟨fun _ => (), fun _ => hTT⟩

end CslibTest
