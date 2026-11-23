/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.Bisimulation

/-!
# Consumer tests for modal bisimulation

The chain has one successor; the related three-world model duplicates that
successor. This tests a relation between different carriers, including the
back condition for the second copy, rather than only an identity relation.
-/

set_option autoImplicit false

open Cslib.Modal

namespace CSLibExtTest.Logics.Modal.Bisimulation

private def chain : KripkeModel Bool Unit where
  nonempty_world := ⟨false⟩
  rel := fun w v => w = false ∧ v = true
  valuation := fun w _ => w = true

private def split : KripkeModel (Fin 3) Unit where
  nonempty_world := ⟨0⟩
  rel := fun w v => w = 0 ∧ v ≠ 0
  valuation := fun w _ => w ≠ 0

private def related (w : Bool) (v : Fin 3) : Prop :=
  (w = false ∧ v = 0) ∨ (w = true ∧ v ≠ 0)

private def deadChain : KripkeModel Bool Unit :=
  { chain with rel := fun _ _ => False }

private def deadSplit : KripkeModel (Fin 3) Unit :=
  { split with rel := fun _ _ => False }

private theorem splitBisimulation : Bisimulation chain split related := by
  constructor
  · rintro w v (⟨rfl, rfl⟩ | ⟨rfl, hv⟩) a
    · simp [chain, split]
    · simp [chain, split, hv]
  · rintro w v w' hr ⟨rfl, rfl⟩
    rcases hr with ⟨_, rfl⟩ | ⟨h, _⟩
    · exact ⟨1, ⟨rfl, by decide⟩, Or.inr ⟨rfl, by decide⟩⟩
    · exact (Bool.false_ne_true h).elim
  · rintro w v v' hr ⟨rfl, hv⟩
    rcases hr with ⟨rfl, _⟩ | ⟨_, hne⟩
    · exact ⟨true, ⟨rfl, rfl⟩, Or.inr ⟨rfl, hv⟩⟩
    · exact (hne rfl).elim

example : Bisimulation.Bisimilar chain split false 0 :=
  ⟨related, splitBisimulation, Or.inl ⟨rfl, rfl⟩⟩

/-- Back matches the duplicated successor at `2`, not only the copy at `1`. -/
example : ∃ w', chain.rel false w' ∧ related w' 2 :=
  splitBisimulation.back (Or.inl ⟨rfl, rfl⟩) ⟨rfl, by decide⟩

example : split.Satisfies 0 (.box (.atom ())) :=
  (splitBisimulation.satisfies_iff (.box (.atom ())) false 0
    (Or.inl ⟨rfl, rfl⟩)).mp (by
      intro v hv
      exact hv.2)

/-- Both duplicated successors are dead ends. -/
example : split.Satisfies 0 (.box (.box (.atom ()))) :=
  (splitBisimulation.satisfies_iff (.box (.box (.atom ()))) false 0
    (Or.inl ⟨rfl, rfl⟩)).mp (by
      rintro v ⟨_, rfl⟩ u ⟨h, _⟩
      exact (Bool.false_ne_true h.symm).elim)

/-- The reverse direction also reflects a false boxed formula. -/
example : ¬ split.Satisfies 0 (.box (Formula.neg (.atom ()))) := by
  intro h
  have hchain := (splitBisimulation.satisfies_iff
    (.box (Formula.neg (.atom ()))) false 0 (Or.inl ⟨rfl, rfl⟩)).mpr h
  exact hchain true ⟨rfl, rfl⟩ rfl

example : split.Satisfies 0 (.imp (.atom ()) .bot) :=
  (splitBisimulation.satisfies_iff (.imp (.atom ()) .bot) false 0
    (Or.inl ⟨rfl, rfl⟩)).mp (by
      intro h
      exact Bool.false_ne_true h)

/-- Matching accessibility alone cannot relate worlds disagreeing on atoms. -/
example : ¬ Bisimulation.Bisimilar chain split true 0 := by
  rintro ⟨R, hR, h⟩
  exact ((hR.atom_iff h ()).mp rfl) rfl

/-- Atoms still match, but a missing target edge violates forth. -/
example : ¬ Bisimulation chain deadSplit related := by
  intro h
  obtain ⟨v', hv, _⟩ := h.forth (Or.inl ⟨rfl, rfl⟩) ⟨rfl, rfl⟩
  exact hv

/-- Atoms still match, but a missing source edge violates back. -/
example : ¬ Bisimulation deadChain split related := by
  intro h
  obtain ⟨w', hw, _⟩ := h.back (v' := (1 : Fin 3))
    (Or.inl ⟨rfl, rfl⟩) ⟨rfl, by decide⟩
  exact hw

end CSLibExtTest.Logics.Modal.Bisimulation
