/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.StandardTranslation

/-!
# Consumer tests for the standard translation

The only edge is `false → true`, and the atom is true only at `true`.
Distinct bound-variable values test that lifting preserves the old world and
that nested boxes use their newly bound successor. A renamed two-world model
checks first-order invariance under a concrete bisimulation.
-/

set_option autoImplicit false

open Cslib.Modal

namespace CSLibExtTest.Logics.Modal.StandardTranslation

private def chain : KripkeModel Bool Unit where
  nonempty_world := ⟨false⟩
  rel := fun w v => w = false ∧ v = true
  valuation := fun w _ => w = true

private def realizesAt (n : ℕ) (i : Fin n) (φ : Formula Unit) (xs : Fin n → Bool) : Prop :=
  @FirstOrder.Language.BoundedFormula.Realize (modalLanguage Unit) Bool
    (kripkeStructure chain) Empty n
    (standardTranslation n (.var (Sum.inr i)) φ) Empty.elim xs

/-- Accessibility is interpreted in the source-to-successor order. -/
example : (kripkeStructure chain).RelMap (ModalRelations.relR : ModalRelations Unit 2)
    ![false, true] := ⟨rfl, rfl⟩

example : ¬ (kripkeStructure chain).RelMap (ModalRelations.relR : ModalRelations Unit 2)
    ![true, false] := by
  intro h
  exact Bool.false_ne_true h.1.symm

example : (frameStructure chain.rel).RelMap FrameRelations.relR ![false, true] :=
  ⟨rfl, rfl⟩

example : ¬ (frameStructure chain.rel).RelMap FrameRelations.relR ![true, false] := by
  intro h
  exact Bool.false_ne_true h.1.symm

example : realizesAt 1 0 (.atom ()) (fun _ => true) := by
  rw [realizesAt, realize_standardTranslation]
  rfl

example : ¬ realizesAt 1 0 (.atom ()) (fun _ => false) := by
  rw [realizesAt, realize_standardTranslation]
  exact Bool.false_ne_true

example : ¬ realizesAt 1 0 .bot (fun _ => true) := by
  rw [realizesAt, realize_standardTranslation]
  intro h
  exact h

example : realizesAt 1 0 (.box (.atom ())) (fun _ => false) := by
  rw [realizesAt, realize_standardTranslation]
  intro v hv
  exact hv.2

/-- Universal quantification over a dead end makes boxed falsity true. -/
example : realizesAt 1 0 (.box .bot) (fun _ => true) := by
  rw [realizesAt, realize_standardTranslation]
  intro v hv
  exact (Bool.false_ne_true hv.1.symm).elim

example : ¬ realizesAt 1 0 (.box .bot) (fun _ => false) := by
  rw [realizesAt, realize_standardTranslation]
  intro h
  exact h true ⟨rfl, rfl⟩

/-- The inner box is evaluated at the new successor, which is a dead end. -/
example : realizesAt 1 0 (.box (.box .bot)) (fun _ => false) := by
  rw [realizesAt, realize_standardTranslation]
  rintro v ⟨_, rfl⟩ u ⟨h, _⟩
  exact (Bool.false_ne_true h.symm).elim

/-- Implication preserves the failure of `□p → p` at the starting world. -/
example : ¬ realizesAt 1 0 (.imp (.box (.atom ())) (.atom ())) (fun _ => false) := by
  rw [realizesAt, realize_standardTranslation]
  intro h
  exact Bool.false_ne_true (h (by
    intro v hv
    exact hv.2))

/-- With two distinct levels, the old level `0` remains the dead-end world. -/
example : realizesAt 2 0 (.box .bot) ![true, false] := by
  rw [realizesAt, realize_standardTranslation]
  intro v hv
  exact (Bool.false_ne_true hv.1.symm).elim

/-- Selecting old level `1` instead selects the world that has a successor. -/
example : ¬ realizesAt 2 1 (.box .bot) ![true, false] := by
  rw [realizesAt, realize_standardTranslation]
  intro h
  exact h true ⟨rfl, rfl⟩

private def renamed : KripkeModel (Fin 2) Unit where
  nonempty_world := ⟨1⟩
  rel := fun w v => w = 1 ∧ v = 0
  valuation := fun w _ => w = 0

private def related (w : Bool) (v : Fin 2) : Prop :=
  (w = false ∧ v = 1) ∨ (w = true ∧ v = 0)

private theorem renamedBisimulation : Bisimulation chain renamed related := by
  constructor
  · rintro w v (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) a <;> simp [chain, renamed]
  · rintro w v w' hr ⟨rfl, rfl⟩
    rcases hr with ⟨_, rfl⟩ | ⟨h, _⟩
    · exact ⟨0, ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
    · exact (Bool.false_ne_true h).elim
  · rintro w v v' hr ⟨rfl, rfl⟩
    rcases hr with ⟨rfl, _⟩ | ⟨_, h⟩
    · exact ⟨true, ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
    · exact ((by decide : (1 : Fin 2) ≠ 0) h).elim

private def renamedRealizes (φ : Formula Unit) (v : Fin 2) : Prop :=
  @FirstOrder.Language.BoundedFormula.Realize (modalLanguage Unit) (Fin 2)
    (kripkeStructure renamed) Empty 1
    (standardTranslation 1 (.var (Sum.inr (0 : Fin 1))) φ) Empty.elim (fun _ => v)

/-- The translated box remains true when the starting world is renamed to `1`. -/
example : renamedRealizes (.box (.atom ())) 1 :=
  (bisimulationInvariant_standardTranslation (.box (.atom ())) chain renamed related
    renamedBisimulation false 1 (Or.inl ⟨rfl, rfl⟩)).mp (by
      rw [realize_standardTranslation]
      intro v hv
      exact hv.2)

/-- First-order invariance also reflects the false implication, in reverse. -/
example : ¬ renamedRealizes (.imp (.box (.atom ())) (.atom ())) 1 := by
  intro h
  have hchain := (bisimulationInvariant_standardTranslation
    (.imp (.box (.atom ())) (.atom ())) chain renamed related
    renamedBisimulation false 1 (Or.inl ⟨rfl, rfl⟩)).mpr h
  rw [realize_standardTranslation] at hchain
  exact Bool.false_ne_true (hchain (by
    intro v hv
    exact hv.2))

end CSLibExtTest.Logics.Modal.StandardTranslation
