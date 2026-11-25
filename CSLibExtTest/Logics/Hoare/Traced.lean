/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Logics.Hoare.Traced

/-! # Generic and concrete consumers of the diagram Hoare calculus -/

@[expose] public section
open CategoryTheory MonoidalCategory CategoryTheory.VerificationFunctor
open scoped MonoidalCategory
open Cslib.TracedHoare
universe u v w a
section Generic
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  {Atom : C → C → Type a} (interpret : ∀ {X Y}, Atom X Y → (X ⟶ Y))
  (T : SymmetricTrace C) (F : C ⥤ MonRelCat.{w}) [F.Monoidal]
  (hF : T.Preserves MonRelCat.symmetricTrace F)

example {X Y} (d : Diagram Atom X Y) (P : F.obj X) (Q : F.obj Y) :
    Derivable interpret F P d Q ↔ Triple F (d.denote interpret T) P Q :=
  derivable_iff_triple interpret T F hF d P Q

example {X Y} (d : Diagram Atom X Y) (P : F.obj X) (Q : F.obj Y)
    (h : Derivable interpret F P d Q) : Triple F (d.denote interpret T) P Q :=
  h.sound hF
end Generic

namespace TracedHoareTests
private abbrev N := MonRelCat.of ℕ
private abbrev E := MonRelCat.of Empty

/-- A small specified instruction set, rather than every morphism as an axiom. -/
private inductive Blocks : MonRelCat → MonRelCat → Type
  | tick : Blocks N N
  | pass : Blocks (N ⊗ N) (N ⊗ N)
  | empty : Blocks (N ⊗ E) (N ⊗ E)

private noncomputable def interpret : ∀ {X Y}, Blocks X Y → (X ⟶ Y)
  | _, _, .tick => MonRelCat.graph ⟨Nat.succ, fun _ _ h => Nat.succ_le_succ h⟩
  | _, _, .pass => 𝟙 _
  | _, _, .empty => 𝟙 _

private abbrev tick : Diagram Blocks N N := .atom .tick
private abbrev proves {X Y : MonRelCat} (P : X) (d : Diagram Blocks X Y) (Q : Y) : Prop :=
  Derivable interpret (𝟭 MonRelCat) P d Q
private abbrev T := MonRelCat.symmetricTrace

-- A derivation constructed from atomic specifications and sequencing.
example : proves (0 : ℕ) (.seq tick tick) (2 : ℕ) := by
  apply Derivable.seq (Q := (1 : ℕ))
  · exact .atom Blocks.tick (by change 1 ≤ 1; exact le_rfl)
  · exact .atom Blocks.tick (by change 2 ≤ 2; exact le_rfl)

example : proves (0 : ℕ) tick (3 : ℕ) := by
  refine Derivable.consequence (F := 𝟭 MonRelCat) (interpret := interpret)
    (d := tick) (P := (1 : ℕ)) (Q := (2 : ℕ)) ?_ ?_ ?_
  · exact .atom Blocks.tick (by change (2 : ℕ) ≤ 2; exact le_rfl)
  · change (0 : ℕ) ≤ 1
    decide
  · change (2 : ℕ) ≤ 3
    decide

-- Completeness constructs a derivation for a composite, not a new composite axiom.
example : proves (0 : ℕ) (.seq tick tick) (3 : ℕ) := by
  apply Derivable.complete (SymmetricTrace.preserves_id T)
  exact (triple_comp_iff (𝟭 MonRelCat) _ _ _ _).mpr
    ⟨(1 : ℕ), by change 1 ≤ 1; decide, by change 2 ≤ 3; decide⟩

-- The two tensor branches use independent assertions and both comparison relations.
example : proves ((0, 3) : ℕ × ℕ) (.tensor tick tick) ((1, 4) : ℕ × ℕ) := by
  refine Derivable.tensor (F := 𝟭 MonRelCat) (interpret := interpret)
    (left := tick) (right := tick) (p := (0 : ℕ)) (u := (3 : ℕ))
    (q := (1 : ℕ)) (v := (4 : ℕ)) ?_ ?_ ?_ ?_
  · exact ⟨le_rfl, le_rfl⟩
  · exact .atom Blocks.tick (by change 1 ≤ 1; exact le_rfl)
  · exact .atom Blocks.tick (by change 4 ≤ 4; exact le_rfl)
  · exact ⟨le_rfl, le_rfl⟩

-- Feedback needs one shared invariant, here chosen explicitly as 7.
example : proves (0 : ℕ) (.feedback (.atom .pass)) (0 : ℕ) := by
  refine .feedback (7 : ℕ) (P' := ((0, 7) : ℕ × ℕ)) (Q' := ((0, 7) : ℕ × ℕ)) ?_ ?_ ?_
  · exact ⟨le_rfl, le_rfl⟩
  · exact .atom Blocks.pass (by exact ⟨le_rfl, le_rfl⟩)
  · exact ⟨le_rfl, le_rfl⟩

-- Consequence has a direction: it cannot make a strict increment preserve zero.
example : ¬ proves (0 : ℕ) tick (0 : ℕ) := by
  intro h
  have hv := h.sound (SymmetricTrace.preserves_id T)
  change 1 ≤ 0 at hv
  omega

-- In MonRelCat, an empty invariant carrier makes feedback impossible.
example : ¬ proves (0 : ℕ) (.feedback (.atom .empty)) (0 : ℕ) := by
  intro h
  have hv := h.sound (SymmetricTrace.preserves_id T)
  obtain ⟨i, _⟩ := (triple_trace_iff (𝟭 MonRelCat)
    (SymmetricTrace.preserves_id T) _ _ _).mp hv
  exact i.elim
end TracedHoareTests
