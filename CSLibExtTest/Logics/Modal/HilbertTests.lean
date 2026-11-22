/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.CslibTranslation

@[expose] public section

/-! # Tests for the modal Hilbert systems and the translation of CSLib's syntax -/

namespace Cslib.Modal.HilbertTests

open Formula

inductive Atom where
  | p
  | q
  deriving DecidableEq

/-- Necessitation applied to a propositional theorem: `⊢_K □(p → p)`. -/
example : Derivable Axioms.K (.box (.imp (.atom Atom.p) (.atom .p))) :=
  .nec (.imp_self _)

/-- The T axiom is a T-theorem. -/
example : Derivable Axioms.T (axiomT (.atom Atom.p)) := .extra ⟨_, rfl⟩

/-- Local consequence by modus ponens and the deduction theorem. -/
example : Deduces Axioms.K {.atom Atom.p, .imp (.atom .p) (.atom .q)} (.atom .q) :=
  .mp (phi := .atom .p) (.hyp (by simp)) (.hyp (by simp))

example : Deduces Axioms.K ∅ (.imp (.atom Atom.p) (.imp (.imp (.atom .p) (.atom .q)) (.atom .q))) :=
  Deduces.imp_of_insert <| Deduces.imp_of_insert <|
    .mp (phi := .atom .p) (.hyp (by simp)) (.hyp (by simp))

/-- Proof by contradiction: `¬¬p ⊢ p`. -/
example : Deduces Axioms.K {(atom Atom.p).neg.neg} (.atom .p) :=
  Deduces.of_insert_neg <| .mp (phi := (atom Atom.p).neg)
    (.hyp (Set.mem_insert_of_mem _ (Set.mem_singleton _))) (.hyp (Set.mem_insert _ _))

/-- A world sees one other world, where `p` holds; `p` fails at the root. -/
def irreflexive : KripkeModel Bool Atom where
  nonempty_world := ⟨false⟩
  rel w w' := w = false ∧ w' = true
  valuation w _ := w = true

/-- Soundness separates K from T: `□p → p` is not a K-theorem, as it fails at the root of a
non-reflexive model. -/
example : ¬Derivable Axioms.K (axiomT (.atom Atom.p)) := fun h ↦ by
  have := h.valid_K (M := irreflexive) false
  simp [axiomT, irreflexive, KripkeModel.Satisfies] at this

/-- The hypothesis of `Derivable.valid_T` is needed: the T axiom fails in the same model. -/
example : ¬irreflexive.Valid (axiomT (.atom Atom.p)) := fun h ↦ by
  simpa [axiomT, irreflexive, KripkeModel.Satisfies] using h false

/-- K, T, S4 and S5 are consistent. -/
example : ¬Derivable (Axioms.S4 : Set (Formula Atom)) .bot := not_derivable_bot_S4
example : ¬Derivable (Axioms.S5 : Set (Formula Atom)) .bot := not_derivable_bot_S5

/-- Non-contradiction, written in CSLib's own syntax, is in CSLib's semantic logic K, through the
translation and soundness. -/
example (World : Type) :
    (Logic.Modal.Proposition.not (.and (.atom Atom.p) (.not (.atom .p))) :
      Logic.Modal.Unimodal.Proposition Atom) ∈ Logic.Modal.Unimodal.K World Atom := by
  refine Derivable.mem_K (deduces_empty_iff.mp ?_)
  exact Deduces.neg_neg (.thm (.imp_self _))

/-- Necessitation applies to theorems only: `p` does not locally entail `□p` in K, as a root
where `p` holds sees a world where it fails. -/
def rootOnly : KripkeModel Bool Atom where
  nonempty_world := ⟨false⟩
  rel w w' := w = false ∧ w' = true
  valuation w _ := w = false

example : ¬Deduces Axioms.K {.atom Atom.p} (.box (.atom .p)) := fun h ↦ by
  have := h.satisfies (M := rootOnly) (by simp [Axioms.K]) (world := false) (by simp [rootOnly])
  simp [rootOnly] at this

/-- Soundness separates S4 from S5: `5` fails in a reflexive transitive, non-symmetric model. -/
def upward : KripkeModel Bool Atom where
  nonempty_world := ⟨false⟩
  rel w w' := w = false ∨ w' = true
  valuation w _ := w = false

example : ¬Derivable Axioms.S4 (axiomFive (.atom Atom.p)) := fun h ↦ by
  have := h.valid_S4 (M := upward) (by intro w; cases w <;> simp [upward])
    (by intro a b c; cases a <;> cases b <;> cases c <;> simp [upward]) false
  simp [axiomFive, upward, KripkeModel.satisfies_dia] at this

/-- Compactness: a consequence of an infinite set follows from a finite part of it. -/
example : ∃ Δ : Finset (Formula Atom), ↑Δ ⊆ Set.range (fun _ : ℕ ↦ (atom Atom.p).box.box)
    ∧ Deduces Axioms.K ↑Δ (atom Atom.p).box.box :=
  Deduces.exists_finset (.hyp ⟨0, rfl⟩)

/-- The S5 bridge: an S5-theorem written in CSLib's syntax is in CSLib's semantic S5 (reflexive,
transitive, right-euclidean models); `mem_S5` turns right-euclidean plus reflexive into the
equivalence that `valid_S5` needs. -/
example (World : Type) :
    (Logic.Modal.Proposition.not (.and (.atom Atom.p) (.not (.atom .p))) :
      Logic.Modal.Unimodal.Proposition Atom) ∈ Logic.Modal.Unimodal.S5 World Atom := by
  refine Derivable.mem_S5 (deduces_empty_iff.mp ?_)
  exact Deduces.neg_neg (.thm (.imp_self _))

end Cslib.Modal.HilbertTests
