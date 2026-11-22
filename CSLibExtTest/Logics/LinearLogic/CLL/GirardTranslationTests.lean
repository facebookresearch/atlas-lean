/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LinearLogic.CLL.GirardTranslation

@[expose] public section

/-! # Tests for Girard's translation of intuitionistic logic into CLL -/

namespace Cslib.Logic.CLL.GirardTests

open Cslib.Logic CLL PL PL.Theory InferenceSystem Girard

inductive Atom where
  | p
  | q
  | falsum
  deriving DecidableEq

instance : Bot Atom := ⟨.falsum⟩

/-- The translation of an implication is a linear implication out of `!`. -/
example : translate (CLL.Proposition.atom (Atom := Atom)) (.imp (.atom .p) (.atom .q)) =
    (.bang (.atom .p) ⊸ .atom .q) := rfl

/-- The translation of a disjunction marks both disjuncts with `!`. -/
example : translate (CLL.Proposition.atom (Atom := Atom)) (.or (.atom .p) (.atom .q)) =
    .oplus (.bang (.atom .p)) (.bang (.atom .q)) := rfl

/-- `p → p` in minimal logic gives the CLL theorem `!p ⊸ p`. -/
example : Derivable (({(translate CLL.Proposition.atom (.imp (.atom Atom.p) (.atom .p)))} :
    CLL.Sequent Atom)) :=
  mpl _ (.implI ∅ (.ass (Finset.mem_insert_self _ _)))

/-- `p ∧ q → q ∧ p` in minimal logic gives a CLL theorem. -/
example : Derivable (({(translate CLL.Proposition.atom
    (.imp (.and (.atom Atom.p) (.atom .q)) (.and (.atom .q) (.atom .p))))} : CLL.Sequent Atom)) :=
  mpl _ (.implI ∅ (.andI (.andE₂ (.ass (Finset.mem_insert_self _ _)))
    (.andE₁ (.ass (Finset.mem_insert_self _ _)))))

/-- Disjunction introduction and elimination: `p ∨ q → q ∨ p`. -/
example : Derivable (({(translate CLL.Proposition.atom
    (.imp (.or (.atom Atom.p) (.atom .q)) (.or (.atom .q) (.atom .p))))} : CLL.Sequent Atom)) :=
  mpl _ (.implI ∅ (.orE (.ass (Finset.mem_insert_self _ _))
    (.orI₂ (.ass (Finset.mem_insert_self _ _))) (.orI₁ (.ass (Finset.mem_insert_self _ _)))))

/-- Modus ponens with a reused hypothesis: `p → (p → q) → q`. -/
example : Derivable (({(translate CLL.Proposition.atom
    (.imp (.atom Atom.p) (.imp (.imp (.atom .p) (.atom .q)) (.atom .q))))} : CLL.Sequent Atom)) :=
  mpl _ (.implI ∅ (.implI _ (.implE (.ass (Finset.mem_insert_self _ _))
    (.ass (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))

/-- A hypothesis is shared by both conjuncts (`p → p ∧ p`): `&` is additive, so the context is
shared without contraction. -/
example : Derivable (({(translate CLL.Proposition.atom
    (.imp (.atom Atom.p) (.and (.atom .p) (.atom .p))))} : CLL.Sequent Atom)) :=
  mpl _ (.implI ∅ (.andI (.ass (Finset.mem_insert_self _ _))
    (.ass (Finset.mem_insert_self _ _))))

/-- Contraction through `→`-elimination: `(p → p → q) → p → q` uses `p` twice. -/
example : Derivable (({(translate CLL.Proposition.atom
    (.imp (.imp (.atom Atom.p) (.imp (.atom .p) (.atom .q))) (.imp (.atom .p) (.atom .q))))} :
      CLL.Sequent Atom)) :=
  mpl _ (.implI ∅ (.implI _ (.implE (.implE (.ass (Finset.mem_insert_of_mem
    (Finset.mem_insert_self _ _))) (.ass (Finset.mem_insert_self _ _)))
    (.ass (Finset.mem_insert_self _ _)))))

/-- The translation of a conjunction is `&`. -/
example : translate (CLL.Proposition.atom (Atom := Atom)) (.and (.atom .p) (.atom .q)) =
    .with (.atom .p) (.atom .q) := rfl

/-- `⊥ ↦ 0`, and ex falso translates to `ʔ⊤ ⅋ p`. -/
example : botToZero (⊥ : Atom) = .zero := botToZero_bot

example : translate botToZero (.imp ⊥ (.atom Atom.p)) =
    .parr (.quest .top) (botToZero Atom.p) := by
  simp only [translate]
  rw [botToZero_bot]
  rfl

/-- Ex falso, an axiom of IPL, translates to a CLL theorem with `⊥ ↦ 0`. -/
example : Derivable (({(translate botToZero (.imp ⊥ (.atom Atom.p)))} : CLL.Sequent Atom)) :=
  ipl _ botToZero_bot (.ax (efq_mem_ipl _))

/-- An intuitionistic theorem using ex falso: `¬p → p → q`. -/
example : Derivable (({(translate botToZero
    (.imp (.imp (.atom Atom.p) ⊥) (.imp (.atom .p) (.atom .q))))} : CLL.Sequent Atom)) :=
  ipl _ botToZero_bot (.implI ∅ (.implI _ (.implE (.ax (efq_mem_ipl _))
    (.implE (.ass (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
      (.ass (Finset.mem_insert_self _ _))))))

/-- Open hypotheses become `?`-propositions: `{p} ⊢ p` gives `⊢ ʔ(p⫠), p`. -/
example : Derivable ((translate CLL.Proposition.atom (.atom Atom.p) ::ₘ
    hyps CLL.Proposition.atom ({.atom Atom.p} : Ctx Atom).val)) :=
  derivable_of_derivation _ (T := MPL Atom) (fun _ h ↦ absurd h (Set.notMem_empty _))
    (.ass (Finset.mem_singleton_self _))

end Cslib.Logic.CLL.GirardTests
