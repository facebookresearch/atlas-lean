/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Embedding propositional logic into first-order logic
-/
module

public import CSLibExt.Logics.Propositional.NaturalDeduction.Semantics
public import Mathlib.ModelTheory.Semantics

/-!
# Embedding propositional logic into first-order logic

Propositional atoms become nullary relation symbols. The embedding
`Proposition.embed` sends a `Cslib.Logic.PL.Proposition` to a sentence over
`propLanguage Atom`, and `realize_embed_iff_evalBool` says the sentence is true
in the `Bool` structure for a valuation `v` exactly when the proposition's
truth-table value under `v` is `true`. This is the propositional-to-first-order
bridge that a proof of Craig interpolation for first-order logic would build
on: the propositional case (`exists_interpolant_cpl`) eliminates atoms by
Boolean quantification, and the first-order case must additionally handle
quantifiers, terms, and equality.

## References

- H. Enderton, *A Mathematical Introduction to Logic*, 2nd ed., Academic Press, 2001, §2.5
  (Craig interpolation), §2.3 (translation between propositional and first-order logic).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Logic.FOL

open FirstOrder FirstOrder.Language
open Cslib.Logic.PL

/-- **Relation symbols of the propositional language.** For a type of atoms, the family of
relation symbols indexed by arity that consists of one nullary relation symbol for each atom
$a$ and has no relation symbols of positive arity. -/
inductive PropRelations (Atom : Type u) : ℕ → Type u
  /-- The propositional atom `a`, as a nullary relation symbol. -/
  | atomRel : Atom → PropRelations Atom 0

/-- **First-order language of propositional atoms.** For a type of atoms, the first-order
language whose relation symbols are exactly one nullary relation symbol for each atom, with
no relation symbols of positive arity and no function symbols. -/
def propLanguage (Atom : Type u) : FirstOrder.Language.{u, u} where
  Functions := fun _ => PEmpty
  Relations := PropRelations Atom

namespace Proposition

variable {Atom : Type u}

/-- **Embedding propositions as first-order sentences.** The translation of propositions over a
type of atoms into sentences of the first-order language of propositional atoms, defined by
recursion: an atom $a$ becomes the atomic sentence given by the nullary relation symbol of $a$,
and $A \wedge B$, $A \vee B$ and $A \to B$ become the conjunction, the disjunction and the
implication of the translations of $A$ and $B$. -/
def embed : Proposition Atom → (propLanguage Atom).Sentence
  | .atom a => (.rel (PropRelations.atomRel a) (fun i => i.elim0))
  | .and A B => (embed A) ⊓ (embed B)
  | .or A B => (embed A) ⊔ (embed B)
  | .imp A B => (embed A).imp (embed B)

/-- **Boolean structure of a valuation.** Given a valuation $v$ assigning a Boolean to each
atom, the Boolean structure of $v$ is the structure for the first-order language of
propositional atoms whose domain is the set of Booleans $\{\mathrm{false}, \mathrm{true}\}$
and in which the nullary relation symbol of an atom $a$ holds exactly when $v(a)$ is true.
The language has no function symbols, so nothing else needs to be interpreted. -/
@[instance_reducible]
def boolStructure (v : Atom → Bool) : (propLanguage Atom).Structure Bool where
  funMap f _ := f.elim
  RelMap R _ := match R with
    | .atomRel a => v a = true

/-- **The embedding of propositions preserves truth-table semantics.** For every valuation $v$
assigning a Boolean to each atom and every proposition $A$, the first-order sentence obtained
by embedding $A$ is true in the Boolean structure of $v$ if and only if the truth-table value
of $A$ under $v$ is true. -/
theorem realize_embed_iff_evalBool (v : Atom → Bool) (A : Proposition Atom) :
    @Formula.Realize (propLanguage Atom) Bool (boolStructure v) Empty (embed A)
      (fun x => x.elim) ↔ A.evalBool v = true := by
  induction A with
  | atom a =>
    simp only [embed, Formula.Realize, BoundedFormula.Realize]
    rfl
  | and A B ihA ihB =>
    simp only [embed, Formula.realize_inf, ihA, ihB, Proposition.evalBool, Bool.and_eq_true]
  | or A B ihA ihB =>
    simp only [embed, Formula.realize_sup, ihA, ihB, Proposition.evalBool, Bool.or_eq_true]
  | imp A B ihA ihB =>
    simp only [embed, Formula.realize_imp, ihA, ihB, Proposition.evalBool]
    constructor
    · intro h
      by_cases hA : A.evalBool v = true
      · simp [hA, h hA]
      · simp [hA]
    · intro h hA
      simp only [hA, Bool.not_true, Bool.false_or] at h
      exact h

end Proposition

end Cslib.Logic.FOL
