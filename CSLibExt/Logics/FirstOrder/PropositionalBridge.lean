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

/-- Nullary relation symbols are the propositional atoms; there are no function symbols
and no relation symbols of positive arity. -/
inductive PropRelations (Atom : Type u) : ℕ → Type u
  /-- The propositional atom `a`, as a nullary relation symbol. -/
  | atomRel : Atom → PropRelations Atom 0

/-- The first-order language with propositional atoms as nullary relation symbols. -/
def propLanguage (Atom : Type u) : FirstOrder.Language.{u, u} where
  Functions := fun _ => PEmpty
  Relations := PropRelations Atom

namespace Proposition

variable {Atom : Type u}

/-- Embed a proposition as a sentence: atoms become nullary relations,
`∧`/`∨` become `⊓`/`⊔`, and `⟹` becomes `.imp`. -/
def embed : Proposition Atom → (propLanguage Atom).Sentence
  | .atom a => (.rel (PropRelations.atomRel a) (fun i => i.elim0))
  | .and A B => (embed A) ⊓ (embed B)
  | .or A B => (embed A) ⊔ (embed B)
  | .imp A B => (embed A).imp (embed B)

/-- The `Bool` structure for a valuation `v`: a nullary relation is true iff `v` makes
its atom true. -/
@[instance_reducible]
def boolStructure (v : Atom → Bool) : (propLanguage Atom).Structure Bool where
  funMap f _ := f.elim
  RelMap R _ := match R with
    | .atomRel a => v a = true

/-- The embedding is faithful for truth-table semantics: the embedded sentence holds in
the `Bool` structure for `v` iff the proposition evaluates to `true` under `v`. -/
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
