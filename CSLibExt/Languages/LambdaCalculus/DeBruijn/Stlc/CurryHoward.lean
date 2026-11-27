/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Syntax
public import CSLibExt.Logics.Propositional.Legacy.NaturalDeduction.Basic

/-!
# Curry-Howard: STLC terms to natural deduction

Under the Curry-Howard correspondence, a simple type over base types `Base`
is an implicational proposition over atoms `Base` (`Ty.toProp`), and a
context `Γ : List (Ty Base)` is the set of hypotheses `ctxHyps Γ`. This
module sends every intrinsically typed de Bruijn term `t : Tm Γ A` of
`CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Syntax` to a derivation of
`A.toProp` from `ctxHyps Γ` in CSLib v4.35's natural deduction, restored in
`Cslib.Logic.LegacyPL` (`Tm.toDerivation`): a variable becomes the assumption of its type, an
application becomes implication elimination, and an abstraction becomes
implication introduction. The derivation uses no axioms, so it exists in
every theory, minimal logic included (`curry_howard`).

This is the soundness direction of the correspondence for the implicational
fragment. The converse direction, from derivations to terms, is not
formalized here.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open Cslib.Logic Cslib.Logic.LegacyPL InferenceSystem

universe u

variable {Base : Type u}

/-- A simple type read as an implicational proposition: base types are
atoms and arrows are implications. -/
def Ty.toProp : Ty Base → Proposition Base
  | .base b => .atom b
  | .arr A B => .imp A.toProp B.toProp

variable [DecidableEq Base]

/-- The hypotheses of a context: the propositions its types denote. -/
def ctxHyps (Γ : List (Ty Base)) : Ctx Base :=
  (Γ.map Ty.toProp).toFinset

/-- Extending a context by `A` adds the hypothesis `A.toProp`. -/
theorem ctxHyps_cons (A : Ty Base) (Γ : List (Ty Base)) :
    ctxHyps (A :: Γ) = insert A.toProp (ctxHyps Γ) := by
  simp [ctxHyps]

/-- The type of a variable is a hypothesis of its context. -/
theorem Var.toProp_mem_ctxHyps {Γ : List (Ty Base)} {A : Ty Base} (x : Var Γ A) :
    A.toProp ∈ ctxHyps Γ := by
  induction x with
  | zero => simp [ctxHyps_cons]
  | succ _ ih => simp [ctxHyps_cons, ih]

/-- The Curry-Howard translation of a term into a natural-deduction
derivation of its type from the hypotheses of its context: a variable
becomes the assumption of its type, an application becomes implication
elimination, and an abstraction becomes implication introduction. -/
def Tm.toDerivation {T : Theory Base} :
    {Γ : List (Ty Base)} → {A : Ty Base} → Tm Γ A → T.Derivation (ctxHyps Γ) A.toProp
  | _, _, .var x => .ass x.toProp_mem_ctxHyps
  | _, _, .app f a => .implE f.toDerivation a.toDerivation
  | Γ, _, .lam (A := A) body =>
      .implI (ctxHyps Γ) (ctxHyps_cons A Γ ▸ body.toDerivation)

/-- Curry-Howard, soundness direction. Assume equality of base types is
decidable. Then the type of every term is derivable in natural deduction from
the hypotheses of its context, in every theory. -/
theorem curry_howard {T : Theory Base} {Γ : List (Ty Base)} {A : Ty Base}
    (t : Tm Γ A) : DerivableIn T (ctxHyps Γ ⊢ A.toProp) :=
  ⟨t.toDerivation⟩

end Cslib.Languages.LambdaCalculus.Stlc
