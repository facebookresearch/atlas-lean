/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.FullBeta
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Semantics

@[expose] public section

/-!
# Client tests for the intrinsic STLC full-beta embedding

These clients separate upstream full beta reduction from the existing weak call-by-value `Step`.
The first term has a beta redex under a lambda, so it is call-by-value normal but its embedding
really full-beta reduces.  The second nested example checks that beta reduction preserves the
outer binder rather than capturing the argument.  An open client exercises context transport.
-/

namespace Cslib.Languages.LambdaCalculus.Stlc.FullBetaTests

open Cslib.Languages.LambdaCalculus.Stlc
open Cslib.LambdaCalculus.LocallyNameless.Untyped
open scoped CslibStlc

abbrev O : Ty Unit := .base ()

/-- `λ x, (λ y, y) x`: the beta redex occurs under the outer lambda. -/
def underLambda : Tm [] (O ⇒ O) :=
  .lam (.app (.lam (.var .zero)) (.var .zero))

/-- The full-beta reduct of `underLambda`. -/
def identity : Tm [] (O ⇒ O) := .lam (.var .zero)

/-- Weak call-by-value does not reduce under lambda. -/
example : Relation.Normal Step underLambda := by
  intro ⟨target, step⟩
  cases step

/-- The intrinsic compatible relation contracts the redex under the lambda. -/
theorem underLambda_intrinsicFullBeta : FullBeta underLambda identity :=
  .lam (.beta _ _)

/-- The canonical embedding exposes the same beta redex under the lambda. -/
theorem underLambda_fullBeta :
    LocallyNamelessFullBeta underLambda.toLocallyNameless identity.toLocallyNameless :=
  underLambda_intrinsicFullBeta.toLocallyNameless

example : underLambda.toLocallyNameless =
    Term.abs (Term.app (Term.abs (Term.bvar 0)) (Term.bvar 0)) := rfl

example : identity.toLocallyNameless = Term.abs (Term.bvar 0) := rfl

/-- The closed client transports to upstream typing. -/
example :
    Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing
      (Tm.locallyNamelessContext ([] : List (Ty Unit))) underLambda.toLocallyNameless
      (Ty.toLocallyNameless (O ⇒ O)) :=
  underLambda.toLocallyNameless_typing

/-- The source term is not normal for intrinsic full beta. -/
example : ¬Relation.Normal FullBeta underLambda := by
  intro normal
  exact normal ⟨identity, underLambda_intrinsicFullBeta⟩

/-- The same source term is not full-beta normal after embedding. -/
example : ¬Relation.Normal LocallyNamelessFullBeta underLambda.toLocallyNameless := by
  intro normal
  exact normal ⟨identity.toLocallyNameless, underLambda_fullBeta⟩

/-- Both the redex and its reduct inherit upstream full-beta strong normalization. -/
example : Relation.SN LocallyNamelessFullBeta underLambda.toLocallyNameless :=
  underLambda.toLocallyNameless_stronglyNormalizing

example : Relation.SN LocallyNamelessFullBeta identity.toLocallyNameless :=
  identity.toLocallyNameless_stronglyNormalizing_closed

example : Relation.SN FullBeta underLambda :=
  underLambda.fullBeta_stronglyNormalizing

example : Relation.SN FullBeta identity :=
  identity.fullBeta_stronglyNormalizing

/-- `λ x, λ y, (λ z, x) y`: reducing must preserve `x`, not capture `y`. -/
def captureProbe : Tm [] (O ⇒ O ⇒ O) :=
  .lam (.lam (.app (.lam (.var (.succ (.succ .zero)))) (.var .zero)))

/-- The capture-avoiding reduct of `captureProbe`. -/
def captureProbeReduced : Tm [] (O ⇒ O ⇒ O) :=
  .lam (.lam (.var (.succ .zero)))

/-- Intrinsic substitution keeps the outer variable. -/
example :
    Tm.instantiate
      (.var (.succ (.succ .zero)) : Tm [O, O, O] O)
      (.var .zero : Tm [O, O] O) =
    (.var (.succ .zero) : Tm [O, O] O) := rfl

/-- Intrinsic full beta reduces under both surrounding lambdas. -/
theorem captureProbe_intrinsicFullBeta :
    FullBeta captureProbe captureProbeReduced :=
  .lam (.lam (.beta _ _))

/-- The embedded nested reduction keeps the outer binder as `bvar 1`. -/
theorem captureProbe_fullBeta :
    LocallyNamelessFullBeta captureProbe.toLocallyNameless
      captureProbeReduced.toLocallyNameless :=
  captureProbe_intrinsicFullBeta.toLocallyNameless

example : captureProbe.toLocallyNameless =
    Term.abs (Term.abs (Term.app (Term.abs (Term.bvar 2)) (Term.bvar 0))) := rfl

example : captureProbeReduced.toLocallyNameless =
    Term.abs (Term.abs (Term.bvar 1)) := rfl

/-- Open source client `(λ y, y) x` in context `x : O`. -/
def openBeta : Tm [O] O := .app (.lam (.var .zero)) (.var .zero)

/-- Its open-context reduct. -/
def openVariable : Tm [O] O := .var .zero

example :
    Cslib.LambdaCalculus.LocallyNameless.Stlc.Typing
      (Tm.locallyNamelessContext [O]) openBeta.toLocallyNameless
      (Ty.toLocallyNameless O) :=
  openBeta.toLocallyNameless_typing

/-- Full beta reduction of the open client is a root beta step. -/
theorem openBeta_intrinsicFullBeta : FullBeta openBeta openVariable :=
  .beta _ _

theorem openBeta_fullBeta :
    LocallyNamelessFullBeta openBeta.toLocallyNameless openVariable.toLocallyNameless :=
  openBeta_intrinsicFullBeta.toLocallyNameless

/-- Open typed clients receive the same upstream full-beta termination theorem. -/
example : Relation.SN LocallyNamelessFullBeta openBeta.toLocallyNameless :=
  openBeta.toLocallyNameless_stronglyNormalizing

example : Relation.SN FullBeta openBeta :=
  openBeta.fullBeta_stronglyNormalizing

/-- Both application positions propagate intrinsic full beta. -/
example {f f' : Tm [O] (O ⇒ O)} (a : Tm [O] O)
    (hf : FullBeta f f') : FullBeta (.app f a) (.app f' a) :=
  .appFun hf a

example (f : Tm [O] (O ⇒ O)) {a a' : Tm [O] O}
    (ha : FullBeta a a') : FullBeta (.app f a) (.app f a') :=
  .appArg f ha

#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.toLocallyNamelessWith_instantiate
#print axioms Cslib.Languages.LambdaCalculus.Stlc.FullBeta.toLocallyNameless
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.fullBeta_stronglyNormalizing
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.toLocallyNameless_typing
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.toLocallyNameless_stronglyNormalizing
#print axioms Cslib.Languages.LambdaCalculus.Stlc.FullBetaTests.underLambda_fullBeta
#print axioms Cslib.Languages.LambdaCalculus.Stlc.FullBetaTests.captureProbe_fullBeta

end Cslib.Languages.LambdaCalculus.Stlc.FullBetaTests
