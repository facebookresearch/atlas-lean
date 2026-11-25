/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ThetaQuotientOpenSources

/-!
# Actual scheme parameters for affine quotient sources

Base change is literal precomposition by the native Over.map functor.
On every scheme over the new base, it evaluates the original quotient
source on that same scheme over the original base. Thus it is the
actual base-changed Θ or ST source, including nonreduced parameters.

The same operation restricts a target stack to an arbitrary trait.
Only the native fppf stack proof is a separate source dependency; no
objectwise equivalence or freely chosen base-change functor is used.

Reference: Alper–Halpern-Leistner–Heinloth, arXiv:1812.01128v5,
§2.3 and the source diagrams in Definitions 3.10 and 3.38.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ThetaSchemeParameters

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.GeneralStackGeometry
open ThetaQuotientSources ThetaTraitCharts StackSourceFiltrations
open scoped Pseudofunctor.StrongTrans

universe u

/-- The literal native relative-stack parameter restriction. -/
def restriction {S V : Scheme.{u}} (X : RelativeStack S) (b : V ⟶ S) :
    Pseudofunctor (LocallyDiscrete (Over V)ᵒᵖ) Cat.{u,u+1} :=
  (Over.map b).op.toPseudofunctor.comp X.toPseudofunctor

/-- Keep that exact pseudofunctor with its native fppf stack dependency. -/
def restrictStack {S V : Scheme.{u}} (X : RelativeStack S) (b : V ⟶ S)
    (h : (restriction X b).IsStack (Scheme.fppfTopology.over V)) : RelativeStack V where
  toPseudofunctor := restriction X b
  isGroupoid T := X.isGroupoid ((Over.map b).obj T)
  isStack := h

@[simp]
theorem restrictStack_source {S V : Scheme.{u}} (X : RelativeStack S) (b : V ⟶ S)
    (h : (restriction X b).IsStack (Scheme.fppfTopology.over V)) :
    (restrictStack X b h).toPseudofunctor =
      (Over.map b).op.toPseudofunctor.comp X.toPseudofunctor :=
  rfl

/-- The actual filtration family on every scheme parameter over a new base. -/
abbrev SchemeFiltrations
    {R : Type u} [CommRing R] [ContractingAction R] (D : FiltrationSource R)
    {S : Scheme.{u}} (b : S ⟶ Spec (.of R))
    (h : (restriction D.quotient.stack b).IsStack (Scheme.fppfTopology.over S))
    (X : RelativeStack S) (T : Over S) :=
  Maps (restrictStack D.quotient.stack b h) X T

/-- Both source evaluations are computed from the original normalized
chart, restricted along the actual parameter map. -/
def schemeChartEvaluation
    {R : Type u} [CommRing R] [A : ContractingAction R]
    {Q : @QuotientSource R _ (multiplicativeGroup R) (affineLine R) _ A.action}
    {a : R} (C : ThetaChart R Q a) {S : Scheme.{u}} (b : S ⟶ Spec (.of R))
    (h : (restriction Q.stack b).IsStack (Scheme.fppfTopology.over S))
    (X : RelativeStack S) (T : Over S) :
    Maps (restrictStack Q.stack b h) X T ⥤ X.Fibre T :=
  evaluate (restrictStack Q.stack b h) X T
    ((SourceSection.mk C.point).point ((Over.map b).obj T))

end MathlibExt.AlgebraicGeometry.ThetaSchemeParameters
