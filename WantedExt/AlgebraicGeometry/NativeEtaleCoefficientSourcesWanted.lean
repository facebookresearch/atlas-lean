/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NativeEtaleCoefficientSourceModels

/-!
# Exact native coefficient ordinary/DG and Grothendieck source construction

The whole DG enrichment is the original full cochain Hom model.
Native scalar-unit, source objects, every cochain map and Grothendieck
identity dictionary are fixed before these construction requests.

Source: Keller Section2; Bhatt--Mathew1807.04725v4, Notation5.8.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicGeometry.NativeEtaleCoefficientSourceModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open GeneralArcCoverModels GeneralEtaleCoefficientModels GeneralEtalePullbackCoherence

/-- Construct the actual full native coefficient DG/ordinary unit comparison. -/
def_wanted native_coefficient_dg_ordinary (Λ : Type) [Ring Λ] (X : Scheme.{0}) :
  CoefficientDGOrdinarySource Λ X

/-- The actual native unit/cochain maps assemble into the whole ordinary source functor. -/
def_wanted native_coefficient_simplicial_functor (Λ : Type) [Ring Λ] (X : Scheme.{0})
    (N : CoefficientDGOrdinarySource Λ X) : CoefficientSimplicialFunctorSource Λ X N

/-- The native pseudofunctor unit/transport dictionary assembles into the original whole fibre-entry functor. -/
def_wanted native_coefficient_fibre_entry (Λ : Type) [Ring Λ]
    [∀ Y : Scheme.{0}, HasSheafify Y.smallEtaleTopology (ModuleCat.{1} Λ)]
    (S : ∀ {Y Z : Scheme.{0}} (f : Y ⟶ Z), EtalePullbackSource Λ f)
    (U : ∀ Y : Scheme.{0}, EtaleComplexesPullbackCoherence.EtaleBaseChangeUnitSource Y)
    (C : CoefficientPseudofunctorSource Λ S U) (X : QcqsScheme) :
  CoefficientFibreEntrySource Λ S U C X

end MathlibExt.AlgebraicGeometry.NativeEtaleCoefficientSourceModels
