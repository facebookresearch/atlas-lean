/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ReductiveGroupHypotheses
public import MathlibExt.AlgebraicGeometry.CameralIncidenceModels
public import MathlibExt.AlgebraicGeometry.CameralSymbolReindexModels
public import MathlibExt.AlgebraicGeometry.TorusLineFrameModels

/-!
# Native cameral foundation construction outputs

These packages collect source-normalized outputs, including the actual
Lie algebra, torus and normalizer, Chevalley invariant algebra, Borel
incidence cover and universal Cartan quotient. The group-level
constructor uses rational-representation reductivity; an abelian Lie
algebra alone does not supply that hypothesis.

Ramification outputs include the actual symbol-line presentation on
every affine chart and its computed dual frame torsor. The stronger
ramification tensor/normalizer and regularized-value functors are
separate construction outputs.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections1--6,11--12.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.CameralFoundationPackages

open _root_.CategoryTheory _root_.AlgebraicGeometry
open ExpansionParameterModels CameralTorusBands CameralIncidenceModels
open CameralReductiveSources RegularCentralizerAffineModels SchemeLieJetFamilies
open CameralRamificationSymbols CameralSymbolReindexModels TorusLineFrameModels

variable {k : Type} [Field k] (G : Over (Spec (.of k))) [GrpObj G]

structure LiePresentation where
  carrier : Type
  [ring : LieRing carrier]
  [algebra : LieAlgebra k carrier]
  [finite : FiniteDimensional k carrier]
  model : AffineGroupLieModels.LieModel G carrier

attribute [instance] LiePresentation.ring LiePresentation.algebra LiePresentation.finite

def schemeCoverIso {W : Type} [Group W] [Fintype W]
    {X : Over (Spec (.of k))} (C : WCover W X) (w : W) : C.scheme.left ≅ C.scheme.left :=
  (Over.forget X.left).mapIso (C.action w).asIso

structure Foundation (tori : ∀ n : ℕ, TorusTheory k n) where
  lie : LiePresentation G
  jets : TangentFamilies G lie.carrier lie.model
  adjoint : AdjointFamilies G lie.carrier lie.model jets
  rank : ℕ
  Weyl : Type
  [weylGroup : Group Weyl]
  [weylFinite : Fintype Weyl]
  roots : Roots (tori rank) (tori 1) Weyl
  source : Source G lie.carrier lie.model jets adjoint (tori rank) (tori 1) Weyl roots
  action : CameralChevalleyModels.Action (tori rank) (tori 1) Weyl roots
  chevalley : CameralChevalleyModels.Geometry (tori rank) (tori 1) Weyl roots action
  weyl : ConstantWeyl (k := k) Weyl
  normalizer : Normalizer G lie.carrier lie.model jets adjoint
    (tori rank) (tori 1) Weyl roots source weyl
  borel : BorelSource source
  centralizers : ParameterScheme (k := k) lie.carrier rank
  flag : FlagScheme borel
  centralizerAction : CentralizerAction (D := adjoint) centralizers
  universalCover : UniversalCover borel centralizers flag chevalley.chevalley
  value : CartanValueMap universalCover
  band : ∀ (X : Over (Spec (.of k))) (C : CameralCover Weyl chevalley.chevalley X),
    BandModel (tori rank) (tori 1) Weyl roots chevalley.chevalley C
  ramification : ∀ (X : Over (Spec (.of k))) (C : CameralCover Weyl chevalley.chevalley X)
      (i : Fin roots.count),
    Σ I : IdealSymbols (overScheme C.cover) (schemeCoverIso C.cover (roots.reflection i)),
      GlobalPresentation I × RamificationSection I ×
        LineFrames (tori 1) (overScheme C.cover) (ramificationLine I)

attribute [instance] Foundation.weylGroup Foundation.weylFinite

end MathlibExt.AlgebraicGeometry.CameralFoundationPackages
