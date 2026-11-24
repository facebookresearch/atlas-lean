/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticMeromorphicCoordinates
public import MathlibExt.AlgebraicGeometry.WittDiscTorsorModels
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Meromorphic Hecke objects and their actual formal coefficient rings

The pole condition asks for a Cartier atlas whose pole charts carry
original integral frames of both torsors, and requires every
representation matrix, in those frames, to become an original analytic
matrix after multiplication by a finite power of the Cartier parameter.
The frames are part of the witness, so the condition cannot hold
vacuously on charts without frames. Bounds are local on affinoid etale
neighbourhoods; an arbitrary non-quasicompact perfectoid family is not
assigned one uniform exponent.

The Hecke objects retain exactly the two original G-torsors and their
punctured comparison. Their formal positive ring is the literal
kernel-adic completion of the original analytic chart ring. The generic
ring is its actual parameter localization. Local Hecke objects below
are genuine algebraic G-torsors on the spectra of these two rings.

The global-to-local constructor and its original frame/refinement
normalizations are separate operations. No arbitrary analytic
isomorphism is assigned a B_dR position by these definitions.

Reference: Fargues--Scholze, arXiv:2102.13459v4, Section III.3, p. 97;
Definition VI.1.6 and Proposition VI.1.7, pp. 193--194.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MeromorphicHeckeModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.GeneralStackGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates AlgebraicGroupPointRepresentations
open MathlibExt.CategoryTheory.SheafTorsorGroupoids

variable (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
  (G : Over (Spec (.of E))) [GrpObj G]
  (H : ∀ V : ESpace p E, GroupDescent p E G V)
  (P : PullbackPreservation p E G H)
  {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)

/-- Multiplication by the actual Cartier parameter clears every matrix pole. -/
def HasPoleBound (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (left : IntegralFrame p E G H d U Q M.left)
    (right : IntegralFrame p E G H d U Q M.right)
    (n : ℕ) (ρ : Representation E G n) (k : ℕ) : Prop :=
  ∃ a : Matrix (Fin n) (Fin n) (SectionRing p E Q.space), ∀ i j,
    sectionMap p E Q.puncture.map (a i j) =
      (sectionMap p E Q.puncture.map Q.parameter) ^ k *
        comparisonMatrix p E G H P d U Q M left right n ρ i j

/-- Meromorphicity is local finite-pole extension: some Cartier atlas has pole charts carrying
integral frames of both torsors, in which every representation matrix has a finite pole. -/
def IsMeromorphic (M : Modification p E G H P d U) : Prop :=
  ∃ A : CartierAtlas p E d U, ∀ i : A.index,
    ∃ (left : IntegralFrame p E G H d U (A.chart i) M.left)
      (right : IntegralFrame p E G H d U (A.chart i) M.right),
      ∀ (n : ℕ) (ρ : Representation E G n), ∃ k : ℕ,
        HasPoleBound p E G H P d U (A.chart i) M left right n ρ k

/-- This full subcategory retains the original punctured isomorphism and all its arrows. -/
abbrev MeromorphicModifications :=
  (show ObjectProperty (Modification p E G H P d U) from
    IsMeromorphic p E G H P d U).FullSubcategory

/-- The actual meromorphic Hecke groupoid. -/
abbrev Hecke := Core (MeromorphicModifications p E G H P d U)

/-- The left leg is the original G-torsor, with its original equivariant map. -/
def leftLeg : Hecke p E G H P d U ⥤ Bundles p E G H X :=
  Core.inclusion _ ⋙
    (show ObjectProperty (Modification p E G H P d U) from
      IsMeromorphic p E G H P d U).ι ⋙ AnalyticBundleModifications.leftLeg p E G H P d U

/-- The right leg is the second original G-torsor. -/
def rightLeg : Hecke p E G H P d U ⥤ Bundles p E G H X :=
  Core.inclusion _ ⋙
    (show ObjectProperty (Modification p E G H P d U) from
      IsMeromorphic p E G H P d U).ι ⋙ AnalyticBundleModifications.rightLeg p E G H P d U

variable (Q : PoleChart p E d U)

/-- The exact chart ring completed along its displayed Cartier-kernel ideal. -/
abbrev FormalRing := AdicCompletion (divisorKernel p E Q.divisorMap ⊤)
  (SectionRing p E Q.space)

/-- The actual completion unit, retaining the original analytic coefficients. -/
def completionMap : SectionRing p E Q.space →+* FormalRing p E d U Q := algebraMap _ _

/-- The original Cartier parameter, mapped by that exact unit. -/
def formalParameter : FormalRing p E d U Q := completionMap p E d U Q Q.parameter

/-- The actual generic coefficient ring, obtained by inverting this parameter. -/
abbrev GenericRing := Localization.Away (formalParameter p E d U Q)

/-- Original E scalars are retained through both coefficient maps. -/
def positiveScalars : E →+* FormalRing p E d U Q :=
  (completionMap p E d U Q).comp (coefficients p E Q.space)

def genericScalars : E →+* GenericRing p E d U Q :=
  (algebraMap (FormalRing p E d U Q) (GenericRing p E d U Q)).comp
    (positiveScalars p E d U Q)

/-- The formal disc is the actual spectrum over the original coefficient field. -/
def positiveScheme : Over (Spec (.of E)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (positiveScalars p E d U Q)))

/-- Its actual punctured spectrum. -/
def genericScheme : Over (Spec (.of E)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (genericScalars p E d U Q)))

/-- The original parameter-localization map, with its coefficient square. -/
def localization : genericScheme p E d U Q ⟶ positiveScheme p E d U Q :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (algebraMap (FormalRing p E d U Q) (GenericRing p E d U Q)))) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      exact (Spec.map_comp _ _).symm)

/-- Original algebraic torsors on the actual completed disc. -/
abbrev FormalTorsors := WittDiscTorsorModels.Torsors E G (positiveScheme p E d U Q)

/-- Restrict their genuine action sheaves along the actual punctured-spectrum map. -/
def genericActions : FormalTorsors p E G d U Q ⥤
    Action (WittDiscTorsorModels.topology E (genericScheme p E d U Q))
      (WittDiscTorsorModels.groupSheaf E G (genericScheme p E d U Q)) :=
  WittDiscTorsorModels.torsorActions E G (positiveScheme p E d U Q) ⋙
    WittDiscTorsorModels.actionPullback G (localization p E d U Q)

/-- Local Hecke objects and arrows are the native isomorphism-comma groupoid. -/
abbrev LocalHecke := Core (IsoFibre (genericActions p E G d U Q)
  (genericActions p E G d U Q))

/-- The original left algebraic torsor. -/
def localLeftLeg : LocalHecke p E G d U Q ⥤ FormalTorsors p E G d U Q :=
  Core.inclusion _ ⋙ CategoryTheory.Limits.CategoricalPullback.π₁ (genericActions p E G d U Q)
    (genericActions p E G d U Q)

/-- The original right algebraic torsor. -/
def localRightLeg : LocalHecke p E G d U Q ⥤ FormalTorsors p E G d U Q :=
  Core.inclusion _ ⋙ CategoryTheory.Limits.CategoricalPullback.π₂ (genericActions p E G d U Q)
    (genericActions p E G d U Q)

/-- The full native punctured comparison, coherent on every local Hecke arrow. -/
def localComparison : localLeftLeg p E G d U Q ⋙ genericActions p E G d U Q ≅
    localRightLeg p E G d U Q ⋙ genericActions p E G d U Q :=
  _root_.CategoryTheory.Functor.associator _ _ _ ≪≫
    _root_.CategoryTheory.Functor.isoWhiskerLeft (Core.inclusion _)
      (CategoryTheory.CatCommSq.iso (CategoryTheory.Limits.CategoricalPullback.π₁ (genericActions p E G d U Q) (genericActions p E G d U Q))
        (CategoryTheory.Limits.CategoricalPullback.π₂ (genericActions p E G d U Q) (genericActions p E G d U Q)) (genericActions p E G d U Q) (genericActions p E G d U Q)) ≪≫
        (_root_.CategoryTheory.Functor.associator _ _ _).symm

end MathlibExt.AlgebraicGeometry.MeromorphicHeckeModels
