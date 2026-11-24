/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DuBoisCanonicalComparison
public import Batteries.Util.ProofWanted

/-!
# Normal-CM Du Bois canonical comparison

Kovács--Schwede--Smith, arXiv0801.1541v3, §2.B and Theorem 1.1.
The constructor compares the actual degree-minus-dimension dual unit
with the actual field-normalized log-resolution canonical pushforward.
The criterion is requested separately; neither endpoint assumes
the Du Bois condition or the isomorphism it is supposed to characterize.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.DuBoisCanonicalComparison

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.PrincipalizationModels
open MathlibExt.AlgebraicGeometry.EmbeddedDuBoisZero
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences
open MathlibExt.AlgebraicGeometry.NaturalPullbackMultiplierModules
open MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces
attribute [local instance] HasDerivedCategory.standard

def_wanted duBoisCanonicalComparison
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    [HasDerivedPushforwards.{0}] [HasDerivedPullbacks.{0}] [HasDerivedTensors.{0}]
    (V : NormalVariety k n) (KX : CanonicalData V)
    (cm : RationalResolution.IsCohenMacaulayStalkwise V.X.left)
    (M : CanonicalModel V KX) [Smooth M.variety.X.hom]
    (G : ReducedExceptional M)
    (snc : NormalCrossingsModels.IsStrictNormalCrossings M.variety.X
      (Scheme.IdealSheafData.vanishingIdeal
        (M.map.left ⁻¹ᵁ isomorphismOpen V KX M).compl))
    [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]
    [∀ p : PrimePoint M.variety, IsDiscreteValuationRing (LocalRing M.variety p.val)]
    (C : LogCanonicalPushforward V KX M G)
    (S : Over (Spec (.of k))) [Smooth S.hom] [LocallyOfFiniteType S.hom]
    [IsNoetherian S.left] (I : S.left.IdealSheafData) [IsReduced I.subscheme]
    (R : Principalization S I) (F : ExceptionalMap R)
    (e : EmbeddedIdentification V I)
    (D : CanonicalWeilReference V) (canonicalNormalized : D.divisor = canonicalDivisor KX)
    [((derivedTensor V.X.left).obj (embeddedObject V F e)).IsLeftAdjoint]
    [((derivedTensor V.X.left).obj (derivedUnit V.X.left)).IsLeftAdjoint] :
    CanonicalComparison V KX M G C F e D canonicalNormalized

theorem_wanted duBoisCanonicalIsomorphismCriterion
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    [HasDerivedPushforwards.{0}] [HasDerivedPullbacks.{0}] [HasDerivedTensors.{0}]
    (V : NormalVariety k n) (KX : CanonicalData V)
    (cm : RationalResolution.IsCohenMacaulayStalkwise V.X.left)
    (M : CanonicalModel V KX) [Smooth M.variety.X.hom]
    (G : ReducedExceptional M)
    (snc : NormalCrossingsModels.IsStrictNormalCrossings M.variety.X
      (Scheme.IdealSheafData.vanishingIdeal
        (M.map.left ⁻¹ᵁ isomorphismOpen V KX M).compl))
    [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]
    [∀ p : PrimePoint M.variety, IsDiscreteValuationRing (LocalRing M.variety p.val)]
    (C : LogCanonicalPushforward V KX M G)
    (S : Over (Spec (.of k))) [Smooth S.hom] [LocallyOfFiniteType S.hom]
    [IsNoetherian S.left] (I : S.left.IdealSheafData) [IsReduced I.subscheme]
    (R : Principalization S I) (F : ExceptionalMap R)
    (e : EmbeddedIdentification V I)
    (D : CanonicalWeilReference V) (canonicalNormalized : D.divisor = canonicalDivisor KX)
    [((derivedTensor V.X.left).obj (embeddedObject V F e)).IsLeftAdjoint]
    [((derivedTensor V.X.left).obj (derivedUnit V.X.left)).IsLeftAdjoint] :
    IsIso C.map ↔ IsIso (embeddedUnit V F e)

end MathlibExt.AlgebraicGeometry.DuBoisCanonicalComparison
