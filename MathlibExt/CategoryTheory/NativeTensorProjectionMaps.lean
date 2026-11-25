/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeRingInverseImages

/-!
# Native finite-form tensor projection and Gauss--Manin scalar transport

Tensor projection is the native derived-adjunction mate of the original
tensor/pullback square, fixed on every original tensor generator and
every cochain unit. Its degree map is native cohomology transport.
These maps exist before any isomorphism proof. Their geometric finite
complex application has an explicit `FiniteForms` guard in WantedExt.

References: Scholze, arXiv:1205.3463v2, Lemma 8.6 and Theorem 8.8;
native Mathlib tensor, adjunction and right-derived cochain operators,
Apache 2.0, revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeTensorProjectionMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open RingedDerivedCoefficientOperations RingSheafModuleTensors
open NativeScalarProjectionMaps

attribute [local instance] HasDerivedCategory.standard

universe v u

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {T : GrothendieckTopology D}
  [UnivLE.{max u v, 1}]
  [HasSheafify J AddCommGrpCat.{1}] [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  [HasSheafify T AddCommGrpCat.{1}] [T.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (G : C ⥤ D) [G.IsContinuous J T]
  (S : Sheaf J CommRingCat.{1}) (R : Sheaf T CommRingCat.{1})
  (φ : S ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj R)
  [(pushforward G S R φ).IsRightAdjoint]
  [EnoughInjectives (Modules S)] [EnoughInjectives (Modules R)]
  [PullbackSourceUnit G S R φ]
  (Ω : Modules S)

abbrev tensorY := tensorFunctor S Ω
abbrev tensorX := tensorFunctor R ((pullback G S R φ).obj Ω)

variable [(tensorY S Ω).Additive] [(tensorX G S R φ Ω).Additive]

/-- The actual native generator and cochain-unit normalized tensor square. -/
structure SourceSquare where
  ordinary : tensorY S Ω ⋙ pullback G S R φ ≅ pullback G S R φ ⋙ tensorX G S R φ Ω
  ordinary_source : ∀ (M : Modules S) (U : Cᵒᵖ) (m : M.val.obj U) (w : Ω.val.obj U),
    ((ordinary.hom.app M).val.app (G.op.obj U)).hom
      (((adjunction G S R φ).unit.app ((tensorY S Ω).obj M)).val.app U
        (generator S M Ω U m w)) =
      generator R ((pullback G S R φ).obj M) ((pullback G S R φ).obj Ω) (G.op.obj U)
        ((((adjunction G S R φ).unit.app M).val.app U).hom m)
        ((((adjunction G S R φ).unit.app Ω).val.app U).hom w)
  derived : (tensorY S Ω).rightDerivedFunctorPlus ⋙ derivedPullback G S R φ ≅
    derivedPullback G S R φ ⋙ (tensorX G S R φ Ω).rightDerivedFunctorPlus
  cochain_source : ∀ K : CochainComplex.Plus (Modules S),
    (pullback G S R φ).rightDerivedFunctorPlusUnit.app
      ((tensorY S Ω).mapCochainComplexPlus.obj K) ≫
      (derivedPullback G S R φ).map ((tensorY S Ω).rightDerivedFunctorPlusUnit.app K) ≫
      derived.hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map (ordinary.hom.mapCochainComplexPlus.app K) ≫
      (tensorX G S R φ Ω).rightDerivedFunctorPlusUnit.app
        ((pullback G S R φ).mapCochainComplexPlus.obj K) ≫
      (tensorX G S R φ Ω).rightDerivedFunctorPlus.map
        ((pullback G S R φ).rightDerivedFunctorPlusUnit.app K)

variable (Q : SourceSquare G S R φ Ω) (A : DerivedAdjunctionSource G S R φ)

/-- Constructed native derived tensor projection. -/
def projection (K : Derived R) :
    (tensorY S Ω).rightDerivedFunctorPlus.obj ((derivedPushforward G S R φ).obj K) ⟶
      (derivedPushforward G S R φ).obj ((tensorX G S R φ Ω).rightDerivedFunctorPlus.obj K) :=
  AdjunctionProjection.mate (derivedPullback G S R φ) (derivedPushforward G S R φ) A.adj
    (derivedPullback G S R φ) (derivedPushforward G S R φ) A.adj
      (tensorY S Ω).rightDerivedFunctorPlus (tensorX G S R φ Ω).rightDerivedFunctorPlus
      Q.derived.hom K

variable [PreservesFiniteLimits (tensorY S Ω)] [PreservesFiniteColimits (tensorY S Ω)]

/-- The actual native finite-form degree projection; IsIso remains a conclusion. -/
def degree (K : Derived R) (i : ℤ) :
    (tensorY S Ω).obj (cohomology S ((derivedPushforward G S R φ).obj K) i) ⟶
      cohomology S ((derivedPushforward G S R φ).obj
        ((tensorX G S R φ Ω).rightDerivedFunctorPlus.obj K)) i :=
  DerivedCohomology.map (tensorY S Ω) ((derivedPushforward G S R φ).obj K) i ≫
    (DerivedCategory.Plus.homologyFunctor (Modules S) i).map (projection G S R φ Ω Q A K)

end MathlibExt.CategoryTheory.NativeTensorProjectionMaps
