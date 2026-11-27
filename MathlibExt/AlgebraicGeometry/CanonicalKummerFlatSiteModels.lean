/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LogRootSiteImageModels
public import MathlibExt.AlgebraicGeometry.LogRootInfiniteCompositionModels
public import MathlibExt.AlgebraicGeometry.NativeKummerFlatModels

/-!
# The actual Kummer-flat to root-fppf site functor

An object Y to X goes to the actual root of Y viewed over X, with its
original family category and canonical root arrow. General site arrows
are fixed by the original log map on every finite root level. Their full
Grothendieck functor is transported through the same source/target image
comparisons; no unrelated site functor is selected.

Source: Talpo--Vistoli1410.1164v2, Section6, Proposition6.14 and Theorem6.16.
Local inverse refinements and sheaf equivalence are separate conclusions.
Constructing the canonical site functor for arbitrary root realizations is
left to a separate development: it needs realizations whose evaluated root
comparisons are coherent over the whole tower (identities, composites, base
change and the mixed base/exponent squares), which they do not record.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CanonicalKummerFlatSiteModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.StackCycleGeometry
open _root_.AlgebraicGeometry.StackFibreModels
open EtaleLogSchemes EtaleLogDiagrams EtaleLogNativeCategory
open DenominatorRootStacks FiniteRootTowers KatoChartCoefficientModels
open LogRootSourceModels CanonicalLogRootArrowModels RelativeStackImageModels
open InfiniteRootPreservationModels LogRootSiteImageModels
open NativeKummerFlatModels RepresentableStackFppfModels RepresentableStackFppfSites
open LogRootNativeCommutingSquares LogRootInfiniteCompositionModels

variable [InverseImageTheory.{0}] [N : NativeCategoryModel.{0}]
  (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
  (X : LogScheme.{0}) (RX : RootRealization X D I)
  [HasBaseChanges RX.infinite.stack] [∀ n : Exponent, HasBaseChanges (RX.finite n).stack]

/-- A site object is sent to this actual root image over X. -/
structure ObjectImage (U : NativeKummerFlatModels.Site D X) where
  sourceRoot : RootRealization U.obj.left D I
  finite : FiniteArrow I D U.obj.hom sourceRoot RX
  infinite : InfiniteArrow I D U.obj.hom sourceRoot RX finite
  image : ImageModel U.obj.hom.map sourceRoot.infinite.stack
  arrow : ImageArrow I D U.obj.hom sourceRoot RX finite infinite image
  fppf : FppfImage I D U.obj.hom sourceRoot RX finite infinite image arrow

def objectChart {U : NativeKummerFlatModels.Site D X}
    (C : ObjectImage I D X RX U) : Chart RX.infinite.stack :=
  siteChart I D U.obj.hom C.sourceRoot RX C.finite C.infinite C.image C.arrow C.fppf

variable (S : NativeSiteCategory RX.infinite.stack)

local instance modificationCategory {Z : Scheme.{0}} (A B : Stack Z) :
    Category (StackHom A B) :=
  Pseudofunctor.StrongTrans.homCategory (F := A.toPseudofunctor) (G := B.toPseudofunctor)

universe u v

/-- Native equality transports cancel with their original inverse equality transport. -/
def nativeCatCastUnit {A B : Cat.{u, v}} (e : A = B) :
    (eqToHom e.symm).toFunctor ⋙ (eqToHom e).toFunctor ≅ 𝟭 B := by
  cases e
  exact Iso.refl _

/-- All source object data are selected together; arrows retain the
native root map and its original family transport through image models. -/
structure FunctorModel where
  objects : ∀ U : NativeKummerFlatModels.Site D X, ObjectImage I D X RX U
  functor : letI := S.category; NativeKummerFlatModels.Site D X ⥤ Chart RX.infinite.stack
  object_eq : letI := S.category
    ∀ U : NativeKummerFlatModels.Site D X, functor.obj U = objectChart I D X RX (objects U)
  sourceBaseChanges : ∀ U : NativeKummerFlatModels.Site D X,
    HasBaseChanges (objects U).sourceRoot.infinite.stack
  sourceFiniteBaseChanges : ∀ (U : NativeKummerFlatModels.Site D X) (n : Exponent),
    HasBaseChanges ((objects U).sourceRoot.finite n).stack
  finiteArrows : ∀ {U V : NativeKummerFlatModels.Site D X} (a : U ⟶ V),
    FiniteArrow I D a.hom.left (objects U).sourceRoot (objects V).sourceRoot
  infiniteArrows : ∀ {U V : NativeKummerFlatModels.Site D X} (a : U ⟶ V),
    letI := sourceBaseChanges V
    letI : ∀ n : Exponent, HasBaseChanges ((objects V).sourceRoot.finite n).stack :=
      sourceFiniteBaseChanges V
    InfiniteArrow I D a.hom.left (objects U).sourceRoot (objects V).sourceRoot (finiteArrows a)
  compositions : ∀ {U V : NativeKummerFlatModels.Site D X} (a : U ⟶ V),
    letI := sourceBaseChanges V
    letI : ∀ n : Exponent, HasBaseChanges ((objects V).sourceRoot.finite n).stack :=
      sourceFiniteBaseChanges V
    InfiniteComposition I D a.hom.left V.obj.hom U.obj.hom
      (objects U).sourceRoot (objects V).sourceRoot RX
      (finiteArrows a) (objects V).finite (objects U).finite
      (infiniteArrows a) (objects V).infinite (objects U).infinite
      (original_square_of_over a.hom)
  arrows : letI := S.category
    ∀ {U V : NativeKummerFlatModels.Site D X} (a : U ⟶ V),
    letI := sourceBaseChanges V
    totalMap (rawArrow S (functor.map a)).map ≅
      (eqToHom (congrArg (fun C : Chart RX.infinite.stack => Cat.of (Total C.domain)) (object_eq U))).toFunctor ⋙
      (objects U).image.comparison.functor ⋙
        totalMap (infiniteArrows a).morphism ⋙
          RootEtaleRestrictions.totalView a.hom.left.map (objects V).sourceRoot.infinite.stack ⋙
            (objects V).image.comparison.inverse ⋙
              (eqToHom (congrArg (fun C : Chart RX.infinite.stack => Cat.of (Total C.domain)) (object_eq V).symm)).toFunctor
  arrow_base_identity : letI := S.category
    ∀ {U V : NativeKummerFlatModels.Site D X} (a : U ⟶ V)
      (r : Total (functor.obj U).domain),
    HEq (((arrows a).hom.app r).base.left) (𝟙 r.base.left)
  rootComposition : letI := S.category
    ∀ {U V : NativeKummerFlatModels.Site D X} (a : U ⟶ V),
      (eqToHom (congrArg (fun C : Chart RX.infinite.stack => Cat.of (Total C.domain))
        (object_eq U))).toFunctor ⋙
      originalTotalMap I D U.obj.hom (objects U).sourceRoot RX
        (objects U).finite (objects U).infinite (objects U).image ≅
      totalMap (rawArrow S (functor.map a)).map ⋙
        (eqToHom (congrArg (fun C : Chart RX.infinite.stack => Cat.of (Total C.domain))
          (object_eq V))).toFunctor ⋙
        originalTotalMap I D V.obj.hom (objects V).sourceRoot RX
          (objects V).finite (objects V).infinite (objects V).image
  triangle_normalization : letI := S.category
    ∀ {U V : NativeKummerFlatModels.Site D X} (a : U ⟶ V)
      (r : Total (functor.obj U).domain),
      HEq ((rootComposition a).hom.app r).fiber
        ((InfiniteDenominatorRoots.componentIso (rawArrow S (functor.map a)).triangle
          r.base).inv.app r.fiber)
  composition_source_normalization : letI := S.category
    ∀ {U V : NativeKummerFlatModels.Site D X} (a : U ⟶ V)
      (r : Total (functor.obj U).domain),
    let qU := (objects U).image.comparison.functor.obj
      ((eqToHom (congrArg (fun C : Chart RX.infinite.stack => Cat.of (Total C.domain))
        (object_eq U))).toFunctor.obj r)
    let qV := (rootTotalMap I D a.hom.left (objects U).sourceRoot (objects V).sourceRoot
      (finiteArrows a) (infiniteArrows a)).obj qU
    let eV := congrArg (fun C : Chart RX.infinite.stack => Cat.of (Total C.domain)) (object_eq V)
    let castV := (eqToHom eV).toFunctor
    let k := (objects V).image.comparison.functor.map (castV.map ((arrows a).hom.app r)) ≫
      (objects V).image.comparison.functor.map
        ((nativeCatCastUnit eV).hom.app ((objects V).image.comparison.inverse.obj qV)) ≫
      (objects V).image.comparison.counitIso.hom.app qV
    (rootComposition a).hom.app r ≫
      (rootTotalMap I D V.obj.hom (objects V).sourceRoot RX
        (objects V).finite (objects V).infinite).map k =
    (compositions a).total.hom.app qU

end MathlibExt.AlgebraicGeometry.CanonicalKummerFlatSiteModels
