/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StablePairAtiyahKernels
public import MathlibExt.AlgebraicGeometry.NormalizedModuleTensorMaps

/-!
# All-degree diagonal tensor and unit normalization

The cochain tensor is the native presheaf totalization and sheafification
used by FourierMukai. Term insertions are the actual coproduct maps.
The diagonal term map is the native projection-formula mate, followed
by pullbackComp, diagonal projection cancellation and the unit map.
The cochain contracts fix every totalization summand, rather than only
the degree-zero map or the map on cohomology.

References: Huybrechts–Thomas, arXiv:0805.3527v2, Definition 2.6;
Stacks 0FYQ, 08EU; the normalized module maps imported above.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairCochainTensorMaps

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open FourierMukai CoherentCurveLinearSeries AlgebraicLineBundleFamilies
open LineBundleTaskContracts
open NormalizedModuleTensorMaps StablePairDiagonalIdeals ModuleDerivedSquares
attribute [local instance] HasDerivedCategory.standard

/-- The ordinary cochain tensor before the fixed localization. -/
def cochainTensor (X : Scheme) : (Cochains X × Cochains X) ⥤ Cochains X :=
  let P := PresheafOfModulesOfCommRing X.sheaf.obj
  let U := SheafOfModules.forget X.ringCatSheaf
  let A := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  letI : (curriedTensor P).PreservesZeroMorphisms := by
    constructor
    intro M N
    apply NatTrans.ext
    funext L
    exact Functor.map_zero (tensorRight L) M N
  (U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ)) ⋙
    Functor.uncurry.obj ((curriedTensor P).map₂CochainComplex) ⋙
      A.mapHomologicalComplex (.up ℤ)

/-- This is exactly the ordinary source of the native derived tensor. -/
theorem tensorSource_eq (X : Scheme) : tensorSource X = cochainTensor X ⋙ DerivedCategory.Q := rfl

/-- The native counit with its target displayed as the actual cochain tensor. -/
def tensorCounit [HasDerivedTensors.{0}] (X : Scheme.{0}) (K L : Cochains X) :
    (derivedTensorUncurried X).obj (DerivedCategory.Q.obj K,DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj ((cochainTensor X).obj (K,L)) := by
  simpa only [tensorSource_eq, Functor.comp_obj, Functor.prod_obj] using
    (derivedTensorCounit X).app (K,L)

/-- The actual insertion of a tensor of two terms into the total cochain degree. -/
def tensorInsertion {X : Scheme} (K L : Cochains X) (i j n : ℤ) (h : i + j = n) :
    moduleTensor X (K.X i) (L.X j) ⟶ ((cochainTensor X).obj (K,L)).X n := by
  let P := PresheafOfModulesOfCommRing X.sheaf.obj
  letI : (curriedTensor P).PreservesZeroMorphisms := by
    constructor
    intro M N
    apply NatTrans.ext
    funext A
    exact Functor.map_zero (tensorRight A) M N
  letI : ∀ M : P, ((curriedTensor P).obj M).PreservesZeroMorphisms :=
    fun M => inferInstanceAs (tensorLeft M).PreservesZeroMorphisms
  exact (sheafifyModules X).map
    (HomologicalComplex.ιMapBifunctor
      (((SheafOfModules.forget X.ringCatSheaf).mapHomologicalComplex (.up ℤ)).obj K)
      (((SheafOfModules.forget X.ringCatSheaf).mapHomologicalComplex (.up ℤ)).obj L)
      (curriedTensor P) (.up ℤ) i j n h)

/-- Actual symmetry after sheafification. -/
def symmetryMap (X : Scheme) (M N : X.Modules) :
    moduleTensor X M N ⟶ moduleTensor X N M :=
  (sheafifyModules X).map (β_ ((forgetModules X).obj M) ((forgetModules X).obj N)).hom

/-- The actual right unit map after sheafification. -/
def rightUnitMap (X : Scheme) (M : X.Modules) :
    moduleTensor X M (structureModule X) ⟶ M :=
  (sheafifyModules X).map (ρ_ ((forgetModules X).obj M)).hom ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app M

variable (Y : Over (Spec (.of ℂ)))

/-- The actual cancellation of diagonal pullback and first projection. -/
def diagonalPullbackIso (M : Y.left.Modules) :
    (Scheme.Modules.pullback (diagonal Y)).obj
      ((Scheme.Modules.pullback (pullback.fst Y.hom Y.hom)).obj M) ≅ M :=
  (Scheme.Modules.pullbackComp (diagonal Y) (pullback.fst Y.hom Y.hom)).app M ≪≫
    (Scheme.Modules.pullbackCongr (by simp [diagonal])).app M ≪≫
      (Scheme.Modules.pullbackId Y.left).app M

/-- The fixed projection-formula map on a single pair of cochain terms. -/
def diagonalTermMap (T : PullbackTensor (diagonal Y)) (M N : Y.left.Modules) :
    moduleTensor (pullback Y.hom Y.hom)
      ((Scheme.Modules.pullback (pullback.fst Y.hom Y.hom)).obj M)
      ((Scheme.Modules.pushforward (diagonal Y)).obj N) ⟶
        (Scheme.Modules.pushforward (diagonal Y)).obj (moduleTensor Y.left M N) :=
  symmetryMap _ _ _ ≫
    projectionFormulaMap (diagonal Y) T N
      ((Scheme.Modules.pullback (pullback.fst Y.hom Y.hom)).obj M) ≫
    (Scheme.Modules.pushforward (diagonal Y)).map
      (tensorMap (𝟙 N) (diagonalPullbackIso Y M).hom ≫ symmetryMap Y.left N M)

/-- A cochain map fixed on every pair of degrees by the actual term mate. -/
structure DiagonalCochainMap (T : PullbackTensor (diagonal Y))
    (K L : Cochains Y.left) where
  map : (cochainTensor (pullback Y.hom Y.hom)).obj
      ((((Scheme.Modules.pullback (pullback.fst Y.hom Y.hom)).mapHomologicalComplex
        (.up ℤ)).obj K),
       (((Scheme.Modules.pushforward (diagonal Y)).mapHomologicalComplex (.up ℤ)).obj L)) ⟶
    ((Scheme.Modules.pushforward (diagonal Y)).mapHomologicalComplex (.up ℤ)).obj
      ((cochainTensor Y.left).obj (K,L))
  normalized : ∀ (i j n : ℤ) (h : i + j = n),
    tensorInsertion
        (((Scheme.Modules.pullback (pullback.fst Y.hom Y.hom)).mapHomologicalComplex
          (.up ℤ)).obj K)
        (((Scheme.Modules.pushforward (diagonal Y)).mapHomologicalComplex (.up ℤ)).obj L)
        i j n h ≫ map.f n =
      diagonalTermMap Y T (K.X i) (L.X j) ≫
        (Scheme.Modules.pushforward (diagonal Y)).map (tensorInsertion K L i j n h)

/-- The right-unit cochain map is fixed in every actual source degree. -/
structure RightUnitCochainMap (K : Cochains Y.left) where
  map : (cochainTensor Y.left).obj
    (K, (CochainComplex.singleFunctor Y.left.Modules 0).obj (structureModule Y.left)) ⟶ K
  normalized : ∀ i : ℤ,
    tensorInsertion K
        ((CochainComplex.singleFunctor Y.left.Modules 0).obj (structureModule Y.left))
        i 0 i (by simp) ≫ map.f i =
      tensorMap (𝟙 (K.X i))
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (structureModule Y.left)).hom ≫
          rightUnitMap Y.left (K.X i)

end MathlibExt.AlgebraicGeometry.StablePairCochainTensorMaps
