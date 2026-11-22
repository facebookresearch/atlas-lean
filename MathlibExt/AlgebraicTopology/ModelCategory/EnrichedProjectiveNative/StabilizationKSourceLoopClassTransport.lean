/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Enriched.ScalarCotensor
import MathlibExt.AlgebraicTopology.Spectra.Sequential.FunctorClosed
import MathlibExt.CategoryTheory.Monoidal.Closed.InternalHomInterchange
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.NativeLoopShift
import MathlibExt.Topology.Category.PointedCGWH.Closed
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.LevelFibrancy
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FreeStabilizationMapping

/-!
# Actual scalar-loop source maps for native spectrum class transport

The scalar cotensor uses the original based one-sphere internal Hom at
every native index. Its complete evaluation comparison and cube group
shift retain every original diagram map.

For the original sequential enriched index, the entire successor action
is the looped original action followed by the original closed-category
coordinate interchange. That interchange is built from the actual
internal currying maps, braiding and evaluation. These identities supply
the source maps for the native scalar-loop weak-class argument.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v uC vC
open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open MonoidalCategory BraidedCategory MonoidalClosed HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.SourceLoopClassTransport

section Structure

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]

variable [HasInitial C]
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full scalar-loop successor transpose keeps the original two-coordinate
interchange between its two internal Hom maps. -/
theorem scalarLoopSequential_adjointStructureMap (K : C)
    (X : CategoryTheory.Spectra.Sequential.Spectrum K) (n : ℕ) :
    CategoryTheory.Spectra.Sequential.adjointStructureMap ((cotensor K).obj X) n =
      (ihom K).map (CategoryTheory.Spectra.Sequential.adjointStructureMap X n) ≫
        (MonoidalClosed.OriginalLoopInterchangeGeometry.originalSelfInterchangeNatIso K).hom.app
          (CategoryTheory.Spectra.Sequential.level X (n + 1)) := by
  apply MonoidalClosed.uncurry_injective
  apply MonoidalClosed.uncurry_injective
  rw [CategoryTheory.Spectra.Sequential.adjointStructureMap_uncurry,
    CategoryTheory.Spectra.Sequential.structureMap, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_natural_left, CategoryTheory.Spectra.Sequential.action,
    EnrichedFunctor.cotensor_doubleUncurry,
    MonoidalClosed.OriginalDoubleLoopCoordinateGeometry.originalWholeSquareSwap_hom_uncurry,
    MonoidalClosed.uncurry_ihom_map, MonoidalClosed.uncurry_natural_left,
    CategoryTheory.Spectra.Sequential.adjointStructureMap_uncurry,
    CategoryTheory.Spectra.Sequential.structureMap]
  let a := CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n
  let b := CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K (n + 1)
  let H := a ⟶[C] b
  let A := (ihom K).obj (X.toEnrichedFunctor.obj a)
  let u := (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso K n).inv
  let e := (ihom.ev K).app (X.toEnrichedFunctor.obj a)
  have h := scalarOperatorInterchange_tensorSwapEvaluation K K A H (X.toEnrichedFunctor.obj a) u e
  have h' := congrArg (fun q => q ≫ CategoryTheory.Spectra.Sequential.action X a b) h
  simp only [Category.assoc, whiskerLeft_comp] at h'
  simp only [tensorHom_id]
  change K ◁ (u ▷ A) ≫ K ◁ (β_ A H).inv ≫ (α_ K A H).inv ≫
      e ▷ H ≫ CategoryTheory.Spectra.Sequential.action X a b =
    (α_ K K A).inv ≫ (β_ K K).inv ▷ A ≫ (α_ K K A).hom ≫ K ◁ e ≫
      u ▷ X.toEnrichedFunctor.obj a ≫ (β_ (X.toEnrichedFunctor.obj a) H).inv ≫
        CategoryTheory.Spectra.Sequential.action X a b
  exact h'

end Structure

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every original native operator inclusion has the actual scalar cotensor
transpose, with its complete coefficient/scalar coordinate interchange. -/
theorem scalarCotensor_adjointOperatorMap (a b : I) (M K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    Native.OperatorStabilizationK.CurrentFree.adjoint a b K D ((cotensor M).obj X) =
      (ihom M).map (Native.OperatorStabilizationK.CurrentFree.adjoint a b K D X) ≫
        (scalarOperatorInterchangeNatIso M K).hom.app (X.toEnrichedFunctor.obj b) := by
  apply MonoidalClosed.uncurry_injective (A := K)
  apply MonoidalClosed.uncurry_injective (A := M)
  rw [Native.OperatorStabilizationK.CurrentFree.adjoint_uncurry,
    Native.OperatorStabilizationK.CurrentFree.action, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_natural_left, EnrichedFunctor.cotensor_doubleUncurry,
    scalarOperatorInterchange_uncurry, MonoidalClosed.uncurry_ihom_map,
    MonoidalClosed.uncurry_natural_left,
    Native.OperatorStabilizationK.CurrentFree.adjoint_uncurry,
    Native.OperatorStabilizationK.CurrentFree.action]
  let H := a ⟶[PointedCGWH.{u, v}] b
  let A := (ihom M).obj (X.toEnrichedFunctor.obj a)
  let e := (ihom.ev M).app (X.toEnrichedFunctor.obj a)
  have h := scalarOperatorInterchange_tensorSwapEvaluation M K A H (X.toEnrichedFunctor.obj a) D e
  have h' := congrArg (fun q => q ≫ MonoidalClosed.uncurry (X.toEnrichedFunctor.map a b)) h
  simp only [Category.assoc, whiskerLeft_comp] at h'
  change M ◁ (D ▷ A) ≫ M ◁ (β_ A H).inv ≫ (α_ M A H).inv ≫
      e ▷ H ≫ MonoidalClosed.uncurry (X.toEnrichedFunctor.map a b) =
    (α_ M K A).inv ≫ (β_ K M).inv ▷ A ≫ (α_ K M A).hom ≫ K ◁ e ≫
      D ▷ X.toEnrichedFunctor.obj a ≫ (β_ (X.toEnrichedFunctor.obj a) H).inv ≫
        MonoidalClosed.uncurry (X.toEnrichedFunctor.map a b)
  exact h'

/-- Scalar loops retain the whole native evaluated one-sphere internal Hom,
naturally in every original diagram map. -/
def scalarLoopEvaluationIso (a : I) :
    cotensor PointedCGWH.sphereOne.{u, v} ⋙ EnrichedFunctorCat.evaluation a ≅
      EnrichedFunctorCat.evaluation a ⋙ PointedCGWH.loop.{u, v} :=
  NatIso.ofComponents (fun X => Iso.refl _) (fun f => by
    change component (cotensorMap PointedCGWH.sphereOne f) a ≫ 𝟙 _ =
      𝟙 _ ≫ (ihom PointedCGWH.sphereOne).map (component f a)
    rw [Category.comp_id, Category.id_comp]
    exact cotensorMap_component PointedCGWH.sphereOne f a)

/-- The original positive cube group shift applies to the actual scalar cotensor
at every original index object, with both full component maps. -/
def scalarLoopGroupEvaluationIso (a : I) (k : ℕ) :
    (cotensor PointedCGWH.sphereOne.{u, v} ⋙ EnrichedFunctorCat.evaluation a) ⋙
        PointedCGWH.piNPositiveFunctor k ≅
      EnrichedFunctorCat.evaluation a ⋙ PointedCGWH.piNPositiveFunctor (k + 1) :=
  Functor.isoWhiskerRight (scalarLoopEvaluationIso a) (PointedCGWH.piNPositiveFunctor k) ≪≫
    Functor.associator (EnrichedFunctorCat.evaluation a) PointedCGWH.loop
      (PointedCGWH.piNPositiveFunctor k) ≪≫
      Functor.isoWhiskerLeft (EnrichedFunctorCat.evaluation a)
        (PointedCGWH.NativeLoopShiftGeometry.nativeLoopGroupShiftNatIso k)

/-- Every original native source arrow retains the full forward group comparison. -/
theorem scalarLoopGroupEvaluationIso_hom_naturality (a : I) (k : ℕ)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    (PointedCGWH.piNPositiveFunctor k).map
        (component ((cotensor PointedCGWH.sphereOne).map f) a) ≫
          (scalarLoopGroupEvaluationIso a k).hom.app Y =
      (scalarLoopGroupEvaluationIso a k).hom.app X ≫
        (PointedCGWH.piNPositiveFunctor (k + 1)).map (component f a) :=
  (scalarLoopGroupEvaluationIso a k).hom.naturality f

end HomotopicalAlgebra.EnrichedProjective.Native.SourceLoopClassTransport
