/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricSmashHomotopyExtension.NativeScalarFunctorFields
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricSmashHomotopyExtension.NativeScalarRightComparison
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Scalar smash as a parametrized left-adjoint comparison

The free symmetric spectrum in degree zero turns a pointed coefficient
into a source for the spectrum smash-function adjunction. Its parametrized
right adjoint is compared with cotensoring, and the left mate identifies
smashing with this free spectrum with the scalar tensor bifunctor.
The component isomorphisms are natural in pointed coefficient maps.
-/

set_option autoImplicit false
noncomputable section
universe u v uP vP uC vC uB vB uD vD

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed CategoryTheory.MonObj

universe uRetP vRetP uRetB vRetB uRetD vRetD

private def retainParametrizedFamily {P : Type uRetP} [Category.{vRetP} P]
    {B : Type uRetB} [Category.{vRetB} B] {D : Type uRetD} [Category.{vRetD} D]
    {F F' : P ⥤ B ⥤ D} {G G' : Pᵒᵖ ⥤ D ⥤ B}
    (a : F ⊣₂ G) (hF : F = F') (hG : G = G')
    (adj : ∀ X, F'.obj X ⊣ G'.obj (.op X)) (hAdj : HEq a.adj adj) : F' ⊣₂ G' :=
  ParametrizedAdjunction.mk' adj (by
    cases hF
    cases hG
    have ha : a.adj = adj := eq_of_heq hAdj
    cases ha
    intro X Y p Z W f
    exact a.homEquiv_naturality_one p f)

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.ScalarLeftBoundary

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory

private def parameterAlong
    {P : Type uP} [Category.{vP} P] {C : Type uC} [Category.{vC} C]
    {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]
    (K : P ⥤ C) {L : C ⥤ B ⥤ D} {R : Cᵒᵖ ⥤ D ⥤ B} (a : L ⊣₂ R) :
    K ⋙ L ⊣₂ K.op ⋙ R :=
  ParametrizedAdjunction.mk' (fun T => a.adj (K.obj T)) (by
    intro T T' p X Y f
    exact a.homEquiv_naturality_one (K.map p) f)

/-- The original degree-zero free functor keeps its original coefficient object and map constructors. -/
def zeroFreeCoefficientFunctor : V.{u, v} ⥤ Carrier.{u, v} where
  obj := zeroFree
  map := Free.coefficientMap (PointedCGWH.symmetricOperatorObj (𝟙_ I))
  map_id := (Free.functor (PointedCGWH.symmetricOperatorObj (𝟙_ I))).map_id
  map_comp := (Free.functor (PointedCGWH.symmetricOperatorObj (𝟙_ I))).map_comp

/-- The entire source remains the original free coefficient functor in degree zero. -/
theorem zeroFreeCoefficientFunctor_whole :
    zeroFreeCoefficientFunctor.{u, v} =
      Free.functor (PointedCGWH.symmetricOperatorObj (𝟙_ I)) := rfl

attribute [local irreducible] NativeOmegaPreparation.NativeSymmetricFunction.functor
  NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor
  NativeOmegaPreparation.NativeSymmetricFunction.adjunction actualFunctionScalarComparison

/-- The actual native left coefficient bifunctor has its original balanced-smash objects and full source maps. -/
def nativeScalarLeft : V.{u, v} ⥤ Carrier.{u, v} ⥤ Carrier.{u, v} where
  obj := fun T => NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor (zeroFree T)
  map := fun p => nativeSmashBifunctorBoundary.map (zeroFreeCoefficientFunctor.map p)
  map_id := (zeroFreeCoefficientFunctor ⋙ nativeSmashBifunctorBoundary).map_id
  map_comp := (zeroFreeCoefficientFunctor ⋙ nativeSmashBifunctorBoundary).map_comp

/-- The entire actual left coefficient constructor remains the real zero-free functor followed by native smash. -/
theorem nativeScalarLeft_whole :
    nativeScalarLeft.{u, v} = zeroFreeCoefficientFunctor ⋙ nativeSmashBifunctorBoundary := rfl

private theorem wholeRightSource :
    zeroFreeCoefficientFunctor.op ⋙ nativeFunctionBifunctorBoundary.{u, v} =
      nativeScalarRightBoundary.{u, v} :=
  (congrArg (fun R : Carrier.{u, v}ᵒᵖ ⥤ Carrier.{u, v} ⥤ Carrier.{u, v} =>
    zeroFreeCoefficientFunctor.op ⋙ R) nativeFunctionBifunctorBoundary_whole).trans
      ((congrArg (fun K : V.{u, v} ⥤ Carrier.{u, v} =>
        K.op ⋙ NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v})
          zeroFreeCoefficientFunctor_whole).trans nativeScalarRightBoundary_whole.symm)

/-- The full original zero-free adjunction initializer is typed over both actual scalar bifunctors. -/
def originalScalarAdjunctionFamily :
    ∀ T : V.{u, v}, nativeScalarLeft.obj T ⊣ nativeScalarRightBoundary.obj (.op T) :=
  fun T => NativeOmegaPreparation.NativeSymmetricFunction.adjunction (zeroFree T)

/-- Both typed scalar endpoints retain the entire original native zero-free adjunction family. -/
theorem originalScalarAdjunctionFamily_whole :
    HEq originalScalarAdjunctionFamily.{u, v}
      (fun T : V.{u, v} => NativeOmegaPreparation.NativeSymmetricFunction.adjunction (zeroFree T)) :=
  HEq.refl _

/-- The complete parametrized adjunction retains the original adjunction at every actual zero-free object. -/
def nativeScalarParametrized : nativeScalarLeft.{u, v} ⊣₂ nativeScalarRightBoundary.{u, v} :=
  retainParametrizedFamily
    (parameterAlong zeroFreeCoefficientFunctor retainedNativeParametrized)
    nativeScalarLeft_whole.symm wholeRightSource
    originalScalarAdjunctionFamily
    (HEq.refl _)

/-- Each source component is the exact original native zero-free adjunction initializer. -/
theorem nativeScalarParametrized_adj (T : V.{u, v}) :
    nativeScalarParametrized.adj T = originalScalarAdjunctionFamily T := rfl

/-- The actual natural left mate compares the two original parametrized adjunctions along the real zero-free source. -/
def actualScalarLeftComparison :
    nativeScalarLeft.{u, v} ≅
      ScalarLeibniz.tensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
  ParametrizedAdjunction.LeftIsoComparison.iso nativeScalarParametrized
    ScalarLeibniz.parametrizedAdjunction actualFunctionScalarComparison

/-- Every left-mate component is the unchanged original balanced-smash/scalar initializer. -/
theorem actualScalarLeftComparison_app (T : V.{u, v}) :
    actualScalarLeftComparison.app T = originalSmashScalarIso T := by
  have h := ParametrizedAdjunction.LeftIsoComparison.iso_app nativeScalarParametrized
    ScalarLeibniz.parametrizedAdjunction actualFunctionScalarComparison T
  have h' := congrArg
    (fun e => Adjunction.RightIsoComparison.comparison
      (NativeOmegaPreparation.NativeSymmetricFunction.adjunction (zeroFree T))
      (ScalarLeibniz.adjunction T) e)
    (actualFunctionScalarComparison_app (.op T))
  exact h.trans h'

/-- Every original pointed coefficient map preserves the actual original left mate and the scalar tensor map. -/
theorem actualScalarLeftComparison_coefficient {T T' : V.{u, v}} (p : T ⟶ T') :
    nativeSmashBifunctorBoundary.map (zeroFreeCoefficientFunctor.map p) ≫
      (originalSmashScalarIso T').hom =
    (originalSmashScalarIso T).hom ≫
      (ScalarLeibniz.tensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p := by
  have h := actualScalarLeftComparison.hom.naturality p
  change nativeScalarLeft.map p ≫ (actualScalarLeftComparison.app T').hom =
    (actualScalarLeftComparison.app T).hom ≫
      (ScalarLeibniz.tensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p at h
  have hT := congrArg (fun e => e.hom) (actualScalarLeftComparison_app T)
  have hT' := congrArg (fun e => e.hom) (actualScalarLeftComparison_app T')
  have hL := congrArg (fun e => nativeScalarLeft.map p ≫ e) hT'
  have hR := congrArg (fun e => e ≫
    (ScalarLeibniz.tensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p) hT
  exact hL.symm.trans (h.trans hR)











end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.ScalarLeftBoundary
