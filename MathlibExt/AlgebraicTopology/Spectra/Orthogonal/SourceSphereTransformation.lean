/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SourceGeneratorRecovery
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorRightSphereNaturality

/-!
# The original right sphere action as a genuine enriched transformation

The two input Hom objects are kept in their entire native smash tensor.
Their independent native unit points determine the whole uncurried action,
while the entire spectrum value and sphere coefficient remain untouched.
The resulting transformation has the original right sphere components.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Spectra.OrthogonalSourceRightModule

open Enriched.SphereOperator

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
attribute [local instance] OrthogonalIndex.enrichedOrdinaryCategory
attribute [local instance] OrthogonalIndex.symmetricCategory
attribute [local instance] Enriched.prodCategory

/-- The actual right sphere action is natural on both entire continuous input Hom objects. -/
theorem sphereAction_full_naturality
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (a b : OrthogonalIndex × OrthogonalIndex) :
    MonoidalClosed.uncurry
        ((((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.externalTensor
          orthogonalSphereFunctor.{u, v}).map a b) ≫ sphereAction.{u, v} F b.1 b.2 =
      (sphereAction.{u, v} F a.1 a.2 ⊗ₘ 𝟙 (a ⟶[PointedCGWH.{u, v}] b)) ≫
        MonoidalClosed.uncurry
          ((OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
            PointedCGWH.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor).map a b) := by
  let X := ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
  let S := orthogonalSphereFunctor.{u, v}
  let E := X.externalTensor S
  let J := OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
    PointedCGWH.{u, v} X
  let Y := E.obj a
  let Z := J.obj a
  let W := J.obj b
  let H := a ⟶[PointedCGWH.{u, v}] b
  let σa : Y ⟶ Z := sphereAction.{u, v} F a.1 a.2
  let σb : E.obj b ⟶ W := sphereAction.{u, v} F b.1 b.2
  let e : Y ⊗ H ⟶ E.obj b := MonoidalClosed.uncurry (E.map a b)
  let j : Z ⊗ H ⟶ W := MonoidalClosed.uncurry (J.map a b)
  change e ≫ σb = (σa ⊗ₘ 𝟙 H) ≫ j
  apply MonoidalClosed.curry_injective
  apply PointedCGWH.tensorPoint_hom_ext
  intro p q
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  let f : a.1 ⟶ b.1 := (eHomEquiv PointedCGWH.{u, v}).symm p
  let u' : a.2 ⟶ b.2 := (eHomEquiv PointedCGWH.{u, v}).symm q
  have hf : eHomEquiv PointedCGWH.{u, v} f = p := Equiv.apply_symm_apply _ p
  have hu : eHomEquiv PointedCGWH.{u, v} u' = q := Equiv.apply_symm_apply _ q
  let c := PointedCGWH.pointPair p q
  let r : Y ⟶ E.obj b := X.toOrdinaryFunctor.map f ⊗ₘ S.toOrdinaryFunctor.map u'
  let s : Z ⟶ W := X.toOrdinaryFunctor.map (f ⊗ₘ u')
  have hE : c ≫ E.map a b = eHomEquiv PointedCGWH.{u, v} r := by
    have h := externalTensor_pairPoint X S f u'
    rw [hf, hu] at h
    exact h
  have hJ : c ≫ J.map a b = eHomEquiv PointedCGWH.{u, v} s := by
    have h := tensorComp_pairPoint OrthogonalIndex.enrichedMonoidalData.{u, v} X f u'
    rw [hf, hu] at h
    exact h
  have hPointE : (Y ◁ c) ≫ e = (ρ_ Y).hom ≫ r :=
    uncurry_unitPoint c (E.map a b) r hE
  have hPointJ : (Z ◁ c) ≫ j = (ρ_ Z).hom ≫ s :=
    uncurry_unitPoint c (J.map a b) s hJ
  have hSphere : r ≫ σb = σa ≫ s :=
    rightSphereAction_twoInputs OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} F f u'
  have hTensor : (Y ◁ c) ≫ (σa ⊗ₘ 𝟙 H) = σa ⊗ₘ c :=
    (congrArg (fun z => (Y ◁ c) ≫ z) (tensorHom_id σa H)).trans
      (tensorHom_def' σa c).symm
  have hNatural : (ρ_ Y).inv ≫ (Y ◁ c) ≫ (σa ⊗ₘ 𝟙 H) =
      σa ≫ (ρ_ Z).inv ≫ Z ◁ c :=
    (congrArg (fun z => (ρ_ Y).inv ≫ z) hTensor).trans
      (rightUnitor_inv_comp_tensorHom σa c)
  have hLeft : (ρ_ Y).inv ≫ (Y ◁ c) ≫ e = r :=
    (congrArg (fun z => (ρ_ Y).inv ≫ z) hPointE).trans (Iso.inv_hom_id_assoc (ρ_ Y) r)
  have hRight : (ρ_ Y).inv ≫ (Y ◁ c) ≫ (σa ⊗ₘ 𝟙 H) ≫ j = σa ≫ s := by
    calc
      _ = ((ρ_ Y).inv ≫ (Y ◁ c) ≫ (σa ⊗ₘ 𝟙 H)) ≫ j := by
        simp only [Category.assoc]
      _ = (σa ≫ (ρ_ Z).inv ≫ Z ◁ c) ≫ j := congrArg (fun z => z ≫ j) hNatural
      _ = σa ≫ (ρ_ Z).inv ≫ ((Z ◁ c) ≫ j) := by simp only [Category.assoc]
      _ = σa ≫ (ρ_ Z).inv ≫ ((ρ_ Z).hom ≫ s) :=
        congrArg (fun z => σa ≫ (ρ_ Z).inv ≫ z) hPointJ
      _ = _ := congrArg (fun z => σa ≫ z) (Iso.inv_hom_id_assoc (ρ_ Z) s)
  apply (cancel_epi (ρ_ Y).inv).1
  calc
    _ = ((ρ_ Y).inv ≫ (Y ◁ c) ≫ e) ≫ σb := by simp only [c, Category.assoc]
    _ = r ≫ σb := congrArg (fun z => z ≫ σb) hLeft
    _ = σa ≫ s := hSphere
    _ = _ := hRight.symm

/-- The original native sphere structure is a genuine full enriched transformation. -/
def sphereTransformation
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :
    GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}))
      (((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.externalTensor
        orthogonalSphereFunctor.{u, v})
      (OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
        PointedCGWH.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor) :=
  GradedNatTrans.unitOfComponents (fun a => sphereAction.{u, v} F a.1 a.2)
    (sphereAction_full_naturality.{u, v} F)

/-- Every actual component is the original full native right sphere action. -/
theorem sphereTransformation_component
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (a : OrthogonalIndex × OrthogonalIndex) :
    (eHomEquiv PointedCGWH.{u, v}).symm ((sphereTransformation.{u, v} F).app a) =
      sphereAction.{u, v} F a.1 a.2 :=
  GradedNatTrans.unitOfComponents_component _ _ a

end CategoryTheory.Spectra.OrthogonalSourceRightModule
