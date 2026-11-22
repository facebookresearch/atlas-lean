/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceActionCompatibility
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SourceSphereModuleLaws

/-!
# Original orthogonal source units in the reverse operator fields

The original external right-unit equation, epsilon and block inverse compute
the actual reverse action on the original unit coend generator. Currying gives
the enriched-functor unit law. Composition and the actual source module carrier
remain separate parts of the reverse construction.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Spectra CategoryTheory.Enriched.SphereOperator
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceUnitCompatibility

/-- The original orthogonal index category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original block-sum monoidal structure on orthogonal indices. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original pointed CGWH enriched ordinary structure on orthogonal indices. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block symmetry on orthogonal indices. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}

attribute [local instance] Enriched.prodCategory

private theorem unitPair_cross_prefix (M A H : PointedCGWH.{u, v})
    (e : 𝟙_ PointedCGWH.{u, v} ⟶ A) (p : 𝟙_ PointedCGWH.{u, v} ⟶ H) :
    (M ◁ ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ (p ⊗ₘ e))) ≫
        (M ◁ (β_ H A).hom) ≫ (α_ M A H).inv =
      (M ◁ e) ≫ (ρ_ (M ⊗ A)).inv ≫ (M ⊗ A) ◁ p := by
  have hc : ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ (p ⊗ₘ e)) ≫ (β_ H A).hom =
      (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ (e ⊗ₘ p) := by
    rw [Category.assoc, BraidedCategory.braiding_naturality,
      braiding_tensorUnit_left]
    simp only [Category.assoc, unitors_equal, unitors_inv_equal, Iso.inv_hom_id_assoc]
  have hp : (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ (e ⊗ₘ p) =
      e ≫ (ρ_ A).inv ≫ A ◁ p := by
    simpa only [unitors_inv_equal] using rightUnitor_inv_comp_tensorHom e p
  have ha : (M ◁ ((ρ_ A).inv ≫ A ◁ p)) ≫ (α_ M A H).inv =
      (ρ_ (M ⊗ A)).inv ≫ (M ⊗ A) ◁ p := by
    rw [whiskerLeft_comp, Category.assoc, associator_inv_naturality_right,
      whiskerLeft_rightUnitor_inv]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  calc
    _ = (M ◁ (((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ (p ⊗ₘ e)) ≫ (β_ H A).hom)) ≫
        (α_ M A H).inv := by simp only [whiskerLeft_comp, Category.assoc]
    _ = (M ◁ ((λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ (e ⊗ₘ p))) ≫
        (α_ M A H).inv := congrArg (fun z => (M ◁ z) ≫ (α_ M A H).inv) hc
    _ = (M ◁ e) ≫ (M ◁ ((ρ_ A).inv ≫ A ◁ p)) ≫ (α_ M A H).inv := by
      rw [hp]
      simp only [whiskerLeft_comp, Category.assoc]
    _ = _ := congrArg (fun z => (M ◁ e) ≫ z) ha

variable
  (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
  (t : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}))
    (X.toEnrichedFunctor.externalTensor orthogonalSphereFunctor.{u, v})
    (OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
      PointedCGWH.{u, v} X.toEnrichedFunctor))
  (hu : ∀ n : OrthogonalIndex,
    (X.toEnrichedFunctor.obj n ◁ orthogonalSphereMonoidalData.{u, v}.epsilon) ≫
        Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n 0 ≫
        X.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom =
      (ρ_ (X.toEnrichedFunctor.obj n)).hom)

include hu

/-- The original source right-unit law computes the whole action on the actual operator unit. -/
theorem reverseOperatorAction_unit (n : OrthogonalIndex) :
    (X.toEnrichedFunctor.obj n ◁
        eId PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n)) ≫
        reverseOperatorAction.{u, v} X t n n = (ρ_ (X.toEnrichedFunctor.obj n)).hom := by
  let M := X.toEnrichedFunctor.obj n
  let a : OrthogonalIndex := 0
  let A := PointedCGWH.orthogonalSphere.{u, v} a
  let H := OrthogonalIndex.hom.{u, v} (a + n) n
  let Z := X.toEnrichedFunctor.obj (a + n)
  let e : 𝟙_ PointedCGWH.{u, v} ⟶ A := orthogonalSphereMonoidalData.{u, v}.epsilon
  let p : 𝟙_ PointedCGWH.{u, v} ⟶ H := eHomEquiv PointedCGWH.{u, v} (λ_ n).hom
  let i : H ⊗ A ⟶ OrthogonalOperatorIndex.hom.{u, v} n n :=
    OrthogonalOperatorIndex.ι.{u, v} n n a
  let c : M ⊗ A ⟶ Z := Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a
  let s : M ⊗ A ⟶ X.toEnrichedFunctor.obj (n + a) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a
  let b : X.toEnrichedFunctor.obj (n + a) ⟶ Z :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ a n).inv
  let l : Z ⟶ M := X.toEnrichedFunctor.toOrdinaryFunctor.map (λ_ n).hom
  let r : Z ⊗ H ⟶ M := MonoidalClosed.uncurry (X.toEnrichedFunctor.map (a + n) n)
  let action : M ⊗ OrthogonalOperatorIndex.hom.{u, v} n n ⟶ M :=
    reverseOperatorAction.{u, v} X t n n
  let pre := (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ (p ⊗ₘ e)
  have hId : eId PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n) = pre ≫ i := by
    rw [OrthogonalOperatorIndex.id_eq]
    rfl
  have hGen : (M ◁ i) ≫ action =
      (M ◁ (β_ H A).hom) ≫ (α_ M A H).inv ≫ (c ▷ H) ≫ r :=
    reverseOperatorAction_generator.{u, v} X t n n a
  have heval : (ρ_ Z).inv ≫ (Z ◁ p) ≫ r = l := by
    have hpoint : (Z ◁ p) ≫ r = (ρ_ Z).hom ≫ l := by
      have h := EnrichedFunctor.uncurry_map_point X.toEnrichedFunctor (λ_ n).hom
      change (𝟙 Z ⊗ₘ p) ≫ r = (ρ_ Z).hom ≫ l at h
      simpa only [id_tensorHom] using h
    exact (congrArg (fun z => (ρ_ Z).inv ≫ z) hpoint).trans (Iso.inv_hom_id_assoc (ρ_ Z) l)
  have htransfer : (ρ_ (M ⊗ A)).inv ≫ ((M ⊗ A) ◁ p) ≫ (c ▷ H) =
      c ≫ (ρ_ Z).inv ≫ Z ◁ p := by
    simpa only [tensorHom_def', Category.assoc] using rightUnitor_inv_comp_tensorHom c p
  have hc : c = s ≫ b := rfl
  have hindex : (β_ a n).inv ≫ (λ_ n).hom = (ρ_ n).hom := by
    let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    let _ : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
    change (β_ (𝟙_ OrthogonalIndex) n).inv ≫ (λ_ n).hom = (ρ_ n).hom
    rw [braiding_inv_tensorUnit_left]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hmaps : b ≫ l = X.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom :=
    (X.toEnrichedFunctor.toOrdinaryFunctor.map_comp (β_ a n).inv (λ_ n).hom).symm.trans
      (congrArg X.toEnrichedFunctor.toOrdinaryFunctor.map hindex)
  have hp := unitPair_cross_prefix M A H e p
  change (M ◁ eId PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n)) ≫ action =
    (ρ_ M).hom
  calc
    _ = (M ◁ (pre ≫ i)) ≫ action := congrArg (fun z => (M ◁ z) ≫ action) hId
    _ = (M ◁ pre) ≫ ((M ◁ i) ≫ action) := by simp only [whiskerLeft_comp, Category.assoc]
    _ = (M ◁ pre) ≫ (M ◁ (β_ H A).hom) ≫ (α_ M A H).inv ≫ (c ▷ H) ≫ r :=
      congrArg (fun z => (M ◁ pre) ≫ z) hGen
    _ = ((M ◁ e) ≫ (ρ_ (M ⊗ A)).inv ≫ (M ⊗ A) ◁ p) ≫ (c ▷ H) ≫ r := by
      simpa only [pre, Category.assoc] using congrArg (fun z => z ≫ (c ▷ H) ≫ r) hp
    _ = (M ◁ e) ≫ c ≫ (ρ_ Z).inv ≫ (Z ◁ p) ≫ r := by
      simpa only [Category.assoc] using congrArg (fun z => (M ◁ e) ≫ z ≫ r) htransfer
    _ = (M ◁ e) ≫ c ≫ l := by
      simpa only [Category.assoc] using congrArg (fun z => (M ◁ e) ≫ c ≫ z) heval
    _ = (M ◁ e) ≫ s ≫ (b ≫ l) := by rw [hc, Category.assoc]
    _ = (M ◁ e) ≫ s ≫ X.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom :=
      congrArg (fun z => (M ◁ e) ≫ s ≫ z) hmaps
    _ = (ρ_ M).hom := hu n

/-- The unchanged curried reverse field preserves the actual original enriched unit point. -/
theorem reverseOperatorMapField_unit (n : OrthogonalIndex) :
    eId PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n) ≫
        reverseOperatorMapField.{u, v} X t n n =
      eId PointedCGWH.{u, v} (X.toEnrichedFunctor.obj n) := by
  rw [MonoidalClosed.enrichedCategorySelf_id, MonoidalClosed.id_eq]
  change eId PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n) ≫
      MonoidalClosed.curry (reverseOperatorAction.{u, v} X t n n) =
    MonoidalClosed.curry (ρ_ (X.toEnrichedFunctor.obj n)).hom
  rw [← MonoidalClosed.curry_natural_left]
  exact congrArg MonoidalClosed.curry (reverseOperatorAction_unit X t hu n)

omit hu

/-- The actual restriction and sphere transformation have the original full source unit. -/
theorem original_source_unit
    (F : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
    (n : OrthogonalIndex) :
    (((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.obj n ◁
        orthogonalSphereMonoidalData.{u, v}.epsilon) ≫
      Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
        (sphereTransformation.{u, v} F) n 0 ≫
      ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom =
    (ρ_ (((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.obj n)).hom := by
  let M := F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n)
  let a : OrthogonalIndex := 0
  let A := PointedCGWH.orthogonalSphere.{u, v} a
  let s : M ⊗ A ⟶ F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a)) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
      (sphereTransformation.{u, v} F) n a
  have hs : s = sphereAction.{u, v} F n a := sphereTransformation_component F (n, a)
  change (M ◁ orthogonalSphereMonoidalData.{u, v}.epsilon) ≫ s ≫
    ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom =
      (ρ_ M).hom
  rw [hs]
  exact sphereAction_unit.{u, v} F n

/-- The original canonical source retains its entire actual reverse enriched-unit map. -/
theorem original_reverseOperatorMapField_unit
    (F : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
    (n : OrthogonalIndex) :
    eId PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex.{u, v} n) ≫
        reverseOperatorMapField.{u, v} ((restrictionFunctor.{u, v}).obj F)
          (sphereTransformation.{u, v} F) n n =
      eId PointedCGWH.{u, v} (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n)) :=
  reverseOperatorMapField_unit ((restrictionFunctor.{u, v}).obj F) (sphereTransformation.{u, v} F)
    (original_source_unit F) n

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceUnitCompatibility
