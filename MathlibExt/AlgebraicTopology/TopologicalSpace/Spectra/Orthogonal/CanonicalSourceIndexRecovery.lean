/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceOperatorFunctor
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorCoefficientRecovery

/-!
# Recovery of the entire original orthogonal index action

The actual original index inclusion inserts the original sphere unit in its
unit coefficient. The original external source unit equation then recovers
every index arrow. The unit separator extends this calculation to the whole
continuous index Hom, retaining every source value.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v uI vI

open CategoryTheory MonoidalCategory BraidedCategory
open CategoryTheory.Spectra CategoryTheory.Enriched.SphereOperator
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceIndexRecovery

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

private theorem unitIndex_label {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
    [BraidedCategory I] (n : I) :
    (β_ (𝟙_ I) n).inv ≫ (λ_ n).hom = (ρ_ n).hom := by
  rw [Iso.inv_comp_eq, braiding_tensorUnit_left]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem sourceFunctor_eq_of_data
    (F G : EnrichedFunctor PointedCGWH.{u, v} OrthogonalIndex PointedCGWH.{u, v})
    (ho : F.obj = G.obj) (hm : HEq F.map G.map) : F = G := by
  cases F
  cases G
  cases ho
  cases hm
  rfl

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

/-- Every original index arrow acts by its original whole source map. -/
theorem reverseOperatorAction_index_point (n k : OrthogonalIndex) (f : n ⟶ k) :
    (X.toEnrichedFunctor.obj n ◁
      (eHomEquiv PointedCGWH.{u, v} f ≫
        indexHom OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} n k)) ≫
      reverseOperatorAction.{u, v} X t n k =
    (ρ_ (X.toEnrichedFunctor.obj n)).hom ≫ X.toEnrichedFunctor.toOrdinaryFunctor.map f := by
  let M := X.toEnrichedFunctor.obj n
  let Y := X.toEnrichedFunctor.obj k
  let A := PointedCGWH.orthogonalSphere.{u, v} 0
  let P := OrthogonalOperatorIndex.hom.{u, v} n k
  let epsilon : 𝟙_ PointedCGWH.{u, v} ⟶ A := orthogonalSphereMonoidalData.{u, v}.epsilon
  let label : 0 + n ⟶ k := (λ_ n).hom ≫ f
  let i : A ⟶ P := coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} n k 0 label
  let action : M ⊗ P ⟶ Y := reverseOperatorAction.{u, v} X t n k
  let s : M ⊗ A ⟶ X.toEnrichedFunctor.obj (n + 0) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n 0
  let c : M ⊗ A ⟶ X.toEnrichedFunctor.obj (0 + n) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n 0
  let b : X.toEnrichedFunctor.obj (n + 0) ⟶ X.toEnrichedFunctor.obj (0 + n) :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ (0 : OrthogonalIndex) n).inv
  let r : X.toEnrichedFunctor.obj (n + 0) ⟶ M :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom
  let q : M ⟶ Y := X.toEnrichedFunctor.toOrdinaryFunctor.map f
  let q0 : X.toEnrichedFunctor.obj (0 + n) ⟶ Y :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map label
  have hIndex : eHomEquiv PointedCGWH.{u, v} f ≫
      indexHom OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} n k = epsilon ≫ i :=
    indexHom_point_eq_coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} n k f
  have hAction : (M ◁ i) ≫ action = c ≫ q0 :=
    CanonicalSourceCoefficientAction.coefficientHom_action X t n k 0 label
  have hc : c = s ≫ b := rfl
  have hLabel : (β_ (0 : OrthogonalIndex) n).inv ≫ label = (ρ_ n).hom ≫ f :=
    (Category.assoc (β_ (0 : OrthogonalIndex) n).inv (λ_ n).hom f).symm.trans
      (congrArg (fun z => z ≫ f) (unitIndex_label n))
  have hMaps : b ≫ q0 = r ≫ q :=
    (X.toEnrichedFunctor.toOrdinaryFunctor.map_comp
      (β_ (0 : OrthogonalIndex) n).inv label).symm.trans
      ((congrArg X.toEnrichedFunctor.toOrdinaryFunctor.map hLabel).trans
        (X.toEnrichedFunctor.toOrdinaryFunctor.map_comp (ρ_ n).hom f))
  have hUnit : (M ◁ epsilon) ≫ s ≫ r = (ρ_ M).hom := hu n
  change (M ◁ (eHomEquiv PointedCGWH.{u, v} f ≫
    indexHom OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} n k)) ≫ action =
    (ρ_ M).hom ≫ q
  calc
    _ = (M ◁ (epsilon ≫ i)) ≫ action := congrArg (fun z => (M ◁ z) ≫ action) hIndex
    _ = (M ◁ epsilon) ≫ (M ◁ i) ≫ action := by rw [whiskerLeft_comp, Category.assoc]
    _ = (M ◁ epsilon) ≫ c ≫ q0 := congrArg (fun z => (M ◁ epsilon) ≫ z) hAction
    _ = (M ◁ epsilon) ≫ s ≫ b ≫ q0 := by rw [hc, Category.assoc]
    _ = (M ◁ epsilon) ≫ s ≫ r ≫ q := by
      simpa only [Category.assoc] using congrArg (fun z => (M ◁ epsilon) ≫ s ≫ z) hMaps
    _ = _ := by simpa only [Category.assoc] using congrArg (fun z => z ≫ q) hUnit

/-- The entire original continuous index Hom map is recovered by the reverse coend field. -/
theorem reverseOperatorMapField_index (n k : OrthogonalIndex) :
    indexHom OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} n k ≫
        reverseOperatorMapField.{u, v} X t n k = X.toEnrichedFunctor.map n k := by
  let M := X.toEnrichedFunctor.obj n
  let Y := X.toEnrichedFunctor.obj k
  let H := OrthogonalIndex.hom.{u, v} n k
  let P := OrthogonalOperatorIndex.hom.{u, v} n k
  let i : H ⟶ P := indexHom OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} n k
  let field : P ⟶ (ihom M).obj Y := reverseOperatorMapField.{u, v} X t n k
  let original : H ⟶ (ihom M).obj Y := X.toEnrichedFunctor.map n k
  let action : M ⊗ P ⟶ Y := reverseOperatorAction.{u, v} X t n k
  change i ≫ field = original
  apply PointedCGWH.isSeparator_tensorUnit.def
  intro p
  let f : n ⟶ k := (eHomEquiv PointedCGWH.{u, v}).symm p
  have hp : eHomEquiv PointedCGWH.{u, v} f = p := Equiv.apply_symm_apply _ p
  let q : M ⟶ Y := X.toEnrichedFunctor.toOrdinaryFunctor.map f
  have hField : MonoidalClosed.uncurry field = action :=
    Reconstruction.uncurry_enrichedMapField OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t PointedCGWH.isSeparator_tensorUnit n k
  have hLeft : MonoidalClosed.uncurry (p ≫ i ≫ field) = (M ◁ (p ≫ i)) ≫ action :=
    (congrArg MonoidalClosed.uncurry (Category.assoc p i field).symm).trans
      ((MonoidalClosed.uncurry_natural_left (p ≫ i) field).trans
        (congrArg (fun z => (M ◁ (p ≫ i)) ≫ z) hField))
  have hInput : M ◁ (eHomEquiv PointedCGWH.{u, v} f ≫ i) = M ◁ (p ≫ i) :=
    congrArg (fun z : 𝟙_ PointedCGWH.{u, v} ⟶ H => M ◁ (z ≫ i)) hp
  have hRecovery : (M ◁ (p ≫ i)) ≫ action = (ρ_ M).hom ≫ q :=
    (congrArg (fun z => z ≫ action) hInput).symm.trans
      (reverseOperatorAction_index_point X t hu n k f)
  have hOriginal : (M ◁ p) ≫ MonoidalClosed.uncurry original = (ρ_ M).hom ≫ q := by
    have h := EnrichedFunctor.uncurry_map_point X.toEnrichedFunctor f
    have ht : 𝟙 M ⊗ₘ eHomEquiv PointedCGWH.{u, v} f = M ◁ p :=
      (congrArg (fun z : 𝟙_ PointedCGWH.{u, v} ⟶ H => 𝟙 M ⊗ₘ z) hp).trans (id_tensorHom M p)
    exact (congrArg (fun z => z ≫ MonoidalClosed.uncurry original) ht).symm.trans h
  have hRight : MonoidalClosed.uncurry (p ≫ original) = (ρ_ M).hom ≫ q :=
    (MonoidalClosed.uncurry_natural_left p original).trans hOriginal
  apply MonoidalClosed.uncurry_injective
  exact hLeft.trans (hRecovery.trans hRight.symm)

variable (ha : ∀ n a b : OrthogonalIndex,
  (α_ (X.toEnrichedFunctor.obj n) (PointedCGWH.orthogonalSphere.{u, v} a)
    (PointedCGWH.orthogonalSphere.{u, v} b)).inv ≫
    (Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a ▷
        PointedCGWH.orthogonalSphere.{u, v} b) ≫
      Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t (n + a) b =
  (X.toEnrichedFunctor.obj n ◁ orthogonalSphereMonoidalData.{u, v}.mu a b) ≫
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n (a + b) ≫
        X.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n a b).inv)

/-- Restriction recovers the entire original source index map function. -/
theorem reverseFunctor_restriction_fullMap :
    ((restrictionFunctor.{u, v}).obj
      (CanonicalSourceOperatorFunctor.reverseFunctor X t hu ha)).toEnrichedFunctor.map =
        X.toEnrichedFunctor.map := by
  funext n k
  exact reverseOperatorMapField_index X t hu n k

/-- The whole original enriched I-space is recovered by native reconstruction and restriction. -/
theorem reverseFunctor_restriction :
    (restrictionFunctor.{u, v}).obj
      (CanonicalSourceOperatorFunctor.reverseFunctor X t hu ha) = X := by
  have h : ((restrictionFunctor.{u, v}).obj
      (CanonicalSourceOperatorFunctor.reverseFunctor X t hu ha)).toEnrichedFunctor =
        X.toEnrichedFunctor :=
    sourceFunctor_eq_of_data _ _ rfl (heq_of_eq (reverseFunctor_restriction_fullMap X t hu ha))
  exact congrArg (fun G : EnrichedFunctor PointedCGWH.{u, v} OrthogonalIndex
    PointedCGWH.{u, v} => (⟨G⟩ : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)) h

/-- The reconstructed functor retains the whole original external sphere structure map. -/
theorem reverseFunctor_sphereAction (n a : OrthogonalIndex) :
    sphereAction.{u, v} (CanonicalSourceOperatorFunctor.reverseFunctor X t hu ha) n a =
      Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a := by
  let F : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
    CanonicalSourceOperatorFunctor.reverseFunctor X t hu ha
  let M := X.toEnrichedFunctor.obj n
  let A := PointedCGWH.orthogonalSphere.{u, v} a
  let P := OrthogonalOperatorIndex.hom.{u, v} n (n + a)
  let field : P ⟶ (ihom M).obj (X.toEnrichedFunctor.obj (n + a)) :=
    F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a))
  let nu : A ⟶ P := OrthogonalOperatorIndex.nu.{u, v} n a
  let original : A ⟶ P := rightSphereHom OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} n a
  have hAction : sphereAction.{u, v} F n a = (M ◁ nu) ≫ MonoidalClosed.uncurry field :=
    sphereAction_original_nu.{u, v} F n a
  have hNu : nu = original := (rightSphereHom_eq_original_nu.{u, v} n a).symm
  have hField : MonoidalClosed.uncurry field = reverseOperatorAction.{u, v} X t n (n + a) :=
    CanonicalSourceOperatorFunctor.reverseFunctor_action X t hu ha n (n + a)
  calc
    _ = (M ◁ nu) ≫ MonoidalClosed.uncurry field := hAction
    _ = (M ◁ original) ≫ MonoidalClosed.uncurry field :=
      congrArg (fun z => (M ◁ z) ≫ MonoidalClosed.uncurry field) hNu
    _ = (M ◁ original) ≫ reverseOperatorAction.{u, v} X t n (n + a) :=
      congrArg (fun z => (M ◁ original) ≫ z) hField
    _ = _ := CanonicalSourceCoefficientAction.rightSphereHom_action X t n a

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceIndexRecovery
