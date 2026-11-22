/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceCoefficientCompatibility

/-!
# Actual coefficient and right sphere actions of the reverse orthogonal fields

Every original source arrow selects its actual coend coefficient generator.
The reverse coend action recovers the entire original source coefficient
action on that generator. The original block arrow then recovers the whole
right sphere transformation, before any carrier packaging.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.Spectra CategoryTheory.Enriched.SphereOperator
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceCoefficientAction

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

private theorem coefficientPoint_prefix (M A H : PointedCGWH.{u, v})
    (p : 𝟙_ PointedCGWH.{u, v} ⟶ H) :
    (M ◁ ((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A))) ≫ (M ◁ (β_ H A).hom) ≫ (α_ M A H).inv =
      (ρ_ (M ⊗ A)).inv ≫ (M ⊗ A) ◁ p := by
  have hc : ((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A)) ≫ (β_ H A).hom =
      (ρ_ A).inv ≫ A ◁ p := by
    rw [tensorHom_id, Category.assoc, braiding_naturality_left,
      braiding_tensorUnit_left]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  calc
    _ = (M ◁ (((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A)) ≫ (β_ H A).hom)) ≫ (α_ M A H).inv := by
      simp only [whiskerLeft_comp, Category.assoc]
    _ = (M ◁ ((ρ_ A).inv ≫ A ◁ p)) ≫ (α_ M A H).inv :=
      congrArg (fun q => (M ◁ q) ≫ (α_ M A H).inv) hc
    _ = _ := by
      rw [whiskerLeft_comp, Category.assoc, associator_inv_naturality_right,
        whiskerLeft_rightUnitor_inv]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]

variable (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
  (t : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}))
    (X.toEnrichedFunctor.externalTensor orthogonalSphereFunctor.{u, v})
    (OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
      PointedCGWH.{u, v} X.toEnrichedFunctor))

/-- Every whole original arrow coefficient acts by the given source coefficient and index map. -/
theorem coefficientHom_action (n k a : OrthogonalIndex) (f : a + n ⟶ k) :
    (X.toEnrichedFunctor.obj n ◁
        coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} n k a f) ≫
      reverseOperatorAction.{u, v} X t n k =
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a ≫
      X.toEnrichedFunctor.toOrdinaryFunctor.map f := by
  let M := X.toEnrichedFunctor.obj n
  let A := PointedCGWH.orthogonalSphere.{u, v} a
  let H := OrthogonalIndex.hom.{u, v} (a + n) k
  let Z := X.toEnrichedFunctor.obj (a + n)
  let T := X.toEnrichedFunctor.obj k
  let p : 𝟙_ PointedCGWH.{u, v} ⟶ H := eHomEquiv PointedCGWH.{u, v} f
  let i : H ⊗ A ⟶ OrthogonalOperatorIndex.hom.{u, v} n k :=
    OrthogonalOperatorIndex.ι.{u, v} n k a
  let c : M ⊗ A ⟶ Z := Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a
  let e : Z ⊗ H ⟶ T := MonoidalClosed.uncurry (X.toEnrichedFunctor.map (a + n) k)
  let q : Z ⟶ T := X.toEnrichedFunctor.toOrdinaryFunctor.map f
  let action : M ⊗ OrthogonalOperatorIndex.hom.{u, v} n k ⟶ T :=
    reverseOperatorAction.{u, v} X t n k
  let pre : A ⟶ H ⊗ A := (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A)
  have hCoeff : coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} n k a f = pre ≫ i := rfl
  have hGen : (M ◁ i) ≫ action =
      (M ◁ (β_ H A).hom) ≫ (α_ M A H).inv ≫ (c ▷ H) ≫ e :=
    reverseOperatorAction_generator.{u, v} X t n k a
  have hEval : (ρ_ Z).inv ≫ (Z ◁ p) ≫ e = q := by
    have hp : (Z ◁ p) ≫ e = (ρ_ Z).hom ≫ q := by
      have h := EnrichedFunctor.uncurry_map_point X.toEnrichedFunctor f
      change (𝟙 Z ⊗ₘ p) ≫ e = (ρ_ Z).hom ≫ q at h
      simpa only [id_tensorHom] using h
    exact (congrArg (fun r => (ρ_ Z).inv ≫ r) hp).trans (Iso.inv_hom_id_assoc (ρ_ Z) q)
  have hTransfer : (ρ_ (M ⊗ A)).inv ≫ ((M ⊗ A) ◁ p) ≫ (c ▷ H) =
      c ≫ (ρ_ Z).inv ≫ Z ◁ p := by
    simpa only [tensorHom_def', Category.assoc] using rightUnitor_inv_comp_tensorHom c p
  have hPrefix := coefficientPoint_prefix M A H p
  change (M ◁ coefficientHom OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} n k a f) ≫ action = c ≫ q
  calc
    _ = (M ◁ (pre ≫ i)) ≫ action := congrArg (fun r => (M ◁ r) ≫ action) hCoeff
    _ = (M ◁ pre) ≫ ((M ◁ i) ≫ action) := by simp only [whiskerLeft_comp, Category.assoc]
    _ = (M ◁ pre) ≫ (M ◁ (β_ H A).hom) ≫ (α_ M A H).inv ≫ (c ▷ H) ≫ e :=
      congrArg (fun r => (M ◁ pre) ≫ r) hGen
    _ = ((ρ_ (M ⊗ A)).inv ≫ (M ⊗ A) ◁ p) ≫ (c ▷ H) ≫ e := by
      simpa only [pre, Category.assoc] using congrArg (fun r => r ≫ (c ▷ H) ≫ e) hPrefix
    _ = c ≫ (ρ_ Z).inv ≫ (Z ◁ p) ≫ e := by
      simpa only [Category.assoc] using congrArg (fun r => r ≫ e) hTransfer
    _ = c ≫ q := by
      simpa only [Category.assoc] using congrArg (fun r => c ≫ r) hEval

/-- The whole source right sphere transformation is recovered on the original block generator. -/
theorem rightSphereHom_action (n a : OrthogonalIndex) :
    (X.toEnrichedFunctor.obj n ◁
        rightSphereHom OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} n a) ≫
      reverseOperatorAction.{u, v} X t n (n + a) =
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a := by
  let A := PointedCGWH.orthogonalSphere.{u, v} a
  let s : X.toEnrichedFunctor.obj n ⊗ A ⟶ X.toEnrichedFunctor.obj (n + a) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a
  let c : X.toEnrichedFunctor.obj n ⊗ A ⟶ X.toEnrichedFunctor.obj (a + n) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a
  let bi : X.toEnrichedFunctor.obj (n + a) ⟶ X.toEnrichedFunctor.obj (a + n) :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ a n).inv
  let bh : X.toEnrichedFunctor.obj (a + n) ⟶ X.toEnrichedFunctor.obj (n + a) :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ a n).hom
  have hc : c = s ≫ bi := rfl
  have hi : bi ≫ bh = 𝟙 (X.toEnrichedFunctor.obj (n + a)) := by
    have h := (X.toEnrichedFunctor.toOrdinaryFunctor.mapIso (β_ a n)).inv_hom_id
    exact h
  have h := coefficientHom_action X t n (n + a) a (β_ a n).hom
  change (X.toEnrichedFunctor.obj n ◁
    rightSphereHom OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} n a) ≫ reverseOperatorAction.{u, v} X t n (n + a) = c ≫ bh at h
  exact h.trans (by rw [hc, Category.assoc, hi, Category.comp_id])

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceCoefficientAction
