/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceActionCompatibility
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SourceSphereModuleLaws
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorRightSphereLaws

/-!
# Original orthogonal coefficient maps before reverse composition

The genuine source sphere transformation gives coefficient naturality for
both original input arrows. The existing original block-braid identity gives
the coefficient-first label of source associativity. All maps retain their
original orientation and order.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v uI vI

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.Spectra CategoryTheory.Enriched.SphereOperator
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceCoefficientCompatibility

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

variable
  (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
  (t : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}))
    (X.toEnrichedFunctor.externalTensor orthogonalSphereFunctor.{u, v})
    (OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
      PointedCGWH.{u, v} X.toEnrichedFunctor))

/-- Both whole original input arrows preserve the coefficient with its actual block inverse. -/
theorem coefficient_twoInputs {n m a b : OrthogonalIndex} (f : n ⟶ m) (g : a ⟶ b) :
    (X.toEnrichedFunctor.toOrdinaryFunctor.map f ⊗ₘ
        orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor.map g) ≫
      Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t m b =
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a ≫
      X.toEnrichedFunctor.toOrdinaryFunctor.map (g ⊗ₘ f) := by
  let A := PointedCGWH.orthogonalSphere.{u, v} a
  let B := PointedCGWH.orthogonalSphere.{u, v} b
  let sx : X.toEnrichedFunctor.obj n ⊗ A ⟶ X.toEnrichedFunctor.obj (n + a) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a
  let sy : X.toEnrichedFunctor.obj m ⊗ B ⟶ X.toEnrichedFunctor.obj (m + b) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t m b
  let bx : X.toEnrichedFunctor.obj (n + a) ⟶ X.toEnrichedFunctor.obj (a + n) :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ a n).inv
  let by' : X.toEnrichedFunctor.obj (m + b) ⟶ X.toEnrichedFunctor.obj (b + m) :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ b m).inv
  let cx : X.toEnrichedFunctor.obj n ⊗ A ⟶ X.toEnrichedFunctor.obj (a + n) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a
  let cy : X.toEnrichedFunctor.obj m ⊗ B ⟶ X.toEnrichedFunctor.obj (b + m) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t m b
  let r := X.toEnrichedFunctor.toOrdinaryFunctor.map f ⊗ₘ
    orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor.map g
  let z := X.toEnrichedFunctor.toOrdinaryFunctor.map (f ⊗ₘ g)
  let w := X.toEnrichedFunctor.toOrdinaryFunctor.map (g ⊗ₘ f)
  have hx : cx = sx ≫ bx := rfl
  have hy : cy = sy ≫ by' := rfl
  have hs : r ≫ sy = sx ≫ z := Reconstruction.sphereComponent_twoInputs
    OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
    X.toEnrichedFunctor t n m a b f g
  have hi : (f ⊗ₘ g) ≫ (β_ b m).inv = (β_ a n).inv ≫ (g ⊗ₘ f) :=
    BraidedCategory.braiding_inv_naturality f g
  have hm : z ≫ by' = bx ≫ w :=
    (X.toEnrichedFunctor.toOrdinaryFunctor.map_comp (f ⊗ₘ g) (β_ b m).inv).symm.trans
      ((congrArg X.toEnrichedFunctor.toOrdinaryFunctor.map hi).trans
        (X.toEnrichedFunctor.toOrdinaryFunctor.map_comp (β_ a n).inv (g ⊗ₘ f)))
  change r ≫ cy = cx ≫ w
  calc
    _ = r ≫ (sy ≫ by') := congrArg (fun q => r ≫ q) hy
    _ = (r ≫ sy) ≫ by' := (Category.assoc _ _ _).symm
    _ = (sx ≫ z) ≫ by' := congrArg (fun q => q ≫ by') hs
    _ = sx ≫ (z ≫ by') := Category.assoc _ _ _
    _ = sx ≫ (bx ≫ w) := congrArg (fun q => sx ≫ q) hm
    _ = (sx ≫ bx) ≫ w := (Category.assoc _ _ _).symm
    _ = cx ≫ w := congrArg (fun q => q ≫ w) hx.symm

/-- The coefficient-first source label follows from the same original full block-braid proof. -/
theorem coefficient_comp_label {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
    [SymmetricCategory I] (n a b : I) :
    (n ◁ (β_ b a).hom) ≫ (α_ n a b).inv ≫ ((β_ a n).inv ▷ b) ≫
        (β_ b (a ⊗ n)).inv = (β_ (b ⊗ a) n).inv ≫ (α_ b a n).hom := by
  rw [← rightSphere_comp_label n a b]
  simp only [Category.assoc]
  rw [braiding_inv_naturality_right_assoc]
  rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry, id_whiskerRight, Category.id_comp]
  rw [braiding_naturality_right_assoc, hom_inv_whiskerRight_assoc]
  simp only [Iso.hom_inv_id, Category.comp_id]

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

include ha

/-- The original external associative source law gives the exact late-first coefficient law. -/
theorem coefficient_assoc (n a b : OrthogonalIndex) :
    (α_ (X.toEnrichedFunctor.obj n) (PointedCGWH.orthogonalSphere.{u, v} a)
        (PointedCGWH.orthogonalSphere.{u, v} b)).inv ≫
      (Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a ▷
          PointedCGWH.orthogonalSphere.{u, v} b) ≫
        Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t (a + n) b =
      (X.toEnrichedFunctor.obj n ◁
        ((β_ (PointedCGWH.orthogonalSphere.{u, v} a)
          (PointedCGWH.orthogonalSphere.{u, v} b)).hom ≫
            orthogonalSphereMonoidalData.{u, v}.mu b a)) ≫
        Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n (b + a) ≫
            X.toEnrichedFunctor.toOrdinaryFunctor.map (α_ b a n).hom := by
  let M := X.toEnrichedFunctor.obj n
  let A := PointedCGWH.orthogonalSphere.{u, v} a
  let B := PointedCGWH.orthogonalSphere.{u, v} b
  let sA : M ⊗ A ⟶ X.toEnrichedFunctor.obj (n + a) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a
  let cA : M ⊗ A ⟶ X.toEnrichedFunctor.obj (a + n) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a
  let ba : X.toEnrichedFunctor.obj (n + a) ⟶ X.toEnrichedFunctor.obj (a + n) :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ a n).inv
  let sB : X.toEnrichedFunctor.obj (n + a) ⊗ B ⟶ X.toEnrichedFunctor.obj ((n + a) + b) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t (n + a) b
  let sBA : X.toEnrichedFunctor.obj (a + n) ⊗ B ⟶ X.toEnrichedFunctor.obj ((a + n) + b) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t (a + n) b
  let cBA : X.toEnrichedFunctor.obj (a + n) ⊗ B ⟶ X.toEnrichedFunctor.obj (b + (a + n)) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t (a + n) b
  let bb : X.toEnrichedFunctor.obj ((a + n) + b) ⟶ X.toEnrichedFunctor.obj (b + (a + n)) :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ b (a + n)).inv
  let fi : X.toEnrichedFunctor.obj ((n + a) + b) ⟶ X.toEnrichedFunctor.obj ((a + n) + b) :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map ((β_ a n).inv ▷ b)
  let sAB : M ⊗ PointedCGWH.orthogonalSphere.{u, v} (a + b) ⟶
      X.toEnrichedFunctor.obj (n + (a + b)) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n (a + b)
  let sBAall : M ⊗ PointedCGWH.orthogonalSphere.{u, v} (b + a) ⟶
      X.toEnrichedFunctor.obj (n + (b + a)) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n (b + a)
  let cBAall : M ⊗ PointedCGWH.orthogonalSphere.{u, v} (b + a) ⟶
      X.toEnrichedFunctor.obj ((b + a) + n) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n (b + a)
  let bba : X.toEnrichedFunctor.obj (n + (b + a)) ⟶ X.toEnrichedFunctor.obj ((b + a) + n) :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ (b + a) n).inv
  let ai : X.toEnrichedFunctor.obj (n + (a + b)) ⟶ X.toEnrichedFunctor.obj ((n + a) + b) :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n a b).inv
  let bi : X.toEnrichedFunctor.obj (n + (b + a)) ⟶ X.toEnrichedFunctor.obj (n + (a + b)) :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (n ◁ (β_ b a).hom)
  let ao : X.toEnrichedFunctor.obj ((b + a) + n) ⟶ X.toEnrichedFunctor.obj (b + (a + n)) :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (α_ b a n).hom
  let muAB : A ⊗ B ⟶ PointedCGWH.orthogonalSphere.{u, v} (a + b) :=
    orthogonalSphereMonoidalData.{u, v}.mu a b
  let muBA : B ⊗ A ⟶ PointedCGWH.orthogonalSphere.{u, v} (b + a) :=
    orthogonalSphereMonoidalData.{u, v}.mu b a
  let sb : PointedCGWH.orthogonalSphere.{u, v} (b + a) ⟶
      PointedCGWH.orthogonalSphere.{u, v} (a + b) :=
    orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor.map (β_ b a).hom
  let m : A ⊗ B ⟶ PointedCGWH.orthogonalSphere.{u, v} (b + a) := (β_ A B).hom ≫ muBA
  have hca : cA = sA ≫ ba := rfl
  have hcb : cBA = sBA ≫ bb := rfl
  have hcab : cBAall = sBAall ≫ bba := rfl
  have hInput : (ba ▷ B) ≫ sBA = sB ≫ fi := by
    have h := Reconstruction.sphereComponent_twoInputs OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t (n + a) (a + n) b b
      (β_ a n).inv (𝟙 b)
    have hid : orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor.map (𝟙 b) = 𝟙 B :=
      orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor.map_id b
    have ht : ba ⊗ₘ orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor.map (𝟙 b) = ba ▷ B :=
      (congrArg (fun z : B ⟶ B => ba ⊗ₘ z) hid).trans (tensorHom_id ba B)
    exact (congrArg (fun z => z ≫ sBA) ht).symm.trans h
  have hAssoc : (α_ M A B).inv ≫ (sA ▷ B) ≫ sB = (M ◁ muAB) ≫ sAB ≫ ai := ha n a b
  have hMu : muAB = m ≫ sb := by
    have hb : muBA ≫ sb = (β_ B A).hom ≫ muAB :=
      orthogonalSphereBraidedData.{u, v}.braided b a
    calc
      _ = (β_ A B).hom ≫ (β_ B A).hom ≫ muAB := by
        simp only [SymmetricCategory.symmetry_assoc]
      _ = (β_ A B).hom ≫ muBA ≫ sb := congrArg (fun q => (β_ A B).hom ≫ q) hb.symm
      _ = m ≫ sb := (Category.assoc _ _ _).symm
  have hCoeff : (M ◁ sb) ≫ sAB = sBAall ≫ bi := by
    have h := Reconstruction.sphereComponent_twoInputs OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n n (b + a) (a + b)
      (𝟙 n) (β_ b a).hom
    have hid : X.toEnrichedFunctor.toOrdinaryFunctor.map (𝟙 n) = 𝟙 M :=
      X.toEnrichedFunctor.toOrdinaryFunctor.map_id n
    have ht : X.toEnrichedFunctor.toOrdinaryFunctor.map (𝟙 n) ⊗ₘ sb = M ◁ sb :=
      (congrArg (fun z : M ⟶ M => z ⊗ₘ sb) hid).trans (id_tensorHom M sb)
    exact (congrArg (fun z => z ≫ sAB) ht).symm.trans h
  have hIndex : bi ≫ ai ≫ fi ≫ bb = bba ≫ ao := by
    have h := congrArg X.toEnrichedFunctor.toOrdinaryFunctor.map (coefficient_comp_label n a b)
    simp only [Functor.map_comp] at h
    change bi ≫ ai ≫ fi ≫ bb = bba ≫ ao at h
    exact h
  change (α_ M A B).inv ≫ (cA ▷ B) ≫ cBA = (M ◁ m) ≫ cBAall ≫ ao
  calc
    _ = (α_ M A B).inv ≫ (sA ▷ B) ≫ (ba ▷ B) ≫ sBA ≫ bb := by
      rw [hca, hcb, comp_whiskerRight]
      simp only [Category.assoc]
    _ = (α_ M A B).inv ≫ (sA ▷ B) ≫ sB ≫ fi ≫ bb := by
      simpa only [Category.assoc] using
        congrArg (fun q => (α_ M A B).inv ≫ (sA ▷ B) ≫ q ≫ bb) hInput
    _ = (M ◁ muAB) ≫ sAB ≫ ai ≫ fi ≫ bb := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ fi ≫ bb) hAssoc
    _ = (M ◁ m) ≫ (M ◁ sb) ≫ sAB ≫ ai ≫ fi ≫ bb := by
      rw [hMu, whiskerLeft_comp]
      simp only [Category.assoc]
    _ = (M ◁ m) ≫ sBAall ≫ bi ≫ ai ≫ fi ≫ bb := by
      simpa only [Category.assoc] using
        congrArg (fun q => (M ◁ m) ≫ q ≫ ai ≫ fi ≫ bb) hCoeff
    _ = (M ◁ m) ≫ sBAall ≫ bba ≫ ao := by
      simpa only [Category.assoc] using congrArg (fun q => (M ◁ m) ≫ sBAall ≫ q) hIndex
    _ = (M ◁ m) ≫ cBAall ≫ ao := by
      rw [hcab]
      simp only [Category.assoc]

omit ha

/-- The original canonical restriction has the same entire external associative source law. -/
theorem original_source_assoc
    (F : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
    (n a b : OrthogonalIndex) :
    (α_ (((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.obj n)
        (PointedCGWH.orthogonalSphere.{u, v} a) (PointedCGWH.orthogonalSphere.{u, v} b)).inv ≫
      (Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
        (sphereTransformation.{u, v} F) n a ▷ PointedCGWH.orthogonalSphere.{u, v} b) ≫
      Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
        (sphereTransformation.{u, v} F) (n + a) b =
    (((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.obj n ◁
      orthogonalSphereMonoidalData.{u, v}.mu a b) ≫
      Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
        (sphereTransformation.{u, v} F) n (a + b) ≫
      ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.toOrdinaryFunctor.map
        (α_ n a b).inv := by
  let M := F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n)
  let A := PointedCGWH.orthogonalSphere.{u, v} a
  let B := PointedCGWH.orthogonalSphere.{u, v} b
  let sa : M ⊗ A ⟶ F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a)) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
      (sphereTransformation.{u, v} F) n a
  let sb : F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a)) ⊗ B ⟶
      F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} ((n + a) + b)) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
      (sphereTransformation.{u, v} F) (n + a) b
  let sab : M ⊗ PointedCGWH.orthogonalSphere.{u, v} (a + b) ⟶
      F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + (a + b))) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
      (sphereTransformation.{u, v} F) n (a + b)
  have hsa : sa = sphereAction.{u, v} F n a := sphereTransformation_component F (n, a)
  have hsb : sb = sphereAction.{u, v} F (n + a) b :=
    sphereTransformation_component F (n + a, b)
  have hsab : sab = sphereAction.{u, v} F n (a + b) :=
    sphereTransformation_component F (n, a + b)
  change (α_ M A B).inv ≫ (sa ▷ B) ≫ sb =
    (M ◁ orthogonalSphereMonoidalData.{u, v}.mu a b) ≫ sab ≫
      ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.toOrdinaryFunctor.map (α_ n a b).inv
  rw [hsa, hsb, hsab]
  exact sphereAction_assoc.{u, v} F n a b

/-- Original canonical diagrams retain the complete coefficient-first associative law. -/
theorem original_coefficient_assoc
    (F : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
    (n a b : OrthogonalIndex) :
    (α_ (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n))
        (PointedCGWH.orthogonalSphere.{u, v} a) (PointedCGWH.orthogonalSphere.{u, v} b)).inv ≫
      (Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
        (sphereTransformation.{u, v} F) n a ▷ PointedCGWH.orthogonalSphere.{u, v} b) ≫
      Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
        (sphereTransformation.{u, v} F) (a + n) b =
    (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ◁
      ((β_ (PointedCGWH.orthogonalSphere.{u, v} a)
        (PointedCGWH.orthogonalSphere.{u, v} b)).hom ≫
          orthogonalSphereMonoidalData.{u, v}.mu b a)) ≫
      Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
        (sphereTransformation.{u, v} F) n (b + a) ≫
      ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.toOrdinaryFunctor.map
        (α_ b a n).hom :=
  coefficient_assoc ((restrictionFunctor.{u, v}).obj F) (sphereTransformation.{u, v} F)
    (original_source_assoc F) n a b

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceCoefficientCompatibility
