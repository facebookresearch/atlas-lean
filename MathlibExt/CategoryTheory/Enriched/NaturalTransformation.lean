/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

/-!
# Unit-graded enriched natural transformations

This file compares Mathlib's unit-graded enriched natural transformations
with the ordinary-underlying natural transformations stored by
`EnrichedNatTrans`.  The forward conversion is unconditional.  Recovering
hom-object naturality in the reverse direction uses the tensor unit as an
explicit separator.

For functors from a plain enriched source into the closed self-enrichment,
`GradedNatTrans.unitOfComponents` constructs a genuine unit-graded transformation
from full uncurried component naturality. `GradedNatTrans.unitId` and source-first
`GradedNatTrans.unitComp` provide identity and composition without a separator or
ordinary source. Their public app/component laws are the construction interface.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory.MonoidalCategory

universe uV vV uC vC uD vD

namespace CategoryTheory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
variable {C : Type uC} [Category.{vC} C]
  [EnrichedOrdinaryCategory V C]
variable {D : Type uD} [Category.{vD} D]
  [EnrichedOrdinaryCategory V D]
variable {F G : EnrichedFunctor V C D}

/-- A full tensor-unit-graded naturality square gives equality of the enriched
pre- and postcomposition maps. No separator or closedness assumption is needed. -/
theorem unitGradedNaturality_eq_whisker
    {P Q R S : C} {H : V}
    (f : H ⟶ (P ⟶[V] Q)) (g : H ⟶ (R ⟶[V] S))
    (a : P ⟶ R) (b : Q ⟶ S)
    (h : (β_ (𝟙_ V) H).hom ≫
          (f ⊗ₘ eHomEquiv V b) ≫ eComp V P Q S =
        (eHomEquiv V a ⊗ₘ g) ≫ eComp V P R S) :
    f ≫ eHomWhiskerLeft V P b =
      g ≫ eHomWhiskerRight V a S := by
  have h' := congrArg (fun k => (λ_ H).inv ≫ k) h
  rw [leftUnitor_inv_braiding_assoc] at h'
  dsimp only [eHomWhiskerLeft, eHomWhiskerRight]
  rw [rightUnitor_inv_naturality_assoc]
  rw [leftUnitor_inv_naturality_assoc]
  rw [← tensorHom_id, ← id_tensorHom]
  rw [whisker_exchange_assoc]
  rw [← tensorHom_def_assoc]
  simpa only [eHomWhiskerLeft, eHomWhiskerRight, Category.assoc,
    tensorHom_comp_tensorHom_assoc, Category.comp_id,
    Category.id_comp] using h'

namespace GradedNatTrans

/-- A transformation graded by the tensor unit determines an ordinary-underlying enriched
natural transformation.  This direction does not require the tensor unit to be a separator. -/
def toEnrichedNatTrans
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G) :
    EnrichedNatTrans F G where
  out :=
    { app := fun X => a.app (ForgetEnrichment.to V X)
      naturality := by
        intro X Y f
        simp only [EnrichedFunctor.forget_map]
        let fV := ForgetEnrichment.homTo V f
        let X' := ForgetEnrichment.to V X
        let Y' := ForgetEnrichment.to V Y
        have h := congrArg
          (fun k =>
            (fV ≫ (λ_ (X' ⟶[V] Y')).inv) ≫ k)
          (a.naturality X' Y')
        dsimp [Center.ofBraided, Center.ofBraidedObj] at h
        rw [Category.assoc, leftUnitor_inv_braiding_assoc] at h
        rw [rightUnitor_inv_naturality_assoc] at h
        rw [Category.assoc] at h
        rw [leftUnitor_inv_naturality_assoc] at h
        rw [← tensorHom_id, ← id_tensorHom] at h
        have h' :
            (λ_ (𝟙_ V)).inv ≫
                  ((fV ≫ F.map X' Y') ⊗ₘ a.app Y') ≫
                eComp V _ _ _ =
              (λ_ (𝟙_ V)).inv ≫
                  (a.app X' ⊗ₘ (fV ≫ G.map X' Y')) ≫
                eComp V _ _ _ := by
          simpa only [Category.assoc, unitors_inv_equal,
            tensorHom_comp_tensorHom_assoc, Category.comp_id,
            Category.id_comp] using h
        exact
          (ForgetEnrichment.homOf_comp (C := D) (W := V)
            (fV ≫ F.map X' Y') (a.app Y')).symm.trans <|
            (congrArg (fun k => ForgetEnrichment.homOf V k) h').trans <|
              ForgetEnrichment.homOf_comp (C := D) (W := V)
                (a.app X') (fV ≫ G.map X' Y') }

end GradedNatTrans

namespace EnrichedNatTrans

/-- Ordinary naturality determines the hom-object naturality equation when the tensor unit is a
separator. -/
theorem enrichedNaturality (a : EnrichedNatTrans F G)
    (hsep : IsSeparator (𝟙_ V)) (X Y : C) :
    (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫
          (F.map X Y ⊗ₘ ForgetEnrichment.homTo V
            (a.out.app (ForgetEnrichment.of V Y))) ≫
        eComp V _ _ _ =
      (ForgetEnrichment.homTo V
            (a.out.app (ForgetEnrichment.of V X)) ⊗ₘ G.map X Y) ≫
        eComp V _ _ _ := by
  apply hsep.def
  intro h
  let fV : 𝟙_ V ⟶ (X ⟶[V] Y) := h ≫ (λ_ (X ⟶[V] Y)).hom
  have hn := a.out.naturality (ForgetEnrichment.homOf V fV)
  have hn' := congrArg (fun k => ForgetEnrichment.homTo V k) hn
  simp only [EnrichedFunctor.forget_map] at hn'
  have hfV : fV ≫ (λ_ (X ⟶[V] Y)).inv = h := by
    dsimp only [fV]
    simp
  rw [← hfV]
  rw [Category.assoc, leftUnitor_inv_braiding_assoc]
  rw [rightUnitor_inv_naturality_assoc]
  rw [Category.assoc]
  rw [leftUnitor_inv_naturality_assoc]
  rw [← tensorHom_id, ← id_tensorHom]
  simpa only [ForgetEnrichment.homTo_comp,
    ForgetEnrichment.homTo_homOf, EnrichedFunctor.forget_obj,
    ForgetEnrichment.to_of, Category.assoc, unitors_inv_equal,
    tensorHom_comp_tensorHom_assoc, Category.comp_id,
    Category.id_comp] using hn'

/-- An ordinary-underlying enriched natural transformation upgrades to a unit-graded enriched
natural transformation when the tensor unit is a separator. -/
def toGradedNatTrans (a : EnrichedNatTrans F G)
    (hsep : IsSeparator (𝟙_ V)) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G where
  app X := ForgetEnrichment.homTo V
    (a.out.app (ForgetEnrichment.of V X))
  naturality X Y := by
    dsimp [Center.ofBraided, Center.ofBraidedObj]
    exact a.enrichedNaturality hsep X Y

end EnrichedNatTrans

namespace GradedNatTrans

/-- Converting a unit-graded transformation to the ordinary-underlying form and back recovers the
original transformation. -/
@[simp]
theorem toEnriched_toGraded
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G)
    (hsep : IsSeparator (𝟙_ V)) :
    a.toEnrichedNatTrans.toGradedNatTrans hsep = a := by
  ext X
  rfl

end GradedNatTrans

namespace EnrichedNatTrans

/-- Converting an ordinary-underlying enriched transformation to the unit-graded form and back
recovers the original transformation. -/
@[simp]
theorem toGraded_toEnriched (a : EnrichedNatTrans F G)
    (hsep : IsSeparator (𝟙_ V)) :
    (a.toGradedNatTrans hsep).toEnrichedNatTrans = a := by
  apply EnrichedFunctor.hom_ext
  intro X
  rfl

end EnrichedNatTrans

section Closed

open scoped MonoidalClosed

variable [MonoidalClosed V]
variable {A : Type uC} [EnrichedCategory V A]
variable {F' G' H' : EnrichedFunctor V A V}

namespace GradedNatTrans

/-- Genuine unit-graded naturality gives naturality of the uncurried enriched actions,
without a separator or an ordinary category on the source. -/
theorem uncurriedNaturality
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' G')
    (X Y : A) :
    MonoidalClosed.uncurry (F'.map X Y) ≫
        (eHomEquiv V).symm (a.app Y) =
      ((eHomEquiv V).symm (a.app X) ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry (G'.map X Y) := by
  have hnat := a.naturality X Y
  dsimp only [Center.ofBraided, Center.ofBraidedObj] at hnat
  have hx : eHomEquiv V ((eHomEquiv V).symm (a.app X)) = a.app X :=
    (eHomEquiv V).apply_symm_apply _
  have hy : eHomEquiv V ((eHomEquiv V).symm (a.app Y)) = a.app Y :=
    (eHomEquiv V).apply_symm_apply _
  have hn := unitGradedNaturality_eq_whisker
    (f := F'.map X Y) (g := G'.map X Y)
    (a := (eHomEquiv V).symm (a.app X))
    (b := (eHomEquiv V).symm (a.app Y))
    (h := by rw [hx, hy]; exact hnat)
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] at hn
  have hu := congrArg MonoidalClosed.uncurry hn
  simpa only [MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.uncurry_pre_app, tensorHom_id] using hu

/-- Construct a genuine unit-graded transformation from ordinary components satisfying
the full uncurried hom-object naturality equation. No separator or ordinary source
category is required. -/
@[no_expose]
def unitOfComponents
    (q : ∀ X, F'.obj X ⟶ G'.obj X)
    (hq : ∀ X Y,
      MonoidalClosed.uncurry (F'.map X Y) ≫ q Y =
        (q X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (G'.map X Y)) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' G' where
  app X := eHomEquiv V (q X)
  naturality X Y := by
    dsimp only [Center.ofBraided, Center.ofBraidedObj]
    have h : F'.map X Y ≫ eHomWhiskerLeft V (F'.obj X) (q Y) =
        G'.map X Y ≫ eHomWhiskerRight V (q X) (G'.obj Y) := by
      rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
        MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight]
      apply MonoidalClosed.uncurry_injective
      rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_pre_app]
      simpa only [tensorHom_id] using hq X Y
    apply (cancel_epi (λ_ (X ⟶[V] Y)).inv).1
    rw [leftUnitor_inv_braiding_assoc]
    dsimp only [eHomWhiskerLeft, eHomWhiskerRight] at h
    rw [rightUnitor_inv_naturality_assoc, leftUnitor_inv_naturality_assoc] at h
    rw [← tensorHom_id, ← id_tensorHom, whisker_exchange_assoc,
      ← tensorHom_def_assoc] at h
    simpa only [Category.assoc, tensorHom_comp_tensorHom_assoc,
      Category.comp_id, Category.id_comp] using h

private theorem unitOfComponents_app_private
    (q : ∀ X, F'.obj X ⟶ G'.obj X)
    (hq : ∀ X Y,
      MonoidalClosed.uncurry (F'.map X Y) ≫ q Y =
        (q X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (G'.map X Y))
    (X : A) :
    (unitOfComponents q hq).app X = eHomEquiv V (q X) :=
  rfl

/-- The enriched component of a unit-graded transformation built from components. -/
@[simp]
theorem unitOfComponents_app
    (q : ∀ X, F'.obj X ⟶ G'.obj X)
    (hq : ∀ X Y,
      MonoidalClosed.uncurry (F'.map X Y) ≫ q Y =
        (q X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (G'.map X Y))
    (X : A) :
    (unitOfComponents q hq).app X = eHomEquiv V (q X) :=
  unitOfComponents_app_private q hq X

/-- The ordinary component of a unit-graded transformation built from components
is exactly the supplied component. -/
@[simp]
theorem unitOfComponents_component
    (q : ∀ X, F'.obj X ⟶ G'.obj X)
    (hq : ∀ X Y,
      MonoidalClosed.uncurry (F'.map X Y) ≫ q Y =
        (q X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (G'.map X Y))
    (X : A) :
    (eHomEquiv V).symm ((unitOfComponents q hq).app X) = q X := by
  rw [unitOfComponents_app]
  exact (eHomEquiv V).symm_apply_apply _

/-- The identity unit-graded transformation into the closed self-enrichment.
Use the public component equations rather than unfolding its construction. -/
@[no_expose]
def unitId (F : EnrichedFunctor V A V) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F :=
  unitOfComponents (fun X => 𝟙 (F.obj X)) (by
    intro X Y
    simp only [id_tensorHom_id, Category.id_comp, Category.comp_id])

/-- The identity unit-graded transformation has enriched identity components. -/
theorem unitId_app (F : EnrichedFunctor V A V) (X : A) :
    (unitId F).app X = eId V (F.obj X) := by
  exact eHomEquiv_id V (F.obj X)

/-- Ordinary components of the identity unit-graded transformation are identities. -/
@[simp]
theorem unitId_component (F : EnrichedFunctor V A V) (X : A) :
    (eHomEquiv V).symm ((unitId F).app X) = 𝟙 (F.obj X) :=
  (eHomEquiv V).symm_apply_apply _

/-- Source-first vertical composition of unit-graded transformations into the
closed self-enrichment; it needs neither an ordinary source nor a separator. -/
@[no_expose]
def unitComp
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' G')
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G' H') :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' H' :=
  unitOfComponents (fun X => (eHomEquiv V).symm (a.app X) ≫
    (eHomEquiv V).symm (b.app X)) (by
      intro X Y
      rw [← Category.assoc, a.uncurriedNaturality, Category.assoc,
        b.uncurriedNaturality, ← Category.assoc, tensorHom_comp_tensorHom]
      simp only [Category.id_comp])

/-- The raw enriched component of source-first unit-graded composition. -/
theorem unitComp_app
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' G')
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G' H') (X : A) :
    (unitComp a b).app X =
      (λ_ (𝟙_ V)).inv ≫ (a.app X ⊗ₘ b.app X) ≫ eComp V _ _ _ := by
  change eHomEquiv V ((eHomEquiv V).symm (a.app X) ≫
    (eHomEquiv V).symm (b.app X)) = _
  rw [eHomEquiv_comp]
  have ha : eHomEquiv V ((eHomEquiv V).symm (a.app X)) = a.app X :=
    (eHomEquiv V).apply_symm_apply _
  have hb : eHomEquiv V ((eHomEquiv V).symm (b.app X)) = b.app X :=
    (eHomEquiv V).apply_symm_apply _
  rw [ha, hb]

/-- Ordinary components of source-first unit-graded composition compose in
the same order. -/
@[simp]
theorem unitComp_component
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' G')
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G' H') (X : A) :
    (eHomEquiv V).symm ((unitComp a b).app X) =
      (eHomEquiv V).symm (a.app X) ≫ (eHomEquiv V).symm (b.app X) :=
  (eHomEquiv V).symm_apply_apply _

end GradedNatTrans

namespace EnrichedNatTrans

variable {F₁ F₂ F₃ : EnrichedFunctor V C V}

/-- The ordinary identity converts to the shared unit-graded identity. -/
@[simp]
theorem toGradedNatTrans_id (F₁ : EnrichedFunctor V C V)
    (hsep : IsSeparator (𝟙_ V)) :
    (𝟙 F₁ : EnrichedNatTrans F₁ F₁).toGradedNatTrans hsep =
      GradedNatTrans.unitId F₁ := by
  ext X
  rw [GradedNatTrans.unitId_app]
  exact ForgetEnrichment.homTo_id V (ForgetEnrichment.of V (F₁.obj X))

/-- Ordinary composition converts to source-first unit-graded composition.
The separator is required only by the existing reverse conversion. -/
@[simp]
theorem toGradedNatTrans_comp (a : F₁ ⟶ F₂)
    (b : F₂ ⟶ F₃) (hsep : IsSeparator (𝟙_ V)) :
    (a ≫ b).toGradedNatTrans hsep =
      GradedNatTrans.unitComp (a.toGradedNatTrans hsep) (b.toGradedNatTrans hsep) := by
  ext X
  rw [GradedNatTrans.unitComp_app]
  change ForgetEnrichment.homTo V
      (a.out.app (ForgetEnrichment.of V X) ≫ b.out.app (ForgetEnrichment.of V X)) =
    (λ_ (𝟙_ V)).inv ≫
      (ForgetEnrichment.homTo V (a.out.app (ForgetEnrichment.of V X)) ⊗ₘ
        ForgetEnrichment.homTo V (b.out.app (ForgetEnrichment.of V X))) ≫ eComp V _ _ _
  rw [ForgetEnrichment.homTo_comp, Category.assoc]

end EnrichedNatTrans

end Closed

end CategoryTheory
