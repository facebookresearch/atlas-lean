/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/Algebra/Homology/HomotopyCategory/Plus.lean` (Mathlib):
Copyright (c) 2026 Joël Riou. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Joël Riou

`Mathlib/Algebra/Homology/DerivedCategory/Plus.lean` (Mathlib):
Copyright (c) 2026 Joël Riou. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Joël Riou
-/

module

public import MathlibExt.AlgebraicGeometry.IndSheafBoundedTensorModels
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Localization.OfQuotient

/-!
# Localization of bounded Ind-sheaf complexes

The original bounded derived-category functor localizes bounded cochain
complexes at their original quasi-isomorphisms. The proof uses bounded
representatives, truncation in the bounded below homotopy category, and
bounded cylinders.

Source: Andrea D'Agnolo and Masaki Kashiwara, Riemann-Hilbert correspondence
for holonomic D-modules, arXiv:1311.2374v2, Sections 2.2, 3.2--3.3 and 4.4;
Masaki Kashiwara and Pierre Schapira, Ind-sheaves and Categories and Sheaves.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.IndSheafDerivedSourceRequests

open CategoryTheory Category Limits ZeroObject Pretriangulated CochainComplex
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafBoundedTensorModels

/-- Use the zero morphisms of the abelian structure of `IndSheaf k X`. -/
local instance boundedLocalizationPreadditive (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : Preadditive (IndSheaf k X) := Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

private def upper (C : Type*) [Category* C] [Abelian C] :
    ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  fun K => ∃ b : ℤ, CochainComplex.IsStrictlyLE K.as b

private def boundedHomotopy (C : Type*) [Category* C] [Abelian C] :
    ObjectProperty (HomotopyCategory.Plus C) :=
  (upper C).inverseImage (HomotopyCategory.Plus.ι C)

private instance boundedHomotopy_zero (C : Type*) [Category* C] [Abelian C] :
    (boundedHomotopy C).ContainsZero where
  exists_zero := ⟨(HomotopyCategory.Plus.quotient C).obj ⟨0, 0, inferInstance⟩,
    Functor.map_isZero _ (IsZero.of_full_of_faithful_of_isZero (CochainComplex.Plus.ι C)
      ⟨0, 0, inferInstance⟩ (isZero_zero _)),
    0, by
      change CochainComplex.IsStrictlyLE (0 : CochainComplex C ℤ) 0
      infer_instance⟩

private instance boundedHomotopy_shift (C : Type*) [Category* C] [Abelian C] :
    (boundedHomotopy C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift := by
        rintro K ⟨b, hb⟩
        with_unfolding_all change upper C (K.obj⟦n⟧)
        obtain ⟨L : CochainComplex C ℤ, hL⟩ := HomotopyCategory.quotient_obj_surjective K.obj
        rw [← hL, HomotopyCategory.shift_quotient_obj]
        have : L.IsStrictlyLE b := by
          change CochainComplex.IsStrictlyLE K.obj.as b at hb
          with_unfolding_all rw [← hL] at hb
          exact hb
        exact ⟨b - n, L.isStrictlyLE_shift b n (b - n) (by lia)⟩ }

private instance boundedHomotopy_closed (C : Type*) [Category* C] [Abelian C] :
    (boundedHomotopy C).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    obtain ⟨b₁, hb₁⟩ := h₁
    obtain ⟨b₂, hb₂⟩ := h₂
    have : CochainComplex.IsStrictlyLE T.obj₁.obj.as b₁ := hb₁
    have : CochainComplex.IsStrictlyLE T.obj₂.obj.as b₂ := hb₂
    obtain ⟨a₁, ha₁⟩ := (HomotopyCategory.plus_quotient_obj_iff T.obj₁.obj.as).mp T.obj₁.property
    obtain ⟨a₂, ha₂⟩ := (HomotopyCategory.plus_quotient_obj_iff T.obj₂.obj.as).mp T.obj₂.property
    obtain ⟨f : T.obj₁.obj.as ⟶ T.obj₂.obj.as, hf⟩ :=
      (HomotopyCategory.quotient C (.up ℤ)).map_surjective T.mor₁.hom
    let M : HomotopyCategory.Plus C :=
      ⟨(HomotopyCategory.quotient C (.up ℤ)).obj (CochainComplex.mappingCone f), by
        rw [HomotopyCategory.plus_quotient_obj_iff]
        exact ⟨min (a₁ - 1) a₂, CochainComplex.isStrictlyGE_mappingCone f a₁ a₂ _
          (by simp) (by simp)⟩⟩
    refine ⟨M, ?_, ⟨(HomotopyCategory.Plus.ι C).preimageIso
      (Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _
        ((HomotopyCategory.Plus.ι C).map_distinguished _ hT)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)
        (Iso.refl _) (Iso.refl _) ?_))⟩⟩
    · refine ⟨max b₁ b₂, ?_⟩
      change CochainComplex.IsStrictlyLE (CochainComplex.mappingCone f) (max b₁ b₂)
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      rw [CochainComplex.mappingCone.isZero_X_iff]
      exact ⟨CochainComplex.isZero_of_isStrictlyLE T.obj₁.obj.as b₁ (i + 1) (by lia),
        CochainComplex.isZero_of_isStrictlyLE T.obj₂.obj.as b₂ i (by lia)⟩
    · simp [hf]

private instance boundedHomotopy_tri (C : Type*) [Category* C] [Abelian C] :
    (boundedHomotopy C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

private instance boundedHomotopy_localizing (C : Type*) [Category* C] [Abelian C] :
    (boundedHomotopy C).IsVerdierLeftLocalizing
      (HomotopyCategory.Plus.subcategoryAcyclic C) where
  fac {K L} φ hK hL := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective K
    obtain ⟨L, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective L
    obtain ⟨b, hb⟩ := hK
    have : K.obj.IsStrictlyLE b := hb
    obtain ⟨a, ha⟩ := L.property
    obtain ⟨φ, rfl⟩ := (HomotopyCategory.Plus.quotient C).map_surjective φ
    have hL' : L.obj.Acyclic := by
      change HomotopyCategory.subcategoryAcyclic C
        ((HomotopyCategory.quotient C (.up ℤ)).obj L.obj) at hL
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp hL
    let M : CochainComplex.Plus C := ⟨L.obj.truncLE b, a, inferInstance⟩
    refine ⟨(HomotopyCategory.Plus.quotient C).obj M,
      (HomotopyCategory.Plus.quotient C).map (ObjectProperty.homMk
        (inv (K.obj.ιTruncLE b) ≫ CochainComplex.truncLEMap φ.hom b)),
      (HomotopyCategory.Plus.quotient C).map (ObjectProperty.homMk (L.obj.ιTruncLE b)),
      ⟨b, by change M.obj.IsStrictlyLE b; dsimp [M]; infer_instance⟩, ?_, ?_⟩
    · change HomotopyCategory.subcategoryAcyclic C
        ((HomotopyCategory.quotient C (.up ℤ)).obj M.obj)
      rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
      exact hL'.truncLE _
    · rw [← Functor.map_comp]
      congr 1
      apply ObjectProperty.hom_ext
      change (inv (K.obj.ιTruncLE b) ≫ CochainComplex.truncLEMap φ.hom b) ≫
        L.obj.ιTruncLE b = φ.hom
      rw [Category.assoc, CochainComplex.ιTruncLE_naturality, IsIso.inv_hom_id_assoc]

private lemma bounded_iff (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] (K : CochainComplex (IndSheaf k X) ℤ) :
    termwiseBounded k X K ↔ ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b := by
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, (CochainComplex.isStrictlyGE_iff K a).mpr (fun n hn => h n (Or.inl hn)),
      (CochainComplex.isStrictlyLE_iff K b).mpr (fun n hn => h n (Or.inr hn))⟩
  · rintro ⟨a, b, ha, hb⟩
    exact ⟨a, b, fun n hn => hn.elim
      (fun hn => K.isZero_of_isStrictlyGE a n hn)
      (fun hn => K.isZero_of_isStrictlyLE b n hn)⟩

private def boundedDerivedToPlus (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : BoundedIndDerived k X ⥤ DerivedCategory.Plus (IndSheaf k X) :=
  DerivedCategory.TStructure.t.plus.lift (IsBounded k X).ι (fun F => by
    obtain ⟨a, b, h⟩ := F.property
    exact ⟨a, (DerivedCategory.isGE_iff F.obj a).mpr (fun n hn => h n (Or.inl hn))⟩)

private instance boundedDerivedToPlus_full (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : (boundedDerivedToPlus k X).Full := by
  dsimp only [boundedDerivedToPlus]
  infer_instance

private instance boundedDerivedToPlus_faithful (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : (boundedDerivedToPlus k X).Faithful := by
  dsimp only [boundedDerivedToPlus]
  infer_instance

private def boundedHomotopyQ (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] :
    (boundedHomotopy (IndSheaf k X)).FullSubcategory ⥤ BoundedIndDerived k X :=
  (IsBounded k X).lift ((boundedHomotopy (IndSheaf k X)).ι ⋙
    DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι) (fun F => by
      obtain ⟨b, hb⟩ := F.property
      obtain ⟨a, ha⟩ := (HomotopyCategory.plus_quotient_obj_iff F.obj.obj.as).mp F.obj.property
      have : CochainComplex.IsStrictlyLE F.obj.obj.as b := hb
      let K : CochainComplex (IndSheaf k X) ℤ := F.obj.obj.as
      let e : DerivedCategory.Qh.obj F.obj.obj ≅ DerivedCategory.Q.obj K :=
        (DerivedCategory.quotientCompQhIso (IndSheaf k X)).app K
      change IsBounded k X (DerivedCategory.Qh.obj F.obj.obj)
      refine ⟨a, b, fun n hn => ?_⟩
      apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor (IndSheaf k X) n).mapIso e)
      rcases hn with hn | hn
      · exact (DerivedCategory.Q.obj K).isZero_of_isGE a n hn
      · exact (DerivedCategory.Q.obj K).isZero_of_isLE b n hn)

private instance boundedHomotopyQ_essSurj (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : (boundedHomotopyQ k X).EssSurj where
  mem_essImage F := by
    obtain ⟨a, b, h⟩ := F.property
    have : F.obj.IsGE a :=
      (DerivedCategory.isGE_iff F.obj a).mpr (fun n hn => h n (Or.inl hn))
    have : F.obj.IsLE b :=
      (DerivedCategory.isLE_iff F.obj b).mpr (fun n hn => h n (Or.inr hn))
    obtain ⟨K, ha, hb, ⟨e⟩⟩ :=
      DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE F.obj a b
    let M : (boundedHomotopy (IndSheaf k X)).FullSubcategory :=
      ⟨⟨(HomotopyCategory.quotient (IndSheaf k X) (.up ℤ)).obj K, by
        rw [HomotopyCategory.plus_quotient_obj_iff]
        exact ⟨a, ha⟩⟩, b, hb⟩
    exact ⟨M, ⟨ObjectProperty.isoMk _
      ((DerivedCategory.quotientCompQhIso (IndSheaf k X)).app K ≪≫ e.symm)⟩⟩

private instance boundedHomotopyQ_localization (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : (boundedHomotopyQ k X).IsLocalization
      ((HomotopyCategory.Plus.subcategoryAcyclic (IndSheaf k X)).inverseImage
        (boundedHomotopy (IndSheaf k X)).ι).trW := by
  let Φ := (boundedHomotopy (IndSheaf k X)).triangulatedLocalizerMorphism
    (HomotopyCategory.Plus.subcategoryAcyclic (IndSheaf k X))
  exact Φ.isLocalization_of_isLocalizedFullyFaithful
    (L₂ := DerivedCategory.Plus.Qh) (F := boundedDerivedToPlus k X) (Iso.refl _)

private lemma boundedHomotopy_quasiIso_eq (C : Type*) [Category* C] [Abelian C] :
    (HomotopyCategory.Plus.quasiIso C).inverseImage (boundedHomotopy C).ι =
      ((HomotopyCategory.Plus.subcategoryAcyclic C).inverseImage (boundedHomotopy C).ι).trW := by
  ext K L f
  rw [MorphismProperty.inverseImage_iff, HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW,
    ← ObjectProperty.inverseImage_trW_iff]

private instance boundedHomotopyQ_localization_quasiIso (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : (boundedHomotopyQ k X).IsLocalization
      ((HomotopyCategory.Plus.quasiIso (IndSheaf k X)).inverseImage
        (boundedHomotopy (IndSheaf k X)).ι) := by
  rw [boundedHomotopy_quasiIso_eq]
  infer_instance

private def boundedHomotopyQuotient (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] :
    BoundedIndComplex k X ⥤ (boundedHomotopy (IndSheaf k X)).FullSubcategory where
  obj K := ⟨⟨(HomotopyCategory.quotient (IndSheaf k X) (.up ℤ)).obj K.obj, by
    rw [HomotopyCategory.plus_quotient_obj_iff]
    obtain ⟨a, b, ha, hb⟩ := (bounded_iff k X K.obj).mp K.property
    exact ⟨a, ha⟩⟩, by
      obtain ⟨a, b, ha, hb⟩ := (bounded_iff k X K.obj).mp K.property
      exact ⟨b, hb⟩⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk
    ((HomotopyCategory.quotient (IndSheaf k X) (.up ℤ)).map f.hom))
  map_id K := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (HomotopyCategory.quotient (IndSheaf k X) (.up ℤ)).map_id K.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (HomotopyCategory.quotient (IndSheaf k X) (.up ℤ)).map_comp f.hom g.hom

private lemma boundedHomotopyQuotient_obj_surjective (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : Function.Surjective (boundedHomotopyQuotient k X).obj := by
  intro K
  obtain ⟨a, ha⟩ := (HomotopyCategory.plus_quotient_obj_iff K.obj.obj.as).mp K.obj.property
  obtain ⟨b, hb⟩ := K.property
  refine ⟨⟨K.obj.obj.as, (bounded_iff k X _).mpr ⟨a, b, ha, hb⟩⟩, ?_⟩
  apply ObjectProperty.FullSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  rfl

private instance boundedHomotopyQuotient_essSurj (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : (boundedHomotopyQuotient k X).EssSurj where
  mem_essImage K := by
    obtain ⟨L, rfl⟩ := boundedHomotopyQuotient_obj_surjective k X K
    exact ⟨L, ⟨Iso.refl _⟩⟩

private instance boundedHomotopyQuotient_full (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : (boundedHomotopyQuotient k X).Full where
  map_surjective f := by
    obtain ⟨g, hg⟩ := (HomotopyCategory.quotient (IndSheaf k X) (.up ℤ)).map_surjective f.hom.hom
    refine ⟨ObjectProperty.homMk g, ?_⟩
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact hg

private lemma boundedHomotopyQuotient_quasiIso_iff (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] {K L : BoundedIndComplex k X} (f : K ⟶ L) :
    ((HomotopyCategory.Plus.quasiIso (IndSheaf k X)).inverseImage
      (boundedHomotopy (IndSheaf k X)).ι) ((boundedHomotopyQuotient k X).map f) ↔
      boundedQuasiIso k X f := by
  change HomotopyCategory.quasiIso (IndSheaf k X) (.up ℤ)
    ((HomotopyCategory.quotient (IndSheaf k X) (.up ℤ)).map f.hom) ↔
      QuasiIso f.hom
  exact HomotopyCategory.quotient_map_mem_quasiIso_iff _

private lemma boundedHomotopyQuotient_map_quasiIso (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] :
    (boundedQuasiIso k X).map (boundedHomotopyQuotient k X) =
      (HomotopyCategory.Plus.quasiIso (IndSheaf k X)).inverseImage
        (boundedHomotopy (IndSheaf k X)).ι := by
  ext K L f
  obtain ⟨K, rfl⟩ := boundedHomotopyQuotient_obj_surjective k X K
  obtain ⟨L, rfl⟩ := boundedHomotopyQuotient_obj_surjective k X L
  obtain ⟨f, rfl⟩ := (boundedHomotopyQuotient k X).map_surjective f
  constructor
  · rintro ⟨K', L', f', hf', ⟨e⟩⟩
    exact (((HomotopyCategory.Plus.quasiIso (IndSheaf k X)).inverseImage
      (boundedHomotopy (IndSheaf k X)).ι).arrow_mk_iso_iff e).mp
        ((boundedHomotopyQuotient_quasiIso_iff k X f').mpr hf')
  · intro hf
    exact ⟨_, _, f, (boundedHomotopyQuotient_quasiIso_iff k X f).mp hf, ⟨Iso.refl _⟩⟩

private lemma cylinder_bounded (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] (K : BoundedIndComplex k X) :
    termwiseBounded k X K.obj.cylinder := by
  obtain ⟨a, b, ha, hb⟩ := (bounded_iff k X K.obj).mp K.property
  obtain ⟨a', ha'⟩ := K.obj.plus_cylinder ⟨a, ha⟩
  refine (bounded_iff k X _).mpr ⟨a', b, ha', ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  dsimp [HomologicalComplex.cylinder]
  refine HomologicalComplex.homotopyCofiber.isZero_X _ _ ?_ (fun j hj => ?_)
  · refine IsZero.of_iso ?_ ((HomologicalComplex.eval (IndSheaf k X) (.up ℤ) i).mapBiprod _ _)
    simpa using K.obj.isZero_of_isStrictlyLE b i hi
  · simp only [ComplexShape.up_Rel] at hj
    exact K.obj.isZero_of_isStrictlyLE b j (by lia)

private def boundedPrecylinder (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] (K : BoundedIndComplex k X) : HomotopicalAlgebra.Precylinder K :=
  K.obj.precylinder.toFullSubcategory (cylinder_bounded k X K)

private instance boundedHomotopyQuotient_localization (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : (boundedHomotopyQuotient k X).IsLocalization
      ((HomologicalComplex.homotopyEquivalences (IndSheaf k X) (.up ℤ)).inverseImage
        (termwiseBounded k X).ι) :=
  Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _
    (fun K L f hf => by
      have : IsIso (((boundedHomotopy (IndSheaf k X)).ι ⋙
          HomotopyCategory.Plus.ι (IndSheaf k X)).map ((boundedHomotopyQuotient k X).map f)) :=
        HomotopyCategory.quotient_inverts_homotopyEquivalences _ _ f.hom hf
      exact isIso_of_fully_faithful
        ((boundedHomotopy (IndSheaf k X)).ι ⋙ HomotopyCategory.Plus.ι (IndSheaf k X)) _)
    (fun K L f₀ f₁ hf => by
      have h := HomotopyCategory.homotopyOfEq f₀.hom f₁.hom
        (((boundedHomotopy (IndSheaf k X)).ι ⋙
          HomotopyCategory.Plus.ι (IndSheaf k X)).congr_map hf)
      exact ⟨boundedPrecylinder k X K,
        HomotopicalAlgebra.Precylinder.LeftHomotopy.fullSubcategoryEquiv.symm
          { h := HomologicalComplex.cylinder.desc _ _ h
            h₀ := by
              change HomologicalComplex.cylinder.ι₀ K.obj ≫
                HomologicalComplex.cylinder.desc _ _ h = f₀.hom
              exact HomologicalComplex.cylinder.ι₀_desc _ _ h
            h₁ := by
              change HomologicalComplex.cylinder.ι₁ K.obj ≫
                HomologicalComplex.cylinder.desc _ _ h = f₁.hom
              exact HomologicalComplex.cylinder.ι₁_desc _ _ h },
        ⟨HomologicalComplex.cylinder.homotopyEquiv _ (fun n => ⟨n - 1, by simp⟩), rfl⟩⟩)

private instance quotient_comp_localization (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : (boundedHomotopyQuotient k X ⋙ boundedHomotopyQ k X).IsLocalization
      (boundedQuasiIso k X) := by
  refine Functor.IsLocalization.comp _ _
    ((HomologicalComplex.homotopyEquivalences (IndSheaf k X) (.up ℤ)).inverseImage
      (termwiseBounded k X).ι)
    ((HomotopyCategory.Plus.quasiIso (IndSheaf k X)).inverseImage
      (boundedHomotopy (IndSheaf k X)).ι) _ ?_ ?_ ?_
  · intro K L f hf
    exact Localization.inverts (boundedHomotopyQ k X) _ _
      ((boundedHomotopyQuotient_quasiIso_iff k X f).mpr hf)
  · intro K L f hf
    exact homotopyEquivalences_le_quasiIso _ _ _ hf
  · rw [boundedHomotopyQuotient_map_quasiIso]

private def quotientCompBoundedHomotopyQIso (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] (R : BoundedCohomologySource k X) :
    boundedHomotopyQuotient k X ⋙ boundedHomotopyQ k X ≅ boundedQ k X R :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _
    ((DerivedCategory.quotientCompQhIso (IndSheaf k X)).app K.obj)) (fun f => by
      apply ObjectProperty.hom_ext
      exact (DerivedCategory.quotientCompQhIso (IndSheaf k X)).hom.naturality f.hom)

/-- The original bounded Q localizes the actual bounded cochain quasi-isomorphisms. -/
theorem actual_bounded_localization_source (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] (R : BoundedCohomologySource k X) : BoundedLocalizationSource k X R
    := by
  exact ⟨Functor.IsLocalization.of_iso _ (quotientCompBoundedHomotopyQIso k X R)⟩

end WantedExt.AlgebraicGeometry.IndSheafDerivedSourceRequests
