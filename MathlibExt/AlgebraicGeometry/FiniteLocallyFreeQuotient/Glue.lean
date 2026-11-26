/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.lean`
and
`P2M/Sol/S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import MathlibExt.AlgebraicGeometry.FiniteLocallyFreeQuotient.Affine
import MathlibExt.AlgebraicGeometry.FiniteLocallyFreeQuotient.GlueAux

/-!
# Gluing local quotients

If `X` is covered by opens that are invariant for `s t : R ⟶ X` and each restricted
relation has a finite locally free quotient, then the local quotients glue to a
global one.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.QuotGlue

open TopologicalSpace

section Saturation

variable {X Y R : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}

private lemma preimage_image_eq (hR : IsPullback s t p p) (O : X.Opens) (hO : s ⁻¹ᵁ O = t ⁻¹ᵁ O) :
    p ⁻¹' (p '' (O : Set X)) = O := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro x ⟨o, ho, hox⟩
  obtain ⟨r, hrs, hrt⟩ := Scheme.exists_preimage_of_isPullback hR x o hox.symm
  have : r ∈ t ⁻¹ᵁ O := by change t r ∈ O; rw [hrt]; exact ho
  rw [← hO] at this
  change s r ∈ O at this
  rwa [hrs] at this

private lemma isOpen_image [Flat p] [LocallyOfFinitePresentation p]
    (O : X.Opens) : IsOpen (p '' (O : Set X)) :=
  p.isOpenMap _ O.2

private def imageOpens [Flat p] [LocallyOfFinitePresentation p] (O : X.Opens) : Y.Opens :=
  ⟨p '' (O : Set X), isOpen_image O⟩

@[local simp] private lemma coe_imageOpens [Flat p] [LocallyOfFinitePresentation p] (O : X.Opens) :
    (imageOpens (p := p) O : Set Y) = p '' (O : Set X) := rfl

private lemma preimage_imageOpens (hR : IsPullback s t p p) [Flat p] [LocallyOfFinitePresentation p]
    (O : X.Opens) (hO : s ⁻¹ᵁ O = t ⁻¹ᵁ O) : p ⁻¹ᵁ imageOpens (p := p) O = O :=
  Opens.ext (preimage_image_eq hR O hO)

private lemma imageOpens_top [Flat p] [LocallyOfFinitePresentation p] [Surjective p] :
    imageOpens (p := p) ⊤ = ⊤ :=
  Opens.ext (by simp [Set.image_univ, p.surjective.range_eq])

private lemma le_imageOpens_iff [Flat p] [LocallyOfFinitePresentation p] (O : X.Opens) (x : X)
    (hx : x ∈ O) :
    p x ∈ imageOpens (p := p) O :=
  ⟨x, hx, rfl⟩

end Saturation

section RestrictPkg

variable {X Y R : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}

private lemma preimage_preimage_eq (hw : s ≫ p = t ≫ p) (U : Y.Opens) :
    s ⁻¹ᵁ (p ⁻¹ᵁ U) = t ⁻¹ᵁ (p ⁻¹ᵁ U) := by
  change (s ≫ p) ⁻¹ᵁ U = (t ≫ p) ⁻¹ᵁ U
  rw [hw]

private noncomputable def tRes (hw : s ≫ p = t ≫ p) (U : Y.Opens) :
    (s ⁻¹ᵁ (p ⁻¹ᵁ U) : Scheme.{u}) ⟶ (p ⁻¹ᵁ U : Scheme.{u}) :=
  (R.isoOfEq (preimage_preimage_eq hw U)).hom ≫ (t ∣_ (p ⁻¹ᵁ U))

@[reassoc]
private lemma tRes_ι (hw : s ≫ p = t ≫ p) (U : Y.Opens) :
    tRes hw U ≫ (p ⁻¹ᵁ U).ι = (s ⁻¹ᵁ (p ⁻¹ᵁ U)).ι ≫ t := by
  rw [tRes, Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]

private lemma sRes_w (hw : s ≫ p = t ≫ p) (U : Y.Opens) :
    (s ∣_ (p ⁻¹ᵁ U)) ≫ (p ∣_ U) = tRes hw U ≫ (p ∣_ U) := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
    morphismRestrict_ι_assoc, tRes_ι_assoc, hw]

private theorem restrict_pkg (hw : s ≫ p = t ≫ p) [IsFinite p] [Flat p]
    [LocallyOfFinitePresentation p]
    [Surjective p] (hR : IsPullback s t p p) (U : Y.Opens) :
    IsFinite (p ∣_ U) ∧ Flat (p ∣_ U) ∧ LocallyOfFinitePresentation (p ∣_ U) ∧
      Surjective (p ∣_ U) ∧ IsPullback (s ∣_ (p ⁻¹ᵁ U)) (tRes hw U) (p ∣_ U) (p ∣_ U) ∧
      Nonempty (IsColimit (Cofork.ofπ (p ∣_ U) (sRes_w hw U))) :=
  Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback hR
    (isPullback_morphismRestrict p U).flip (isPullback_morphismRestrict s (p ⁻¹ᵁ U)).flip
    (tRes_ι hw U).symm (sRes_w hw U)

end RestrictPkg

section Compare

variable {R₁ X₁ Y₁ R₂ X₂ Y₂ : Scheme.{u}} {s₁ t₁ : R₁ ⟶ X₁} {s₂ t₂ : R₂ ⟶ X₂}
  {p₁ : X₁ ⟶ Y₁} {p₂ : X₂ ⟶ Y₂} {w₁ : s₁ ≫ p₁ = t₁ ≫ p₁} {w₂ : s₂ ≫ p₂ = t₂ ≫ p₂}

private noncomputable def quotIso (h₁ : IsColimit (Cofork.ofπ p₁ w₁))
    (h₂ : IsColimit (Cofork.ofπ p₂ w₂))
    (eR : R₁ ≅ R₂) (eX : X₁ ≅ X₂) (hs : s₁ ≫ eX.hom = eR.hom ≫ s₂)
    (ht : t₁ ≫ eX.hom = eR.hom ≫ t₂) :
    Y₁ ≅ Y₂ :=
  IsColimit.coconePointsIsoOfNatIso h₁ h₂ (parallelPair.ext eR eX hs ht)

@[reassoc]
private lemma π_quotIso_hom (h₁ : IsColimit (Cofork.ofπ p₁ w₁))
    (h₂ : IsColimit (Cofork.ofπ p₂ w₂))
    (eR : R₁ ≅ R₂) (eX : X₁ ≅ X₂) (hs : s₁ ≫ eX.hom = eR.hom ≫ s₂)
    (ht : t₁ ≫ eX.hom = eR.hom ≫ t₂) :
    p₁ ≫ (quotIso h₁ h₂ eR eX hs ht).hom = eX.hom ≫ p₂ :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom h₁ h₂ (parallelPair.ext eR eX hs ht)
    WalkingParallelPair.one

end Compare

section Main

variable {X R : Scheme.{u}} (s t : R ⟶ X) (W : X → X.Opens) (hxW : ∀ x, x ∈ W x)
  (hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x)

private noncomputable abbrev tW (x : X) : (s ⁻¹ᵁ W x : Scheme.{u}) ⟶ (W x : Scheme.{u}) :=
  (R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)

@[reassoc]
private lemma tW_ι (x : X) : tW s t W hinv x ≫ (W x).ι = (s ⁻¹ᵁ W x).ι ≫ t := by
  rw [Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]

variable (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p)

private noncomputable def Yloc (x : X) : Scheme.{u} := (loc x).choose

private noncomputable def ploc (x : X) : (W x : Scheme.{u}) ⟶ Yloc s t W hinv loc x :=
  (loc x).choose_spec.choose
private lemma ploc_spec (x : X) :
    (s ∣_ W x) ≫ ploc s t W hinv loc x = tW s t W hinv x ≫ ploc s t W hinv loc x ∧
      IsFinite (ploc s t W hinv loc x) ∧ Flat (ploc s t W hinv loc x) ∧
      LocallyOfFinitePresentation (ploc s t W hinv loc x) ∧ Surjective (ploc s t W hinv loc x) ∧
      IsPullback (s ∣_ W x) (tW s t W hinv x) (ploc s t W hinv loc x) (ploc s t W hinv loc x) :=
  (loc x).choose_spec.choose_spec

private instance (x : X) : IsFinite (ploc s t W hinv loc x) := (ploc_spec s t W hinv loc x).2.1
private instance (x : X) : Flat (ploc s t W hinv loc x) := (ploc_spec s t W hinv loc x).2.2.1
private instance (x : X) : LocallyOfFinitePresentation (ploc s t W hinv loc x) :=
  (ploc_spec s t W hinv loc x).2.2.2.1
private instance (x : X) : Surjective (ploc s t W hinv loc x) :=
  (ploc_spec s t W hinv loc x).2.2.2.2.1

private lemma inv_overlap (x y : X) :
    (s ∣_ W x) ⁻¹ᵁ ((W x).ι ⁻¹ᵁ W y) = (tW s t W hinv x) ⁻¹ᵁ ((W x).ι ⁻¹ᵁ W y) := by
  change ((s ∣_ W x) ≫ (W x).ι) ⁻¹ᵁ W y = (tW s t W hinv x ≫ (W x).ι) ⁻¹ᵁ W y
  rw [morphismRestrict_ι, tW_ι]
  change (s ⁻¹ᵁ W x).ι ⁻¹ᵁ (s ⁻¹ᵁ W y) = (s ⁻¹ᵁ W x).ι ⁻¹ᵁ (t ⁻¹ᵁ W y)
  rw [hinv y]

private noncomputable def V (x y : X) : (Yloc s t W hinv loc x).Opens :=
  imageOpens (p := ploc s t W hinv loc x) ((W x).ι ⁻¹ᵁ W y)

private lemma preimage_V (x y : X) :
    ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y = (W x).ι ⁻¹ᵁ W y :=
  preimage_imageOpens (ploc_spec s t W hinv loc x).2.2.2.2.2 _ (inv_overlap s t W hinv x y)

private lemma range_overlap (x y : X) :
    Set.range ((ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ (W x).ι) =
      (W x ⊓ W y : X.Opens) := by
  rw [preimage_V]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    TopologicalSpace.Opens.map_coe, Set.image_preimage_eq_inter_range,
    TopologicalSpace.Opens.coe_inf,
    Set.inter_comm]

variable {s t W hinv}

private lemma hw (x : X) :
    (s ∣_ W x) ≫ ploc s t W hinv loc x = tW s t W hinv x ≫ ploc s t W hinv loc x :=
  (ploc_spec s t W hinv loc x).1

private lemma hpb (x : X) :
    IsPullback (s ∣_ W x) (tW s t W hinv x) (ploc s t W hinv loc x) (ploc s t W hinv loc x) :=
  (ploc_spec s t W hinv loc x).2.2.2.2.2

private noncomputable abbrev pV (x y : X) := ploc s t W hinv loc x ∣_ V s t W hinv loc x y

private noncomputable def coeqV (x y : X) :
    IsColimit (Cofork.ofπ (pV loc x y) (sRes_w (hw loc x) (V s t W hinv loc x y))) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.2.2.2.some

private lemma isPullback_V (x y : X) :
    IsPullback ((s ∣_ W x) ∣_ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y))
      (tRes (hw loc x) (V s t W hinv loc x y)) (pV loc x y) (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.2.2.1

private noncomputable def eX (x y : X) :
    (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y : Scheme.{u}) ≅
      (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _ ≫ (W x).ι) (Scheme.Opens.ι _ ≫ (W y).ι)
    (by rw [range_overlap, range_overlap, inf_comm])

@[reassoc]
private lemma eX_hom_ι (x y : X) :
    (eX loc x y).hom ≫ Scheme.Opens.ι _ ≫ (W y).ι = Scheme.Opens.ι _ ≫ (W x).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private lemma sres_preimage (x y : X) :
    (s ∣_ W x) ⁻¹ᵁ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y) =
      (s ⁻¹ᵁ W x).ι ⁻¹ᵁ (s ⁻¹ᵁ W y) := by
  rw [preimage_V]
  change ((s ∣_ W x) ≫ (W x).ι) ⁻¹ᵁ W y = _
  rw [morphismRestrict_ι]
  rfl

private lemma range_roverlap (x y : X) :
    Set.range (((s ∣_ W x) ⁻¹ᵁ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y)).ι ≫
      (s ⁻¹ᵁ W x).ι) =
      (s ⁻¹ᵁ W x ⊓ s ⁻¹ᵁ W y : R.Opens) := by
  rw [sres_preimage]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    TopologicalSpace.Opens.map_coe, Set.image_preimage_eq_inter_range,
    TopologicalSpace.Opens.coe_inf,
    Set.inter_comm]

private noncomputable def eR (x y : X) :
    ((s ∣_ W x) ⁻¹ᵁ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y) : Scheme.{u}) ≅
      ((s ∣_ W y) ⁻¹ᵁ (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x) : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W x).ι) (Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W y).ι)
    (by rw [range_roverlap, range_roverlap, inf_comm])

@[reassoc]
private lemma eR_hom_ι (x y : X) :
    (eR loc x y).hom ≫ Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W y).ι = Scheme.Opens.ι _ ≫ (s ⁻¹ᵁ W x).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private lemma hs_comm (x y : X) :
    ((s ∣_ W x) ∣_ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y)) ≫ (eX loc x y).hom =
      (eR loc x y).hom ≫ ((s ∣_ W y) ∣_ (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x)) := by
  rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W y).ι), Category.assoc, eX_hom_ι,
    morphismRestrict_ι_assoc, morphismRestrict_ι]
  simp only [Category.assoc]
  rw [morphismRestrict_ι_assoc, morphismRestrict_ι, eR_hom_ι_assoc]

private lemma ht_comm (x y : X) :
    tRes (hw loc x) (V s t W hinv loc x y) ≫ (eX loc x y).hom =
      (eR loc x y).hom ≫ tRes (hw loc y) (V s t W hinv loc y x) := by
  rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W y).ι), Category.assoc, eX_hom_ι,
    tRes_ι_assoc, tW_ι]
  simp only [Category.assoc]
  rw [tRes_ι_assoc, tW_ι, eR_hom_ι_assoc]

private noncomputable def φ (x y : X) :
    (V s t W hinv loc x y : Scheme.{u}) ≅ (V s t W hinv loc y x : Scheme.{u}) :=
  quotIso (coeqV loc x y) (coeqV loc y x) (eR loc x y) (eX loc x y) (hs_comm loc x y)
    (ht_comm loc x y)

@[reassoc]
private lemma pV_φ_hom (x y : X) : pV loc x y ≫ (φ loc x y).hom = (eX loc x y).hom ≫ pV loc y x :=
  π_quotIso_hom _ _ _ _ _ _

private lemma V_self (x : X) : V s t W hinv loc x x = ⊤ := by
  rw [V, Scheme.Opens.ι_preimage_self]
  exact imageOpens_top

private instance epi_pV (x y : X) : Epi (pV loc x y) := by
  have h := restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)
  have : Flat (pV loc x y) := h.2.1
  have : LocallyOfFinitePresentation (pV loc x y) := h.2.2.1
  have : Surjective (pV loc x y) := h.2.2.2.1
  infer_instance

private lemma eX_self (x : X) : (eX loc x x).hom = 𝟙 _ := by
  rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W x).ι), eX_hom_ι, Category.id_comp]

private lemma φ_self (x : X) : (φ loc x x).hom = 𝟙 _ := by
  rw [← cancel_epi (pV loc x x), pV_φ_hom, eX_self, Category.id_comp, Category.comp_id]

end Main



section Core

variable {X R : Scheme.{u}} {s t : R ⟶ X} {W : X → X.Opens}
  {hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x}
  (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p)

private instance isFinite_pV (x y : X) : IsFinite (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).1
private instance flat_pV (x y : X) : Flat (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.1
private instance lfp_pV (x y : X) : LocallyOfFinitePresentation (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.1
private instance surj_pV (x y : X) : Surjective (pV loc x y) :=
  (restrict_pkg (hw loc x) (hpb loc x) (V s t W hinv loc x y)).2.2.2.1

private instance epi_pV_restrict (x y : X) (O : (V s t W hinv loc x y : Scheme.{u}).Opens) :
    Epi (pV loc x y ∣_ O) := by
  have h := restrict_pkg (sRes_w (hw loc x) (V s t W hinv loc x y)) (isPullback_V loc x y) O
  have : Flat (pV loc x y ∣_ O) := h.2.1
  have : LocallyOfFinitePresentation (pV loc x y ∣_ O) := h.2.2.1
  have : Surjective (pV loc x y ∣_ O) := h.2.2.2.1
  infer_instance

private lemma ι_mem_preimage_V {x y z : X} (u : ↑(ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y))
    (hu : ((ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ ploc s t W hinv loc x) u ∈
      V s t W hinv loc x z) :
    (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι u ∈
      ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z :=
  hu

private lemma core_t_inter (x y z : X) :
    (V s t W hinv loc x y).ι ⁻¹ᵁ (V s t W hinv loc x z) ≤
      (φ loc x y).hom ⁻¹ᵁ ((V s t W hinv loc y x).ι ⁻¹ᵁ (V s t W hinv loc y z)) := by
  intro v hv
  obtain ⟨u, rfl⟩ := (pV loc x y).surjective v
  have hv' : ((pV loc x y ≫ (V s t W hinv loc x y).ι) u) ∈ V s t W hinv loc x z := hv
  rw [morphismRestrict_ι] at hv'
  have hu : (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι u ∈
      ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z := hv'
  rw [preimage_V] at hu
  change ((pV loc x y ≫ (φ loc x y).hom) ≫ (V s t W hinv loc y x).ι) u ∈ V s t W hinv loc y z
  rw [pV_φ_hom, Category.assoc, morphismRestrict_ι]
  change ploc s t W hinv loc y (((eX loc x y).hom ≫ Scheme.Opens.ι _) u) ∈
    imageOpens (p := ploc s t W hinv loc y) ((W y).ι ⁻¹ᵁ W z)
  refine le_imageOpens_iff _ _ ?_
  change (((eX loc x y).hom ≫ Scheme.Opens.ι _ ≫ (W y).ι) u) ∈ W z
  rw [eX_hom_ι]
  exact hu

private lemma core_cocycle (x y z : X) :
    ((φ loc x y).hom.resLE ((V s t W hinv loc y x).ι ⁻¹ᵁ (V s t W hinv loc y z))
        ((V s t W hinv loc x y).ι ⁻¹ᵁ (V s t W hinv loc x z)) (core_t_inter loc x y z) ≫
      ((Yloc s t W hinv loc y).restrictRestrictComm (V s t W hinv loc y x)
          (V s t W hinv loc y z)).hom ≫
        ((V s t W hinv loc y z).ι ⁻¹ᵁ (V s t W hinv loc y x)).ι ≫
          (φ loc y z).hom ≫ (V s t W hinv loc z y).ι) =
    ((Yloc s t W hinv loc x).restrictRestrictComm (V s t W hinv loc x y)
        (V s t W hinv loc x z)).hom ≫
      ((V s t W hinv loc x z).ι ⁻¹ᵁ (V s t W hinv loc x y)).ι ≫
        (φ loc x z).hom ≫ (V s t W hinv loc z x).ι := by
  set O : (V s t W hinv loc x y : Scheme.{u}).Opens :=
    (V s t W hinv loc x y).ι ⁻¹ᵁ (V s t W hinv loc x z) with hO
  rw [← cancel_epi (pV loc x y ∣_ O)]
  have hQ : (pV loc x y ∣_ O) ≫ O.ι = (pV loc x y ⁻¹ᵁ O).ι ≫ pV loc x y := morphismRestrict_ι _ _
  have hmem : ∀ u : ↑(pV loc x y ⁻¹ᵁ O),
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι) u ∈
        ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z := by
    intro u
    have h1 : (pV loc x y ⁻¹ᵁ O).ι u ∈ ((pV loc x y ⁻¹ᵁ O : (_ : Scheme.{u}).Opens) : Set _) :=
      (Scheme.Opens.range_ι _).le ⟨u, rfl⟩
    have h2 : (((pV loc x y ⁻¹ᵁ O).ι ≫ pV loc x y ≫ (V s t W hinv loc x y).ι) u) ∈
        V s t W hinv loc x z := h1
    rw [morphismRestrict_ι] at h2
    exact h2
  have hmemW : ∀ u : ↑(pV loc x y ⁻¹ᵁ O),
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ (W x).ι) u ∈
        W z := by
    intro u
    have := hmem u
    rw [preimage_V] at this
    exact this
  let lam₁ : (pV loc x y ⁻¹ᵁ O : Scheme.{u}) ⟶ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z) :=
    IsOpenImmersion.lift (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z).ι
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι) (by
        rintro _ ⟨u, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact hmem u)
  have hlam₁ : lam₁ ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x z).ι =
      (pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι :=
    IsOpenImmersion.lift_fac _ _ _
  let kap : (pV loc x y ⁻¹ᵁ O : Scheme.{u}) ⟶ (W z : Scheme.{u}) :=
    IsOpenImmersion.lift (W z).ι
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ (W x).ι) (by
        rintro _ ⟨u, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact hmemW u)
  have hkap : kap ≫ (W z).ι =
      (pV loc x y ⁻¹ᵁ O).ι ≫ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y).ι ≫ (W x).ι :=
    IsOpenImmersion.lift_fac _ _ _
  let lam₂ : (pV loc x y ⁻¹ᵁ O : Scheme.{u}) ⟶ (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y z) :=
    IsOpenImmersion.lift (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y z).ι
      ((pV loc x y ⁻¹ᵁ O).ι ≫ (eX loc x y).hom ≫
        (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x).ι) (by
        rintro _ ⟨u, rfl⟩
        rw [Scheme.Opens.range_ι]
        change _ ∈ ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y z
        rw [preimage_V]
        change (((pV loc x y ⁻¹ᵁ O).ι ≫ (eX loc x y).hom ≫ Scheme.Opens.ι _ ≫ (W y).ι) u) ∈ W z
        rw [eX_hom_ι]
        exact hmemW u)
  have hlam₂ : lam₂ ≫ (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y z).ι =
      (pV loc x y ⁻¹ᵁ O).ι ≫ (eX loc x y).hom ≫
        (ploc s t W hinv loc y ⁻¹ᵁ V s t W hinv loc y x).ι :=
    IsOpenImmersion.lift_fac _ _ _
  have σx : ((Yloc s t W hinv loc x).restrictRestrictComm (V s t W hinv loc x y)
      (V s t W hinv loc x z)).hom ≫ ((V s t W hinv loc x z).ι ⁻¹ᵁ V s t W hinv loc x y).ι ≫
        (V s t W hinv loc x z).ι = O.ι ≫ (V s t W hinv loc x y).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have σy : ((Yloc s t W hinv loc y).restrictRestrictComm (V s t W hinv loc y x)
      (V s t W hinv loc y z)).hom ≫ ((V s t W hinv loc y z).ι ⁻¹ᵁ V s t W hinv loc y x).ι ≫
        (V s t W hinv loc y z).ι =
      ((V s t W hinv loc y x).ι ⁻¹ᵁ V s t W hinv loc y z).ι ≫ (V s t W hinv loc y x).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have R1 : (pV loc x y ∣_ O) ≫ ((Yloc s t W hinv loc x).restrictRestrictComm (V s t W hinv loc x y)
      (V s t W hinv loc x z)).hom ≫ ((V s t W hinv loc x z).ι ⁻¹ᵁ V s t W hinv loc x y).ι =
      lam₁ ≫ pV loc x z := by
    rw [← cancel_mono (V s t W hinv loc x z).ι]
    simp only [Category.assoc]
    rw [σx, reassoc_of% hQ, morphismRestrict_ι (ploc s t W hinv loc x) (V s t W hinv loc x y),
      morphismRestrict_ι (ploc s t W hinv loc x) (V s t W hinv loc x z), reassoc_of% hlam₁]
  have R3 : lam₁ ≫ (eX loc x z).hom ≫ (ploc s t W hinv loc z ⁻¹ᵁ V s t W hinv loc z x).ι = kap := by
    rw [← cancel_mono (W z).ι]
    simp only [Category.assoc]
    rw [eX_hom_ι, reassoc_of% hlam₁, hkap]
  have R : (pV loc x y ∣_ O) ≫ ((Yloc s t W hinv loc x).restrictRestrictComm (V s t W hinv loc x y)
      (V s t W hinv loc x z)).hom ≫ ((V s t W hinv loc x z).ι ⁻¹ᵁ V s t W hinv loc x y).ι ≫
        (φ loc x z).hom ≫ (V s t W hinv loc z x).ι = kap ≫ ploc s t W hinv loc z := by
    rw [reassoc_of% R1, pV_φ_hom_assoc,
      morphismRestrict_ι (ploc s t W hinv loc z) (V s t W hinv loc z x), reassoc_of% R3]
  have L1 : (pV loc x y ∣_ O) ≫
      (φ loc x y).hom.resLE ((V s t W hinv loc y x).ι ⁻¹ᵁ (V s t W hinv loc y z)) O
        (core_t_inter loc x y z) ≫
      ((Yloc s t W hinv loc y).restrictRestrictComm (V s t W hinv loc y x)
          (V s t W hinv loc y z)).hom ≫ ((V s t W hinv loc y z).ι ⁻¹ᵁ V s t W hinv loc y x).ι =
      lam₂ ≫ pV loc y z := by
    rw [← cancel_mono (V s t W hinv loc y z).ι]
    simp only [Category.assoc]
    rw [σy, Scheme.Hom.resLE_comp_ι_assoc, reassoc_of% hQ, pV_φ_hom_assoc,
      morphismRestrict_ι (ploc s t W hinv loc y) (V s t W hinv loc y x),
      morphismRestrict_ι (ploc s t W hinv loc y) (V s t W hinv loc y z), reassoc_of% hlam₂]
  have L3 : lam₂ ≫ (eX loc y z).hom ≫ (ploc s t W hinv loc z ⁻¹ᵁ V s t W hinv loc z y).ι = kap := by
    rw [← cancel_mono (W z).ι]
    simp only [Category.assoc]
    rw [eX_hom_ι, reassoc_of% hlam₂, eX_hom_ι, hkap]
  have L : (pV loc x y ∣_ O) ≫
      (φ loc x y).hom.resLE ((V s t W hinv loc y x).ι ⁻¹ᵁ (V s t W hinv loc y z)) O
        (core_t_inter loc x y z) ≫
      ((Yloc s t W hinv loc y).restrictRestrictComm (V s t W hinv loc y x)
          (V s t W hinv loc y z)).hom ≫ ((V s t W hinv loc y z).ι ⁻¹ᵁ V s t W hinv loc y x).ι ≫
        (φ loc y z).hom ≫ (V s t W hinv loc z y).ι = kap ≫ ploc s t W hinv loc z := by
    rw [reassoc_of% L1, pV_φ_hom_assoc,
      morphismRestrict_ι (ploc s t W hinv loc z) (V s t W hinv loc z y), reassoc_of% L3]
  rw [L, R]

private noncomputable abbrev core : Scheme.GlueData.MkCore.{u} where
  U := Yloc s t W hinv loc
  V := V s t W hinv loc
  t x y := (φ loc x y).hom
  V_id := V_self loc
  t_id := φ_self loc
  t_inter := core_t_inter loc
  cocycle := core_cocycle loc

private lemma core_J : (core loc).J = X := rfl
private lemma core_U (x : X) : (core loc).U x = Yloc s t W hinv loc x := rfl
private lemma core_V (x y : X) : (core loc).V x y = V s t W hinv loc x y := rfl
private lemma core_t (x y : X) : (core loc).t x y = (φ loc x y).hom := rfl

end Core



section Main56

variable {X R : Scheme.{u}} {s t : R ⟶ X} {W : X → X.Opens} (hxW : ∀ x, x ∈ W x)
  {hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x}
  (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p)

private noncomputable abbrev D := (core loc).glueData

private instance isOpenImmersion_D_ι (x : X) : IsOpenImmersion ((D loc).ι x) :=
  Scheme.GlueData.ι_isOpenImmersion (D loc) (show (core loc).J from x)

private noncomputable def coverW : X.OpenCover :=
  Scheme.Cover.mkOfCovers X (fun x => (W x : Scheme.{u})) (fun x => (W x).ι)
    (fun x => ⟨x, ⟨x, hxW x⟩, rfl⟩)

private lemma coverW_f (x : X) : (coverW hxW).f x = (W x).ι := rfl

private noncomputable def ιY (x : X) : Yloc s t W hinv loc x ⟶ (D loc).glued := (D loc).ι x

private lemma ιY_def (x : X) : ιY loc x = (D loc).ι x := rfl

private instance isOpenImmersion_ιY (x : X) : IsOpenImmersion (ιY loc x) :=
  Scheme.GlueData.ι_isOpenImmersion (D loc) (show (core loc).J from x)

private noncomputable abbrev chart (x : X) : (W x : Scheme.{u}) ⟶ (D loc).glued :=
  ploc s t W hinv loc x ≫ ιY loc x

private noncomputable def liftOverlap {T : Scheme.{u}} (x y : X) (a : T ⟶ (W x : Scheme.{u}))
    (ha : Set.range (a ≫ (W x).ι) ⊆ (W y : Set X)) :
    T ⟶ (ploc s t W hinv loc x ⁻¹ᵁ V s t W hinv loc x y : Scheme.{u}) :=
  IsOpenImmersion.lift (Scheme.Opens.ι _) a (by
    rw [Scheme.Opens.range_ι, preimage_V]
    rintro _ ⟨z, rfl⟩
    exact ha ⟨z, rfl⟩)

@[reassoc]
private lemma liftOverlap_ι {T : Scheme.{u}} (x y : X) (a : T ⟶ (W x : Scheme.{u}))
    (ha : Set.range (a ≫ (W x).ι) ⊆ (W y : Set X)) :
    liftOverlap loc x y a ha ≫ Scheme.Opens.ι _ = a :=
  IsOpenImmersion.lift_fac _ _ _

private lemma chart_comp_eq {T : Scheme.{u}} (x y : X) (a : T ⟶ (W x : Scheme.{u}))
    (b : T ⟶ (W y : Scheme.{u})) (hab : a ≫ (W x).ι = b ≫ (W y).ι) :
    a ≫ chart loc x = b ≫ chart loc y := by
  have ha : Set.range (a ≫ (W x).ι) ⊆ (W y : Set X) := by
    rw [hab]; rintro _ ⟨z, rfl⟩; exact (b z).2
  have hb : Set.range (b ≫ (W y).ι) ⊆ (W x : Set X) := by
    rw [← hab]; rintro _ ⟨z, rfl⟩; exact (a z).2
  let a' := liftOverlap loc x y a ha
  let b' := liftOverlap loc y x b hb
  have hab' : a' ≫ (eX loc x y).hom = b' := by
    rw [← cancel_mono (Scheme.Opens.ι _ ≫ (W y).ι), Category.assoc, eX_hom_ι,
      liftOverlap_ι_assoc, liftOverlap_ι_assoc, hab]
  calc a ≫ chart loc x
      = a' ≫ Scheme.Opens.ι _ ≫ ploc s t W hinv loc x ≫ ιY loc x := by
        rw [liftOverlap_ι_assoc]
    _ = a' ≫ pV loc x y ≫ (V s t W hinv loc x y).ι ≫ ιY loc x := by
        rw [← morphismRestrict_ι_assoc (ploc s t W hinv loc x) (V s t W hinv loc x y)]
    _ = a' ≫ pV loc x y ≫ (φ loc x y).hom ≫ (V s t W hinv loc y x).ι ≫ ιY loc y := by
        have := (core loc).t_ι_ι x y
        simp only [core_V] at this
        rw [show (V s t W hinv loc x y).ι ≫ ιY loc x =
          (φ loc x y).hom ≫ (V s t W hinv loc y x).ι ≫ ιY loc y from this.symm]
    _ = b' ≫ pV loc y x ≫ (V s t W hinv loc y x).ι ≫ ιY loc y := by
        rw [pV_φ_hom_assoc, ← Category.assoc, hab']
    _ = b ≫ chart loc y := by
        rw [morphismRestrict_ι_assoc (ploc s t W hinv loc y) (V s t W hinv loc y x),
          liftOverlap_ι_assoc]

private noncomputable def pglued : X ⟶ (D loc).glued :=
  (coverW hxW).glueMorphisms (fun x => chart loc x) fun x y =>
    chart_comp_eq loc x y _ _ pullback.condition

private lemma ι_pglued (x : X) : (W x).ι ≫ pglued hxW loc = chart loc x :=
  (coverW hxW).ι_glueMorphisms _ _ x

private lemma s_pglued : s ≫ pglued hxW loc = t ≫ pglued hxW loc := by
  let 𝒰 : R.OpenCover := Scheme.Cover.mkOfCovers X (fun x => (s ⁻¹ᵁ W x : Scheme.{u}))
    (fun x => (s ⁻¹ᵁ W x).ι) (fun r => ⟨s r, ⟨r, hxW (s r)⟩, rfl⟩)
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun (x : X) => ?_
  change (s ⁻¹ᵁ W x).ι ≫ s ≫ pglued hxW loc = (s ⁻¹ᵁ W x).ι ≫ t ≫ pglued hxW loc
  rw [← morphismRestrict_ι_assoc, ι_pglued hxW loc x, ← tW_ι_assoc s t W hinv,
    ι_pglued hxW loc x, chart,
    ← Category.assoc, hw loc x]
  simp only [tW, Category.assoc]

private lemma preimage_chart (x : X) :
    pglued hxW loc ⁻¹ᵁ ((D loc).ι x).opensRange = (W x).ι.opensRange := by
  ext z
  rw [Scheme.Opens.opensRange_ι]
  constructor
  · intro hz
    change pglued hxW loc z ∈ Set.range ((D loc).ι x) at hz
    have hzW : z ∈ W z := hxW z
    have hpz : pglued hxW loc z = (D loc).ι z (ploc s t W hinv loc z ⟨z, hzW⟩) := by
      have h := congrArg (fun φ : (W z : Scheme.{u}) ⟶ _ => φ ⟨z, hzW⟩) (ι_pglued hxW loc z)
      exact h
    rw [hpz] at hz
    have : ploc s t W hinv loc z ⟨z, hzW⟩ ∈ ((D loc).ι z) ⁻¹ᵁ ((D loc).ι x).opensRange := hz
    rw [(core loc).preimage_opensRange] at this
    have : (⟨z, hzW⟩ : (W z : Scheme.{u})) ∈ ploc s t W hinv loc z ⁻¹ᵁ V s t W hinv loc z x := this
    rw [preimage_V] at this
    exact this
  · intro hz
    change pglued hxW loc z ∈ Set.range ((D loc).ι x)
    refine ⟨ploc s t W hinv loc x ⟨z, hz⟩, ?_⟩
    have h := congrArg (fun φ : (W x : Scheme.{u}) ⟶ _ => φ ⟨z, hz⟩) (ι_pglued hxW loc x)
    exact h.symm

private lemma isPullback_chart (x : X) :
    IsPullback (ploc s t W hinv loc x) (W x).ι (ιY loc x) (pglued hxW loc) :=
  IsOpenImmersion.isPullback (ploc s t W hinv loc x) (W x).ι (ιY loc x) (pglued hxW loc)
    (ι_pglued hxW loc x) (preimage_chart hxW loc x)

set_option backward.isDefEq.respectTransparency.types false in
private lemma isFinite_pglued : IsFinite (pglued hxW loc) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) (D loc).openCover]
  change ∀ x : X, _
  intro x
  change IsFinite (pullback.snd (pglued hxW loc) (ιY loc x))
  erw [← (isPullback_chart hxW loc x).flip.isoPullback_inv_snd]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
private lemma flat_pglued : Flat (pglued hxW loc) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) (D loc).openCover]
  change ∀ x : X, _
  intro x
  change Flat (pullback.snd (pglued hxW loc) (ιY loc x))
  erw [← (isPullback_chart hxW loc x).flip.isoPullback_inv_snd]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
private lemma lfp_pglued : LocallyOfFinitePresentation (pglued hxW loc) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFinitePresentation) (D loc).openCover]
  change ∀ x : X, _
  intro x
  change LocallyOfFinitePresentation (pullback.snd (pglued hxW loc) (ιY loc x))
  erw [← (isPullback_chart hxW loc x).flip.isoPullback_inv_snd]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
private lemma surjective_pglued : Surjective (pglued hxW loc) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Surjective) (D loc).openCover]
  change ∀ x : X, _
  intro x
  change Surjective (pullback.snd (pglued hxW loc) (ιY loc x))
  erw [← (isPullback_chart hxW loc x).flip.isoPullback_inv_snd]
  infer_instance

private lemma isPullback_pglued : IsPullback s t (pglued hxW loc) (pglued hxW loc) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (coverW hxW) fun x => ?_
  dsimp only [Scheme.Cover.pullbackHom, Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_f, coverW_f, coverW,
    Scheme.Cover.mkOfCovers_X, Scheme.Cover.mkOfCovers_f]
  have K : IsPullback (s ∣_ W x) (tW s t W hinv x ≫ (W x).ι) ((W x).ι ≫ pglued hxW loc)
      (pglued hxW loc) := by
    rw [ι_pglued hxW loc x]
    exact (hpb loc x).paste_vert (isPullback_chart hxW loc x)
  have hsq := (isPullback_morphismRestrict s (W x)).flip
  refine IsPullback.of_iso K hsq.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · erw [Iso.refl_hom, Category.comp_id]
    exact hsq.isoPullback_hom_snd.symm
  · erw [Iso.refl_hom, Category.comp_id, tW_ι, ← Category.assoc, hsq.isoPullback_hom_fst]
  · erw [Iso.refl_hom, Iso.refl_hom, Category.comp_id]
  · erw [Iso.refl_hom, Iso.refl_hom, Category.comp_id]

include hxW loc in
private theorem main :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  have := isFinite_pglued hxW loc
  have := flat_pglued hxW loc
  have := lfp_pglued hxW loc
  have := surjective_pglued hxW loc
  have hk : IsKernelPair (pglued hxW loc) s t := isPullback_pglued hxW loc
  exact ⟨_, pglued hxW loc, s_pglued hxW loc, inferInstance, inferInstance, inferInstance,
    inferInstance, isPullback_pglued hxW loc, ⟨hk.toCoequalizer (regularEpiOfEffectiveEpi _)⟩⟩

end Main56

end AlgebraicGeometry.Scheme.QuotGlue

namespace AlgebraicGeometry.Scheme

/-- Local finite locally free quotients on an invariant open cover glue: if every point
`x` lies in an invariant open `W x` on which the restriction of `s t : R ⟶ X` has a finite
locally free surjective quotient with kernel pair the restricted relation, then so
does `X`, and the quotient map is the coequalizer of `s` and `t`. -/
public theorem exists_quotient_of_forall_exists_quotient_restrict
    {X R : Scheme.{u}} (s t : R ⟶ X)
    (W : X → X.Opens) (hxW : ∀ x, x ∈ W x) (hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x)
    (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) :=
  QuotGlue.main hxW loc

end AlgebraicGeometry.Scheme
