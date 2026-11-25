/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalAdjacentCore
public import MathlibExt.Algebra.Homology.PartialTotalConnectingHorizontal
public import MathlibExt.Algebra.Homology.PartialTotalFirstPageDifferential
public import MathlibExt.Algebra.Homology.PartialTotalSignedRowHomology
public import MathlibExt.Algebra.Homology.VerticalHomologyComplex
public import MathlibExt.Algebra.Homology.HomotopyCategory.MappingConeCompHomology
public import MathlibExt.Algebra.Homology.Embedding.RestrictionHomology

/-!
# The second page of a partial-total spectral sequence

This file identifies the fixed-row part of the first page with the signed
horizontal complex of vertical homology objects, and consequently identifies
the second page with horizontal homology of vertical homology.

The sign in the first-page horizontal differential is retained explicitly:
in vertical degree `q` it is multiplication by `ε(q)`.  A canonical complex
isomorphism removes this constant sign only after the signed complex has been
constructed.

No Tor, Cartan--Eilenberg, convergence, abutment, or boundedness statement is
made.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ComposableArrows

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

private theorem partialTotalHomologyFactors_inv_naturality
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).inv.app K ≫
        (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
          HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).map f =
      HomologicalComplex.homologyMap f n ≫
        (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).inv.app L := by
  simpa only [HomologicalComplex.homologyFunctor_map] using
    ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).inv.naturality f).symm

private theorem partialTotalHomologyFactors_hom_naturality
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).map f ≫
        (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.app L =
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.app K ≫
        HomologicalComplex.homologyMap f n := by
  simpa only [HomologicalComplex.homologyFunctor_map] using
    (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.naturality f

private theorem partialTotalConeSpectralHMap
    {D E : ComposableArrows (CochainComplex C ℤ) 1} (φ : D ⟶ E) (n : ℤ) :
    (((HomotopyCategory.spectralObjectMappingCone C).mapHomologicalFunctor
        (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0)).H n).map φ =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).map
          ((HomotopyCategory.composableArrowsFunctor C).map φ) := rfl

private theorem partialTotalSpectralδ_precompose
    {J : Type*} [Category J] (Y : CategoryTheory.Abelian.SpectralObject C J)
    {i j k i' j' k' a b : J}
    (f : i ⟶ j) (g : j ⟶ k) (f' : i' ⟶ j') (g' : j' ⟶ k')
    (α : ComposableArrows.mk₁ f ⟶ ComposableArrows.mk₁ f')
    (β : ComposableArrows.mk₁ g ⟶ ComposableArrows.mk₁ g') {c : a ⟶ b}
    (s : ComposableArrows.mk₁ c ⟶ ComposableArrows.mk₁ g)
    (t : ComposableArrows.mk₁ c ⟶ ComposableArrows.mk₁ g') (ht : t = s ≫ β)
    (n n' : ℤ) (hαβ : α.app 1 = β.app 0) (hn : n + 1 = n') :
    (Y.H n).map s ≫ Y.δ f g n n' hn ≫ (Y.H n').map α =
      (Y.H n).map t ≫ Y.δ f' g' n n' hn := by
  have hδ := Y.δ_naturality f g f' g' α β n n' hαβ hn
  have h := congrArg
    (fun z : (Y.H n).obj (ComposableArrows.mk₁ g) ⟶
        (Y.H n').obj (ComposableArrows.mk₁ f') => (Y.H n).map s ≫ z) hδ.symm
  simpa only [ht, Functor.map_comp, Category.assoc] using h

private theorem partialTotalTransportHomEquality
    {ι : Type*} {X Y : ι → C} (f g : ∀ i, X i ⟶ Y i)
    {i j : ι} (h : i = j) (hj : f j = g j) : f i = g i := by
  subst j
  exact hj

private theorem partialTotalMapEqToIso
    {D E : Type*} [Category D] [Category E] (F : D ⥤ E) {X Y : D} (h : X = Y) :
    F.mapIso (eqToIso h) = eqToIso (congrArg F.obj h) := by
  subst Y
  apply Iso.ext
  simp

/-- The embedding of the fixed vertical-degree row into the increasing
homological first-page shape. -/
def partialTotalFirstPageRowEmbedding (q : ℕ) :
    (ComplexShape.down ℕ).Embedding
      (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩) :=
  ComplexShape.Embedding.mk'
    (ComplexShape.down ℕ)
    (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩)
    (fun p => (p, q))
    (fun _ _ h => by simpa using congrArg Prod.fst h)
    (fun p p' => by
      simp only [ComplexShape.spectralSequenceNat_rel_iff]
      constructor
      · intro h
        change p' + 1 = p at h
        constructor <;> omega
      · rintro ⟨h, _⟩
        change p' + 1 = p
        omega)

@[simp]
theorem partialTotalFirstPageRowEmbedding_f (p q : ℕ) :
    (partialTotalFirstPageRowEmbedding q).f p = (p, q) :=
  rfl

instance (q : ℕ) : (partialTotalFirstPageRowEmbedding q).IsRelIff where
  rel' p p' h := by
    change (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).Rel
      (p, q) (p', q) at h
    change p' + 1 = p
    have hfst : (p : ℤ) + (-1 : ℤ) = p' :=
      ((ComplexShape.spectralSequenceNat_rel_iff
        ⟨(-1 : ℤ), 0⟩ (p, q) (p', q)).mp h).1
    omega

private noncomputable def partialTotalE₁MiddleTransportIso (m q : ℕ) :
    B.partialTotalCochainFiltration.obj ((core).i₂ (m, q)) ≅
      B.partialTotalCochainFiltration.obj ((core).i₁ (m + 1, q)) := by
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  exact eqToIso (congrArg B.partialTotalCochainFiltration.obj hmid)

private noncomputable def partialTotalE₁MiddleTransportRawIso (m q : ℕ) :
    B.partialTotalEIntFiltration.obj ((core).i₂ (m, q)) ≅
      B.partialTotalEIntFiltration.obj ((core).i₁ (m + 1, q)) := by
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  exact eqToIso (congrArg B.partialTotalEIntFiltration.obj hmid)

private theorem partialTotalE₁_middle_iso_raw (m q : ℕ) :
    let e₀ := B.partialTotalE₁StepIso m q
    let e₁ := B.partialTotalE₁StepIso (m + 1) q
    let t := B.partialTotalE₁MiddleTransportRawIso m q
    let eA :
        (B.partialTotalStepShortComplex (m + 1)).X₁ ≅
          (B.partialTotalStepShortComplex m).X₂ :=
      eqToIso (by
        rw [B.partialTotalStepShortComplex_X₁_succ,
          B.partialTotalStepShortComplex_X₂])
    (e₀.app 1).symm ≪≫ t ≪≫ e₁.app 0 = eA.symm := by
  dsimp only
  cases m with
  | zero =>
      apply Iso.ext
      dsimp only [partialTotalE₁StepIso,
        partialTotalE₁StepIsoZero, partialTotalE₁StepIsoSucc,
        partialTotalE₁UpperIso, partialTotalE₁LowerSuccIso,
        partialTotalE₁MiddleTransportRawIso]
      cat_disch
  | succ m =>
      apply Iso.ext
      dsimp only [partialTotalE₁StepIso,
        partialTotalE₁StepIso, partialTotalE₁StepIsoSucc,
        partialTotalE₁UpperIso, partialTotalE₁LowerSuccIso,
        partialTotalE₁MiddleTransportRawIso]
      cat_disch

private theorem partialTotalE₁CochainStepIso_app_one (p q : ℕ) :
    (B.partialTotalE₁CochainStepIso p q).app 1 =
      (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
        ((B.partialTotalE₁StepIso p q).app 1) := by
  let F : ChainComplex C ℕ ⥤ CochainComplex C ℤ :=
    ComplexShape.embeddingDownNat.extendFunctor C
  apply Iso.ext
  dsimp only [partialTotalE₁CochainStepIso,
    CategoryTheory.Functor.mapComposableArrowsObjMk₁Iso]
  change (𝟙 _ ≫ F.map ((B.partialTotalE₁StepIso p q).app 1).hom ≫ 𝟙 _) =
    F.map ((B.partialTotalE₁StepIso p q).app 1).hom
  simp only [Category.id_comp, Category.comp_id]

private theorem partialTotalE₁CochainStepIso_app_zero (p q : ℕ) :
    (B.partialTotalE₁CochainStepIso p q).app 0 =
      (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
        ((B.partialTotalE₁StepIso p q).app 0) := by
  let F : ChainComplex C ℕ ⥤ CochainComplex C ℤ :=
    ComplexShape.embeddingDownNat.extendFunctor C
  apply Iso.ext
  dsimp only [partialTotalE₁CochainStepIso,
    CategoryTheory.Functor.mapComposableArrowsObjMk₁Iso]
  change (𝟙 _ ≫ F.map ((B.partialTotalE₁StepIso p q).app 0).hom ≫ 𝟙 _) =
    F.map ((B.partialTotalE₁StepIso p q).app 0).hom
  simp only [Category.id_comp, Category.comp_id]

private theorem partialTotalE₁MiddleTransportIso_eq_mapIso (m q : ℕ) :
    B.partialTotalE₁MiddleTransportIso m q =
      (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
      (B.partialTotalE₁MiddleTransportRawIso m q) := by
  let F : ChainComplex C ℕ ⥤ CochainComplex C ℤ :=
    ComplexShape.embeddingDownNat.extendFunctor C
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  let hraw : B.partialTotalEIntFiltration.obj ((core).i₂ (m, q)) =
      B.partialTotalEIntFiltration.obj ((core).i₁ (m + 1, q)) :=
    congrArg B.partialTotalEIntFiltration.obj hmid
  dsimp only [partialTotalE₁MiddleTransportIso,
    partialTotalE₁MiddleTransportRawIso]
  change eqToIso (congrArg F.obj hraw) = F.mapIso (eqToIso hraw)
  exact (partialTotalMapEqToIso F hraw).symm

private theorem partialTotalE₁_middle_iso (m q : ℕ) :
    let e₀ := B.partialTotalE₁CochainStepIso m q
    let e₁ := B.partialTotalE₁CochainStepIso (m + 1) q
    let t := B.partialTotalE₁MiddleTransportIso m q
    let eA := B.partialTotalAdjacentStepCochainIso m
    (e₀.app 1).symm ≪≫ t ≪≫ e₁.app 0 = eA.symm := by
  let F : ChainComplex C ℕ ⥤ CochainComplex C ℤ :=
    ComplexShape.embeddingDownNat.extendFunctor C
  dsimp only
  rw [B.partialTotalE₁CochainStepIso_app_one m q,
    B.partialTotalE₁MiddleTransportIso_eq_mapIso m q,
    B.partialTotalE₁CochainStepIso_app_zero (m + 1) q]
  dsimp only [partialTotalAdjacentStepCochainIso]
  have hStep :
      (B.partialTotalStepShortComplex (m + 1)).X₁ =
        (B.partialTotalStepShortComplex m).X₂ :=
    (B.partialTotalStepShortComplex_X₁_succ m).trans
      (B.partialTotalStepShortComplex_X₂ m).symm
  change
    (F.mapIso ((B.partialTotalE₁StepIso m q).app 1)).symm ≪≫
        F.mapIso (B.partialTotalE₁MiddleTransportRawIso m q) ≪≫
        F.mapIso ((B.partialTotalE₁StepIso (m + 1) q).app 0) =
      (F.mapIso (eqToIso hStep)).symm
  simpa only [Functor.mapIso_symm, Functor.mapIso_trans] using
    congrArg F.mapIso (B.partialTotalE₁_middle_iso_raw m q)

private theorem partialTotalE₁CoreSuccessorMap_eq (m q : ℕ) :
    B.partialTotalE₁CoreSuccessorMap m q =
      (B.partialTotalE₁MiddleTransportIso m q).hom ≫
        B.partialTotalCochainFiltration.map
          (homOfLE ((core).le₁₂ (m + 1, q))) := by
  let F := B.partialTotalCochainFiltration
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  dsimp only [partialTotalE₁CoreSuccessorMap,
    partialTotalE₁MiddleTransportIso]
  change F.map _ = eqToHom (congrArg F.obj hmid) ≫ F.map _
  rw [← eqToHom_map F hmid, ← F.map_comp]
  apply F.congr_map
  subsingleton

/-- In adjacent step coordinates, the actual filtration map is the source
coordinate isomorphism followed by the successor-step inclusion. -/
theorem partialTotalE₁AdjacentCochainMap_eq (m q : ℕ) :
    B.partialTotalE₁AdjacentCochainMap m q =
      (B.partialTotalAdjacentStepCochainIso m).inv ≫
        (B.partialTotalStepCochainShortComplex (m + 1)).f := by
  let e₀ := B.partialTotalE₁CochainStepIso m q
  let e₁ := B.partialTotalE₁CochainStepIso (m + 1) q
  let t : B.partialTotalCochainFiltration.obj ((core).i₂ (m, q)) ≅
      B.partialTotalCochainFiltration.obj ((core).i₁ (m + 1, q)) :=
    B.partialTotalE₁MiddleTransportIso m q
  let eA : (B.partialTotalStepCochainShortComplex (m + 1)).X₁ ≅
      (B.partialTotalStepCochainShortComplex m).X₂ := B.partialTotalAdjacentStepCochainIso m
  have hmidIso := B.partialTotalE₁_middle_iso m q
  have hmid : (e₀.app 1).inv ≫ t.hom ≫ (e₁.app 0).hom = eA.inv := by
    change ((e₀.app 1).symm ≪≫ t ≪≫ e₁.app 0).hom = eA.symm.hom
    exact congrArg Iso.hom hmidIso
  have hcore := B.partialTotalE₁CoreSuccessorMap_eq m q
  dsimp only [partialTotalE₁AdjacentCochainMap]
  rw [hcore]
  calc
    (e₀.app 1).inv ≫
          (t.hom ≫ B.partialTotalCochainFiltration.map
            (homOfLE ((core).le₁₂ (m + 1, q)))) ≫
          (e₁.app 1).hom =
        ((e₀.app 1).inv ≫ t.hom ≫ (e₁.app 0).hom) ≫
          (B.partialTotalStepCochainShortComplex (m + 1)).f := by
            have hnat :
                B.partialTotalCochainFiltration.map
                (homOfLE ((core).le₁₂ (m + 1, q))) ≫
                  (e₁.app 1).hom =
              (e₁.app 0).hom ≫
                (B.partialTotalStepCochainShortComplex (m + 1)).f := by
              exact ComposableArrows.naturality' e₁.hom 0 1
            have hnat' := congrArg
              (fun f => (e₀.app 1).inv ≫ t.hom ≫ f) hnat
            simpa only [Category.assoc] using hnat'
    _ = eA.inv ≫
          (B.partialTotalStepCochainShortComplex (m + 1)).f := by
            rw [hmid]

private theorem mappingCone_shiftMap_eq_shortExact
    (R : ShortComplex (CochainComplex C ℤ))
    (hR : R.ShortExact) (n n' : ℤ) (h : n + 1 = n') :
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingCone.triangle R.f).mor₃ n n' (by omega) =
      HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.descShortComplex R) n ≫
        hR.δ n n' h := by
  let fac₀ : (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).obj
        (CochainComplex.mappingCone R.f) ⟶ (CochainComplex.mappingCone R.f).homology n :=
    (HomotopyCategory.homologyFunctorFactors
    C (ComplexShape.up ℤ) n).hom.app
      (CochainComplex.mappingCone R.f)
  let fac₁ : R.X₁.homology n' ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n').obj R.X₁ :=
    (HomotopyCategory.homologyFunctorFactors
    C (ComplexShape.up ℤ) n').inv.app R.X₁
  apply (cancel_epi fac₀).1
  apply (cancel_mono fac₁).1
  have hq := CochainComplex.homologySequenceδ_quotient_mapTriangle_obj
    (CochainComplex.mappingCone.triangle R.f) n n' h
  have hs :=
    CochainComplex.mappingCone.homologySequenceδ_triangleh hR n n' h
  change
    (HomotopyCategory.homologyFunctor C
      (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingCone.triangleh R.f) n n' h =
      fac₀ ≫
        (HomologicalComplex.homologyFunctor C
          (ComplexShape.up ℤ) 0).shiftMap
            (CochainComplex.mappingCone.triangle R.f).mor₃
              n n' (by omega) ≫ fac₁ at hq
  simp only [Category.assoc]
  rw [← hq, hs]

private theorem mappingCone_homologySequenceδ_normalized
    (S : ShortComplex (CochainComplex C ℤ))
    {X : CochainComplex C ℤ} (g : S.X₂ ⟶ X)
    (n n' : ℤ) (h : n + 1 = n') :
    (HomotopyCategory.homologyFunctorFactors
        C (ComplexShape.up ℤ) n).inv.app
          (CochainComplex.mappingCone g) ≫
      (HomotopyCategory.homologyFunctor C
        (ComplexShape.up ℤ) 0).homologySequenceδ
          (CochainComplex.mappingConeCompTriangleh S.f g) n n' h ≫
      (HomotopyCategory.homologyFunctorFactors
        C (ComplexShape.up ℤ) n').hom.app
          (CochainComplex.mappingCone S.f) ≫
      HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.descShortComplex S) n' =
    (HomologicalComplex.homologyFunctor C
        (ComplexShape.up ℤ) 0).shiftMap
          (CochainComplex.mappingCone.triangle g).mor₃
            n n' (by omega) ≫
      HomologicalComplex.homologyMap S.g n' := by
  have h₀ :=
    CochainComplex.mappingCone.homologySequenceδ_mappingConeCompTriangleh_comp_descShortComplex
      S g n n' h
  let facG : (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).obj
        (CochainComplex.mappingCone g) ⟶ (CochainComplex.mappingCone g).homology n :=
    (HomotopyCategory.homologyFunctorFactors
    C (ComplexShape.up ℤ) n).hom.app (CochainComplex.mappingCone g)
  apply (cancel_epi facG).1
  simpa only [facG, Category.assoc, Iso.hom_inv_id_app_assoc] using h₀

private theorem partialTotalE₁_delta_conjugation (m q : ℕ) :
    let T := B.partialTotalStepCochainShortComplex m
    let S := B.partialTotalStepCochainShortComplex (m + 1)
    let g := B.partialTotalE₁AdjacentCochainMap m q
    let n : ℤ := (core).deg (m + 1, q)
    let n' : ℤ := (core).deg (m, q)
    let hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
      change ((m : ℤ) : EInt) =
        ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
      congr 1
      omega
    let γIdx :
        ComposableArrows.mk₁
            (homOfLE (show (core).i₂ (m, q) ≤ (core).i₂ (m + 1, q) by
              change (((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt))
              simp)) ≅
          ComposableArrows.mk₁
            (homOfLE ((core).le₁₂ (m + 1, q))) :=
      ComposableArrows.isoMk₁ (eqToIso hmid) (Iso.refl _)
    let eArrow : ComposableArrows.mk₁ S.f ≅ ComposableArrows.mk₁ g :=
      ComposableArrows.isoMk₁
        (B.partialTotalAdjacentStepCochainIso m) (Iso.refl _) (by
          have hg := B.partialTotalE₁AdjacentCochainMap_eq m q
          change g =
            (B.partialTotalAdjacentStepCochainIso m).inv ≫ S.f at hg
          change S.f ≫ 𝟙 _ =
            (B.partialTotalAdjacentStepCochainIso m).hom ≫ g
          rw [Category.comp_id, hg, Iso.hom_inv_id_assoc])
    let coneMap :=
      (HomotopyCategory.composableArrowsFunctor C).map eArrow.hom
    (B.partialTotalSpectralObjectHStepIso (m + 1) q).inv ≫
        (B.partialTotalSpectralObject.H n).map γIdx.inv ≫
        B.partialTotalSpectralObject.δ
          (homOfLE ((core).le₁₂ (m, q)))
          (homOfLE (show (core).i₂ (m, q) ≤ (core).i₂ (m + 1, q) by
            change (((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt))
            simp)) n n' (by
              dsimp only [n, n',
                CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
              omega) ≫
        (B.partialTotalSpectralObjectHStepIso m q).hom =
      HomologicalComplex.homologyMap coneMap n ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n).inv.app
            (CochainComplex.mappingCone g) ≫
        (HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) 0).homologySequenceδ
            (CochainComplex.mappingConeCompTriangleh T.f g)
              n n' (by
                dsimp only [n, n',
                  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
                omega) ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n').hom.app
            (CochainComplex.mappingCone T.f) := by
  dsimp only
  let T : ShortComplex (CochainComplex C ℤ) := B.partialTotalStepCochainShortComplex m
  let S : ShortComplex (CochainComplex C ℤ) :=
    B.partialTotalStepCochainShortComplex (m + 1)
  let g : T.X₂ ⟶ S.X₂ := B.partialTotalE₁AdjacentCochainMap m q
  let n : ℤ := (core).deg (m + 1, q)
  let n' : ℤ := (core).deg (m, q)
  have hnn' : n + 1 = n' := by
    dsimp only [n, n',
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
    omega
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  let γIdx :
      ComposableArrows.mk₁
          (homOfLE (show (core).i₂ (m, q) ≤ (core).i₂ (m + 1, q) by
            change (((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt))
            simp)) ≅
        ComposableArrows.mk₁ (homOfLE ((core).le₁₂ (m + 1, q))) :=
    ComposableArrows.isoMk₁ (eqToIso hmid) (Iso.refl _)
  let D₀ : ComposableArrows (CochainComplex C ℤ) 2 :=
    B.partialTotalE₁AdjacentCoreDiagram m q
  let D₁ : ComposableArrows (CochainComplex C ℤ) 2 :=
    B.partialTotalE₁AdjacentStepDiagram m q
  let d₀₀₁ : B.partialTotalCochainFiltration.obj ((core).i₁ (m, q)) ⟶
      B.partialTotalCochainFiltration.obj ((core).i₂ (m, q)) :=
    D₀.map' 0 1 (by omega) (by omega)
  let d₀₁₂ : B.partialTotalCochainFiltration.obj ((core).i₂ (m, q)) ⟶
      B.partialTotalCochainFiltration.obj ((core).i₂ (m + 1, q)) :=
    D₀.map' 1 2 (by omega) (by omega)
  let d₁₀₁ : T.X₁ ⟶ T.X₂ := D₁.map' 0 1 (by omega) (by omega)
  let d₁₁₂ : T.X₂ ⟶ S.X₂ := D₁.map' 1 2 (by omega) (by omega)
  let E : D₀ ≅ D₁ := B.partialTotalE₁AdjacentDiagramIso m q
  let α : ComposableArrows.mk₁ d₀₀₁ ⟶ ComposableArrows.mk₁ d₁₀₁ :=
    (ComposableArrows.functorArrows (CochainComplex C ℤ) 0 1 2).map E.hom
  let β : ComposableArrows.mk₁ d₀₁₂ ⟶ ComposableArrows.mk₁ d₁₁₂ :=
    (ComposableArrows.functorArrows (CochainComplex C ℤ) 1 2 2).map E.hom
  let Y : CategoryTheory.Abelian.SpectralObject C (CochainComplex C ℤ) :=
    (HomotopyCategory.spectralObjectMappingCone C).mapHomologicalFunctor
      (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0)
  let e₀ := B.partialTotalE₁CochainStepIso m q
  let e₁ := B.partialTotalE₁CochainStepIso (m + 1) q
  let t : B.partialTotalCochainFiltration.obj ((core).i₂ (m, q)) ≅
      B.partialTotalCochainFiltration.obj ((core).i₁ (m + 1, q)) :=
    B.partialTotalE₁MiddleTransportIso m q
  let eA : S.X₁ ≅ T.X₂ := B.partialTotalAdjacentStepCochainIso m
  let eArrow : ComposableArrows.mk₁ S.f ≅ ComposableArrows.mk₁ g :=
    ComposableArrows.isoMk₁ eA (Iso.refl _) (by
      have hg := B.partialTotalE₁AdjacentCochainMap_eq m q
      change g = eA.inv ≫ S.f at hg
      change S.f ≫ 𝟙 _ = eA.hom ≫ g
      rw [Category.comp_id, hg, Iso.hom_inv_id_assoc])
  let coneMap : CochainComplex.mappingCone S.f ⟶
      CochainComplex.mappingCone g :=
    (HomotopyCategory.composableArrowsFunctor C).map eArrow.hom
  have hα : α = e₀.hom := by
    apply ComposableArrows.hom_ext₁
    · rfl
    · rfl
  let γ :
      (ComposableArrows.functorArrows
          (CochainComplex C ℤ) 1 2 2).obj D₀ ≅
        ComposableArrows.mk₁
          (B.partialTotalCochainFiltration.map
            (homOfLE ((core).le₁₂ (m + 1, q)))) :=
    ComposableArrows.isoMk₁ t (Iso.refl _) (by
      have hcore := B.partialTotalE₁CoreSuccessorMap_eq m q
      change d₀₁₂ ≫ 𝟙 _ =
        t.hom ≫ B.partialTotalCochainFiltration.map
          (homOfLE ((core).le₁₂ (m + 1, q)))
      rw [Category.comp_id]
      exact hcore)
  let eSource : ComposableArrows.mk₁ d₀₁₂ ≅ ComposableArrows.mk₁ S.f := γ ≪≫ e₁
  let eRight : ComposableArrows.mk₁ d₀₁₂ ≅ ComposableArrows.mk₁ d₁₁₂ :=
    (ComposableArrows.functorArrows (CochainComplex C ℤ) 1 2 2).mapIso E
  have hSourceβ : eSource.symm ≪≫ eRight = eArrow := by
    apply Iso.ext
    apply ComposableArrows.hom_ext₁
    · change ComposableArrows.app' eSource.inv 0 ≫
        ComposableArrows.app' eRight.hom 0 =
          ComposableArrows.app' eArrow.hom 0
      have hs : ComposableArrows.app' eSource.inv 0 =
          (e₁.app 0).inv ≫ t.inv := rfl
      have hr : ComposableArrows.app' eRight.hom 0 =
          (e₀.app 1).hom := by
        dsimp only [eRight, E]
        rfl
      have ha : ComposableArrows.app' eArrow.hom 0 = eA.hom := rfl
      rw [hs, hr, ha]
      have hm := congrArg Iso.inv (B.partialTotalE₁_middle_iso m q)
      dsimp only [e₀, e₁, t, eA] at hm ⊢
      simpa only [Iso.trans_inv, Iso.symm_inv,
        Category.assoc] using hm
    · change ComposableArrows.app' eSource.inv 1 ≫
        ComposableArrows.app' eRight.hom 1 =
          ComposableArrows.app' eArrow.hom 1
      have hs : ComposableArrows.app' eSource.inv 1 =
          (e₁.app 1).inv := by
        dsimp only [eSource, γ, Iso.trans_inv]
        change (e₁.app 1).inv ≫ 𝟙 _ = (e₁.app 1).inv
        simp only [Category.comp_id]
      have hr : ComposableArrows.app' eRight.hom 1 =
          (e₁.app 1).hom := by
        dsimp only [eRight, E]
        rfl
      have ha : ComposableArrows.app' eArrow.hom 1 = 𝟙 _ := rfl
      rw [hs, hr, ha, Iso.inv_hom_id]
  let sourceMap : CochainComplex.mappingCone S.f ⟶
      CochainComplex.mappingCone d₀₁₂ :=
    (HomotopyCategory.composableArrowsFunctor C).map eSource.inv
  let targetMap : CochainComplex.mappingCone d₀₀₁ ⟶
      CochainComplex.mappingCone T.f :=
    (HomotopyCategory.composableArrowsFunctor C).map α
  have hδ := Y.δ_naturality
    d₀₀₁ d₀₁₂ d₁₀₁ d₁₁₂
    α β n n' (by rfl) hnn'
  have hHomotopy :
      (Y.H n).map eSource.inv ≫
          Y.δ d₀₀₁ d₀₁₂ n n' hnn' ≫
          (Y.H n').map α =
        (Y.H n).map eArrow.hom ≫
          Y.δ d₁₀₁ d₁₁₂ n n' hnn' := by
    have hSource : eArrow.hom = eSource.inv ≫ β := by
      have h := congrArg Iso.hom hSourceβ
      change eSource.inv ≫ β = eArrow.hom at h
      exact h.symm
    exact partialTotalSpectralδ_precompose Y d₀₀₁ d₀₁₂ d₁₀₁ d₁₁₂
      α β eSource.inv eArrow.hom hSource n n' (by rfl) hnn'
  let F₀ : HomotopyCategory C (ComplexShape.up ℤ) ⥤ C :=
    HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0
  let facS : (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).obj
        (CochainComplex.mappingCone S.f) ⟶ (CochainComplex.mappingCone S.f).homology n :=
    (HomotopyCategory.homologyFunctorFactors
    C (ComplexShape.up ℤ) n).hom.app (CochainComplex.mappingCone S.f)
  let facG : (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).obj
        (CochainComplex.mappingCone g) ⟶ (CochainComplex.mappingCone g).homology n :=
    (HomotopyCategory.homologyFunctorFactors
    C (ComplexShape.up ℤ) n).hom.app (CochainComplex.mappingCone g)
  let facT : (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n').obj
        (CochainComplex.mappingCone T.f) ⟶ (CochainComplex.mappingCone T.f).homology n' :=
    (HomotopyCategory.homologyFunctorFactors
    C (ComplexShape.up ℤ) n').hom.app (CochainComplex.mappingCone T.f)
  have hConeMap :
      (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n).inv.app
            (CochainComplex.mappingCone S.f) ≫
        (Y.H n).map eArrow.hom =
      HomologicalComplex.homologyMap coneMap n ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n).inv.app
            (CochainComplex.mappingCone g) := by
    rw [partialTotalConeSpectralHMap]
    exact partialTotalHomologyFactors_inv_naturality coneMap n
  have hTargetMap :
      (Y.H n').map α ≫ facT =
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n').hom.app
            (CochainComplex.mappingCone d₀₀₁) ≫
          HomologicalComplex.homologyMap targetMap n' := by
    rw [partialTotalConeSpectralHMap]
    exact partialTotalHomologyFactors_hom_naturality targetMap n'
  have hSourceMap :
      (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n).inv.app
            (CochainComplex.mappingCone S.f) ≫
        (Y.H n).map eSource.inv =
      HomologicalComplex.homologyMap sourceMap n ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n).inv.app
            (CochainComplex.mappingCone d₀₁₂) := by
    rw [partialTotalConeSpectralHMap]
    exact partialTotalHomologyFactors_inv_naturality sourceMap n
  have hHomotopy' := congrArg
    (fun k : (Y.H n).obj (ComposableArrows.mk₁ S.f) ⟶
        (Y.H n').obj (ComposableArrows.mk₁ T.f) =>
    (HomotopyCategory.homologyFunctorFactors
      C (ComplexShape.up ℤ) n).inv.app
        (CochainComplex.mappingCone S.f) ≫ k ≫ facT) hHomotopy
  simp only [Category.assoc] at hHomotopy'
  erw [reassoc_of% hSourceMap, hTargetMap,
    reassoc_of% hConeMap] at hHomotopy'
  dsimp only [Y] at hHomotopy'
  change
    HomologicalComplex.homologyMap sourceMap n ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n).inv.app
            (CochainComplex.mappingCone d₀₁₂) ≫
        F₀.homologySequenceδ
          (CochainComplex.mappingConeCompTriangleh
            d₀₀₁ d₀₁₂) n n' hnn' ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n').hom.app
            (CochainComplex.mappingCone d₀₀₁) ≫
        HomologicalComplex.homologyMap targetMap n' =
      HomologicalComplex.homologyMap coneMap n ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n).inv.app
            (CochainComplex.mappingCone g) ≫
        F₀.homologySequenceδ
          (CochainComplex.mappingConeCompTriangleh
            T.f g) n n' hnn' ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n').hom.app
            (CochainComplex.mappingCone T.f)
      at hHomotopy'
  let F : EInt ⥤ CochainComplex C ℤ := B.partialTotalCochainFiltration
  let fIdx : (core).i₁ (m, q) ⟶ (core).i₂ (m, q) :=
    homOfLE ((core).le₁₂ (m, q))
  let gIdx : (core).i₂ (m, q) ⟶ (core).i₂ (m + 1, q) :=
    homOfLE (show (core).i₂ (m, q) ≤
      (core).i₂ (m + 1, q) by
    change (((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt))
    simp)
  let eF := F.mapComposableArrowsObjMk₁Iso fIdx
  let eG := F.mapComposableArrowsObjMk₁Iso gIdx
  have hdF : F.map fIdx = d₀₀₁ := by
    dsimp only [F, fIdx, d₀₀₁, D₀,
      partialTotalE₁AdjacentCoreDiagram]
    convert rfl using 1
    all_goals subsingleton
  have hdG : F.map gIdx = d₀₁₂ := by
    dsimp only [F, gIdx, d₀₁₂, D₀,
      partialTotalE₁AdjacentCoreDiagram]
    convert rfl using 1
    all_goals subsingleton
  let iF : ComposableArrows.mk₁ (F.map fIdx) ≅
      ComposableArrows.mk₁ d₀₀₁ :=
    ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _) (by
      change F.map fIdx ≫ 𝟙 _ = 𝟙 _ ≫ d₀₀₁
      simpa only [Category.comp_id, Category.id_comp] using hdF)
  let iG : ComposableArrows.mk₁ (F.map gIdx) ≅
      ComposableArrows.mk₁ d₀₁₂ :=
    ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _) (by
      change F.map gIdx ≫ 𝟙 _ = 𝟙 _ ≫ d₀₁₂
      simpa only [Category.comp_id, Category.id_comp] using hdG)
  have hiFInv : iF.inv = 𝟙 _ := by
    apply ComposableArrows.hom_ext₁ <;> rfl
  have hiGHom : iG.hom = 𝟙 _ := by
    apply ComposableArrows.hom_ext₁ <;> rfl
  let eFCore := eF ≪≫ iF
  let eGCore := eG ≪≫ iG
  let canonicalMap : F.obj ((core).i₁ (m + 1, q)) ⟶
      F.obj ((core).i₂ (m + 1, q)) := F.map (homOfLE ((core).le₁₂ (m + 1, q)))
  let eC := F.mapComposableArrowsObjMk₁Iso
    (homOfLE ((core).le₁₂ (m + 1, q)))
  have hSourceArrowF :
      e₁.inv ≫ eC.inv ≫
          (F.mapComposableArrows 1).map γIdx.inv ≫ eG.hom =
        eSource.inv := by
    have ht : F.map (eqToHom hmid.symm) = t.inv := by
      dsimp only [t, partialTotalE₁MiddleTransportIso]
      convert CategoryTheory.eqToHom_map F hmid.symm using 1
      all_goals subsingleton
    have he10 : ComposableArrows.app' e₁.inv 0 = (e₁.app 0).inv := rfl
    have he11 : ComposableArrows.app' e₁.inv 1 = (e₁.app 1).inv := rfl
    have heC0 : ComposableArrows.app' eC.inv 0 = 𝟙 _ := rfl
    have heC1 : ComposableArrows.app' eC.inv 1 = 𝟙 _ := rfl
    have hγ0 : ComposableArrows.app'
        ((F.mapComposableArrows 1).map γIdx.inv) 0 =
        F.map (eqToHom hmid.symm) := by
      convert rfl using 1
      all_goals subsingleton
    have hγ1 : ComposableArrows.app'
        ((F.mapComposableArrows 1).map γIdx.inv) 1 = 𝟙 _ := by
      change F.map (𝟙 _) = 𝟙 _
      exact F.map_id _
    have heG0 : ComposableArrows.app' eG.hom 0 = 𝟙 _ := rfl
    have heG1 : ComposableArrows.app' eG.hom 1 = 𝟙 _ := rfl
    have hsrc0 : ComposableArrows.app' eSource.inv 0 =
        (e₁.app 0).inv ≫ t.inv := rfl
    have hsrc1 : ComposableArrows.app' eSource.inv 1 =
        (e₁.app 1).inv ≫ 𝟙 _ := rfl
    apply ComposableArrows.hom_ext₁
    · simp only [NatTrans.comp_app, he10, heC0, hγ0, heG0, hsrc0]
      rw [ht]
      cat_disch
    · simp only [NatTrans.comp_app, he11, heC1, hγ1,
        heG1, hsrc1]
      cat_disch
  have hPrecompGamma :
      (B.partialTotalSpectralObject.H n).map γIdx.inv =
        (Y.H n).map eC.inv ≫
          (Y.H n).map ((F.mapComposableArrows 1).map γIdx.inv) := by
    have hYCInv : (Y.H n).map eC.inv = 𝟙 _ := by
      have hConeC :
          (HomotopyCategory.composableArrowsFunctor C).map eC.inv =
            𝟙 (CochainComplex.mappingCone canonicalMap) := by
        dsimp only [eC, canonicalMap,
          CategoryTheory.Functor.mapComposableArrowsObjMk₁Iso,
          HomotopyCategory.composableArrowsFunctor]
        convert CochainComplex.mappingCone.map_id canonicalMap using 1 <;> rfl
      rw [partialTotalConeSpectralHMap, hConeC]
      exact (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).map_id _
    dsimp only [partialTotalSpectralObject,
      partialTotalHomotopySpectralObject,
      CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor,
      CategoryTheory.Triangulated.SpectralObject.precomp]
    rw [hYCInv, Category.id_comp]
    rfl
  have hSourceFunctor := congrArg (Y.H n).map hSourceArrowF
  simp only [Functor.map_comp] at hSourceFunctor
  have hTargetArrowF : eF.inv ≫ eF.hom ≫ e₀.hom = α := by
    rw [Iso.inv_hom_id_assoc]
    rw [hα]
  have hTargetArrow :
      iF.inv ≫ eF.inv ≫ eF.hom ≫ e₀.hom = α := by
    rw [hiFInv, Category.id_comp]
    exact hTargetArrowF
  let stepInvMap : CochainComplex.mappingCone S.f ⟶
      CochainComplex.mappingCone canonicalMap :=
    (HomotopyCategory.composableArrowsFunctor C).map e₁.inv
  have hStepNatural :
      HomologicalComplex.homologyMap stepInvMap n ≫
          (HomotopyCategory.homologyFunctorFactors C
            (ComplexShape.up ℤ) n).inv.app
              (CochainComplex.mappingCone canonicalMap) =
        (HomotopyCategory.homologyFunctorFactors C
            (ComplexShape.up ℤ) n).inv.app
              (CochainComplex.mappingCone S.f) ≫
          (Y.H n).map e₁.inv := by
    rw [partialTotalConeSpectralHMap]
    exact (partialTotalHomologyFactors_inv_naturality stepInvMap n).symm
  have hSourceCoordinate :
      (B.partialTotalSpectralObjectHStepIso (m + 1) q).inv ≫
          (B.partialTotalSpectralObject.H n).map γIdx.inv ≫
          (Y.H n).map eGCore.hom =
        HomologicalComplex.homologyMap sourceMap n ≫
          (HomotopyCategory.homologyFunctorFactors
            C (ComplexShape.up ℤ) n).inv.app
              (CochainComplex.mappingCone d₀₁₂) := by
    dsimp only [eGCore, Iso.trans_hom]
    rw [hiGHom, Category.comp_id]
    dsimp only [partialTotalSpectralObjectHStepIso,
      partialTotalSpectralObjectHObjIso, Iso.trans_inv]
    simp only [HomologicalComplex.homologyMapIso_inv, Category.assoc]
    change
      HomologicalComplex.homologyMap stepInvMap n ≫
        (HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) n).inv.app
            (CochainComplex.mappingCone canonicalMap) ≫ _ ≫ _ = _
    rw [← Category.assoc, hStepNatural, Category.assoc]
    rw [hPrecompGamma]
    simp only [Category.assoc]
    rw [hSourceFunctor]
    exact hSourceMap
  have hConeFHom :
      (HomotopyCategory.composableArrowsFunctor C).map eF.hom =
        𝟙 (CochainComplex.mappingCone (F.map fIdx)) := by
    dsimp only [eF,
      CategoryTheory.Functor.mapComposableArrowsObjMk₁Iso,
      HomotopyCategory.composableArrowsFunctor]
    convert CochainComplex.mappingCone.map_id (F.map fIdx) using 1 <;> rfl
  let targetBridgeMap : CochainComplex.mappingCone d₀₀₁ ⟶
      CochainComplex.mappingCone (F.map fIdx) :=
    (HomotopyCategory.composableArrowsFunctor C).map
      (eFCore.inv ≫ eF.hom)
  have hTargetBridgeMap_eq :
      targetBridgeMap =
        (HomotopyCategory.composableArrowsFunctor C).map eFCore.inv := by
    dsimp only [targetBridgeMap]
    rw [(HomotopyCategory.composableArrowsFunctor C).map_comp,
      hConeFHom]
    cat_disch
  have hTargetBridgeMap :
      (Y.H n').map eFCore.inv =
        (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
          HomotopyCategory.homologyFunctor C
            (ComplexShape.up ℤ) n').map targetBridgeMap := by
    rw [partialTotalConeSpectralHMap, hTargetBridgeMap_eq]
  have hTargetNatural :
      (Y.H n').map eFCore.inv ≫
          (HomotopyCategory.homologyFunctorFactors C
            (ComplexShape.up ℤ) n').hom.app
              (CochainComplex.mappingCone (F.map fIdx)) =
        (HomotopyCategory.homologyFunctorFactors C
            (ComplexShape.up ℤ) n').hom.app
              (CochainComplex.mappingCone d₀₀₁) ≫
          HomologicalComplex.homologyMap targetBridgeMap n' := by
    rw [hTargetBridgeMap]
    exact partialTotalHomologyFactors_hom_naturality targetBridgeMap n'
  have hTargetBridgeComposite :
      targetBridgeMap ≫
          ((HomotopyCategory.composableArrowsFunctor C).mapIso e₀).hom =
        targetMap := by
    dsimp only [targetBridgeMap, targetMap, Functor.mapIso_hom]
    rw [← (HomotopyCategory.composableArrowsFunctor C).map_comp]
    dsimp only [eFCore, Iso.trans_inv]
    simp only [Category.assoc]
    rw [hTargetArrow]
  have hTargetCoordinate :
      (Y.H n').map eFCore.inv ≫
          (B.partialTotalSpectralObjectHStepIso m q).hom =
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n').hom.app
            (CochainComplex.mappingCone d₀₀₁) ≫
          HomologicalComplex.homologyMap targetMap n' := by
    dsimp only [partialTotalSpectralObjectHStepIso,
      partialTotalSpectralObjectHObjIso, Iso.trans_hom]
    simp only [HomologicalComplex.homologyMapIso_hom]
    erw [reassoc_of% hTargetNatural]
    rw [← HomologicalComplex.homologyMap_comp]
    rw [hTargetBridgeComposite]
  have hDeltaF :
      B.partialTotalSpectralObject.δ fIdx gIdx n n' hnn' =
        (Y.H n).map eG.hom ≫
          Y.δ (F.map fIdx) (F.map gIdx) n n' hnn' ≫
        (Y.H n').map eF.inv := by
    dsimp only [partialTotalSpectralObject,
      partialTotalHomotopySpectralObject]
    rw [CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor_δ]
    dsimp only [partialTotalHomotopySpectralObject,
      CategoryTheory.Triangulated.SpectralObject.triangle,
      CategoryTheory.Triangulated.SpectralObject.precomp,
      CategoryTheory.Triangulated.SpectralObject.δ,
      CategoryTheory.Functor.homologySequenceδ]
    simp only [Pretriangulated.Triangle.mk_mor₃]
    rw [F₀.shiftMap_comp', F₀.shiftMap_comp]
    rfl
  have hδCoreNat := Y.δ_naturality
    (F.map fIdx) (F.map gIdx) d₀₀₁ d₀₁₂
    iF.hom iG.hom n n' (by rfl) hnn'
  have hδCore :
      Y.δ (F.map fIdx) (F.map gIdx) n n' hnn' =
        (Y.H n).map iG.hom ≫
          Y.δ d₀₀₁ d₀₁₂ n n' hnn' ≫
        (Y.H n').map iF.inv := by
    symm
    rw [← Category.assoc, hδCoreNat, Category.assoc,
      ← (Y.H n').map_comp, Iso.hom_inv_id, (Y.H n').map_id,
      Category.comp_id]
  have hDelta :
      B.partialTotalSpectralObject.δ fIdx gIdx n n' hnn' =
        (Y.H n).map eGCore.hom ≫
          Y.δ d₀₀₁ d₀₁₂ n n' hnn' ≫
        (Y.H n').map eFCore.inv := by
    rw [hDeltaF, hδCore]
    dsimp only [eGCore, eFCore, Iso.trans_hom, Iso.trans_inv]
    rw [(Y.H n).map_comp, (Y.H n').map_comp]
    simp only [Category.assoc]
  have hRawDelta :
      Y.δ d₀₀₁ d₀₁₂ n n' hnn' =
        F₀.homologySequenceδ
          (CochainComplex.mappingConeCompTriangleh
            d₀₀₁ d₀₁₂)
            n n' hnn' := by
    rfl
  rw [hDelta]
  simp only [Category.assoc]
  erw [reassoc_of% hSourceCoordinate, hTargetCoordinate]
  rw [hRawDelta]
  exact hHomotopy'

private theorem partialTotalE₁_mappingConeDifferential_eq_connecting
    (m q : ℕ)
    (hnn' : (core).deg (m + 1, q) + 1 = (core).deg (m, q)) :
    let T := B.partialTotalStepCochainShortComplex m
    let S := B.partialTotalStepCochainShortComplex (m + 1)
    let g := B.partialTotalE₁AdjacentCochainMap m q
    let n : ℤ := (core).deg (m + 1, q)
    let n' : ℤ := (core).deg (m, q)
    let eArrow : ComposableArrows.mk₁ S.f ≅ ComposableArrows.mk₁ g :=
      ComposableArrows.isoMk₁
        (B.partialTotalAdjacentStepCochainIso m) (Iso.refl _) (by
          have hg := B.partialTotalE₁AdjacentCochainMap_eq m q
          change g =
            (B.partialTotalAdjacentStepCochainIso m).inv ≫ S.f at hg
          change S.f ≫ 𝟙 _ =
            (B.partialTotalAdjacentStepCochainIso m).hom ≫ g
          rw [Category.comp_id, hg, Iso.hom_inv_id_assoc])
    let coneMap :=
      (HomotopyCategory.composableArrowsFunctor C).map eArrow.hom
    (B.partialTotalStepE₁HomologyIso (m + 1) q).inv ≫
        HomologicalComplex.homologyMap coneMap n ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n).inv.app
            (CochainComplex.mappingCone g) ≫
        (HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) 0).homologySequenceδ
            (CochainComplex.mappingConeCompTriangleh T.f g) n n' hnn' ≫
        (HomotopyCategory.homologyFunctorFactors
          C (ComplexShape.up ℤ) n').hom.app
            (CochainComplex.mappingCone T.f) ≫
        (B.partialTotalStepE₁HomologyIso m q).hom =
      B.partialTotalE₁ConnectingDifferential m q := by
  dsimp only
  let T : ShortComplex (CochainComplex C ℤ) := B.partialTotalStepCochainShortComplex m
  let S : ShortComplex (CochainComplex C ℤ) :=
    B.partialTotalStepCochainShortComplex (m + 1)
  let eA : S.X₁ ≅ T.X₂ := B.partialTotalAdjacentStepCochainIso m
  let g : T.X₂ ⟶ S.X₂ := B.partialTotalE₁AdjacentCochainMap m q
  let hS : S.ShortExact :=
    B.partialTotalStepCochainShortExact (m + 1)
  let hT : T.ShortExact := B.partialTotalStepCochainShortExact m
  let R : ShortComplex (CochainComplex C ℤ) :=
    ShortComplex.mk g S.g (by
      dsimp only [g]
      rw [B.partialTotalE₁AdjacentCochainMap_eq m q,
        Category.assoc, S.zero, comp_zero])
  let eS : S ≅ R :=
    ShortComplex.isoMk eA (Iso.refl _) (Iso.refl _)
      (by
        dsimp only [R]
        have hg := B.partialTotalE₁AdjacentCochainMap_eq m q
        change g = eA.inv ≫ S.f at hg
        change eA.hom ≫ g = S.f ≫ 𝟙 _
        rw [hg, Iso.hom_inv_id_assoc, Category.comp_id])
      (by
        dsimp only [R]
        change (𝟙 S.X₂) ≫ S.g = S.g ≫ 𝟙 S.X₃
        simp only [Category.id_comp, Category.comp_id])
  let hR : R.ShortExact := ShortComplex.shortExact_of_iso eS hS
  let eArrow : ComposableArrows.mk₁ S.f ≅ ComposableArrows.mk₁ g :=
    ComposableArrows.isoMk₁
      (B.partialTotalAdjacentStepCochainIso m) (Iso.refl _) (by
        have hg := B.partialTotalE₁AdjacentCochainMap_eq m q
        change g =
          (B.partialTotalAdjacentStepCochainIso m).inv ≫ S.f at hg
        change S.f ≫ 𝟙 _ =
          (B.partialTotalAdjacentStepCochainIso m).hom ≫ g
        rw [Category.comp_id, hg, Iso.hom_inv_id_assoc])
  let coneMap : CochainComplex.mappingCone S.f ⟶
      CochainComplex.mappingCone g :=
    (HomotopyCategory.composableArrowsFunctor C).map eArrow.hom
  let descS : CochainComplex.mappingCone S.f ⟶ S.X₃ :=
    CochainComplex.mappingCone.descShortComplex S
  let descR : CochainComplex.mappingCone R.f ⟶ R.X₃ :=
    CochainComplex.mappingCone.descShortComplex R
  let descT : CochainComplex.mappingCone T.f ⟶ T.X₃ :=
    CochainComplex.mappingCone.descShortComplex T
  let _ : QuasiIso descS :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hS
  let _ : QuasiIso descR :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hR
  let _ : QuasiIso descT :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hT
  let n : ℤ := (core).deg (m + 1, q)
  let n' : ℤ := (core).deg (m, q)
  have hDescChain : coneMap ≫ descR = descS := by
    have h := CochainComplex.mappingCone.descShortComplex_naturality eS.hom
    change coneMap ≫ descR = descS ≫ eS.hom.τ₃ at h
    have hτ₃ : eS.hom.τ₃ = 𝟙 _ := rfl
    rw [hτ₃, Category.comp_id] at h
    exact h
  have hDesc :
      HomologicalComplex.homologyMap coneMap n ≫
          HomologicalComplex.homologyMap descR n =
        HomologicalComplex.homologyMap descS n := by
    rw [← HomologicalComplex.homologyMap_comp, hDescChain]
  have hδShort :
      hS.δ n n' hnn' ≫ HomologicalComplex.homologyMap eA.hom n' =
        hR.δ n n' hnn' := by
    have h := HomologicalComplex.HomologySequence.δ_naturality
      eS.hom hS hR n n' hnn'
    have hτ₁ : eS.hom.τ₁ = eA.hom := rfl
    have hτ₃ : eS.hom.τ₃ = 𝟙 _ := rfl
    rw [hτ₁, hτ₃, HomologicalComplex.homologyMap_id,
      Category.id_comp] at h
    exact h
  dsimp only [partialTotalStepE₁HomologyIso, Iso.trans_inv,
    Iso.trans_hom]
  simp only [Category.assoc]
  slice_lhs 5 8 =>
    erw [mappingCone_homologySequenceδ_normalized T g n n' hnn']
  erw [mappingCone_shiftMap_eq_shortExact R hR n n' hnn']
  slice_lhs 4 5 => rw [hDesc]
  slice_lhs 3 4 =>
    change (asIso (HomologicalComplex.homologyMap descS n)).inv ≫
      HomologicalComplex.homologyMap descS n
    rw [asIso_inv, IsIso.inv_hom_id]
  simp only [Category.id_comp]
  rw [← hδShort]
  have hn : ComplexShape.embeddingDownNat.f (m + 1 + q) = n := by
    dsimp only [n,
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
    change -((m + 1 + q : ℕ) : ℤ) =
      -((m + 1 : ℕ) : ℤ) - (q : ℤ)
    omega
  have hn' : ComplexShape.embeddingDownNat.f (m + q) = n' := by
    dsimp only [n',
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
    change -((m + q : ℕ) : ℤ) = -(m : ℤ) - (q : ℤ)
    omega
  have hn₀ : n = -((m + 1 + q : ℕ) : ℤ) := by
    dsimp only [n,
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
    omega
  have hn₀' : n' = -((m + q : ℕ) : ℤ) := by
    dsimp only [n',
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
    omega
  let D := { d : ℤ × ℤ //
    ComplexShape.embeddingDownNat.f (m + 1 + q) = d.1 ∧
      ComplexShape.embeddingDownNat.f (m + q) = d.2 }
  let dCore : D := ⟨(n, n'), hn, hn'⟩
  let dNat : D := ⟨
    (-((m + 1 + q : ℕ) : ℤ), -((m + q : ℕ) : ℤ)), rfl, rfl⟩
  have hRel (d : D) : d.1.1 + 1 = d.1.2 := by
    rw [← d.2.1, ← d.2.2]
    change -((m + 1 + q : ℕ) : ℤ) + 1 =
      -((m + q : ℕ) : ℤ)
    omega
  let wholeAt (d : D) :
      (B.totalRow (m + 1)).homology (m + 1 + q) ⟶
        (B.totalRow m).homology (m + q) :=
    ((B.totalRow (m + 1)).extendHomologyIso
        ComplexShape.embeddingDownNat d.2.1).inv ≫
      (HomologicalComplex.homologyMapIso
        (B.partialTotalStepCochainX₃Iso (m + 1)) d.1.1).inv ≫
      hS.δ d.1.1 d.1.2 (hRel d) ≫
      (HomologicalComplex.homologyMapIso eA d.1.2).hom ≫
      HomologicalComplex.homologyMap T.g d.1.2 ≫
      (HomologicalComplex.homologyMapIso
        (B.partialTotalStepCochainX₃Iso m) d.1.2).hom ≫
      ((B.totalRow m).extendHomologyIso
        ComplexShape.embeddingDownNat d.2.2).hom
  have hd : dCore = dNat := by
    apply Subtype.ext
    apply Prod.ext
    · exact hn₀
    · exact hn₀'
  dsimp only [partialTotalE₁ConnectingDifferential]
  have hwhole := congrArg wholeAt hd
  dsimp only [wholeAt, dCore, dNat, D] at hwhole
  simpa only [HomologicalComplex.homologyMapIso_hom,
    Category.assoc] using hwhole

private theorem partialTotalE₁_mappingConeDifferential_eq_connectingAt
    (m q nPlus nZero : ℕ)
    (hPlus : (m + 1) + q = nPlus)
    (hZero : m + q = nZero)
    (hSProof :
      (B.partialTotalStepCochainShortComplex (m + 1)).ShortExact)
    (hν : -((nPlus : ℕ) : ℤ) + 1 = -((nZero : ℕ) : ℤ))
    (hnn' : (core).deg (m + 1, q) + 1 = (core).deg (m, q)) :
    let T := B.partialTotalStepCochainShortComplex m
    let S := B.partialTotalStepCochainShortComplex (m + 1)
    let g := B.partialTotalE₁AdjacentCochainMap m q
    let n : ℤ := (core).deg (m + 1, q)
    let n' : ℤ := (core).deg (m, q)
    let eArrow : ComposableArrows.mk₁ S.f ≅ ComposableArrows.mk₁ g :=
      ComposableArrows.isoMk₁
        (B.partialTotalAdjacentStepCochainIso m) (Iso.refl _) (by
          have hg := B.partialTotalE₁AdjacentCochainMap_eq m q
          change g =
            (B.partialTotalAdjacentStepCochainIso m).inv ≫ S.f at hg
          change S.f ≫ 𝟙 _ =
            (B.partialTotalAdjacentStepCochainIso m).hom ≫ g
          rw [Category.comp_id, hg, Iso.hom_inv_id_assoc])
    let coneMap :=
      (HomotopyCategory.composableArrowsFunctor C).map eArrow.hom
    let eNat := ComplexShape.embeddingDownNat
    let νPlus : ℤ := -((nPlus : ℕ) : ℤ)
    let νZero : ℤ := -((nZero : ℕ) : ℤ)
    let hS : S.ShortExact := hSProof
    let cAt :
        (B.totalRow (m + 1)).homology nPlus ⟶
          (B.totalRow m).homology nZero :=
      ((B.totalRow (m + 1)).extendHomologyIso eNat rfl).inv ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalStepCochainX₃Iso (m + 1)) νPlus).inv ≫
        hS.δ νPlus νZero hν ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalAdjacentStepCochainIso m) νZero).hom ≫
        HomologicalComplex.homologyMap T.g νZero ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalStepCochainX₃Iso m) νZero).hom ≫
        ((B.totalRow m).extendHomologyIso eNat rfl).hom
    (B.partialTotalStepE₁HomologyIsoAt (m + 1) q nPlus hPlus).inv ≫
        (HomologicalComplex.homologyMap coneMap n ≫
          (HomotopyCategory.homologyFunctorFactors
            C (ComplexShape.up ℤ) n).inv.app
              (CochainComplex.mappingCone g) ≫
          (HomotopyCategory.homologyFunctor C
            (ComplexShape.up ℤ) 0).homologySequenceδ
              (CochainComplex.mappingConeCompTriangleh T.f g) n n' hnn' ≫
          (HomotopyCategory.homologyFunctorFactors
            C (ComplexShape.up ℤ) n').hom.app
              (CochainComplex.mappingCone T.f)) ≫
        (B.partialTotalStepE₁HomologyIsoAt m q nZero hZero).hom =
      cAt := by
  subst nPlus
  subst nZero
  have hIsoPlus :
      B.partialTotalStepE₁HomologyIsoAt
          (m + 1) q ((m + 1) + q) rfl =
        B.partialTotalStepE₁HomologyIso (m + 1) q := by
    rfl
  have hIsoZero :
      B.partialTotalStepE₁HomologyIsoAt m q (m + q) rfl =
        B.partialTotalStepE₁HomologyIso m q := by
    rfl
  rw [hIsoPlus, hIsoZero]
  change _ = B.partialTotalE₁ConnectingDifferential m q
  let T := B.partialTotalStepCochainShortComplex m
  let S := B.partialTotalStepCochainShortComplex (m + 1)
  let g := B.partialTotalE₁AdjacentCochainMap m q
  let n : ℤ := (core).deg (m + 1, q)
  let n' : ℤ := (core).deg (m, q)
  let eArrow : ComposableArrows.mk₁ S.f ≅ ComposableArrows.mk₁ g :=
    ComposableArrows.isoMk₁
      (B.partialTotalAdjacentStepCochainIso m) (Iso.refl _) (by
        have hg := B.partialTotalE₁AdjacentCochainMap_eq m q
        change g =
          (B.partialTotalAdjacentStepCochainIso m).inv ≫ S.f at hg
        change S.f ≫ 𝟙 _ =
          (B.partialTotalAdjacentStepCochainIso m).hom ≫ g
        rw [Category.comp_id, hg, Iso.hom_inv_id_assoc])
  let coneMap :=
    (HomotopyCategory.composableArrowsFunctor C).map eArrow.hom
  let HPlus := B.partialTotalStepE₁Homology (m + 1) q
  let HG := HomologicalComplex.homology
    (CochainComplex.mappingCone g) n
  let QG := ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
    HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).obj
      (CochainComplex.mappingCone g))
  let QT := ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
    HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n').obj
      (CochainComplex.mappingCone T.f))
  let HZero := B.partialTotalStepE₁Homology m q
  let a := (B.partialTotalStepE₁HomologyIso (m + 1) q).inv
  let b : HPlus ⟶ HG := HomologicalComplex.homologyMap coneMap n
  let c : HG ⟶ QG := (HomotopyCategory.homologyFunctorFactors
    C (ComplexShape.up ℤ) n).inv.app (CochainComplex.mappingCone g)
  let d : QG ⟶ QT := (HomotopyCategory.homologyFunctor C
    (ComplexShape.up ℤ) 0).homologySequenceδ
      (CochainComplex.mappingConeCompTriangleh T.f g) n n' hnn'
  let e : QT ⟶ HZero := (HomotopyCategory.homologyFunctorFactors
    C (ComplexShape.up ℤ) n').hom.app (CochainComplex.mappingCone T.f)
  let f := (B.partialTotalStepE₁HomologyIso m q).hom
  have hAssoc : (b ≫ c ≫ d ≫ e) ≫ f =
      b ≫ c ≫ d ≫ e ≫ f := by
    simp only [Category.assoc]
  have h :=
    B.partialTotalE₁_mappingConeDifferential_eq_connecting m q hnn'
  dsimp only at h
  change a ≫ ((b ≫ c ≫ d ≫ e) ≫ f) =
    B.partialTotalE₁ConnectingDifferential m q
  rw [hAssoc]
  change a ≫ (b ≫ c ≫ d ≫ e ≫ f) =
    B.partialTotalE₁ConnectingDifferential m q at h
  exact h

/-- The actual first-page row differential is the connecting-map model of the
adjacent filtration steps. -/
@[reassoc]
theorem partialTotalE₁RowDifferential_eq_connecting (m q : ℕ) :
    B.partialTotalE₁RowDifferential m q =
      B.partialTotalE₁ConnectingDifferential m q := by
  let P₁ : HomologicalComplex C
      (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩) :=
    (B.partialTotalSpectralObject.spectralSequence core).page 1
  let n : ℤ := (core).deg (m + 1, q)
  let n' : ℤ := (core).deg (m, q)
  have hnn' : n + 1 = n' := by
    dsimp only [n, n',
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
    omega
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  let γIdx :
      ComposableArrows.mk₁
          (homOfLE (show (core).i₂ (m, q) ≤ (core).i₂ (m + 1, q) by
            change (((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt))
            simp)) ≅
        ComposableArrows.mk₁
          (homOfLE ((core).le₁₂ (m + 1, q))) :=
    ComposableArrows.isoMk₁ (eqToIso hmid) (Iso.refl _)
  have hpage :=
    B.partialTotalSpectralObject.spectralSequence_first_page_d_eq core
      (m + 1, q) (m, q)
      (coreE₁IncreasingHomologicalNat_rel_succ m q)
      ((core).i₁ (m, q)) ((core).i₂ (m, q))
      ((core).i₂ (m + 1, q)) rfl hmid rfl n n' rfl hnn'
  let ePageSource : P₁.X (m + 1, q) ≅
      (B.partialTotalSpectralObject.H n).obj
        (ComposableArrows.mk₁ (homOfLE ((core).le₁₂ (m + 1, q)))) :=
    B.partialTotalSpectralObject.spectralSequenceFirstPageXIso core
      (m + 1, q) ((core).i₁ (m + 1, q))
      ((core).i₂ (m + 1, q)) rfl rfl n rfl
  let ePageSourceCore :=
    B.partialTotalSpectralObject.spectralSequenceFirstPageXIso core
      (m + 1, q) ((core).i₂ (m, q))
      ((core).i₂ (m + 1, q)) hmid rfl n rfl
  have hPageSource :
      ePageSource.inv ≫ ePageSourceCore.hom =
        (B.partialTotalSpectralObject.H n).map γIdx.inv := by
    have hAux (j : EInt) (hj : j = (core).i₁ (m + 1, q)) :
        let γj :
            ComposableArrows.mk₁
                (homOfLE ((core).le₁₂' (m + 1, q) hj rfl)) ≅
              ComposableArrows.mk₁
                (homOfLE ((core).le₁₂ (m + 1, q))) :=
          ComposableArrows.isoMk₁ (eqToIso hj) (Iso.refl _)
        ePageSource.inv ≫
            (B.partialTotalSpectralObject.spectralSequenceFirstPageXIso core
              (m + 1, q) j ((core).i₂ (m + 1, q)) hj rfl n rfl).hom =
          (B.partialTotalSpectralObject.H n).map γj.inv := by
      dsimp only
      subst j
      dsimp only [ePageSource]
      rw [Iso.inv_hom_id]
      rw [← (B.partialTotalSpectralObject.H n).map_id]
      apply (B.partialTotalSpectralObject.H n).congr_map
      subsingleton
    let γMid :
        ComposableArrows.mk₁
            (homOfLE ((core).le₁₂' (m + 1, q) hmid rfl)) ≅
      ComposableArrows.mk₁
            (homOfLE ((core).le₁₂ (m + 1, q))) :=
      ComposableArrows.isoMk₁ (eqToIso hmid) (Iso.refl _)
        (by subsingleton)
    calc
      _ = (B.partialTotalSpectralObject.H n).map γMid.inv := by
        exact hAux ((core).i₂ (m, q)) hmid
      _ = (B.partialTotalSpectralObject.H n).map γIdx.inv := by
        apply (B.partialTotalSpectralObject.H n).congr_map
        apply ComposableArrows.hom_ext₁ <;> subsingleton
  rw [partialTotalE₁RowDifferential, hpage]
  dsimp only [partialTotalSpectralSequenceFirstPageRowIso,
    Iso.trans_inv, Iso.trans_hom]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [hPageSource]
  slice_lhs 5 6 => rw [Iso.inv_hom_id]
  simp only [Category.id_comp]
  slice_lhs 2 5 => erw [B.partialTotalE₁_delta_conjugation m q]
  simpa only [Category.assoc] using
    B.partialTotalE₁_mappingConeDifferential_eq_connecting m q hnn'

/-- The actual first-page row differential is the signed horizontal homology
map. -/
@[reassoc]
theorem partialTotalE₁RowDifferential_eq_horizontalRowHomology
    (m q : ℕ) :
    B.partialTotalE₁RowDifferential m q =
      B.partialTotalHorizontalRowHomology m q :=
  (B.partialTotalE₁RowDifferential_eq_connecting m q).trans
    (B.partialTotalE₁ConnectingDifferential_eq_horizontalRowHomology m q)

/-- The sign-correct complex occurring in the first-page row coordinate.
Its differential is `ε(q)` times the ordinary horizontal differential. -/
noncomputable def signedVerticalHomologyComplex (q : ℕ) :
    ChainComplex C ℕ where
  X p := (B.verticalHomologyComplex q).X p
  d p p' := (ComplexShape.down ℕ).ε q •
    (B.verticalHomologyComplex q).d p p'
  shape p p' h := by
    rw [HomologicalComplex.shape _ _ _ h, smul_zero]
  d_comp_d' p p' p'' hp hp' := by
    simp only [Linear.units_smul_comp, Linear.comp_units_smul,
      HomologicalComplex.d_comp_d, smul_zero]

/-- The signed and ordinary vertical-homology complexes have the same
objects. -/
@[simp]
theorem signedVerticalHomologyComplex_X (p q : ℕ) :
    (B.signedVerticalHomologyComplex q).X p = (B.X p).homology q :=
  rfl

/-- Literal differential formula for the signed vertical-homology complex. -/
@[simp]
theorem signedVerticalHomologyComplex_d (p p' q : ℕ) :
    (B.signedVerticalHomologyComplex q).d p p' =
      (ComplexShape.down ℕ).ε q •
        HomologicalComplex.homologyMap (B.d p p') q :=
  rfl

/-- Multiplication by `ε(q)^p` in horizontal degree `p` removes the constant
sign from the horizontal differential. -/
noncomputable def signedVerticalHomologyIso (q : ℕ) :
    B.signedVerticalHomologyComplex q ≅ B.verticalHomologyComplex q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => ((ComplexShape.down ℕ).ε q) ^ p • Iso.refl _)
    (fun i j hij => by
      change j + 1 = i at hij
      subst i
      change
        (((ComplexShape.down ℕ).ε q) ^ (j + 1) • 𝟙 _) ≫
            (B.verticalHomologyComplex q).d (j + 1) j =
          ((ComplexShape.down ℕ).ε q •
              (B.verticalHomologyComplex q).d (j + 1) j) ≫
            (((ComplexShape.down ℕ).ε q) ^ j • 𝟙 _)
      simp only [Linear.units_smul_comp, Linear.comp_units_smul,
        Category.id_comp, Category.comp_id, smul_smul, pow_succ])

/-- Forward component of the constant-sign-removal isomorphism. -/
@[simp]
theorem signedVerticalHomologyIso_hom_f (p q : ℕ) :
    (B.signedVerticalHomologyIso q).hom.f p =
      ((ComplexShape.down ℕ).ε q) ^ p •
        𝟙 ((B.X p).homology q) := by
  rfl

/-- Inverse component of the constant-sign-removal isomorphism. -/
@[simp]
theorem signedVerticalHomologyIso_inv_f (p q : ℕ) :
    (B.signedVerticalHomologyIso q).inv.f p =
      (((ComplexShape.down ℕ).ε q) ^ p)⁻¹ •
        𝟙 ((B.X p).homology q) := by
  rfl

private theorem epsilon_down_succ (p : ℕ) :
    (ComplexShape.down ℕ).ε (p + 1) =
      -(ComplexShape.down ℕ).ε p := by
  have h := ComplexShape.ε_succ
    (c := ComplexShape.down ℕ)
    (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl)
  have h' := congrArg Neg.neg h
  simpa only [neg_neg] using h'.symm

private theorem epsilon_down_succ_pow (p q : ℕ) :
    ((ComplexShape.down ℕ).ε (p + 1)) ^ q =
      (ComplexShape.down ℕ).ε q *
        ((ComplexShape.down ℕ).ε p) ^ q := by
  simp only [ComplexShape.ε_down_ℕ, pow_add, pow_one, mul_pow]
  rw [mul_comm]

/-- The horizontal bicomplex map between adjacent signed rows. Its component
in vertical degree `q` necessarily carries the sign `ε(q)`. -/
noncomputable def partialTotalHorizontalSignedRowMap (p : ℕ) :
    B.signedRow (p + 1) ⟶ B.signedRow p where
  f q := (ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q
  comm' q q' h := by
    have hp : (ComplexShape.down ℕ).ε (p + 1) =
        -(ComplexShape.down ℕ).ε p := epsilon_down_succ p
    have hq : (ComplexShape.down ℕ).ε q =
        -(ComplexShape.down ℕ).ε q' := by
      have h₀ := ComplexShape.ε_succ (c := ComplexShape.down ℕ) h
      have h₁ := congrArg Neg.neg h₀
      simpa only [neg_neg] using h₁.symm
    change
      ((ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q) ≫
          ((ComplexShape.down ℕ).ε p • (B.X p).d q q') =
        ((ComplexShape.down ℕ).ε (p + 1) •
            (B.X (p + 1)).d q q') ≫
          ((ComplexShape.down ℕ).ε q' • (B.d (p + 1) p).f q')
    simp only [Linear.units_smul_comp,
      Linear.comp_units_smul, smul_smul]
    rw [(B.d (p + 1) p).comm]
    rw [hp, hq]
    have hscalar :
        (ComplexShape.down ℕ).ε p * (-(ComplexShape.down ℕ).ε q') =
          (ComplexShape.down ℕ).ε q' *
            (-(ComplexShape.down ℕ).ε p) := by
      rw [mul_neg, mul_neg, mul_comm]
    rw [hscalar]

@[simp]
theorem partialTotalHorizontalSignedRowMap_f (p q : ℕ) :
    (B.partialTotalHorizontalSignedRowMap p).f q =
      (ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q :=
  rfl

/-- Removing the signed-row coordinates conjugates the signed horizontal map
to the original horizontal bicomplex map. -/
@[reassoc]
theorem partialTotalHorizontalSignedRowMap_comp_signedRowIso (p : ℕ) :
    B.partialTotalHorizontalSignedRowMap p ≫
        (B.signedRowIso p).hom =
      (B.signedRowIso (p + 1)).hom ≫ B.d (p + 1) p := by
  ext q
  change
    ((ComplexShape.down ℕ).ε q • (B.d (p + 1) p).f q) ≫
        (((ComplexShape.down ℕ).ε p) ^ q • 𝟙 _) =
      (((ComplexShape.down ℕ).ε (p + 1)) ^ q • 𝟙 _) ≫
        (B.d (p + 1) p).f q
  simp only [
    Linear.units_smul_comp, Linear.comp_units_smul,
    Category.id_comp, Category.comp_id, smul_smul]
  have hscalar :
      ((ComplexShape.down ℕ).ε p) ^ q *
          (ComplexShape.down ℕ).ε q =
        ((ComplexShape.down ℕ).ε (p + 1)) ^ q := by
    rw [epsilon_down_succ_pow]
    exact mul_comm _ _
  rw [hscalar]

private theorem partialTotalHorizontalRowShift_homology_coordinate
    (p q : ℕ) :
    let ePlus := ComplexShape.embeddingDown'Add 1 (p + 1)
    let eZero := ComplexShape.embeddingDown'Add 1 p
    let NPlus := p + 1 + q
    let NZero := p + q
    let F := B.partialTotalHorizontalSignedRowMap p
    B.partialTotalHorizontalRowHomology p q ≫
        ((B.signedRow p).extendHomologyIso eZero
          (show eZero.f q = NZero by
            change q + p = p + q
            omega)).hom =
      (ComplexShape.down ℕ).ε q •
        (HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap F ePlus) NPlus ≫
          ((B.signedRow p).extendHomologyIso ePlus
            (show ePlus.f q = NPlus by
              change q + (p + 1) = p + 1 + q
              omega)).hom) := by
  dsimp only
  let eNat : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ) :=
    ComplexShape.embeddingDownNat
  let ePlus : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add 1 (p + 1)
  let eZero : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add 1 p
  let NPlus : ℕ := p + 1 + q
  let NZero : ℕ := p + q
  let nPlus : ℤ := -((NPlus : ℕ) : ℤ)
  let nZero : ℤ := -((NZero : ℕ) : ℤ)
  have hNatPlus : eNat.f NPlus = nPlus := rfl
  have hNatZero : eNat.f NZero = nZero := rfl
  have hRowPlus : ePlus.f q = NPlus := by
    change q + (p + 1) = p + 1 + q
    omega
  have hRowZero : eZero.f q = NZero := by
    change q + p = p + q
    omega
  have hN : NZero + 1 = NPlus := by
    dsimp only [NZero, NPlus]
    omega
  have hShift : 1 + nPlus = nZero := by
    dsimp only [nPlus, nZero, NPlus, NZero]
    omega
  have hShiftX : nZero = nPlus + 1 := by
    dsimp only [nPlus, nZero, NPlus, NZero]
    omega
  have hnextPlus : (ComplexShape.up ℤ).next nPlus = nPlus + 1 := by
    exact CochainComplex.next ℤ nPlus
  have hnextZero : (ComplexShape.up ℤ).next nZero = nZero + 1 := by
    exact CochainComplex.next ℤ nZero
  let Kext : CochainComplex C ℤ := (B.totalRow (p + 1)).extend eNat
  let Lext : CochainComplex C ℤ := (B.totalRow p).extend eNat
  let z : Kext ⟶ Lext⟦(1 : ℤ)⟧ := B.partialTotalHorizontalRowShift p
  let F : B.signedRow (p + 1) ⟶ B.signedRow p := B.partialTotalHorizontalSignedRowMap p
  let xRowPlus : (B.totalRow (p + 1)).X NPlus ≅ (B.X (p + 1)).X q :=
    B.totalRowXIso (p + 1) q NPlus (by rfl)
  let xRowZero : (B.totalRow p).X NZero ≅ (B.X p).X q :=
    B.totalRowXIso p q NZero (by rfl)
  let eNatPlus := (B.totalRow (p + 1)).extendHomologyIso
    eNat hNatPlus
  let eNatZero := (B.totalRow p).extendHomologyIso
    eNat hNatZero
  let eRowPlusSource := (B.signedRow (p + 1)).extendHomologyIso
    ePlus hRowPlus
  let eRowZero := (B.signedRow p).extendHomologyIso
    eZero hRowZero
  let eRowPlusTarget := (B.signedRow p).extendHomologyIso
    ePlus hRowPlus
  let cNatPlus := (B.totalRow (p + 1)).extendCyclesIso
    eNat hNatPlus
  let cNatZero := (B.totalRow p).extendCyclesIso eNat hNatZero
  let cRowPlusSource := (B.signedRow (p + 1)).extendCyclesIso
    ePlus hRowPlus
  let cRowZero := (B.signedRow p).extendCyclesIso eZero hRowZero
  rw [B.partialTotalHorizontalRowHomology_eq]
  simp only [Category.assoc]
  change eNatPlus.inv ≫
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        z nPlus nZero (by dsimp [nPlus, nZero, NPlus, NZero]; omega) ≫
      eNatZero.hom ≫ eRowZero.hom =
    (ComplexShape.down ℕ).ε q •
      (HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap F ePlus) NPlus ≫
        eRowPlusTarget.hom)
  rw [← cancel_epi eNatPlus.hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← cancel_epi
    (((B.totalRow (p + 1)).extend eNat).homologyπ nPlus)]
  dsimp only [CategoryTheory.Functor.shiftMap,
    CochainComplex.homologyFunctor_shift]
  have hMapZ :
      (HomologicalComplex.homologyFunctor C
        (ComplexShape.up ℤ) nPlus).map z =
        HomologicalComplex.homologyMap z nPlus :=
    rfl
  rw [hMapZ]
  slice_lhs 1 2 =>
    rw [HomologicalComplex.homologyπ_naturality]
  let x : Kext.cycles nPlus ⟶ (Lext⟦(1 : ℤ)⟧).X nPlus :=
    Kext.iCycles nPlus ≫ z.f nPlus
  have hx : x ≫ (Lext⟦(1 : ℤ)⟧).d nPlus (nPlus + 1) = 0 := by
    dsimp only [x]
    rw [Category.assoc, z.comm, ← Category.assoc,
      Kext.iCycles_d, zero_comp]
  have hcycles :
      HomologicalComplex.cyclesMap z nPlus =
        (Lext⟦(1 : ℤ)⟧).liftCycles x (nPlus + 1) hnextPlus hx := by
    rw [← cancel_mono ((Lext⟦(1 : ℤ)⟧).iCycles nPlus),
      HomologicalComplex.cyclesMap_i,
      HomologicalComplex.liftCycles_i]
  have hz := B.partialTotalHorizontalRowShift_f_comp_shiftIso p NZero
  have hF := B.partialTotalHorizontalRowF_eq p q
  have hIndex : eNat.f (NZero + 1) = nPlus := by
    rw [hN, hNatPlus]
  have hComponent :
      Kext.iCycles nPlus ≫ z.f nPlus ≫
          (CochainComplex.shiftFunctorObjXIso
            Lext 1 nPlus nZero hShiftX).hom ≫
          ((B.totalRow p).extendXIso eNat hNatZero).hom ≫
          xRowZero.hom =
        (ComplexShape.down ℕ).ε q •
          (Kext.iCycles nPlus ≫
            ((B.totalRow (p + 1)).extendXIso eNat hNatPlus).hom ≫
            xRowPlus.hom ≫
            ((ComplexShape.down ℕ).ε q •
              (B.d (p + 1) p).f q)) := by
    let nrPlus := eNat.f (NZero + 1)
    let nrZero := eNat.f NZero
    have hShiftRow : nrZero = nrPlus + 1 := by
      change -((NZero : ℕ) : ℤ) =
        -(((NZero + 1 : ℕ) : ℤ)) + 1
      omega
    let xRowPlus' := B.totalRowXIso (p + 1) q (NZero + 1) (by
      dsimp only [NZero]
      omega)
    have hComponentRow :
        Kext.iCycles nrPlus ≫ z.f nrPlus ≫
            (CochainComplex.shiftFunctorObjXIso
              Lext 1 nrPlus nrZero hShiftRow).hom ≫
            ((B.totalRow p).extendXIso eNat rfl).hom ≫
            xRowZero.hom =
          (ComplexShape.down ℕ).ε q •
            (Kext.iCycles nrPlus ≫
              ((B.totalRow (p + 1)).extendXIso eNat rfl).hom ≫
              xRowPlus'.hom ≫
              ((ComplexShape.down ℕ).ε q •
                (B.d (p + 1) p).f q)) := by
      slice_lhs 2 3 => rw [hz]
      simp only [Category.assoc]
      slice_lhs 4 5 => rw [Iso.inv_hom_id]
      slice_lhs 3 4 => rw [Category.comp_id]
      rw [hF]
      simp only [Category.assoc]
      slice_lhs 5 6 => rw [Iso.inv_hom_id]
      slice_lhs 4 5 => rw [Category.comp_id]
      let g := Kext.iCycles nrPlus ≫
        ((B.totalRow (p + 1)).extendXIso eNat rfl).hom ≫
        xRowPlus'.hom
      have hg : g ≫ (B.d (p + 1) p).f q =
          (ComplexShape.down ℕ).ε q •
            (g ≫ ((ComplexShape.down ℕ).ε q •
              (B.d (p + 1) p).f q)) := by
        rw [Linear.comp_units_smul, smul_smul,
          Int.units_mul_self, one_smul]
      dsimp only [g, xRowPlus', eNat] at hg ⊢
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hg
    let D := {n : ℕ // NZero + 1 = n}
    let dMain : D := ⟨NPlus, hN⟩
    let dRow : D := ⟨NZero + 1, rfl⟩
    let nAt (d : D) : ℤ := eNat.f d.1
    have hShiftAt (d : D) : nZero = nAt d + 1 := by
      change -((NZero : ℕ) : ℤ) = -((d.1 : ℕ) : ℤ) + 1
      have hd := d.2
      omega
    let xRowAt (d : D) := B.totalRowXIso (p + 1) q d.1 (by
      have hd := d.2
      dsimp only [NZero] at hd
      omega)
    let lhsAt (d : D) : Kext.cycles (nAt d) ⟶ (B.X p).X q :=
      Kext.iCycles (nAt d) ≫ z.f (nAt d) ≫
        (CochainComplex.shiftFunctorObjXIso
          Lext 1 (nAt d) nZero (hShiftAt d)).hom ≫
        ((B.totalRow p).extendXIso eNat hNatZero).hom ≫
        xRowZero.hom
    let rhsAt (d : D) : Kext.cycles (nAt d) ⟶ (B.X p).X q :=
      (ComplexShape.down ℕ).ε q •
        (Kext.iCycles (nAt d) ≫
          ((B.totalRow (p + 1)).extendXIso eNat rfl).hom ≫
          (xRowAt d).hom ≫
          ((ComplexShape.down ℕ).ε q •
            (B.d (p + 1) p).f q))
    have hRow : lhsAt dRow = rhsAt dRow := by
      change
        Kext.iCycles nrPlus ≫ z.f nrPlus ≫
            (CochainComplex.shiftFunctorObjXIso
              Lext 1 nrPlus nrZero hShiftRow).hom ≫
            ((B.totalRow p).extendXIso eNat rfl).hom ≫
            xRowZero.hom =
          (ComplexShape.down ℕ).ε q •
            (Kext.iCycles nrPlus ≫
              ((B.totalRow (p + 1)).extendXIso eNat rfl).hom ≫
              xRowPlus'.hom ≫
              ((ComplexShape.down ℕ).ε q •
                (B.d (p + 1) p).f q))
      exact hComponentRow
    have hd : dMain = dRow := by
      apply Subtype.ext
      exact hN.symm
    change lhsAt dMain = rhsAt dMain
    exact partialTotalTransportHomEquality lhsAt rhsAt hd hRow
  have hRowZeroICycles :
      cRowZero.hom ≫ (B.signedRow p).iCycles q =
        (B.totalRow p).iCycles NZero ≫
          xRowZero.hom := by
    simpa only [xRowZero, totalRowXIso, totalRow] using
      (HomologicalComplex.extendCyclesIso_hom_iCycles
        (K := B.signedRow p) (e := eZero) (hj' := hRowZero))
  have hRowPlusICycles :
      cRowPlusSource.hom ≫ (B.signedRow (p + 1)).iCycles q =
        (B.totalRow (p + 1)).iCycles NPlus ≫
          xRowPlus.hom := by
    simpa only [xRowPlus, totalRowXIso, totalRow] using
      (HomologicalComplex.extendCyclesIso_hom_iCycles
        (K := B.signedRow (p + 1)) (e := ePlus) (hj' := hRowPlus))
  have hRowZeroHomologyπ :
      (B.totalRow p).homologyπ NZero ≫ eRowZero.hom =
        cRowZero.hom ≫ (B.signedRow p).homologyπ q := by
    simpa only [totalRow] using
      (HomologicalComplex.homologyπ_extendHomologyIso_hom
        (K := B.signedRow p) (e := eZero) (hj' := hRowZero))
  have hRowPlusHomologyπ :
      (B.totalRow (p + 1)).homologyπ NPlus ≫
          eRowPlusSource.hom =
        cRowPlusSource.hom ≫
          (B.signedRow (p + 1)).homologyπ q := by
    simpa only [totalRow] using
      (HomologicalComplex.homologyπ_extendHomologyIso_hom
        (K := B.signedRow (p + 1)) (e := ePlus) (hj' := hRowPlus))
  have hLeftCycles
      (hy :
        (x ≫ (CochainComplex.shiftFunctorObjXIso
          Lext 1 nPlus nZero hShiftX).hom) ≫
            Lext.d nZero (nZero + 1) = 0) :
      Lext.liftCycles
          (x ≫ (CochainComplex.shiftFunctorObjXIso
            Lext 1 nPlus nZero hShiftX).hom)
          (nZero + 1) hnextZero hy ≫
          cNatZero.hom ≫ cRowZero.hom ≫
          (B.signedRow p).iCycles q =
        x ≫
          (CochainComplex.shiftFunctorObjXIso
            Lext 1 nPlus nZero hShiftX).hom ≫
          ((B.totalRow p).extendXIso eNat hNatZero).hom ≫
          xRowZero.hom := by
    slice_lhs 3 4 => rw [hRowZeroICycles]
    slice_lhs 2 3 =>
      rw [HomologicalComplex.extendCyclesIso_hom_iCycles]
    slice_lhs 1 2 => rw [HomologicalComplex.liftCycles_i]
    dsimp only [Kext]
    simp only [Category.assoc]
  have hRightCycles :
      cNatPlus.hom ≫ cRowPlusSource.hom ≫
          HomologicalComplex.cyclesMap F q ≫
          (B.signedRow p).iCycles q =
        Kext.iCycles nPlus ≫
          ((B.totalRow (p + 1)).extendXIso eNat hNatPlus).hom ≫
          xRowPlus.hom ≫
          ((ComplexShape.down ℕ).ε q •
            (B.d (p + 1) p).f q) := by
    slice_lhs 3 4 => rw [HomologicalComplex.cyclesMap_i]
    slice_lhs 2 3 => rw [hRowPlusICycles]
    slice_lhs 1 2 =>
      rw [HomologicalComplex.extendCyclesIso_hom_iCycles]
    rw [partialTotalHorizontalSignedRowMap_f]
    dsimp only [Kext]
    simp only [Category.assoc]
  have hCycle
      (hy :
        (x ≫ (CochainComplex.shiftFunctorObjXIso
          Lext 1 nPlus nZero hShiftX).hom) ≫
            Lext.d nZero (nZero + 1) = 0) :
      Lext.liftCycles
          (x ≫ (CochainComplex.shiftFunctorObjXIso
            Lext 1 nPlus nZero hShiftX).hom)
          (nZero + 1) hnextZero hy ≫
          cNatZero.hom ≫ cRowZero.hom =
        (ComplexShape.down ℕ).ε q •
          (cNatPlus.hom ≫ cRowPlusSource.hom ≫
            HomologicalComplex.cyclesMap F q) := by
    rw [← cancel_mono ((B.signedRow p).iCycles q)]
    simp only [Category.assoc, Linear.units_smul_comp]
    rw [hLeftCycles, hRightCycles]
    dsimp only [x]
    simpa only [Category.assoc] using hComponent
  have hFextNat :
      HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap F ePlus) NPlus ≫
          eRowPlusTarget.hom =
        eRowPlusSource.hom ≫
          HomologicalComplex.homologyMap F q := by
    exact HomologicalComplex.extendHomologyIso_hom_naturality
      (φ := F) (e := ePlus) (hj' := hRowPlus)
  have hScaledFextNat :
      ((-1 : ℤˣ) ^ q) •
          (HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap F ePlus) NPlus ≫
            eRowPlusTarget.hom) =
        ((-1 : ℤˣ) ^ q) •
          (eRowPlusSource.hom ≫
            HomologicalComplex.homologyMap F q) := by
    exact congrArg (fun f => ((-1 : ℤˣ) ^ q) • f) hFextNat
  have hRightHomology :
      Kext.homologyπ nPlus ≫ eNatPlus.hom ≫
          eRowPlusSource.hom ≫
          HomologicalComplex.homologyMap F q =
        cNatPlus.hom ≫ cRowPlusSource.hom ≫
          HomologicalComplex.cyclesMap F q ≫
          (B.signedRow p).homologyπ q := by
    slice_lhs 1 2 =>
      rw [HomologicalComplex.homologyπ_extendHomologyIso_hom]
    slice_lhs 2 3 => rw [hRowPlusHomologyπ]
    slice_lhs 3 4 =>
      rw [HomologicalComplex.homologyπ_naturality]
  rw [hcycles]
  rw [CochainComplex.liftCycles_shift_homologyπ
    Lext x (nPlus + 1) hnextPlus hx nZero hShift
      (nZero + 1) hnextZero]
  simp only [Category.assoc]
  slice_lhs 3 5 => rw [Iso.inv_hom_id_app_assoc]
  slice_lhs 2 3 =>
    rw [HomologicalComplex.homologyπ_extendHomologyIso_hom]
  simp only [Category.assoc]
  rw [hRowZeroHomologyπ]
  slice_rhs 3 4 => rw [hScaledFextNat]
  simp only [Linear.comp_units_smul]
  rw [hRightHomology]
  slice_lhs 1 3 => rw [hCycle]
  simp only [ComplexShape.ε_down_ℕ, Linear.units_smul_comp,
    Category.assoc]

/-- In the signed-row homology coordinates, the horizontal-row homology map
is the signed differential on the horizontal complex of vertical homology. -/
@[reassoc]
theorem partialTotalHorizontalRowHomology_totalRowHomologyIso
    (p q : ℕ) :
    B.partialTotalHorizontalRowHomology p q ≫
        (B.totalRowHomologyIso p q).hom =
      (B.totalRowHomologyIso (p + 1) q).hom ≫
        (B.signedVerticalHomologyComplex q).d (p + 1) p := by
  let ePlus : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add 1 (p + 1)
  let eZero : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add 1 p
  let NPlus : ℕ := p + 1 + q
  let NZero : ℕ := p + q
  let F : B.signedRow (p + 1) ⟶ B.signedRow p := B.partialTotalHorizontalSignedRowMap p
  have hRowPlus : ePlus.f q = NPlus := by
    change q + (p + 1) = p + 1 + q
    omega
  have hRowZero : eZero.f q = NZero := by
    change q + p = p + q
    omega
  let eRowPlusSource :=
    (B.signedRow (p + 1)).extendHomologyIso ePlus hRowPlus
  let eRowPlusTarget :=
    (B.signedRow p).extendHomologyIso ePlus hRowPlus
  let eRowZero := (B.signedRow p).extendHomologyIso eZero hRowZero
  have hCoordinate :=
    B.partialTotalHorizontalRowShift_homology_coordinate p q
  have hFextNat :
      HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap F ePlus) NPlus ≫
          eRowPlusTarget.hom =
        eRowPlusSource.hom ≫
          HomologicalComplex.homologyMap F q := by
    exact HomologicalComplex.extendHomologyIso_hom_naturality
      (φ := F) (e := ePlus) (hj' := hRowPlus)
  have hMiddle :
      B.partialTotalHorizontalRowHomology p q ≫ eRowZero.hom =
        (ComplexShape.down ℕ).ε q •
          (eRowPlusSource.hom ≫
            HomologicalComplex.homologyMap F q) :=
    hCoordinate.trans
      (congrArg (fun f => (ComplexShape.down ℕ).ε q • f) hFextNat)
  have hSignedHomology :
      HomologicalComplex.homologyMap F q ≫
          (HomologicalComplex.homologyMapIso (B.signedRowIso p) q).hom =
        (HomologicalComplex.homologyMapIso
            (B.signedRowIso (p + 1)) q).hom ≫
          HomologicalComplex.homologyMap (B.d (p + 1) p) q := by
    have h := congrArg
      (fun f => HomologicalComplex.homologyMap f q)
      (B.partialTotalHorizontalSignedRowMap_comp_signedRowIso p)
    simpa only [HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMapIso_hom] using h
  have hTotalZero :
      (B.totalRowHomologyIso p q).hom =
        eRowZero.hom ≫
          (HomologicalComplex.homologyMapIso (B.signedRowIso p) q).hom := by
    rfl
  have hTotalPlus :
      (B.totalRowHomologyIso (p + 1) q).hom =
        eRowPlusSource.hom ≫
          (HomologicalComplex.homologyMapIso
            (B.signedRowIso (p + 1)) q).hom := by
    rfl
  rw [hTotalZero, hTotalPlus, signedVerticalHomologyComplex_d]
  rw [← Category.assoc, hMiddle]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [hSignedHomology]
  simp only [Linear.comp_units_smul]

private theorem partialTotalHorizontalRowHomology_totalRowHomologyIsoAtAux
    (p q nPlus nZero : ℕ)
    (hPlus : (p + 1) + q = nPlus)
    (hZero : p + q = nZero)
    (hShift :
      1 + ComplexShape.embeddingDownNat.f nPlus =
        ComplexShape.embeddingDownNat.f nZero) :
    let eNat := ComplexShape.embeddingDownNat
    let nPlus' : ℤ := eNat.f nPlus
    let nZero' : ℤ := eNat.f nZero
    let rAt :
        (B.totalRow (p + 1)).homology nPlus ⟶
          (B.totalRow p).homology nZero :=
      ((B.totalRow (p + 1)).extendHomologyIso eNat rfl).inv ≫
        (HomologicalComplex.homologyFunctor C
          (ComplexShape.up ℤ) 0).shiftMap
            (B.partialTotalHorizontalRowShift p) nPlus' nZero' hShift ≫
        ((B.totalRow p).extendHomologyIso eNat rfl).hom
    rAt ≫
        (B.totalRowHomologyIsoAt p q nZero hZero).hom =
      (B.totalRowHomologyIsoAt
          (p + 1) q nPlus hPlus).hom ≫
        (B.signedVerticalHomologyComplex q).d (p + 1) p := by
  subst nPlus
  subst nZero
  have hIsoPlus :
      B.totalRowHomologyIsoAt
          (p + 1) q ((p + 1) + q) rfl =
        B.totalRowHomologyIso (p + 1) q := by
    rfl
  have hIsoZero :
      B.totalRowHomologyIsoAt p q (p + q) rfl =
        B.totalRowHomologyIso p q := by
    rfl
  rw [hIsoPlus, hIsoZero]
  change B.partialTotalHorizontalRowHomology p q ≫
      (B.totalRowHomologyIso p q).hom =
    (B.totalRowHomologyIso (p + 1) q).hom ≫
      (B.signedVerticalHomologyComplex q).d (p + 1) p
  exact B.partialTotalHorizontalRowHomology_totalRowHomologyIso p q

private theorem partialTotalHorizontalRowHomology_totalRowHomologyIsoAt
    (p q : ℕ)
    (hPlus : (p + 1) + q = (q + p) + 1)
    (hZero : p + q = q + p) :
    let eNat := ComplexShape.embeddingDownNat
    let NZero := q + p
    let NPlus := NZero + 1
    let nPlus : ℤ := eNat.f NPlus
    let nZero : ℤ := eNat.f NZero
    let rAt :
        (B.totalRow (p + 1)).homology NPlus ⟶
          (B.totalRow p).homology NZero :=
      ((B.totalRow (p + 1)).extendHomologyIso eNat rfl).inv ≫
        (HomologicalComplex.homologyFunctor C
          (ComplexShape.up ℤ) 0).shiftMap
            (B.partialTotalHorizontalRowShift p) nPlus nZero (by
              change 1 + -((NPlus : ℕ) : ℤ) = -((NZero : ℕ) : ℤ)
              omega) ≫
        ((B.totalRow p).extendHomologyIso eNat rfl).hom
    rAt ≫
        (B.totalRowHomologyIsoAt p q NZero hZero).hom =
      (B.totalRowHomologyIsoAt
          (p + 1) q NPlus hPlus).hom ≫
        (B.signedVerticalHomologyComplex q).d (p + 1) p := by
  have hShift :
      1 + ComplexShape.embeddingDownNat.f (q + p + 1) =
        ComplexShape.embeddingDownNat.f (q + p) := by
    change 1 + -((q + p + 1 : ℕ) : ℤ) = -((q + p : ℕ) : ℤ)
    omega
  exact B.partialTotalHorizontalRowHomology_totalRowHomologyIsoAtAux
    p q (q + p + 1) (q + p) hPlus hZero hShift

/-- Restricting the first-page complex to a fixed vertical degree preserves
homology in horizontal degree `p`. -/
noncomputable def partialTotalFirstPageRowRestrictionHomologyIso (p q : ℕ) :
    ((((B.partialTotalSpectralObject.spectralSequence core).page 1).restriction
        (partialTotalFirstPageRowEmbedding q)).homology p) ≅
      ((B.partialTotalSpectralObject.spectralSequence core).page 1).homology
        (p, q) := by
  let P₁ := (B.partialTotalSpectralObject.spectralSequence core).page 1
  let e := partialTotalFirstPageRowEmbedding q
  refine P₁.restrictionHomologyIsoAt e p ?_ ?_
  · apply (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).prev_eq'
    exact e.rel (by
      change p + 1 = (ComplexShape.down ℕ).prev p
      simp)
  · rcases p with _ | p
    · simp only [ChainComplex.next_nat_zero]
      apply (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).next_eq_self'
      intro z hz
      have hfst : (0 : ℤ) + (-1 : ℤ) = z.1 :=
        ((ComplexShape.spectralSequenceNat_rel_iff
          ⟨(-1 : ℤ), 0⟩ (0, q) z).mp hz).1
      omega
    · exact (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).next_eq'
        (e.rel (by
          simp only [ChainComplex.next_nat_succ]
          rfl))

/-- A fixed row of the first page is the signed horizontal complex of
vertical homology objects. -/
noncomputable def partialTotalFirstPageSignedVerticalHomologyIso (q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).restriction
        (partialTotalFirstPageRowEmbedding q) ≅
      B.signedVerticalHomologyComplex q :=
  let P₁ : HomologicalComplex C
      (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩) :=
    (B.partialTotalSpectralObject.spectralSequence core).page 1
  let e : (ComplexShape.down ℕ).Embedding
      (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩) :=
    partialTotalFirstPageRowEmbedding q
  let L : ChainComplex C ℕ := B.signedVerticalHomologyComplex q
  let component (p : ℕ) : (P₁.restriction e).X p ≅ L.X p :=
    B.partialTotalSpectralSequenceFirstPageRowIso p q ≪≫ B.totalRowHomologyIso p q
  HomologicalComplex.Hom.isoOfComponents (C₁ := P₁.restriction e) (C₂ := L)
    component
    (fun i j hij => by
      change j + 1 = i at hij
      subst i
      have hres :
          (P₁.restriction e).d (j + 1) j =
            P₁.d (j + 1, q) (j, q) := by
        rw [P₁.restriction_d_eq e
          (show e.f (j + 1) = (j + 1, q) by rfl)
          (show e.f j = (j, q) by rfl)]
        change
          (𝟙 (P₁.X (j + 1, q))) ≫ P₁.d (j + 1, q) (j, q) ≫
              𝟙 (P₁.X (j, q)) =
            P₁.d (j + 1, q) (j, q)
        simp only [Category.id_comp, Category.comp_id]
      change
        ((B.partialTotalSpectralSequenceFirstPageRowIso (j + 1) q).hom ≫
          (B.totalRowHomologyIso (j + 1) q).hom) ≫
            (B.signedVerticalHomologyComplex q).d (j + 1) j =
          (P₁.restriction e).d (j + 1) j ≫
            ((B.partialTotalSpectralSequenceFirstPageRowIso j q).hom ≫
              (B.totalRowHomologyIso j q).hom)
      rw [hres, B.partialTotalSpectralSequenceFirstPage_d_eq j q]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [B.partialTotalE₁RowDifferential_eq_horizontalRowHomology j q]
      simpa only [Category.assoc] using
        congrArg
          (fun f =>
            (B.partialTotalSpectralSequenceFirstPageRowIso
              (j + 1) q).hom ≫ f)
          (B.partialTotalHorizontalRowHomology_totalRowHomologyIso
            j q).symm)

/-- Forward components of the signed first-page row isomorphism. -/
@[simp]
theorem partialTotalFirstPageSignedVerticalHomologyIso_hom_f (p q : ℕ) :
    (B.partialTotalFirstPageSignedVerticalHomologyIso q).hom.f p =
      (B.partialTotalSpectralSequenceFirstPageRowIso p q).hom ≫
        (B.totalRowHomologyIso p q).hom := by
  rfl

/-- Inverse components of the signed first-page row isomorphism. -/
@[simp]
theorem partialTotalFirstPageSignedVerticalHomologyIso_inv_f (p q : ℕ) :
    (B.partialTotalFirstPageSignedVerticalHomologyIso q).inv.f p =
      (B.totalRowHomologyIso p q).inv ≫
        (B.partialTotalSpectralSequenceFirstPageRowIso p q).inv := by
  rfl

/-- Removing the constant row sign identifies a fixed first-page row with
the ordinary horizontal complex of vertical homology. -/
noncomputable def partialTotalFirstPageVerticalHomologyIso (q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).restriction
        (partialTotalFirstPageRowEmbedding q) ≅
      B.verticalHomologyComplex q :=
  B.partialTotalFirstPageSignedVerticalHomologyIso q ≪≫
    B.signedVerticalHomologyIso q

/-- The explicit `Y.E` coordinate underlying the `(p, q)` object on page two
of the partial-total spectral sequence. -/
noncomputable def partialTotalSpectralSequencePageTwoCoordinate
    (p q : ℕ) : C := by
  let Y := B.partialTotalSpectralObject
  let i₀ : EInt := (((p : ℤ) - 2 : ℤ) : EInt)
  let i₁ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
  let i₂ : EInt := ((p : ℤ) : EInt)
  let i₃ : EInt := (((p : ℤ) + 1 : ℤ) : EInt)
  let n₀ : ℤ := -(p : ℤ) - (q : ℤ) - 1
  let n₁ : ℤ := -(p : ℤ) - (q : ℤ)
  let n₂ : ℤ := -(p : ℤ) - (q : ℤ) + 1
  have hi₀₁ : i₀ ≤ i₁ := by
    dsimp only [i₀, i₁]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₁₂ : i₁ ≤ i₂ := by
    dsimp only [i₁, i₂]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₂₃ : i₂ ≤ i₃ := by
    dsimp only [i₂, i₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hn₁ : n₀ + 1 = n₁ := by omega
  have hn₂ : n₁ + 1 = n₂ := by omega
  exact Y.E (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE hi₂₃)
    n₀ n₁ n₂ hn₁ hn₂

/-- Page two in bidegree `(p, q)` is the explicit literal partial-total
coordinate. -/
noncomputable def partialTotalSpectralSequencePageTwoIso (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page (2 : ℤ)).X
        (p, q) ≅
      B.partialTotalSpectralSequencePageTwoCoordinate p q := by
  let Y := B.partialTotalSpectralObject
  let r : ℤ := 2
  let pq : ℕ × ℕ := (p, q)
  let i₀ : EInt := (((p : ℤ) - 2 : ℤ) : EInt)
  let i₁ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
  let i₂ : EInt := ((p : ℤ) : EInt)
  let i₃ : EInt := (((p : ℤ) + 1 : ℤ) : EInt)
  let n₀ : ℤ := -(p : ℤ) - (q : ℤ) - 1
  let n₁ : ℤ := -(p : ℤ) - (q : ℤ)
  let n₂ : ℤ := -(p : ℤ) - (q : ℤ) + 1
  have hr : (1 : ℤ) ≤ r := by omega
  have h₀ : i₀ = (core).i₀ r pq hr := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
  have h₁ : i₁ = (core).i₁ pq := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁]
  have h₂ : i₂ = (core).i₂ pq := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₂]
  have h₃ : i₃ = (core).i₃ r pq hr := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
    dsimp only [i₃, r, pq]
    congr 1
    omega
  have hn : n₁ = (core).deg pq := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
  have hn₁ : n₀ + 1 = n₁ := by omega
  have hn₂ : n₁ + 1 = n₂ := by omega
  exact Y.spectralSequencePageXIso core r hr pq
    i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ hn
      (hn₁ := hn₁) (hn₂ := hn₂)

/-- Page-one homology in bidegree `(p, q)` identifies with the same explicit
coordinate used for page two. -/
noncomputable def partialTotalSpectralSequencePageOneHomologyCoordinateIso
    (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page (1 : ℤ)).homology
        (p, q) ≅
      B.partialTotalSpectralSequencePageTwoCoordinate p q := by
  let Y := B.partialTotalSpectralObject
  let E := Y.spectralSequence core
  let pq : ℕ × ℕ := (p, q)
  let c₁ := ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩
  let pqPrev : ℕ × ℕ := c₁.prev pq
  let pqNext : ℕ × ℕ := c₁.next pq
  have hpq : c₁.prev pq = pqPrev := rfl
  have hpq' : c₁.next pq = pqNext := rfl
  let r : ℤ := 1
  let r' : ℤ := 2
  have hrr' : r + 1 = r' := by
    dsimp only [r, r']
    omega
  have hr : (1 : ℤ) ≤ r := by
    dsimp only [r]
    omega
  have hr' : (1 : ℤ) ≤ r' := by
    dsimp only [r']
    omega
  let i₀' : EInt := (((p : ℤ) - 2 : ℤ) : EInt)
  let i₀ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
  let i₁ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
  let i₂ : EInt := ((p : ℤ) : EInt)
  let i₃ : EInt := ((p : ℤ) : EInt)
  let i₃' : EInt := (((p : ℤ) + 1 : ℤ) : EInt)
  let n₀ : ℤ := -(p : ℤ) - (q : ℤ) - 1
  let n₁ : ℤ := -(p : ℤ) - (q : ℤ)
  let n₂ : ℤ := -(p : ℤ) - (q : ℤ) + 1
  have hi₀' : i₀' = (core).i₀ r' pq hr' := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
  have hi₀ : i₀ = (core).i₀ r pq hr := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
  have hi₁ : i₁ = (core).i₁ pq := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁]
  have hi₂ : i₂ = (core).i₂ pq := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₂]
  have hi₃ : i₃ = (core).i₃ r pq hr := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
    dsimp only [i₃, r, pq]
    congr 1
    omega
  have hi₃' : i₃' = (core).i₃ r' pq hr' := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
    dsimp only [i₃', r', pq]
    congr 1
    omega
  have hn : n₁ = (core).deg pq := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
  have hn₁ : n₀ + 1 = n₁ := by
    dsimp only [n₀, n₁]
    omega
  have hn₂ : n₁ + 1 = n₂ := by
    dsimp only [n₁, n₂]
  let D :=
    Y.spectralSequenceHomologyData core
      r r' hrr' hr pqPrev pq pqNext hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃'
      hi₀' hi₀ hi₁ hi₂ hi₃ hi₃'
      n₀ n₁ n₂ hn hn₁ hn₂
  exact
    (E.page r).homologyIsoSc' pqPrev pq pqNext hpq hpq' ≪≫
      D.left.homologyIso

/-- The page-one-to-page-two isomorphism in bidegree `(p, q)`, with the bound
witnesses fixed by the displayed source and target pages. -/
noncomputable def partialTotalSpectralSequencePageOneTwoIso (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).homology
        (p, q) ≅
      ((B.partialTotalSpectralObject.spectralSequence core).page 2).X
        (p, q) :=
  B.partialTotalSpectralSequencePageOneHomologyCoordinateIso p q ≪≫
    (B.partialTotalSpectralSequencePageTwoIso p q).symm

/-- In the zero column, the page-one-to-page-two map followed by the shared
page-two coordinate is the page-one homology coordinate. -/
theorem
    partialTotalSpectralSequencePageOneTwoIso_zero_hom_comp_pageTwoIso_hom
    (q : ℕ) :
    (B.partialTotalSpectralSequencePageOneTwoIso 0 q).hom ≫
        (B.partialTotalSpectralSequencePageTwoIso 0 q).hom =
      (B.partialTotalSpectralSequencePageOneHomologyCoordinateIso 0 q).hom := by
  change
    ((B.partialTotalSpectralSequencePageOneHomologyCoordinateIso 0 q).hom ≫
        (B.partialTotalSpectralSequencePageTwoIso 0 q).inv) ≫
          (B.partialTotalSpectralSequencePageTwoIso 0 q).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Page two of the partial-total spectral sequence is horizontal homology
of the vertical-homology complex. -/
noncomputable def partialTotalSecondPageVerticalHomologyIso (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 2).X
        (p, q) ≅
      (B.verticalHomologyComplex q).homology p :=
  (B.partialTotalSpectralSequencePageOneTwoIso p q).symm ≪≫
    (B.partialTotalFirstPageRowRestrictionHomologyIso p q).symm ≪≫
    HomologicalComplex.homologyMapIso
      (B.partialTotalFirstPageVerticalHomologyIso q) p

/-- The page-two vertical-homology coordinate is the page transition followed
by restriction homology and the fixed-row homology comparison. -/
@[reassoc]
theorem partialTotalSecondPageVerticalHomologyIso_hom (p q : ℕ) :
    (B.partialTotalSecondPageVerticalHomologyIso p q).hom =
      (B.partialTotalSpectralSequencePageOneTwoIso p q).inv ≫
        (B.partialTotalFirstPageRowRestrictionHomologyIso p q).inv ≫
        HomologicalComplex.homologyMap
          (B.partialTotalFirstPageVerticalHomologyIso q).hom p :=
  rfl

/-- The page-one bound witness shared by the page-one and page-two coordinates. -/
structure PartialTotalFirstPageChoice
    (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) : Prop where
  pageOneBound : (1 : ℤ) ≤ 1

/-- The canonical page-one bound witness. -/
theorem partialTotalFirstPageChoice :
    PartialTotalFirstPageChoice B :=
  { pageOneBound := by omega }

namespace PartialTotalFirstPageChoice

variable {B}

/-- The exact successor proof used by the package's HomologyData. -/
theorem pageOneToTwo (χ : PartialTotalFirstPageChoice B) :
    (1 : ℤ) + 1 = 2 := by
  have hχ := χ.pageOneBound
  omega

/-- The page-two bound derived from the chosen page-one bound. -/
theorem pageTwoBound (χ : PartialTotalFirstPageChoice B) : (1 : ℤ) ≤ 2 :=
  χ.pageOneBound.trans (by omega)

/-- The page-one object using the package's literal bound proof. -/
noncomputable abbrev pageOne (χ : PartialTotalFirstPageChoice B) :
    HomologicalComplex C
      (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩) :=
  (B.partialTotalSpectralObject.spectralSequence core).page
    1 χ.pageOneBound

/-- The page-two object using the bound proof derived from the same package. -/
noncomputable abbrev pageTwo (χ : PartialTotalFirstPageChoice B) :
    HomologicalComplex C
      (ComplexShape.spectralSequenceNat ⟨(-2 : ℤ), 1⟩) :=
  (B.partialTotalSpectralObject.spectralSequence core).page
    2 χ.pageTwoBound

/-- The fixed vertical-degree row of the package's literal page one. -/
noncomputable abbrev rowRestriction
    (χ : PartialTotalFirstPageChoice B) (q : ℕ) : ChainComplex C ℕ :=
  χ.pageOne.restriction (partialTotalFirstPageRowEmbedding q)

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- The package-bound first-page core coordinate at an explicit presentation
of the lower middle cut and adjacent degrees. -/
noncomputable def firstPageCoreIsoAtOfCut
    (χ : PartialTotalFirstPageChoice B)
    (p q : ℕ) (k : EInt)
    (hk : k = (core).i₁ (p, q))
    (n₀ n₂ : ℤ)
    (hn₀ : n₀ + 1 = (core).deg (p, q))
    (hn₂ : (core).deg (p, q) + 1 = n₂) :
    χ.pageOne.X (p, q) ≅
      (B.partialTotalSpectralObject.H ((core).deg (p, q))).obj
        (ComposableArrows.mk₁
          (homOfLE ((core).le₁₂' (p, q) hk rfl))) :=
  let Y := B.partialTotalSpectralObject
  CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      Y core 1 χ.pageOneBound (p, q)
      k k ((core).i₂ (p, q)) ((core).i₂ (p, q))
      (by rw [hk, ← (core).hi₀₁]) hk rfl
      (by rw [(core).hi₂₃])
      n₀ ((core).deg (p, q)) n₂ rfl hn₀ hn₂ ≪≫
    Y.EIsoH
      (homOfLE ((core).le₁₂' (p, q) hk rfl))
      n₀ ((core).deg (p, q)) n₂ hn₀ hn₂

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- The explicit-cut first-page core coordinate is the lower page coordinate
followed by the spectral-object homology coordinate. -/
theorem firstPageCoreIsoAtOfCut_eq
    (χ : PartialTotalFirstPageChoice B)
    (p q : ℕ) (k : EInt)
    (hk : k = (core).i₁ (p, q))
    (n₀ n₂ : ℤ)
    (hn₀ : n₀ + 1 = (core).deg (p, q))
    (hn₂ : (core).deg (p, q) + 1 = n₂) :
    let Y := B.partialTotalSpectralObject
    χ.firstPageCoreIsoAtOfCut p q k hk n₀ n₂ hn₀ hn₂ =
      (CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
          Y core 1 χ.pageOneBound (p, q)
          k k ((core).i₂ (p, q)) ((core).i₂ (p, q))
          (by rw [hk, ← (core).hi₀₁]) hk rfl
          (by rw [(core).hi₂₃])
          n₀ ((core).deg (p, q)) n₂ rfl hn₀ hn₂ ≪≫
        Y.EIsoH
          (homOfLE ((core).le₁₂' (p, q) hk rfl))
          n₀ ((core).deg (p, q)) n₂ hn₀ hn₂) :=
  rfl

/-- The package-bound explicit first-page core factor. -/
noncomputable def firstPageCoreIsoAt
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageOne.X (p, q) ≅
      (B.partialTotalSpectralObject.H ((core).deg (p, q))).obj
        (ComposableArrows.mk₁ (homOfLE ((core).le₁₂ (p, q)))) :=
  χ.firstPageCoreIsoAtOfCut p q
    ((core).i₁ (p, q)) rfl
    ((core).deg (p, q) - 1)
    ((core).deg (p, q) + 1)
    (by omega) rfl

/-- The package-bound first-page coordinate at an explicitly chosen total
degree. -/
noncomputable def firstPageRowIsoAt
    (χ : PartialTotalFirstPageChoice B)
    (p q n : ℕ) (h : p + q = n) :
    χ.pageOne.X (p, q) ≅ (B.totalRow p).homology n :=
  χ.firstPageCoreIsoAt p q ≪≫
    B.partialTotalSpectralObjectHStepIso p q ≪≫
    B.partialTotalStepE₁HomologyIsoAt p q n h

/-- The proof-sensitive embedding indices shared by all restriction
coordinates at `(p,q)`. -/
structure RestrictionIndex
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) : Prop where
  hMid : (partialTotalFirstPageRowEmbedding q).f p = (p, q)
  hPrev :
    (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).prev (p, q) =
      (partialTotalFirstPageRowEmbedding q).f
        ((ComplexShape.down ℕ).prev p)
  hNext :
    (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).next (p, q) =
      (partialTotalFirstPageRowEmbedding q).f
        ((ComplexShape.down ℕ).next p)

/-- The canonical row-restriction index data at `(p, q)`. -/
theorem restrictionIndex
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.RestrictionIndex p q := by
  refine ⟨partialTotalFirstPageRowEmbedding_f p q, ?_, ?_⟩
  · apply (ComplexShape.spectralSequenceNat
      ⟨(-1 : ℤ), 0⟩).prev_eq'
    exact (partialTotalFirstPageRowEmbedding q).rel (by
      change p + 1 = (ComplexShape.down ℕ).prev p
      simp)
  · rcases p with _ | p
    · simp only [ChainComplex.next_nat_zero]
      apply (ComplexShape.spectralSequenceNat
        ⟨(-1 : ℤ), 0⟩).next_eq_self'
      intro z hz
      have hfst : (0 : ℤ) + (-1 : ℤ) = z.1 :=
        ((ComplexShape.spectralSequenceNat_rel_iff
          ⟨(-1 : ℤ), 0⟩ (0, q) z).mp hz).1
      omega
    · exact (ComplexShape.spectralSequenceNat
        ⟨(-1 : ℤ), 0⟩).next_eq'
          ((partialTotalFirstPageRowEmbedding q).rel (by
            simp only [ChainComplex.next_nat_succ]
            rfl))

/-- The object coordinate of the package's named row restriction. -/
noncomputable def restrictionXIso
    (χ : PartialTotalFirstPageChoice B) {p q : ℕ}
    (ρ : χ.RestrictionIndex p q) :
    (χ.rowRestriction q).X p ≅ χ.pageOne.X (p, q) :=
  χ.pageOne.restrictionXIso
    (partialTotalFirstPageRowEmbedding q) ρ.hMid

/-- The cycles coordinate of the package's named row restriction. -/
noncomputable def restrictionCyclesIso
    (χ : PartialTotalFirstPageChoice B) {p q : ℕ}
    (ρ : χ.RestrictionIndex p q) :
    (χ.rowRestriction q).cycles p ≅ χ.pageOne.cycles (p, q) :=
  χ.pageOne.restrictionCyclesIsoAt
    (partialTotalFirstPageRowEmbedding q) p ρ.hNext

/-- The homology coordinate of the package's named row restriction. -/
noncomputable def restrictionHomologyIso
    (χ : PartialTotalFirstPageChoice B) {p q : ℕ}
    (ρ : χ.RestrictionIndex p q) :
    (χ.rowRestriction q).homology p ≅
      χ.pageOne.homology (p, q) :=
  χ.pageOne.restrictionHomologyIsoAt
    (partialTotalFirstPageRowEmbedding q) p ρ.hPrev ρ.hNext

/-- The restriction cycles coordinate commutes with inclusion into objects. -/
@[reassoc]
theorem restrictionCyclesIso_hom_iCycles
    (χ : PartialTotalFirstPageChoice B) {p q : ℕ}
    (ρ : χ.RestrictionIndex p q) :
    (χ.restrictionCyclesIso ρ).hom ≫
        χ.pageOne.iCycles (p, q) =
      (χ.rowRestriction q).iCycles p ≫
        (χ.restrictionXIso ρ).hom := by
  exact HomologicalComplex.restrictionCyclesIsoAt_hom_iCycles
    χ.pageOne (partialTotalFirstPageRowEmbedding q) p ρ.hNext

/-- The restriction homology coordinate commutes with projection from
cycles. -/
@[reassoc]
theorem homologyπ_restrictionHomologyIso_hom
    (χ : PartialTotalFirstPageChoice B) {p q : ℕ}
    (ρ : χ.RestrictionIndex p q) :
    (χ.rowRestriction q).homologyπ p ≫
        (χ.restrictionHomologyIso ρ).hom =
      (χ.restrictionCyclesIso ρ).hom ≫
        χ.pageOne.homologyπ (p, q) := by
  exact HomologicalComplex.homologyπ_restrictionHomologyIsoAt_hom
    χ.pageOne (partialTotalFirstPageRowEmbedding q) p ρ.hPrev ρ.hNext

/-- The objectwise coordinate from the package's fixed row to vertical
homology. -/
noncomputable def componentIso
    (χ : PartialTotalFirstPageChoice B) (q p : ℕ) :
    (χ.rowRestriction q).X p ≅ (B.X p).homology q :=
  χ.restrictionXIso (χ.restrictionIndex p q) ≪≫
    χ.firstPageRowIsoAt p q (q + p) (Nat.add_comm p q) ≪≫
    B.totalRowHomologyIsoAt p q (q + p) (Nat.add_comm p q)

/- Compatibility of the fixed-row comparison with differentials -/

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
theorem component_comm
    (χ : PartialTotalFirstPageChoice B)
    (q i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (χ.componentIso q i).hom ≫
        (B.signedVerticalHomologyComplex q).d i j =
      (χ.rowRestriction q).d i j ≫
        (χ.componentIso q j).hom := by
  change j + 1 = i at hij
  subst i
  let Y := B.partialTotalSpectralObject
  let P₁ := χ.pageOne
  let K := χ.rowRestriction q
  let m := j
  let NZero := q + m
  let NPlus := NZero + 1
  have hPlus : (m + 1) + q = NPlus := by
    dsimp only [NPlus, NZero, m]
    omega
  have hZero : m + q = NZero := Nat.add_comm m q
  let ePagePlus := χ.firstPageRowIsoAt (m + 1) q NPlus hPlus
  let ePageZero := χ.firstPageRowIsoAt m q NZero hZero
  let eRowPlus :
      (B.totalRow (m + 1)).homology NPlus ≅
        (B.signedVerticalHomologyComplex q).X (m + 1) :=
    B.totalRowHomologyIsoAt (m + 1) q NPlus hPlus
  let eRowZero :
      (B.totalRow m).homology NZero ≅
        (B.signedVerticalHomologyComplex q).X m :=
    B.totalRowHomologyIsoAt m q NZero hZero
  let dAt :
      (B.totalRow (m + 1)).homology NPlus ⟶
        (B.totalRow m).homology NZero :=
    ePagePlus.inv ≫ P₁.d (m + 1, q) (m, q) ≫ ePageZero.hom
  let eNat := ComplexShape.embeddingDownNat
  let νPlus : ℤ := -((NPlus : ℕ) : ℤ)
  let νZero : ℤ := -((NZero : ℕ) : ℤ)
  let S := B.partialTotalStepCochainShortComplex (m + 1)
  let T := B.partialTotalStepCochainShortComplex m
  let hS : S.ShortExact :=
    B.partialTotalStepCochainShortExact (m + 1)
  have hν : νPlus + 1 = νZero := by
    change -((NPlus : ℕ) : ℤ) + 1 = -((NZero : ℕ) : ℤ)
    omega
  let cAt :
      (B.totalRow (m + 1)).homology NPlus ⟶
        (B.totalRow m).homology NZero :=
    ((B.totalRow (m + 1)).extendHomologyIso eNat rfl).inv ≫
      (HomologicalComplex.homologyMapIso
        (B.partialTotalStepCochainX₃Iso (m + 1)) νPlus).inv ≫
      hS.δ νPlus νZero hν ≫
      (HomologicalComplex.homologyMapIso
        (B.partialTotalAdjacentStepCochainIso m) νZero).hom ≫
      HomologicalComplex.homologyMap T.g νZero ≫
      (HomologicalComplex.homologyMapIso
        (B.partialTotalStepCochainX₃Iso m) νZero).hom ≫
      ((B.totalRow m).extendHomologyIso eNat rfl).hom
  let rAtNat :
      (B.totalRow (m + 1)).homology NPlus ⟶
        (B.totalRow m).homology NZero :=
    ((B.totalRow (m + 1)).extendHomologyIso eNat rfl).inv ≫
      (HomologicalComplex.homologyFunctor C
        (ComplexShape.up ℤ) 0).shiftMap
          (B.partialTotalHorizontalRowShift m) νPlus νZero (by
            change 1 + -((NPlus : ℕ) : ℤ) = -((NZero : ℕ) : ℤ)
            omega) ≫
      ((B.totalRow m).extendHomologyIso eNat rfl).hom
  let rAt :
      (B.totalRow (m + 1)).homology NPlus ⟶
        (B.totalRow m).homology NZero :=
    ((B.totalRow (m + 1)).extendHomologyIso eNat rfl).inv ≫
      (HomologicalComplex.homologyFunctor C
        (ComplexShape.up ℤ) 0).shiftMap
          (B.partialTotalHorizontalRowShift m)
          (eNat.f NPlus) (eNat.f NZero) (by
            change 1 + -((NPlus : ℕ) : ℤ) = -((NZero : ℕ) : ℤ)
            omega) ≫
      ((B.totalRow m).extendHomologyIso eNat rfl).hom
  let n : ℤ := (core).deg (m + 1, q)
  let n' : ℤ := (core).deg (m, q)
  have hnn' : n + 1 = n' := by
    dsimp only [n, n',
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
    omega
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  let fLeft := homOfLE ((core).le₁₂ (m, q))
  let fRight := homOfLE ((core).le₁₂' (m + 1, q) hmid rfl)
  have hPrev : (n - 1) + 1 = n := by omega
  have hNext : n' + 1 = n' + 1 := rfl
  let ePageSource := χ.firstPageCoreIsoAt (m + 1) q
  let ePageSourceCore := χ.firstPageCoreIsoAtOfCut
    (m + 1) q ((core).i₂ (m, q)) hmid
    (n - 1) n' hPrev hnn'
  let ePageSourceCoreX :=
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      Y core 1 χ.pageOneBound (m + 1, q)
      ((core).i₂ (m, q)) ((core).i₂ (m, q))
      ((core).i₂ (m + 1, q)) ((core).i₂ (m + 1, q))
      (by rw [hmid, ← (core).hi₀₁]) hmid rfl
      (by rw [(core).hi₂₃])
      (n - 1) n n' rfl hPrev hnn'
  let ePageSourceCoreH := Y.EIsoH fRight (n - 1) n n' hPrev hnn'
  have hSourceFactors :
      ePageSourceCore.hom =
        ePageSourceCoreX.hom ≫ ePageSourceCoreH.hom := by
    have h := congrArg Iso.hom
      (χ.firstPageCoreIsoAtOfCut_eq
        (m + 1) q ((core).i₂ (m, q)) hmid
        (n - 1) n' hPrev hnn')
    change ePageSourceCore.hom =
      ePageSourceCoreX.hom ≫ ePageSourceCoreH.hom at h
    exact h
  let γIdx :
      ComposableArrows.mk₁
          (homOfLE (show (core).i₂ (m, q) ≤ (core).i₂ (m + 1, q) by
            change (((m : ℤ) : EInt) ≤ (((m + 1 : ℕ) : ℤ) : EInt))
            simp)) ≅
        ComposableArrows.mk₁
          (homOfLE ((core).le₁₂ (m + 1, q))) :=
    ComposableArrows.isoMk₁ (eqToIso hmid) (Iso.refl _)
  have hPageSource :
      ePageSource.inv ≫ ePageSourceCore.hom =
        (Y.H n).map γIdx.inv := by
    have hAux
        (k : EInt) (hk : k = (core).i₁ (m + 1, q))
        (n₂ : ℤ) (hn₂ : n + 1 = n₂) :
        let fK := homOfLE ((core).le₁₂' (m + 1, q) hk rfl)
        let γk :
            ComposableArrows.mk₁ fK ≅
              ComposableArrows.mk₁
                (homOfLE ((core).le₁₂ (m + 1, q))) :=
          ComposableArrows.isoMk₁ (eqToIso hk) (Iso.refl _)
        let ePageK := χ.firstPageCoreIsoAtOfCut
          (m + 1) q k hk (n - 1) n₂ hPrev hn₂
        ePageSource.inv ≫ ePageK.hom = (Y.H n).map γk.inv := by
      dsimp only
      subst k
      subst n₂
      dsimp only [ePageSource, firstPageCoreIsoAt]
      rw [Iso.inv_hom_id]
      rw [← (Y.H n).map_id]
      apply (Y.H n).congr_map
      subsingleton
    let γMid :
        ComposableArrows.mk₁
            (homOfLE ((core).le₁₂' (m + 1, q) hmid rfl)) ≅
          ComposableArrows.mk₁
            (homOfLE ((core).le₁₂ (m + 1, q))) :=
      ComposableArrows.isoMk₁ (eqToIso hmid) (Iso.refl _)
        (by subsingleton)
    calc
      _ = (Y.H n).map γMid.inv := by
        exact hAux ((core).i₂ (m, q)) hmid n' hnn'
      _ = (Y.H n).map γIdx.inv := by
        apply (Y.H n).congr_map
        apply ComposableArrows.hom_ext₁ <;> subsingleton
  let ePageTargetRaw := χ.firstPageCoreIsoAtOfCut
    m q ((core).i₁ (m, q)) rfl n (n' + 1) hnn' hNext
  let ePageTargetRawX :=
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      Y core 1 χ.pageOneBound (m, q)
      ((core).i₁ (m, q)) ((core).i₁ (m, q))
      ((core).i₂ (m, q)) ((core).i₂ (m, q))
      (by rw [← (core).hi₀₁]) rfl rfl
      (by rw [(core).hi₂₃])
      n n' (n' + 1) rfl hnn' hNext
  let ePageTargetRawH := Y.EIsoH fLeft n n' (n' + 1) hnn' hNext
  have hTargetFactors :
      ePageTargetRaw.inv =
        ePageTargetRawH.inv ≫ ePageTargetRawX.inv := by
    have h := congrArg Iso.inv
      (χ.firstPageCoreIsoAtOfCut_eq
        m q ((core).i₁ (m, q)) rfl
        n (n' + 1) hnn' hNext)
    change ePageTargetRaw.inv =
      ePageTargetRawH.inv ≫ ePageTargetRawX.inv at h
    exact h
  let ePageTarget := χ.firstPageCoreIsoAt m q
  have hPageTarget :
      ePageTargetRaw.inv ≫ ePageTarget.hom = 𝟙 _ := by
    have hTargetCoordinate
        (n₀ : ℤ) (hn₀ : n₀ + 1 = n') :
        χ.firstPageCoreIsoAtOfCut
            m q ((core).i₁ (m, q)) rfl
            n₀ (n' + 1) hn₀ hNext =
          ePageTarget := by
      have h : n₀ = n' - 1 := by omega
      subst n₀
      dsimp only [ePageTarget, firstPageCoreIsoAt]
    have hTargetIso : ePageTargetRaw = ePageTarget :=
      hTargetCoordinate n hnn'
    have hInv : ePageTargetRaw.inv = ePageTarget.inv :=
      congrArg Iso.inv hTargetIso
    calc
      ePageTargetRaw.inv ≫ ePageTarget.hom =
          ePageTarget.inv ≫ ePageTarget.hom :=
        congrArg (fun f => f ≫ ePageTarget.hom) hInv
      _ = 𝟙 _ := ePageTarget.inv_hom_id
  let dRaw := Y.d (𝟙 _) fLeft (𝟙 _) fRight (𝟙 _)
    (n - 1) n n' (n' + 1) hPrev hnn' hNext
  have hpageRaw :=
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD_eq
      Y core 1 χ.pageOneBound (m + 1, q) (m, q)
      (coreE₁IncreasingHomologicalNat_rel_succ m q)
      (𝟙 _) fLeft (𝟙 _) fRight (𝟙 _)
      (by rw [← (core).hi₀₁]) rfl
      (by rw [hmid, ← (core).hi₀₁]) hmid rfl
      (by rw [(core).hi₂₃])
      (n - 1) n n' (n' + 1) rfl hPrev hnn' hNext
  change P₁.d (m + 1, q) (m, q) =
    ePageSourceCoreX.hom ≫ dRaw ≫ ePageTargetRawX.inv at hpageRaw
  have hD :
      dRaw = ePageSourceCoreH.hom ≫
        Y.δ fLeft fRight n n' hnn' ≫ ePageTargetRawH.inv := by
    apply (cancel_mono ePageTargetRawH.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Y.d_EIsoH_hom fLeft fRight
      (n - 1) n n' (n' + 1) hPrev hnn' hNext
  have hpage :
      P₁.d (m + 1, q) (m, q) =
        ePageSourceCore.hom ≫ Y.δ fLeft fRight n n' hnn' ≫
          ePageTargetRaw.inv := by
    rw [hpageRaw, hD]
    rw [hSourceFactors, hTargetFactors]
    simp only [Category.assoc]
    exact (Category.assoc
      ePageSourceCoreX.hom ePageSourceCoreH.hom
      (Y.δ fLeft fRight n n' hnn' ≫
        ePageTargetRawH.inv ≫ ePageTargetRawX.inv)).symm
  have hPagePresented :
      ePageSource.inv ≫ P₁.d (m + 1, q) (m, q) ≫ ePageTarget.hom =
        (Y.H n).map γIdx.inv ≫
          Y.δ fLeft fRight n n' hnn' := by
    have hpageAt :=
      congrArg
        (fun (k : P₁.X (m + 1, q) ⟶ P₁.X (m, q)) =>
          ePageSource.inv ≫ k ≫ ePageTarget.hom)
        hpage
    have hSourceAt :
        ((ePageSource.inv ≫ ePageSourceCore.hom) ≫
              Y.δ fLeft fRight n n' hnn') ≫
            (ePageTargetRaw.inv ≫ ePageTarget.hom) =
          (((Y.H n).map γIdx.inv ≫
              Y.δ fLeft fRight n n' hnn') ≫
            (ePageTargetRaw.inv ≫ ePageTarget.hom)) :=
      congrArg
        (fun f =>
          (f ≫ Y.δ fLeft fRight n n' hnn') ≫
            (ePageTargetRaw.inv ≫ ePageTarget.hom))
        hPageSource
    have hTargetAt :
        (((Y.H n).map γIdx.inv ≫
              Y.δ fLeft fRight n n' hnn') ≫
            (ePageTargetRaw.inv ≫ ePageTarget.hom)) =
          (((Y.H n).map γIdx.inv ≫
              Y.δ fLeft fRight n n' hnn') ≫ 𝟙 _) :=
      congrArg
        (fun f =>
          ((Y.H n).map γIdx.inv ≫
            Y.δ fLeft fRight n n' hnn') ≫ f)
        hPageTarget
    calc
      ePageSource.inv ≫ P₁.d (m + 1, q) (m, q) ≫ ePageTarget.hom =
          ePageSource.inv ≫
            (ePageSourceCore.hom ≫
              Y.δ fLeft fRight n n' hnn' ≫ ePageTargetRaw.inv) ≫
            ePageTarget.hom := hpageAt
      _ = (((ePageSource.inv ≫ ePageSourceCore.hom) ≫
              Y.δ fLeft fRight n n' hnn') ≫
            (ePageTargetRaw.inv ≫ ePageTarget.hom)) := by
          simp only [Category.assoc]
      _ = ((Y.H n).map γIdx.inv ≫
              Y.δ fLeft fRight n n' hnn') ≫
            (ePageTargetRaw.inv ≫ ePageTarget.hom) := hSourceAt
      _ = ((Y.H n).map γIdx.inv ≫
              Y.δ fLeft fRight n n' hnn') ≫ 𝟙 _ := hTargetAt
      _ = (Y.H n).map γIdx.inv ≫
            Y.δ fLeft fRight n n' hnn' := Category.comp_id _
  have hDeltaAt : dAt = cAt := by
    dsimp only [dAt, ePagePlus, ePageZero, firstPageRowIsoAt]
    simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
    slice_lhs 3 5 => rw [hPagePresented]
    slice_lhs 2 5 => erw [B.partialTotalE₁_delta_conjugation m q]
    erw [B.partialTotalE₁_mappingConeDifferential_eq_connectingAt
      m q NPlus NZero hPlus hZero hS hν hnn']
  have hConnectingAtNat : cAt = rAtNat := by
    simpa only [cAt, rAtNat, eNat, νPlus, νZero, S, T, hS,
      Category.assoc] using
      B.partialTotalE₁Connecting_eq_horizontalRowAt
        m q NPlus NZero hPlus hZero
  have hRAt : rAtNat = rAt := by
    let D := { d : ℤ × ℤ //
      eNat.f NPlus = d.1 ∧ eNat.f NZero = d.2 }
    let dNat : D := ⟨(νPlus, νZero), rfl, rfl⟩
    let dEmbed : D :=
      ⟨(eNat.f NPlus, eNat.f NZero), rfl, rfl⟩
    have hRel (d : D) : 1 + d.1.1 = d.1.2 := by
      rw [← d.2.1, ← d.2.2]
      change 1 + -((NPlus : ℕ) : ℤ) = -((NZero : ℕ) : ℤ)
      omega
    let wholeAt (d : D) :
        (B.totalRow (m + 1)).homology NPlus ⟶
          (B.totalRow m).homology NZero :=
      ((B.totalRow (m + 1)).extendHomologyIso eNat d.2.1).inv ≫
        (HomologicalComplex.homologyFunctor C
          (ComplexShape.up ℤ) 0).shiftMap
            (B.partialTotalHorizontalRowShift m)
              d.1.1 d.1.2 (hRel d) ≫
        ((B.totalRow m).extendHomologyIso eNat d.2.2).hom
    have hd : dNat = dEmbed := by
      apply Subtype.ext
      apply Prod.ext <;> rfl
    have hRAtNatWhole : rAtNat = wholeAt dNat := by
      dsimp only [rAtNat, wholeAt, dNat, D]
      rfl
    have hWholeRAt : wholeAt dEmbed = rAt := by
      dsimp only [rAt, wholeAt, dEmbed, D]
    exact hRAtNatWhole.trans
      ((congrArg wholeAt hd).trans hWholeRAt)
  have hConnectingAt : cAt = rAt :=
    hConnectingAtNat.trans hRAt
  have hRowAt :
      rAt ≫ eRowZero.hom =
        eRowPlus.hom ≫
          (B.signedVerticalHomologyComplex q).d (m + 1) m := by
    dsimp only [rAt, eNat, νPlus, νZero, eRowZero, eRowPlus,
      NPlus, NZero]
    erw [B.partialTotalHorizontalRowHomology_totalRowHomologyIsoAt
      m q hPlus hZero]
    rfl
  have hRowD :
      dAt ≫ eRowZero.hom =
        eRowPlus.hom ≫
          (B.signedVerticalHomologyComplex q).d (m + 1) m := by
    rw [hDeltaAt, hConnectingAt, hRowAt]
  have hBase :
      (ePagePlus.hom ≫ eRowPlus.hom) ≫
          (B.signedVerticalHomologyComplex q).d (m + 1) m =
        P₁.d (m + 1, q) (m, q) ≫
          (ePageZero.hom ≫ eRowZero.hom) := by
    simp only [Category.assoc]
    rw [← hRowD]
    dsimp only [dAt]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change
    (χ.componentIso q (m + 1)).hom ≫
        (B.signedVerticalHomologyComplex q).d (m + 1) m =
      K.d (m + 1) m ≫ (χ.componentIso q m).hom
  let ρPlus : χ.RestrictionIndex (m + 1) q :=
    χ.restrictionIndex (m + 1) q
  let ρZero : χ.RestrictionIndex m q :=
    χ.restrictionIndex m q
  let eXPlus : K.X (m + 1) ≅ P₁.X (m + 1, q) :=
    χ.restrictionXIso ρPlus
  let eXZero : K.X m ≅ P₁.X (m, q) :=
    χ.restrictionXIso ρZero
  have hRestriction :
      K.d (m + 1) m =
        eXPlus.hom ≫ P₁.d (m + 1, q) (m, q) ≫ eXZero.inv := by
    exact P₁.restriction_d_eq
      (partialTotalFirstPageRowEmbedding q) ρPlus.hMid ρZero.hMid
  have hPre := congrArg (fun f => eXPlus.hom ≫ f) hBase
  change
    (eXPlus.hom ≫ ePagePlus.hom ≫ eRowPlus.hom) ≫
        (B.signedVerticalHomologyComplex q).d (m + 1) m =
      K.d (m + 1) m ≫
        (eXZero.hom ≫ ePageZero.hom ≫ eRowZero.hom)
  rw [hRestriction]
  simp only [Category.assoc]
  slice_rhs 3 4 => rw [eXZero.inv_hom_id]
  simp only [Category.id_comp]
  simpa only [Category.assoc] using hPre

/- Comparison with ordinary vertical homology -/


/-- The package-bound fixed first-page row is canonically the ordinary
horizontal complex of vertical homology. -/
noncomputable def verticalHomologyIso
    (χ : PartialTotalFirstPageChoice B) (q : ℕ) :
    χ.rowRestriction q ≅ B.verticalHomologyComplex q :=
  HomologicalComplex.Hom.isoOfComponents
      (fun p => χ.componentIso q p)
      (fun i j hij => χ.component_comm q i j hij) ≪≫
    B.signedVerticalHomologyIso q

/-- In horizontal degree zero, the inverse package-bound row comparison is
the inverse of its exact shared component. -/
theorem verticalHomologyIso_inv_f_zero
    (χ : PartialTotalFirstPageChoice B) (q : ℕ) :
    (χ.verticalHomologyIso q).inv.f 0 =
      (χ.componentIso q 0).inv := by
  let K := χ.rowRestriction q
  let components : ∀ p, K.X p ≅
      (B.signedVerticalHomologyComplex q).X p :=
    fun p => χ.componentIso q p
  let hcomm : ∀ i j, (ComplexShape.down ℕ).Rel i j →
      (components i).hom ≫
          (B.signedVerticalHomologyComplex q).d i j =
        K.d i j ≫ (components j).hom :=
    fun i j hij => χ.component_comm q i j hij
  let eSigned : K ≅ B.signedVerticalHomologyComplex q :=
    HomologicalComplex.Hom.isoOfComponents components hcomm
  let eVertical : K ≅ B.verticalHomologyComplex q :=
    eSigned ≪≫ B.signedVerticalHomologyIso q
  change eVertical.inv.f 0 = _
  have hApp :=
    HomologicalComplex.Hom.isoOfComponents_app components hcomm 0
  have hSignedInv :
      eSigned.inv.f 0 = (χ.componentIso q 0).inv := by
    change (HomologicalComplex.Hom.isoApp eSigned 0).inv = _
    rw [hApp]
  change (B.signedVerticalHomologyIso q).inv.f 0 ≫
      eSigned.inv.f 0 = _
  rw [signedVerticalHomologyIso_inv_f, hSignedInv]
  simp only [pow_zero, inv_one, one_smul]
  exact Category.id_comp _

/- Page-one transition HomologyData -/


/-- The proof-sensitive cuts and degree witnesses shared by the package's
page-one HomologyData and page-two coordinates. -/
structure PageTransitionIndex
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) : Type where
  /-- The predecessor bidegree at `(p, q)` on page one. -/
  pqPrev : ℕ × ℕ
  /-- The successor bidegree at `(p, q)` on page one. -/
  pqNext : ℕ × ℕ
  hpq :
    (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).prev (p, q) = pqPrev
  hpq' :
    (ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩).next (p, q) = pqNext
  /-- The outer lower cut for the page-two coordinate. -/
  i₀' : EInt
  /-- The lower page-one cut. -/
  i₀ : EInt
  /-- The lower middle cut shared by both pages. -/
  i₁ : EInt
  /-- The upper middle cut shared by both pages. -/
  i₂ : EInt
  /-- The upper page-one cut. -/
  i₃ : EInt
  /-- The outer upper cut for the page-two coordinate. -/
  i₃' : EInt
  /-- The predecessor total degree. -/
  n₀ : ℤ
  /-- The total degree at `(p, q)`. -/
  n₁ : ℤ
  /-- The successor total degree. -/
  n₂ : ℤ
  hi₀' : i₀' = (core).i₀ 2 (p, q) χ.pageTwoBound
  hi₀ : i₀ = (core).i₀ 1 (p, q) χ.pageOneBound
  hi₁ : i₁ = (core).i₁ (p, q)
  hi₂ : i₂ = (core).i₂ (p, q)
  hi₃ : i₃ = (core).i₃ 1 (p, q) χ.pageOneBound
  hi₃' : i₃' = (core).i₃ 2 (p, q) χ.pageTwoBound
  hn : n₁ = (core).deg (p, q)
  hn₁ : n₀ + 1 = n₁
  hn₂ : n₁ + 1 = n₂
  hiBot₀' : (⊥ : EInt) ≤ i₀'
  hi₀'₁ : i₀' ≤ i₁
  hi₀'₀ : i₀' ≤ i₀
  hi₀₁ : i₀ ≤ i₁
  hi₁₂ : i₁ ≤ i₂
  hi₂₃ : i₂ ≤ i₃
  hi₂₃' : i₂ ≤ i₃'
  hi₃₃' : i₃ ≤ i₃'
  hiBot₁ : (⊥ : EInt) ≤ i₁
  hi₃'Top : i₃' ≤ (⊤ : EInt)

/-- The canonical page-transition index data derived from the same choice. -/
noncomputable def pageTransitionIndex
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.PageTransitionIndex p q := by
  let c₁ := ComplexShape.spectralSequenceNat ⟨(-1 : ℤ), 0⟩
  let pq : ℕ × ℕ := (p, q)
  let i₀' : EInt := (((p : ℤ) - 2 : ℤ) : EInt)
  let i₀ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
  let i₁ : EInt := (((p : ℤ) - 1 : ℤ) : EInt)
  let i₂ : EInt := ((p : ℤ) : EInt)
  let i₃ : EInt := ((p : ℤ) : EInt)
  let i₃' : EInt := (((p : ℤ) + 1 : ℤ) : EInt)
  let n₀ : ℤ := -(p : ℤ) - (q : ℤ) - 1
  let n₁ : ℤ := -(p : ℤ) - (q : ℤ)
  let n₂ : ℤ := -(p : ℤ) - (q : ℤ) + 1
  refine
    { pqPrev := c₁.prev pq
      pqNext := c₁.next pq
      hpq := rfl
      hpq' := rfl
      i₀' := i₀'
      i₀ := i₀
      i₁ := i₁
      i₂ := i₂
      i₃ := i₃
      i₃' := i₃'
      n₀ := n₀
      n₁ := n₁
      n₂ := n₂
      hi₀' := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
      hi₀ := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
      hi₁ := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁]
      hi₂ := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₂]
      hi₃ := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
        dsimp only [i₃, pq]
        congr 1
        omega
      hi₃' := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
        dsimp only [i₃', pq]
        congr 1
        omega
      hn := by
        rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
      hn₁ := by omega
      hn₂ := by omega
      hiBot₀' := bot_le
      hi₀'₁ := by
        dsimp only [i₀', i₁]
        simp only [WithBotTop.coe_le_coe]
        omega
      hi₀'₀ := by
        dsimp only [i₀', i₀]
        simp only [WithBotTop.coe_le_coe]
        omega
      hi₀₁ := by
        dsimp only [i₀, i₁]
        simp only [WithBotTop.coe_le_coe]
        rfl
      hi₁₂ := by
        dsimp only [i₁, i₂]
        simp only [WithBotTop.coe_le_coe]
        omega
      hi₂₃ := by
        dsimp only [i₂, i₃]
        simp only [WithBotTop.coe_le_coe]
        rfl
      hi₂₃' := by
        dsimp only [i₂, i₃']
        simp only [WithBotTop.coe_le_coe]
        omega
      hi₃₃' := by
        dsimp only [i₃, i₃']
        simp only [WithBotTop.coe_le_coe]
        omega
      hiBot₁ := bot_le
      hi₃'Top := le_top }

/-- The package-owned HomologyData for the transition from page one to page
two at `(p,q)`. -/
noncomputable def pageOneHomologyData
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    let η := χ.pageTransitionIndex p q
    (χ.pageOne.sc' η.pqPrev (p, q) η.pqNext).HomologyData := by
  let Y := B.partialTotalSpectralObject
  let η := χ.pageTransitionIndex p q
  exact Y.spectralSequenceHomologyData core
    1 2 χ.pageOneToTwo χ.pageOneBound
    η.pqPrev (p, q) η.pqNext η.hpq η.hpq'
    η.i₀' η.i₀ η.i₁ η.i₂ η.i₃ η.i₃'
    η.hi₀' η.hi₀ η.hi₁ η.hi₂ η.hi₃ η.hi₃'
    η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- The left inclusion of the package HomologyData is the literal lower
map-four factor followed by the inverse explicit-bound page coordinate. -/
@[reassoc]
theorem pageOneHomologyData_left_i
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    let η := χ.pageTransitionIndex p q
    (χ.pageOneHomologyData p q).left.i =
      B.partialTotalSpectralObject.mapFourδ₁Toδ₀'
          η.i₀' η.i₀ η.i₁ η.i₂ η.i₃
          η.hi₀'₀ η.hi₀₁ η.hi₁₂ η.hi₂₃
          η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ ≫
        (CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
          B.partialTotalSpectralObject core 1 χ.pageOneBound (p, q)
          η.i₀ η.i₁ η.i₂ η.i₃
          η.hi₀ η.hi₁ η.hi₂ η.hi₃
          η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂).inv := by
  let Y := B.partialTotalSpectralObject
  let η := χ.pageTransitionIndex p q
  exact
    CategoryTheory.Abelian.SpectralObject.spectralSequenceHomologyData_left_i
      Y core 1 2 χ.pageOneToTwo χ.pageOneBound
      η.pqPrev (p, q) η.pqNext η.hpq η.hpq'
      η.i₀' η.i₀ η.i₁ η.i₂ η.i₃ η.i₃'
      η.hi₀' η.hi₀ η.hi₁ η.hi₂ η.hi₃ η.hi₃'
      η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- The left projection of the package HomologyData is the literal upper
map-four factor. -/
@[reassoc]
theorem pageOneHomologyData_left_π
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    let η := χ.pageTransitionIndex p q
    (χ.pageOneHomologyData p q).left.π =
      B.partialTotalSpectralObject.mapFourδ₄Toδ₃'
        η.i₀' η.i₁ η.i₂ η.i₃ η.i₃'
        η.hi₀'₁ η.hi₁₂ η.hi₂₃ η.hi₃₃'
        η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ := by
  let Y := B.partialTotalSpectralObject
  let η := χ.pageTransitionIndex p q
  exact
    CategoryTheory.Abelian.SpectralObject.spectralSequenceHomologyData_left_π
      Y core 1 2 χ.pageOneToTwo χ.pageOneBound
      η.pqPrev (p, q) η.pqNext η.hpq η.hpq'
      η.i₀' η.i₀ η.i₁ η.i₂ η.i₃ η.i₃'
      η.hi₀' η.hi₀ η.hi₁ η.hi₂ η.hi₃ η.hi₃'
      η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂

/- Common page-one and page-two coordinates -/


/-- The common coordinate underlying page two and the homology of page one at
`(p,q)`, taken from the package-owned HomologyData. -/
noncomputable abbrev pageTwoCoordinate
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) : C :=
  (χ.pageOneHomologyData p q).left.H

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- The package page-two object in bidegree `(p,q)` is the common
HomologyData coordinate. -/
noncomputable def pageTwoCoordinateIso
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageTwo.X (p, q) ≅ χ.pageTwoCoordinate p q := by
  let η := χ.pageTransitionIndex p q
  exact
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      B.partialTotalSpectralObject core 2 χ.pageTwoBound (p, q)
      η.i₀' η.i₁ η.i₂ η.i₃'
      η.hi₀' η.hi₁ η.hi₂ η.hi₃'
      η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- The exact-bound raw page-two coordinate identifies with the package-owned
common page-two coordinate. -/
noncomputable def pageTwoRawCoordinateIso
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    let η := χ.pageTransitionIndex p q
    B.partialTotalSpectralObject.E
        (homOfLE η.hi₀'₁) (homOfLE η.hi₁₂) (homOfLE η.hi₂₃')
        η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ ≅
      χ.pageTwoCoordinate p q := by
  let η := χ.pageTransitionIndex p q
  let ePage₂ :
      χ.pageTwo.X (p, q) ≅
        B.partialTotalSpectralObject.E
          (homOfLE η.hi₀'₁) (homOfLE η.hi₁₂) (homOfLE η.hi₂₃')
          η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ :=
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      B.partialTotalSpectralObject core 2 χ.pageTwoBound (p, q)
      η.i₀' η.i₁ η.i₂ η.i₃'
      η.hi₀' η.hi₁ η.hi₂ η.hi₃'
      η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂
  exact ePage₂.symm ≪≫ χ.pageTwoCoordinateIso p q

/-- Page-one homology in bidegree `(p,q)` identifies with the same common
coordinate used for page two. -/
noncomputable def pageOneHomologyCoordinateIso
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageOne.homology (p, q) ≅ χ.pageTwoCoordinate p q := by
  let η := χ.pageTransitionIndex p q
  exact
    χ.pageOne.homologyIsoSc'
        η.pqPrev (p, q) η.pqNext η.hpq η.hpq' ≪≫
      (χ.pageOneHomologyData p q).left.homologyIso

/-- The selected transition from page-one homology to the package page-two
object. -/
noncomputable def pageOneTwoIso
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageOne.homology (p, q) ≅ χ.pageTwo.X (p, q) :=
  χ.pageOneHomologyCoordinateIso p q ≪≫
    (χ.pageTwoCoordinateIso p q).symm

/-- In horizontal degree zero, P12 followed by the page-two coordinate is
the page-one homology coordinate. -/
@[reassoc]
theorem pageOneTwoIso_zero_hom_comp_pageTwoCoordinateIso_hom
    (χ : PartialTotalFirstPageChoice B) (q : ℕ) :
    (χ.pageOneTwoIso 0 q).hom ≫
        (χ.pageTwoCoordinateIso 0 q).hom =
      (χ.pageOneHomologyCoordinateIso 0 q).hom := by
  change
    ((χ.pageOneHomologyCoordinateIso 0 q).hom ≫
        (χ.pageTwoCoordinateIso 0 q).inv) ≫
          (χ.pageTwoCoordinateIso 0 q).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/- Page-two vertical-homology identification and representative -/


/-- Page two in the package-owned coordinates is horizontal homology of the
vertical-homology complex. -/
noncomputable def secondPageVerticalHomologyIso
    (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageTwo.X (p, q) ≅
      (B.verticalHomologyComplex q).homology p :=
  (χ.pageOneTwoIso p q).symm ≪≫
    (χ.restrictionHomologyIso (χ.restrictionIndex p q)).symm ≪≫
    HomologicalComplex.homologyMapIso (χ.verticalHomologyIso q) p

/-- The inverse package-owned page-two coordinate is represented at
horizontal degree zero by the exact shared first-page component. -/
theorem secondPageVerticalHomologyIso_inv_representation_zero
    (χ : PartialTotalFirstPageChoice B) (q : ℕ) :
    (B.verticalHomologyComplex q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀
          (B.verticalHomologyComplex q)).inv ≫
        (χ.secondPageVerticalHomologyIso 0 q).inv =
      (χ.componentIso q 0).inv ≫
        (χ.rowRestriction q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀
          (χ.rowRestriction q)).inv ≫
        (χ.restrictionHomologyIso
          (χ.restrictionIndex 0 q)).hom ≫
        (χ.pageOneTwoIso 0 q).hom := by
  have hData :
      χ.secondPageVerticalHomologyIso 0 q =
        (χ.pageOneTwoIso 0 q).symm ≪≫
          (χ.restrictionHomologyIso
            (χ.restrictionIndex 0 q)).symm ≪≫
          HomologicalComplex.homologyMapIso
            (χ.verticalHomologyIso q) 0 := by
    rfl
  rw [hData]
  simp only [Iso.trans_inv, Iso.symm_inv,
    HomologicalComplex.homologyMapIso_inv, Category.assoc]
  rw [ChainComplex.isoHomologyι₀_inv_naturality_assoc]
  rw [HomologicalComplex.p_opcyclesMap_assoc]
  rw [χ.verticalHomologyIso_inv_f_zero q]
  rfl

end PartialTotalFirstPageChoice

end HomologicalComplex₂

end
