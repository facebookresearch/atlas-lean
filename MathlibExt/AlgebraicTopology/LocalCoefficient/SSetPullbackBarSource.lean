/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetBaseCoherence

/-!
# The actual original pullback source and its weighted-bar chart

The chart is forced by naturality of the existing fundamental-groupoid
nerve unit. Its simplex equation records the original coefficient transport;
it is not a supplied isomorphism or an inferred chain-map calibration.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

universe uR uX

namespace SSet

variable {R : Type uR} [CommRing R] {X Y : SSet.{uX}}

private theorem localCoefficientPullbackRawDataEq
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) :
    nervePullbackCoefficientData (fundamentalGroupoidNerveUnit X) (L.pullback f) =
      nervePullbackCoefficientData
        (fundamentalGroupoidNerveUnit X ≫ nerveMap (mapFundamentalGroupoid f)) L := by
  rfl

private theorem localCoefficientPullbackRawComplexEq
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) :
    localCoefficientChainComplex (L.pullback f) =
      nervePullbackCoefficientComplex
        (fundamentalGroupoidNerveUnit X ≫ nerveMap (mapFundamentalGroupoid f)) L := by
  exact congrArg
    (fun D : SimplicialObject.Data (ModuleCat.{max uR uX} R) =>
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max uR uX} R)).obj
        (SimplicialObject.Data.toSimplicialObject D))
    (localCoefficientPullbackRawDataEq f L)

/-- The source chart is the equality Iso forced by actual nerve-unit
naturality. The original coefficient category is retained. -/
public def localCoefficientPullbackBarSourceIso
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) :
    CategoryTheory.Iso (C := ChainComplex (ModuleCat.{max uR uX} R) ℕ)
      (localCoefficientChainComplex (L.pullback f))
      (nervePullbackCoefficientComplex (f ≫ fundamentalGroupoidNerveUnit Y) L) := by
  let φ : X ⟶ nerve (FundamentalGroupoid Y) :=
    fundamentalGroupoidNerveUnit X ≫ nerveMap (mapFundamentalGroupoid f)
  let ψ : X ⟶ nerve (FundamentalGroupoid Y) :=
    f ≫ fundamentalGroupoidNerveUnit Y
  have h : φ = ψ := (fundamentalGroupoidNerveUnit_naturality f).symm
  let H : localCoefficientChainComplex (L.pullback f) =
      nervePullbackCoefficientComplex ψ L :=
    (localCoefficientPullbackRawComplexEq f L).trans
      (congrArg (fun q : X ⟶ nerve (FundamentalGroupoid Y) =>
        nervePullbackCoefficientComplex q L) h)
  exact eqToIso H

/-- Every chart component is the same equality transport appearing in
the existing original pullback-chain-map formula. -/
public theorem localCoefficientPullbackBarSourceIso_hom_f
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) (n : ℕ) :
    (localCoefficientPullbackBarSourceIso f L).hom.f n =
      eqToHom (localCoefficientPullbackObjEq f L n) := by
  let φ : X ⟶ nerve (FundamentalGroupoid Y) :=
    fundamentalGroupoidNerveUnit X ≫ nerveMap (mapFundamentalGroupoid f)
  let ψ : X ⟶ nerve (FundamentalGroupoid Y) :=
    f ≫ fundamentalGroupoidNerveUnit Y
  have hφ : φ = ψ := (fundamentalGroupoidNerveUnit_naturality f).symm
  let H : localCoefficientChainComplex (L.pullback f) =
      nervePullbackCoefficientComplex ψ L :=
    (localCoefficientPullbackRawComplexEq f L).trans
      (congrArg (fun q : X ⟶ nerve (FundamentalGroupoid Y) =>
        nervePullbackCoefficientComplex q L) hφ)
  exact HomologicalComplex.eqToHom_f H n

private theorem componentChartRecipe
    {K T : ChainComplex (ModuleCat.{max uR uX} R) ℕ} (m : K ⟶ T) (n : ℕ)
    {A B : ModuleCat.{max uR uX} R} (hA : K.X n = A) (hB : T.X n = B)
    (b : A ⟶ B) (hb : m.f n ≍ b) :
    m.f n = (eqToIso hA).hom ≫ b ≫ (eqToIso hB).inv := by
  change m.f n = eqToHom hA ≫ b ≫ eqToHom (hB.symm)
  exact (conj_eqToHom_iff_heq (m.f n) b hA hB).mpr hb

private theorem nerveComplexEq_componentRecipe
    {G : Type uX} [Category.{uX} G] {K : SSet.{uX}}
    {φ ψ : K ⟶ nerve G} (M : G ⥤ ModuleCat.{max uR uX} R)
    (h : φ = ψ) (n : ℕ) :
    (eqToHom (congrArg (fun θ => nervePullbackCoefficientComplex θ M) h)).f n =
      (eqToIso (nervePullbackCoefficientComplex_X φ M n)).hom ≫
        eqToHom (congrArg (fun θ => nervePullbackCoefficientObj θ M n) h) ≫
          (eqToIso (nervePullbackCoefficientComplex_X ψ M n)).inv := by
  subst ψ
  simpa only [eqToHom_refl, HomologicalComplex.id_f, Category.id_comp] using
    (eqToIso (nervePullbackCoefficientComplex_X φ M n)).hom_inv_id.symm

private theorem localCoefficientPullbackRawFamilyEq
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) (n : ℕ) :
    localCoefficientFamily (L.pullback f) n =
      nervePullbackCoefficientFamily
        (fundamentalGroupoidNerveUnit X ≫ nerveMap (mapFundamentalGroupoid f)) L n := by
  rfl

private theorem localCoefficientPullbackOriginalObjEq
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) (n : ℕ) :
    localCoefficientObj (L.pullback f) n =
      nervePullbackCoefficientObj (f ≫ fundamentalGroupoidNerveUnit Y) L n :=
  (congrArg (fun F : X _⦋n⦌ → ModuleCat.{max uR uX} R => ∐ F)
    (localCoefficientPullbackRawFamilyEq f L n)).trans
      (congrArg (fun q => nervePullbackCoefficientObj q L n)
        (fundamentalGroupoidNerveUnit_naturality f).symm)

private theorem localCoefficientPullbackOriginalFamilyEq
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) {n : ℕ} (σ : X _⦋n⦌) :
    localCoefficientFamily (L.pullback f) n σ =
      nervePullbackCoefficientFamily (f ≫ fundamentalGroupoidNerveUnit Y) L n σ :=
  (congrFun (localCoefficientPullbackRawFamilyEq f L n) σ).trans
    (congrArg (fun q => nervePullbackCoefficientFamily q L n σ)
      (fundamentalGroupoidNerveUnit_naturality f).symm)

private theorem localCoefficientPullbackOriginalObjMap_heq
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) (n : ℕ) :
    eqToHom (localCoefficientPullbackOriginalObjEq f L n) ≍
      eqToHom (localCoefficientPullbackObjEq f L n) := by
  let φ := fundamentalGroupoidNerveUnit X ≫ nerveMap (mapFundamentalGroupoid f)
  let ψ := f ≫ fundamentalGroupoidNerveUnit Y
  let hS : localCoefficientObj (L.pullback f) n =
      (nervePullbackCoefficientData φ L).obj n :=
    (congrArg (fun F : X _⦋n⦌ → ModuleCat.{max uR uX} R => ∐ F)
      (localCoefficientPullbackRawFamilyEq f L n)).trans
        (nervePullbackCoefficientData_obj φ L n).symm
  let hT : nervePullbackCoefficientObj ψ L n =
      (nervePullbackCoefficientData ψ L).obj n :=
    (nervePullbackCoefficientData_obj ψ L n).symm
  apply (conj_eqToHom_iff_heq _ _ hS hT).mp
  simp only [eqToHom_trans]

private theorem localCoefficientPullbackOriginalBaseMap_heq
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) (n : ℕ) :
    (eqToHom (localCoefficientPullbackOriginalObjEq f L n) ≫
      nervePullbackCoefficientBaseMap f (fundamentalGroupoidNerveUnit Y) L n) ≍
    (eqToHom (localCoefficientPullbackObjEq f L n) ≫
      nervePullbackCoefficientBaseMap f (fundamentalGroupoidNerveUnit Y) L n) := by
  let φ := fundamentalGroupoidNerveUnit X ≫ nerveMap (mapFundamentalGroupoid f)
  let ψ := f ≫ fundamentalGroupoidNerveUnit Y
  let hS : localCoefficientObj (L.pullback f) n =
      (nervePullbackCoefficientData φ L).obj n :=
    (congrArg (fun F : X _⦋n⦌ → ModuleCat.{max uR uX} R => ∐ F)
      (localCoefficientPullbackRawFamilyEq f L n)).trans
        (nervePullbackCoefficientData_obj φ L n).symm
  let hT : nervePullbackCoefficientObj ψ L n =
      (nervePullbackCoefficientData ψ L).obj n :=
    (nervePullbackCoefficientData_obj ψ L n).symm
  exact CategoryTheory.heq_comp hS hT rfl
    (localCoefficientPullbackOriginalObjMap_heq f L n) (HEq.refl _)

@[reassoc]
private theorem rawBarSource_ι
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) {n : ℕ} (σ : X _⦋n⦌) :
    localCoefficientι (L.pullback f) σ ≫
        eqToHom (localCoefficientPullbackOriginalObjEq f L n) =
      eqToHom (localCoefficientPullbackOriginalFamilyEq f L σ) ≫
        nervePullbackCoefficientι (f ≫ fundamentalGroupoidNerveUnit Y) L σ := by
  let φ := fundamentalGroupoidNerveUnit X ≫ nerveMap (mapFundamentalGroupoid f)
  let ψ := f ≫ fundamentalGroupoidNerveUnit Y
  let H := localCoefficientPullbackRawFamilyEq f L n
  let h := (fundamentalGroupoidNerveUnit_naturality f).symm
  have h₀ : localCoefficientι (L.pullback f) σ ≫
      eqToHom (congrArg (fun F : X _⦋n⦌ → ModuleCat.{max uR uX} R => ∐ F) H) =
      eqToHom (congrFun H σ) ≫ nervePullbackCoefficientι φ L σ :=
    CategoryTheory.eqToHom_naturality (fun F => Sigma.ι F σ) H
  have h₁ : nervePullbackCoefficientι φ L σ ≫
      eqToHom (congrArg (fun q => nervePullbackCoefficientObj q L n) h) =
      eqToHom (congrArg (fun q => nervePullbackCoefficientFamily q L n σ) h) ≫
        nervePullbackCoefficientι ψ L σ :=
    CategoryTheory.eqToHom_naturality (fun q => nervePullbackCoefficientι q L σ) h
  let p : localCoefficientObj (L.pullback f) n = nervePullbackCoefficientObj φ L n :=
    congrArg (fun F : X _⦋n⦌ → ModuleCat.{max uR uX} R => ∐ F) H
  let q : nervePullbackCoefficientObj φ L n = nervePullbackCoefficientObj ψ L n :=
    congrArg (fun r => nervePullbackCoefficientObj r L n) h
  change localCoefficientι (L.pullback f) σ ≫ eqToHom (p.trans q) = _
  rw [← eqToHom_trans p q, ← Category.assoc, h₀, Category.assoc, h₁,
    ← Category.assoc, eqToHom_trans]

/-- The original map equals the source chart followed by the actual
existing bar base map, as an equality of whole chain maps. -/
public theorem localCoefficientPullbackChainMap_eq_barSource_base
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) :
    localCoefficientPullbackChainMap f L =
      (localCoefficientPullbackBarSourceIso f L).hom ≫
        nervePullbackCoefficientBaseComplexMap f (fundamentalGroupoidNerveUnit Y) L := by
  ext n : 1
  let ψ := f ≫ fundamentalGroupoidNerveUnit Y
  let hS := localCoefficientChainComplex_X (L.pullback f) n
  let hM := nervePullbackCoefficientComplex_X ψ L n
  let hT := localCoefficientChainComplex_X L n
  let eS := eqToIso hS
  let eM := eqToIso hM
  let eT := eqToIso hT
  let c := eqToHom (localCoefficientPullbackOriginalObjEq f L n)
  let b := nervePullbackCoefficientBaseMap f (fundamentalGroupoidNerveUnit Y) L n
  let a := (localCoefficientPullbackBarSourceIso f L).hom
  let B : nervePullbackCoefficientComplex ψ L ⟶ localCoefficientChainComplex L :=
    nervePullbackCoefficientBaseComplexMap f (fundamentalGroupoidNerveUnit Y) L
  have ha : a.f n = eS.hom ≫ c ≫ eM.inv :=
    componentChartRecipe a n hS hM c
      ((heq_of_eq (localCoefficientPullbackBarSourceIso_hom_f f L n)).trans
        (localCoefficientPullbackOriginalObjMap_heq f L n).symm)
  have hb : B.f n = eM.hom ≫ b ≫ eT.inv :=
    componentChartRecipe B n hM hT b
      (heq_of_eq (nervePullbackCoefficientBaseComplexMap_f
        f (fundamentalGroupoidNerveUnit Y) L n))
  have ho : (localCoefficientPullbackChainMap f L).f n =
      eS.hom ≫ (c ≫ b) ≫ eT.inv :=
    componentChartRecipe (localCoefficientPullbackChainMap f L) n hS hT (c ≫ b)
      ((heq_of_eq (localCoefficientPullbackChainMap_f f L n)).trans
        (localCoefficientPullbackOriginalBaseMap_heq f L n).symm)
  change (localCoefficientPullbackChainMap f L).f n = a.f n ≫ B.f n
  have hab : a.f n ≫ B.f n = eS.hom ≫ (c ≫ b) ≫ eT.inv := by
    rw [ha, hb]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact ho.trans hab.symm

/-- The chart keeps the ACTUAL first-vertex transport on each original
simplex summand. -/
@[reassoc]
public theorem localCoefficientι_barSource
    (f : X ⟶ Y) (L : SSet.LocalSystem R Y) {n : ℕ} (σ : X _⦋n⦌) :
    localCoefficientι (L.pullback f) σ ≫
        (localCoefficientPullbackBarSourceIso f L).hom.f n =
      eqToHom (localCoefficientPullbackFamilyEq f L σ) ≫
        nervePullbackCoefficientι (f ≫ fundamentalGroupoidNerveUnit Y) L σ := by
  rw [localCoefficientPullbackBarSourceIso_hom_f]
  exact CategoryTheory.eqToHom_naturality
    (fun q => nervePullbackCoefficientι q L σ)
    (fundamentalGroupoidNerveUnit_naturality f).symm

section OverBase

variable {Z : SSet.{uX}}

/-- The forced source chart is natural for the ACTUAL original maps over
one coefficient base. The full square includes the original congruence and
composition transports and the existing raw bar source equality. -/
public theorem localCoefficientChainMapOver_barSource
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : X ⟶ Z) (ha : a = f ≫ g)
    (L : SSet.LocalSystem R Z) :
    localCoefficientChainMapOver f g a ha L ≫
        (localCoefficientPullbackBarSourceIso g L).hom =
      (localCoefficientPullbackBarSourceIso a L).hom ≫
        eqToHom (congrArg (fun θ => nervePullbackCoefficientComplex θ L)
          (show a ≫ fundamentalGroupoidNerveUnit Z =
            f ≫ (g ≫ fundamentalGroupoidNerveUnit Z) by
              rw [ha, Category.assoc])) ≫
        nervePullbackCoefficientBaseComplexMap f
          (g ≫ fundamentalGroupoidNerveUnit Z) L := by
  subst a
  ext n : 1
  let L₀ := L.pullback (f ≫ g)
  let L₁ := (L.pullback g).pullback f
  let L₂ := L.pullback g
  let E := (LocalSystem.pullbackCongrIso (rfl : f ≫ g = f ≫ g) L) ≪≫
    LocalSystem.pullbackCompIso f g L
  let ψ := g ≫ fundamentalGroupoidNerveUnit Z
  let χ := (f ≫ g) ≫ fundamentalGroupoidNerveUnit Z
  let θ := f ≫ ψ
  let he : χ = θ := Category.assoc _ _ _
  let h₀ := localCoefficientChainComplex_X L₀ n
  let h₁ := localCoefficientChainComplex_X L₁ n
  let h₂ := localCoefficientChainComplex_X L₂ n
  let h₃ := nervePullbackCoefficientComplex_X ψ L n
  let h₄ := nervePullbackCoefficientComplex_X χ L n
  let h₅ := nervePullbackCoefficientComplex_X θ L n
  let e₀ := eqToIso h₀
  let e₁ := eqToIso h₁
  let e₂ := eqToIso h₂
  let e₃ := eqToIso h₃
  let e₄ := eqToIso h₄
  let e₅ := eqToIso h₅
  let er : localCoefficientObj L₀ n ⟶ localCoefficientObj L₁ n := localCoefficientMap E.hom n
  let fr : localCoefficientObj L₁ n ⟶ localCoefficientObj L₂ n :=
    eqToHom (localCoefficientPullbackOriginalObjEq f L₂ n) ≫
      nervePullbackCoefficientBaseMap f (fundamentalGroupoidNerveUnit Y) L₂ n
  let gr : localCoefficientObj L₂ n ⟶ nervePullbackCoefficientObj ψ L n :=
    eqToHom (localCoefficientPullbackOriginalObjEq g L n)
  let hr : localCoefficientObj L₀ n ⟶ nervePullbackCoefficientObj χ L n :=
    eqToHom (localCoefficientPullbackOriginalObjEq (f ≫ g) L n)
  let ar : nervePullbackCoefficientObj χ L n ⟶ nervePullbackCoefficientObj θ L n :=
    eqToHom (congrArg (fun q => nervePullbackCoefficientObj q L n) he)
  let br := nervePullbackCoefficientBaseMap f ψ L n
  have hE : (localCoefficientChainMap E.hom).f n = e₀.hom ≫ er ≫ e₁.inv :=
    componentChartRecipe (localCoefficientChainMap E.hom) n h₀ h₁ er
      (heq_of_eq (localCoefficientChainMap_f E.hom n))
  have hF : (localCoefficientPullbackChainMap f L₂).f n = e₁.hom ≫ fr ≫ e₂.inv :=
    componentChartRecipe (localCoefficientPullbackChainMap f L₂) n h₁ h₂ fr
      ((heq_of_eq (localCoefficientPullbackChainMap_f f L₂ n)).trans
        (localCoefficientPullbackOriginalBaseMap_heq f L₂ n).symm)
  have hG : (localCoefficientPullbackBarSourceIso g L).hom.f n = e₂.hom ≫ gr ≫ e₃.inv :=
    componentChartRecipe (localCoefficientPullbackBarSourceIso g L).hom n h₂ h₃ gr
      ((heq_of_eq (localCoefficientPullbackBarSourceIso_hom_f g L n)).trans
        (localCoefficientPullbackOriginalObjMap_heq g L n).symm)
  have hH : (localCoefficientPullbackBarSourceIso (f ≫ g) L).hom.f n =
      e₀.hom ≫ hr ≫ e₄.inv :=
    componentChartRecipe (localCoefficientPullbackBarSourceIso (f ≫ g) L).hom n h₀ h₄ hr
      ((heq_of_eq (localCoefficientPullbackBarSourceIso_hom_f (f ≫ g) L n)).trans
        (localCoefficientPullbackOriginalObjMap_heq (f ≫ g) L n).symm)
  have hA : (eqToHom (congrArg (fun q => nervePullbackCoefficientComplex q L) he)).f n =
      e₄.hom ≫ ar ≫ e₅.inv := nerveComplexEq_componentRecipe L he n
  have hB : (nervePullbackCoefficientBaseComplexMap f ψ L).f n =
      e₅.hom ≫ br ≫ e₃.inv :=
    componentChartRecipe (nervePullbackCoefficientBaseComplexMap f ψ L) n h₅ h₃ br
      (heq_of_eq (nervePullbackCoefficientBaseComplexMap_f f ψ L n))
  have hEapp (v : SSet.FundamentalGroupoid X) :
      E.hom.app v = 𝟙 (L₀.obj v) := by
    have hc : (LocalSystem.pullbackCongrIso (rfl : f ≫ g = f ≫ g) L).hom.app v =
        𝟙 ((L.pullback (f ≫ g)).obj v) := by
      rw [LocalSystem.pullbackCongrIso_hom_app]
      change L.map (𝟙 ((mapFundamentalGroupoid (f ≫ g)).obj v)) = 𝟙 _
      exact CategoryTheory.Functor.map_id L _
    dsimp only [E]
    rw [Iso.trans_hom, NatTrans.comp_app, hc,
      LocalSystem.pullbackCompIso_hom_app, Category.id_comp]
  have hιE (σ : X _⦋n⦌) :
      localCoefficientι L₀ σ ≫ er = localCoefficientι L₁ σ := by
    let s : ComposableArrows (SSet.FundamentalGroupoid X) n :=
      (fundamentalGroupoidNerveUnit X).app (op ⦋n⦌) σ
    let v : SSet.FundamentalGroupoid X := s.left
    let j₀ : L₀.obj v ⟶ localCoefficientObj L₀ n := localCoefficientι L₀ σ
    let j₁ : L₀.obj v ⟶ localCoefficientObj L₁ n := localCoefficientι L₁ σ
    let A : L₀.obj v ⟶ L₀.obj v := E.hom.app v
    have hm : j₀ ≫ er = A ≫ j₁ := localCoefficientι_map E.hom (n := n) σ
    have hA : A = 𝟙 (L₀.obj v) := hEapp v
    have hAj : A ≫ j₁ = j₁ :=
      (congrArg (fun k : L₀.obj v ⟶ L₀.obj v => k ≫ j₁) hA).trans
        (Category.id_comp j₁)
    exact hm.trans hAj
  have hraw : er ≫ fr ≫ gr = hr ≫ ar ≫ br := by
    apply nervePullbackCoefficient_hom_ext (n := n)
      (fundamentalGroupoidNerveUnit X) L₀
    intro σ
    let τ : Y _⦋n⦌ := f.app (op ⦋n⦌) σ
    let Tsrc : ModuleCat.{max uR uX} R := localCoefficientFamily L₀ n σ
    let Ucoef : ModuleCat.{max uR uX} R := localCoefficientFamily L₂ n τ
    let Vcoef : ModuleCat.{max uR uX} R := nervePullbackCoefficientFamily χ L n σ
    let Mcoef : ModuleCat.{max uR uX} R := nervePullbackCoefficientFamily ψ L n τ
    let Ttarget : ModuleCat.{max uR uX} R := nervePullbackCoefficientObj ψ L n
    let j₀ : Tsrc ⟶ localCoefficientObj L₀ n := localCoefficientι L₀ σ
    let j₁ : Tsrc ⟶ localCoefficientObj L₁ n := localCoefficientι L₁ σ
    let j₂ : Ucoef ⟶ localCoefficientObj L₂ n := localCoefficientι L₂ τ
    let jf : Ucoef ⟶
        nervePullbackCoefficientObj (f ≫ fundamentalGroupoidNerveUnit Y) L₂ n :=
      nervePullbackCoefficientι (f ≫ fundamentalGroupoidNerveUnit Y) L₂ σ
    let jh : Vcoef ⟶ nervePullbackCoefficientObj χ L n :=
      nervePullbackCoefficientι χ L σ
    let jt : Mcoef ⟶ nervePullbackCoefficientObj θ L n :=
      nervePullbackCoefficientι θ L σ
    let jg : Mcoef ⟶ Ttarget := nervePullbackCoefficientι ψ L τ
    let cf : localCoefficientObj L₁ n ⟶
        nervePullbackCoefficientObj (f ≫ fundamentalGroupoidNerveUnit Y) L₂ n :=
      eqToHom (localCoefficientPullbackOriginalObjEq f L₂ n)
    let bf : nervePullbackCoefficientObj (f ≫ fundamentalGroupoidNerveUnit Y) L₂ n ⟶
        localCoefficientObj L₂ n :=
      nervePullbackCoefficientBaseMap f (fundamentalGroupoidNerveUnit Y) L₂ n
    let pf : Tsrc = Ucoef := localCoefficientPullbackOriginalFamilyEq f L₂ σ
    let pg : Ucoef = Mcoef := localCoefficientPullbackOriginalFamilyEq g L τ
    let ph : Tsrc = Vcoef := localCoefficientPullbackOriginalFamilyEq (f ≫ g) L σ
    let pa : Vcoef = Mcoef :=
      congrArg (fun q => nervePullbackCoefficientFamily q L n σ) he
    let kf : Tsrc ⟶ Ucoef := eqToHom pf
    let kg : Ucoef ⟶ Mcoef := eqToHom pg
    let kh : Tsrc ⟶ Vcoef := eqToHom ph
    let ka : Vcoef ⟶ Mcoef := eqToHom pa
    have h₀₁ : j₀ ≫ er = j₁ := hιE σ
    have hcf : j₁ ≫ cf = kf ≫ jf := rawBarSource_ι f L₂ (n := n) σ
    have hbf : jf ≫ bf = j₂ :=
      nervePullbackCoefficientι_baseMap f (fundamentalGroupoidNerveUnit Y) L₂ σ
    have hF : j₁ ≫ fr = kf ≫ j₂ :=
      (Category.assoc j₁ cf bf).symm.trans
        ((congrArg (fun m : Tsrc ⟶
          nervePullbackCoefficientObj (f ≫ fundamentalGroupoidNerveUnit Y) L₂ n =>
            m ≫ bf) hcf).trans
          ((Category.assoc kf jf bf).trans
            (congrArg (fun m : Ucoef ⟶ localCoefficientObj L₂ n => kf ≫ m) hbf)))
    have hG : j₂ ≫ gr = kg ≫ jg := rawBarSource_ι g L (n := n) τ
    have hH : j₀ ≫ hr = kh ≫ jh := rawBarSource_ι (f ≫ g) L (n := n) σ
    have hA : jh ≫ ar = ka ≫ jt :=
      CategoryTheory.eqToHom_naturality
        (fun q => nervePullbackCoefficientι q L σ) he
    have hB : jt ≫ br = jg := nervePullbackCoefficientι_baseMap f ψ L σ
    have hL₁ : j₀ ≫ (er ≫ fr ≫ gr) = j₁ ≫ (fr ≫ gr) :=
      (Category.assoc j₀ er (fr ≫ gr)).symm.trans
        (congrArg (fun m : Tsrc ⟶ localCoefficientObj L₁ n => m ≫ (fr ≫ gr)) h₀₁)
    have hL₂ : j₁ ≫ (fr ≫ gr) = kf ≫ kg ≫ jg :=
      (Category.assoc j₁ fr gr).symm.trans
        ((congrArg (fun m : Tsrc ⟶ localCoefficientObj L₂ n => m ≫ gr) hF).trans
          ((Category.assoc kf j₂ gr).trans
            (congrArg (fun m : Ucoef ⟶ Ttarget => kf ≫ m) hG)))
    have hR₁ : j₀ ≫ (hr ≫ ar ≫ br) = kh ≫ jh ≫ ar ≫ br :=
      (Category.assoc j₀ hr (ar ≫ br)).symm.trans
        ((congrArg (fun m : Tsrc ⟶ nervePullbackCoefficientObj χ L n =>
          m ≫ (ar ≫ br)) hH).trans
            (Category.assoc kh jh (ar ≫ br)))
    have hAB : jh ≫ (ar ≫ br) = ka ≫ jg :=
      (Category.assoc jh ar br).symm.trans
        ((congrArg (fun m : Vcoef ⟶ nervePullbackCoefficientObj θ L n => m ≫ br) hA).trans
          ((Category.assoc ka jt br).trans
            (congrArg (fun m : Mcoef ⟶ Ttarget => ka ≫ m) hB)))
    have transport_square {D E E' F : ModuleCat.{max uR uX} R}
        (p : D = E) (q : E = F) (r : D = E') (t : E' = F) :
        eqToHom p ≫ eqToHom q = eqToHom r ≫ eqToHom t := by
      rw [eqToHom_trans, eqToHom_trans]
    have hk : kf ≫ kg = kh ≫ ka := transport_square pf pg ph pa
    have hw : kf ≫ kg ≫ jg = kh ≫ ka ≫ jg :=
      (Category.assoc kf kg jg).symm.trans
        ((congrArg (fun m : Tsrc ⟶ Mcoef => m ≫ jg) hk).trans
          (Category.assoc kh ka jg))
    have hR₂ : kh ≫ jh ≫ ar ≫ br = kh ≫ ka ≫ jg :=
      congrArg (fun m : Vcoef ⟶ Ttarget => kh ≫ m) hAB
    exact (hL₁.trans hL₂).trans (hw.trans (hR₁.trans hR₂).symm)
  have hleft :
      (localCoefficientChainMapOver f g (f ≫ g) rfl L ≫
        (localCoefficientPullbackBarSourceIso g L).hom).f n =
      e₀.hom ≫ (er ≫ fr ≫ gr) ≫ e₃.inv := by
    change ((localCoefficientChainMap E.hom ≫ localCoefficientPullbackChainMap f L₂) ≫
      (localCoefficientPullbackBarSourceIso g L).hom).f n = _
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hE, hF, hG]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hright :
      ((localCoefficientPullbackBarSourceIso (f ≫ g) L).hom ≫
        eqToHom (congrArg (fun q => nervePullbackCoefficientComplex q L) he) ≫
          nervePullbackCoefficientBaseComplexMap f ψ L).f n =
      e₀.hom ≫ (hr ≫ ar ≫ br) ≫ e₃.inv := by
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hH, hA, hB]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact hleft.trans ((congrArg (fun b : localCoefficientObj L₀ n ⟶
    nervePullbackCoefficientObj ψ L n => e₀.hom ≫ b ≫ e₃.inv) hraw).trans hright.symm)

end OverBase

end SSet

end
