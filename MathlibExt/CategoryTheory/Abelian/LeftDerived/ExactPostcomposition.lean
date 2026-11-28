/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.CompositionNaturality
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ZeroNaturality
public import MathlibExt.Algebra.Homology.ShortComplex.MapHomologyOpcycles
public import MathlibExt.Algebra.Homology.HomologySequenceMap
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.LongExact
public import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Homology-preserving postcomposition of left-derived maps

Let `C,D,E` be abelian, with projective resolutions in `C`,
`F : C → D` additive and `U : D → E` additive and preserving homology.
The comparison `L_nF ⋙ U ≅ L_n(F ⋙ U)` preserves canonical
augmentations in degree zero and connecting maps on short exact
sequences. It is natural in transformations of homology-preserving
target functors. No right-exactness assumption on `F` is needed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory

section ResolutionAugmentation

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E]

/-- Let `C,D,E` be abelian, `P` a projective resolution of `X`,
`F : C → D` additive, and `U : D → E` additive and preserving right
homology of the degree-zero short complex of `F(P)`. Its opcycles
comparison followed by `U` of the augmentation to `F(X)` equals the
augmentation to `U(F(X))` for `(F ⋙ U)(P)`. -/
@[reassoc]
theorem ProjectiveResolution.mapOpcyclesIso_hom_comp_fromLeftDerivedZero'
    {X : C} (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive]
    (U : D ⥤ E) [U.Additive]
    [U.PreservesRightHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).sc 0)] :
    ((((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).sc 0).mapOpcyclesIso U).hom ≫
        U.map (P.fromLeftDerivedZero' F) =
      P.fromLeftDerivedZero' (F ⋙ U) := by
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let S := K.sc 0
  let SU := S.map U
  let eO := S.mapOpcyclesIso U
  let a : S.opcycles ⟶ F.obj X := P.fromLeftDerivedZero' F
  let aU : SU.opcycles ⟶ U.obj (F.obj X) := P.fromLeftDerivedZero' (F ⋙ U)
  have hp : SU.pOpcycles ≫ eO.hom = U.map S.pOpcycles :=
    ShortComplex.pOpcycles_comp_mapOpcyclesIso_hom S U
  have ha : S.pOpcycles ≫ a = F.map (P.π.f 0) :=
    P.pOpcycles_comp_fromLeftDerivedZero' F
  have haU : SU.pOpcycles ≫ aU = U.map (F.map (P.π.f 0)) :=
    P.pOpcycles_comp_fromLeftDerivedZero' (F ⋙ U)
  have h : eO.hom ≫ U.map a = aU := by
    apply (cancel_epi SU.pOpcycles).1
    have hassoc :
        SU.pOpcycles ≫ (eO.hom ≫ U.map a) =
          (SU.pOpcycles ≫ eO.hom) ≫ U.map a :=
      (Category.assoc _ _ _).symm
    have hprojection :
        (SU.pOpcycles ≫ eO.hom) ≫ U.map a =
          U.map S.pOpcycles ≫ U.map a :=
      congrArg (fun (f : SU.X₂ ⟶ U.obj S.opcycles) => f ≫ U.map a) hp
    have hcomp :
        U.map S.pOpcycles ≫ U.map a = U.map (S.pOpcycles ≫ a) :=
      (U.map_comp S.pOpcycles a).symm
    have haugmentation :
        U.map (S.pOpcycles ≫ a) = U.map (F.map (P.π.f 0)) :=
      congrArg (fun (f : S.X₂ ⟶ F.obj X) => U.map f) ha
    exact hassoc.trans (hprojection.trans (hcomp.trans (haugmentation.trans haU.symm)))
  exact h

end ResolutionAugmentation

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E]
  (F : C ⥤ D) [F.Additive]

private lemma exactPostcomp_hom_app (U : D ⥤ E) [U.Additive] [U.PreservesHomology]
    (n : ℕ) (X : C) :
    let P := projectiveResolution X
    let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
    (F.leftDerivedCompIsoOfPreservesHomology U n).hom.app X =
      U.map (P.isoLeftDerivedObj F n).hom ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n U).inv.app K ≫
          (P.isoLeftDerivedObj (F ⋙ U) n).inv := by
  rfl

private lemma canonicalHomologyIncl_inv (K : ChainComplex D ℕ)
    (U : D ⥤ E) [U.Additive] [U.PreservesHomology] (n : ℕ) :
    (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n U).inv.app K ≫
        ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homologyι n =
      U.map (K.homologyι n) ≫ ((K.sc n).mapOpcyclesIso U).inv := by
  have h := ShortComplex.mapHomologyIso_inv_comp_homologyι (K.sc n) U
  exact h

/-- Let `C,D,E` be abelian, with projective resolutions in `C`,
`F : C → D` additive and `U : D → E` additive and preserving homology. The forward degree-zero
postcomposition comparison followed
by the augmentation of `F ⋙ U` equals `U` applied to the canonical
augmentation `L₀F → F`. -/
@[reassoc]
theorem leftDerivedCompIsoOfPreservesHomology_hom_fromLeftDerivedZero
    (U : D ⥤ E) [U.Additive] [U.PreservesHomology] :
    (F.leftDerivedCompIsoOfPreservesHomology U 0).hom ≫
        (F ⋙ U).fromLeftDerivedZero =
      whiskerRight F.fromLeftDerivedZero U := by
  apply NatTrans.ext
  funext X
  let P := projectiveResolution X
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let KU := (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  let H := HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) 0
  let HU := HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) 0
  let eH := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) 0 U).app K
  let eO := (K.sc 0).mapOpcyclesIso U
  let I := P.isoLeftDerivedObj F 0
  let J := P.isoLeftDerivedObj (F ⋙ U) 0
  let i : H.obj K ⟶ K.opcycles 0 := K.homologyι 0
  let iU : HU.obj KU ⟶ (KU.sc 0).opcycles := KU.homologyι 0
  let a : K.opcycles 0 ⟶ F.obj X := P.fromLeftDerivedZero' F
  let aU : (KU.sc 0).opcycles ⟶ U.obj (F.obj X) := P.fromLeftDerivedZero' (F ⋙ U)
  let b : H.obj K ⟶ F.obj X := i ≫ a
  let bU : HU.obj KU ⟶ U.obj (F.obj X) := iU ≫ aU
  have hF : F.fromLeftDerivedZero.app X = I.hom ≫ b := P.fromLeftDerivedZero_eq F
  have hFU : (F ⋙ U).fromLeftDerivedZero.app X = J.hom ≫ bU :=
    P.fromLeftDerivedZero_eq (F ⋙ U)
  have hO : eO.hom ≫ U.map a = aU :=
    P.mapOpcyclesIso_hom_comp_fromLeftDerivedZero' F U
  have hOinv : eO.inv ≫ aU = U.map a :=
    (congrArg (fun f => eO.inv ≫ f) hO).symm.trans (eO.inv_hom_id_assoc (U.map a))
  have hIncl : eH.inv ≫ iU = U.map i ≫ eO.inv := canonicalHomologyIncl_inv K U 0
  have hTail : eH.inv ≫ bU = U.map b := by
    calc
      eH.inv ≫ (iU ≫ aU) = (eH.inv ≫ iU) ≫ aU := (Category.assoc _ _ _).symm
      _ = (U.map i ≫ eO.inv) ≫ aU := congrArg (fun f => f ≫ aU) hIncl
      _ = U.map i ≫ (eO.inv ≫ aU) := Category.assoc _ _ _
      _ = U.map i ≫ U.map a := congrArg (fun f => U.map i ≫ f) hOinv
      _ = U.map (i ≫ a) := (U.map_comp i a).symm
  have hJ : J.inv ≫ (F ⋙ U).fromLeftDerivedZero.app X = bU :=
    (congrArg (fun f => J.inv ≫ f) hFU).trans (J.inv_hom_id_assoc bU)
  have hComp : (F.leftDerivedCompIsoOfPreservesHomology U 0).hom.app X =
      U.map I.hom ≫ eH.inv ≫ J.inv := exactPostcomp_hom_app F U 0 X
  have hAll : (F.leftDerivedCompIsoOfPreservesHomology U 0).hom.app X ≫
      (F ⋙ U).fromLeftDerivedZero.app X = U.map (F.fromLeftDerivedZero.app X) := by
    calc
      _ = (U.map I.hom ≫ eH.inv ≫ J.inv) ≫ (F ⋙ U).fromLeftDerivedZero.app X :=
        congrArg (fun f => f ≫ (F ⋙ U).fromLeftDerivedZero.app X) hComp
      _ = U.map I.hom ≫ (eH.inv ≫ (J.inv ≫ (F ⋙ U).fromLeftDerivedZero.app X)) := by
        simp only [Category.assoc]
      _ = U.map I.hom ≫ (eH.inv ≫ bU) :=
        congrArg (fun f => U.map I.hom ≫ (eH.inv ≫ f)) hJ
      _ = U.map I.hom ≫ U.map b := congrArg (fun f => U.map I.hom ≫ f) hTail
      _ = U.map (I.hom ≫ b) := (U.map_comp I.hom b).symm
      _ = U.map (F.fromLeftDerivedZero.app X) := congrArg U.map hF.symm
  exact hAll

/-- Let `C,D,E` be abelian, with projective resolutions in `C`,
`F : C → D` additive and `U : D → E` additive and preserving homology. The inverse degree-zero
comparison followed by `U` of the
augmentation `L₀F → F` equals the augmentation of `F ⋙ U`. -/
@[reassoc]
theorem leftDerivedCompIsoOfPreservesHomology_inv_fromLeftDerivedZero
    (U : D ⥤ E) [U.Additive] [U.PreservesHomology] :
    (F.leftDerivedCompIsoOfPreservesHomology U 0).inv ≫
        whiskerRight F.fromLeftDerivedZero U =
      (F ⋙ U).fromLeftDerivedZero := by
  rw [← leftDerivedCompIsoOfPreservesHomology_hom_fromLeftDerivedZero F U]
  exact (F.leftDerivedCompIsoOfPreservesHomology U 0).inv_hom_id_assoc _

/-- Let `C,D,E` be abelian, with projective resolutions in `C`,
`F : C → D` additive, and `U,V : D → E` additive and preserving
homology. For `τ : U → V`, the forward comparisons satisfy
`τ_(L_nF) ≫ e_V = e_U ≫ L_n(F ⋙ τ)`. -/
@[reassoc]
theorem leftDerivedCompIsoOfPreservesHomology_hom_naturality_postcomposition
    {U V : D ⥤ E} [U.Additive] [V.Additive]
    [U.PreservesHomology] [V.PreservesHomology] (τ : U ⟶ V) (n : ℕ) :
    whiskerLeft (F.leftDerived n) τ ≫
        (F.leftDerivedCompIsoOfPreservesHomology V n).hom =
      (F.leftDerivedCompIsoOfPreservesHomology U n).hom ≫
        NatTrans.leftDerived (whiskerLeft F τ) n := by
  apply NatTrans.ext
  funext X
  let P := projectiveResolution X
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let H := HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n
  let A := (F.leftDerived n).obj X
  let A' := (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).obj K
  let I := P.isoLeftDerivedObj F n
  let eU := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n U).app K
  let eV := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V).app K
  let JU := P.isoLeftDerivedObj (F ⋙ U) n
  let JV := P.isoLeftDerivedObj (F ⋙ V) n
  let φ := (NatTrans.mapHomologicalComplex τ (ComplexShape.down ℕ)).app K
  let r := (NatTrans.leftDerived (whiskerLeft F τ) n).app X
  have hφ : (NatTrans.mapHomologicalComplex (whiskerLeft F τ) (ComplexShape.down ℕ)).app
      P.complex = φ := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  have hA : τ.app A ≫ V.map I.hom = U.map I.hom ≫ τ.app A' := (τ.naturality I.hom).symm
  have hCan : H.map φ ≫ eV.hom = eU.hom ≫ τ.app A' :=
    HomologicalComplex.mapHomologyFunctorIso_naturality_transformation K n U V τ
  have hB : τ.app A' ≫ eV.inv = eU.inv ≫ H.map φ := by
    apply (cancel_mono eV.hom).1
    calc
      (τ.app A' ≫ eV.inv) ≫ eV.hom = τ.app A' := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = eU.inv ≫ (eU.hom ≫ τ.app A') := by simp only [Iso.inv_hom_id_assoc]
      _ = eU.inv ≫ (H.map φ ≫ eV.hom) := congrArg (fun f => eU.inv ≫ f) hCan.symm
      _ = (eU.inv ≫ H.map φ) ≫ eV.hom := (Category.assoc _ _ _).symm
  have hC : H.map φ ≫ JV.inv = JU.inv ≫ r := by
    have h := P.isoLeftDerivedObj_inv_naturality_functor (whiskerLeft F τ) n
    rw [hφ] at h
    exact h
  have sa : CommSq (U.map I.hom) (τ.app A) (τ.app A') (V.map I.hom) := ⟨hA.symm⟩
  have sb : CommSq eU.inv (τ.app A') (H.map φ) eV.inv := ⟨hB.symm⟩
  have sc : CommSq JU.inv (H.map φ) r JV.inv := ⟨hC.symm⟩
  simp only [NatTrans.comp_app]
  rw [exactPostcomp_hom_app F U n X, exactPostcomp_hom_app F V n X]
  change τ.app A ≫ (V.map I.hom ≫ eV.inv ≫ JV.inv) =
    (U.map I.hom ≫ eU.inv ≫ JU.inv) ≫ r
  exact (sa.horiz_comp (sb.horiz_comp sc)).w.symm

/-- Let `C,D,E` be abelian, with projective resolutions in `C`,
`F : C → D` additive, and `U,V : D → E` additive and preserving
homology. For `τ : U → V`, the inverse comparisons satisfy
`L_n(F ⋙ τ) ≫ e_V⁻¹ = e_U⁻¹ ≫ τ_(L_nF)`. -/
@[reassoc]
theorem leftDerivedCompIsoOfPreservesHomology_inv_naturality_postcomposition
    {U V : D ⥤ E} [U.Additive] [V.Additive]
    [U.PreservesHomology] [V.PreservesHomology] (τ : U ⟶ V) (n : ℕ) :
    NatTrans.leftDerived (whiskerLeft F τ) n ≫
        (F.leftDerivedCompIsoOfPreservesHomology V n).inv =
      (F.leftDerivedCompIsoOfPreservesHomology U n).inv ≫
        whiskerLeft (F.leftDerived n) τ := by
  apply (cancel_epi (F.leftDerivedCompIsoOfPreservesHomology U n).hom).1
  rw [← Category.assoc,
    ← leftDerivedCompIsoOfPreservesHomology_hom_naturality_postcomposition F τ n]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Let `C,D,E` be abelian, with projective resolutions in `C`,
`F : C → D` additive and `U : D → E` additive and preserving homology. For any `V : D → E` naturally
isomorphic to `U`, additivity
and homology preservation transfer to `V`; the forward postcomposition
comparisons commute with the given target-functor isomorphism. -/
@[reassoc]
theorem leftDerivedCompIsoOfPreservesHomology_hom_naturality_postcomposition_iso
    {U V : D ⥤ E} [U.Additive] [U.PreservesHomology] (e : U ≅ V) (n : ℕ) :
    letI := Functor.additive_of_iso e
    letI := Functor.preservesHomology_of_iso e
    whiskerLeft (F.leftDerived n) e.hom ≫
        (F.leftDerivedCompIsoOfPreservesHomology V n).hom =
      (F.leftDerivedCompIsoOfPreservesHomology U n).hom ≫
        NatTrans.leftDerived (whiskerLeft F e.hom) n := by
  let := Functor.additive_of_iso e
  let := Functor.preservesHomology_of_iso e
  exact leftDerivedCompIsoOfPreservesHomology_hom_naturality_postcomposition F e.hom n


/-- Let `C,D,E` be abelian, with projective resolutions in `C`,
`F : C → D` additive and `U : D → E` additive and preserving homology. For short exact `S : X₁ → X₂
→ X₃`, the forward comparisons
in degrees `n+1,n` satisfy
`e_(n+1),X₃ ≫ δ_(F⋙U),n = U(δ_F,n) ≫ e_n,X₁`. -/
@[reassoc]
theorem leftDerivedCompIsoOfPreservesHomology_hom_LDdelta
    (U : D ⥤ E) [U.Additive] [U.PreservesHomology]
    (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact) :
    (F.leftDerivedCompIsoOfPreservesHomology U (n + 1)).hom.app S.X₃ ≫
        LeftDerivedDelta.LDdelta (F ⋙ U) n S hS =
      U.map (LeftDerivedDelta.LDdelta F n S hS) ≫
        (F.leftDerivedCompIsoOfPreservesHomology U n).hom.app S.X₁ := by
  let : ∀ {X Y : D} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) U :=
    fun {X Y} f => Functor.PreservesHomology.preservesKernel U f
  let : ∀ {X Y : D} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) U :=
    fun {X Y} f => Functor.PreservesHomology.preservesCokernel U f
  let : PreservesFiniteLimits U := Functor.preservesFiniteLimits_of_preservesKernels U
  let : PreservesFiniteColimits U := Functor.preservesFiniteColimits_of_preservesCokernels U
  let K₃ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (projectiveResolution S.X₃).complex
  let K₁ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (projectiveResolution S.X₁).complex
  let a₃ := (projectiveResolution S.X₃).isoLeftDerivedObj F (n + 1)
  let a₁ := (projectiveResolution S.X₁).isoLeftDerivedObj F n
  let b₃ := (projectiveResolution S.X₃).isoLeftDerivedObj (F ⋙ U) (n + 1)
  let b₁ := (projectiveResolution S.X₁).isoLeftDerivedObj (F ⋙ U) n
  let e₃ := (HomologicalComplex.mapHomologyFunctorIso
    (c := ComplexShape.down ℕ) (n + 1) U).app K₃
  let e₁ := (HomologicalComplex.mapHomologyFunctorIso
    (c := ComplexShape.down ℕ) n U).app K₁
  let hF := LeftDerivedDelta.LDhorseshoeF_shortExact F S hS
  let hFU := LeftDerivedDelta.LDhorseshoeF_shortExact (F ⋙ U) S hS
  have hMU : ((LeftDerivedDelta.LDhorseshoeF F S hS).map
      (U.mapHomologicalComplex (ComplexShape.down ℕ))).ShortExact := by
    change (LeftDerivedDelta.LDhorseshoeF (F ⋙ U) S hS).ShortExact
    exact hFU
  let dF := LeftDerivedDelta.LDdelta F n S hS
  let dFU := LeftDerivedDelta.LDdelta (F ⋙ U) n S hS
  let dH := hF.δ (n + 1) n (ComplexShape.down_mk _ _ rfl)
  let dHU := hFU.δ (n + 1) n (ComplexShape.down_mk _ _ rfl)
  have hFaug : dF ≫ a₁.hom = a₃.hom ≫ dH :=
    (Iso.eq_comp_inv a₁).mp
      ((LeftDerivedDelta.LDdelta_eq F n S hS hF).trans
        (Category.assoc a₃.hom dH a₁.inv).symm)
  have hMapped : U.map dF ≫ U.map a₁.hom = U.map a₃.hom ≫ U.map dH :=
    (U.map_comp dF a₁.hom).symm.trans
      ((congrArg U.map hFaug).trans (U.map_comp a₃.hom dH))
  have hMiddle : e₃.inv ≫ dHU = U.map dH ≫ e₁.inv := by
    have h := ShortComplex.ShortExact.mapHomologyFunctorIso_inv_δ U hF hMU
      (n + 1) n (ComplexShape.down_mk _ _ rfl)
    exact h
  have hLast : b₃.inv ≫ dFU = dHU ≫ b₁.inv :=
    (Iso.inv_comp_eq b₃).2 (LeftDerivedDelta.LDdelta_eq (F ⋙ U) n S hS hFU)
  have sa : CommSq (U.map a₃.hom) (U.map dF) (U.map dH) (U.map a₁.hom) :=
    ⟨hMapped.symm⟩
  have sb : CommSq e₃.inv (U.map dH) dHU e₁.inv := ⟨hMiddle⟩
  have sc : CommSq b₃.inv dHU dFU b₁.inv := ⟨hLast⟩
  have hCore : (U.map a₃.hom ≫ e₃.inv ≫ b₃.inv) ≫ dFU =
      U.map dF ≫ (U.map a₁.hom ≫ e₁.inv ≫ b₁.inv) :=
    (sa.horiz_comp (sb.horiz_comp sc)).w
  have hσ₃ : (F.leftDerivedCompIsoOfPreservesHomology U (n + 1)).hom.app S.X₃ =
      U.map a₃.hom ≫ e₃.inv ≫ b₃.inv := exactPostcomp_hom_app F U (n + 1) S.X₃
  have hσ₁ : (F.leftDerivedCompIsoOfPreservesHomology U n).hom.app S.X₁ =
      U.map a₁.hom ≫ e₁.inv ≫ b₁.inv := exactPostcomp_hom_app F U n S.X₁
  exact (congrArg (fun q => q ≫ dFU) hσ₃).trans
    (hCore.trans (congrArg (fun q => U.map dF ≫ q) hσ₁.symm))

/-- Let `C,D,E` be abelian, with projective resolutions in `C`,
`F : C → D` additive and `U : D → E` additive and preserving homology. For short exact `S : X₁ → X₂
→ X₃`, the inverse comparisons
satisfy `e_(n+1),X₃⁻¹ ≫ U(δ_F,n) = δ_(F⋙U),n ≫ e_n,X₁⁻¹`. -/
@[reassoc]
theorem leftDerivedCompIsoOfPreservesHomology_inv_LDdelta
    (U : D ⥤ E) [U.Additive] [U.PreservesHomology]
    (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact) :
    (F.leftDerivedCompIsoOfPreservesHomology U (n + 1)).inv.app S.X₃ ≫
        U.map (LeftDerivedDelta.LDdelta F n S hS) =
      LeftDerivedDelta.LDdelta (F ⋙ U) n S hS ≫
        (F.leftDerivedCompIsoOfPreservesHomology U n).inv.app S.X₁ := by
  let e₃ := (F.leftDerivedCompIsoOfPreservesHomology U (n + 1)).app S.X₃
  let e₁ := (F.leftDerivedCompIsoOfPreservesHomology U n).app S.X₁
  let d := U.map (LeftDerivedDelta.LDdelta F n S hS)
  let d' := LeftDerivedDelta.LDdelta (F ⋙ U) n S hS
  have h : e₃.hom ≫ d' = d ≫ e₁.hom :=
    leftDerivedCompIsoOfPreservesHomology_hom_LDdelta F U n S hS
  exact (Iso.eq_comp_inv e₁).2
    ((Category.assoc e₃.inv d e₁.hom).trans ((Iso.inv_comp_eq e₃).2 h.symm))

end Functor
end CategoryTheory
