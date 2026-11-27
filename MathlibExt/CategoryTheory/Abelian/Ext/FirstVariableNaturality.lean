/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.Ext.DerivedFirstVariable
public import MathlibExt.CategoryTheory.Abelian.Projective.ResolutionComparison
public import MathlibExt.CategoryTheory.Abelian.DerivedDeltaFunctor
public import MathlibExt.CategoryTheory.Abelian.RightDerived.FunctorDiagram

/-!
# First-argument naturality of Ext comparisons

In an `R`-linear abelian category, the injective derived-Hom and
projective Ext comparisons commute with precomposition in the first
object. A map `f : M → N` therefore gives maps from the comparisons
at `N` to those at `M`. With both resolution constructions available,
the bridge is an isomorphism of bifunctors, contravariant in the first
object and covariant in the second. Ext retains the category's
hom-set universe.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

universe t u v
variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CategoryTheory.DerivedCoyoneda
variable [HasInjectiveResolutions C] [HasExt.{v} C]

private def sourceComplexMap {M N Y : C} (f : M ⟶ N) (I : InjectiveResolution Y) :
    mappedCocomplex N I ⟶ mappedCocomplex M I :=
  (NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map f.op)
    (ComplexShape.up ℕ)).app I.cocomplex

private def sourceCyclesMap {M N Y : C} (f : M ⟶ N) (I : InjectiveResolution Y) (n : ℕ) :
    cocyclesObj N I n ⟶ cocyclesObj M I n :=
  AddCommGrpCat.ofHom
    { toFun c := ⟨f ≫ c.val, by
        change (f ≫ c.val) ≫ I.cocomplex.d n (n + 1) = 0
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun g => f ≫ g) c.property).trans comp_zero)⟩
      map_zero' := by
        apply Subtype.ext
        exact comp_zero
      map_add' a b := by
        apply Subtype.ext
        exact Preadditive.comp_add M N (I.cocomplex.X n) f a.val b.val }

omit [HasInjectiveResolutions C] in
private lemma sourceCyclesMap_commi {M N Y : C} (f : M ⟶ N)
    (I : InjectiveResolution Y) (n : ℕ) :
    sourceCyclesMap f I n ≫ (homologyDataExt M I n).i =
      (homologyDataExt N I n).i ≫
        ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v}
          (ComplexShape.up ℕ) n).map (sourceComplexMap f I)).τ₂ := by
  apply AddCommGrpCat.ext
  intro c
  rfl

private def sourceHomologyMapData {M N Y : C} (f : M ⟶ N)
    (I : InjectiveResolution Y) (n : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v}
        (ComplexShape.up ℕ) n).map (sourceComplexMap f I))
      (homologyDataExt N I n) (homologyDataExt M I n) where
  φK := sourceCyclesMap f I n
  φH := ((Abelian.extFunctor (C := C) n).map f.op).app Y
  commi := sourceCyclesMap_commi f I n
  commf' := by
    let hN := homologyDataExt N I n
    let hM := homologyDataExt M I n
    let χ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v}
      (ComplexShape.up ℕ) n).map (sourceComplexMap f I)
    have hfN : hN.f' ≫ hN.i = ((mappedCocomplex N I).sc n).f :=
      ShortComplex.LeftHomologyData.f'_i hN
    have hfM : hM.f' ≫ hM.i = ((mappedCocomplex M I).sc n).f :=
      ShortComplex.LeftHomologyData.f'_i hM
    have hi : sourceCyclesMap f I n ≫ hM.i = hN.i ≫ χ.τ₂ :=
      sourceCyclesMap_commi f I n
    have hm : Mono hM.i :=
      ⟨fun _ _ => Fork.IsLimit.hom_ext (cocycleIsKernel M I n)⟩
    have hpost : (hN.f' ≫ sourceCyclesMap f I n) ≫ hM.i =
        (χ.τ₁ ≫ hM.f') ≫ hM.i := by
      calc
        _ = hN.f' ≫ (sourceCyclesMap f I n ≫ hM.i) := Category.assoc _ _ _
        _ = hN.f' ≫ (hN.i ≫ χ.τ₂) := congrArg (fun g => hN.f' ≫ g) hi
        _ = (hN.f' ≫ hN.i) ≫ χ.τ₂ := (Category.assoc _ _ _).symm
        _ = ((mappedCocomplex N I).sc n).f ≫ χ.τ₂ :=
          congrArg (fun g => g ≫ χ.τ₂) hfN
        _ = χ.τ₁ ≫ ((mappedCocomplex M I).sc n).f := χ.comm₁₂.symm
        _ = χ.τ₁ ≫ (hM.f' ≫ hM.i) := congrArg (fun g => χ.τ₁ ≫ g) hfM.symm
        _ = (χ.τ₁ ≫ hM.f') ≫ hM.i := (Category.assoc _ _ _).symm
    exact hm.right_cancellation _ _ hpost
  commπ := by
    apply AddCommGrpCat.ext
    intro c
    exact I.mk₀_comp_extMk c.val (n + 1) rfl c.property f

private theorem comparison_hom_naturality_source {M N : C} (f : M ⟶ N) (n : ℕ) :
    NatTrans.rightDerived (preadditiveCoyoneda.map f.op) n ≫
        (Abelian.rightDerivedCoyonedaIsoExtFunctorObj M n).hom =
      (Abelian.rightDerivedCoyonedaIsoExtFunctorObj N n).hom ≫
        (Abelian.extFunctor (C := C) n).map f.op := by
  apply NatTrans.ext
  funext Y
  let I := injectiveResolution Y
  let FN := preadditiveCoyoneda.obj (op N)
  let FM := preadditiveCoyoneda.obj (op M)
  let iN := I.isoRightDerivedObj FN n
  let iM := I.isoRightDerivedObj FM n
  let hN := (homologyDataExt N I n).homologyIso
  let hM := (homologyDataExt M I n).homologyIso
  let a := (NatTrans.rightDerived (preadditiveCoyoneda.map f.op) n).app Y
  let b := ((Abelian.extFunctor (C := C) n).map f.op).app Y
  let χ := sourceComplexMap f I
  have hi : a ≫ iM.hom = iN.hom ≫ HomologicalComplex.homologyMap χ n :=
    I.isoRightDerivedObj_hom_naturality_functor (preadditiveCoyoneda.map f.op) n
  have hh : HomologicalComplex.homologyMap χ n ≫ hM.hom = hN.hom ≫ b :=
    (sourceHomologyMapData f I n).homologyMap_comm
  have heN : (Abelian.rightDerivedCoyonedaIsoExtFunctorObj N n).hom.app Y =
      iN.hom ≫ hN.hom := by
    apply AddCommGrpCat.ext
    intro z
    rfl
  have heM : (Abelian.rightDerivedCoyonedaIsoExtFunctorObj M n).hom.app Y =
      iM.hom ≫ hM.hom := by
    apply AddCommGrpCat.ext
    intro z
    rfl
  have s₁ : CommSq iN.hom a (HomologicalComplex.homologyMap χ n) iM.hom :=
    ⟨hi.symm⟩
  have s₂ : CommSq hN.hom (HomologicalComplex.homologyMap χ n) b hM.hom :=
    ⟨hh.symm⟩
  have hCore : a ≫ (iM.hom ≫ hM.hom) = (iN.hom ≫ hN.hom) ≫ b :=
    (s₁.horiz_comp s₂).w.symm
  change a ≫ (Abelian.rightDerivedCoyonedaIsoExtFunctorObj M n).hom.app Y =
    (Abelian.rightDerivedCoyonedaIsoExtFunctorObj N n).hom.app Y ≫ b
  exact (congrArg (fun η => a ≫ η) heM).trans
    (hCore.trans (congrArg (fun η => η ≫ b) heN.symm))

end CategoryTheory.DerivedCoyoneda

namespace CategoryTheory.Abelian
variable (R : Type t) [CommRing R] [Linear R C]
  [HasInjectiveResolutions C] [HasExt.{v} C]

private theorem forgetComparison_hom_naturality_first
    {M N : C} (f : M ⟶ N) (n : ℕ) :
    Functor.whiskerRight
        (NatTrans.rightDerived ((linearCoyoneda R C).map f.op) n)
        (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) ≫
      (rightDerivedLinearCoyonedaForgetIso R M n).hom =
        (rightDerivedLinearCoyonedaForgetIso R N n).hom ≫
          (extFunctor (C := C) n).map f.op := by
  let FN : C ⥤ ModuleCat.{v} R := (linearCoyoneda R C).obj (op N)
  let FM : C ⥤ ModuleCat.{v} R := (linearCoyoneda R C).obj (op M)
  let α : FN ⟶ FM := (linearCoyoneda R C).map f.op
  let U : ModuleCat.{v} R ⥤ AddCommGrpCat.{v} := forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
  let cN := FN.rightDerivedCompIsoOfPreservesHomology U n
  let cM := FM.rightDerivedCompIsoOfPreservesHomology U n
  let eN := rightDerivedCoyonedaIsoExtFunctorObj N n
  let eM := rightDerivedCoyonedaIsoExtFunctorObj M n
  let a := Functor.whiskerRight (NatTrans.rightDerived α n) U
  let b := NatTrans.rightDerived (preadditiveCoyoneda.map f.op) n
  let d := (extFunctor (C := C) n).map f.op
  have hc : a ≫ cM.hom = cN.hom ≫ b :=
    Functor.rightDerivedCompIsoOfPreservesHomology_hom_naturality_source FN FM α U n
  have he : b ≫ eM.hom = eN.hom ≫ d :=
    DerivedCoyoneda.comparison_hom_naturality_source f n
  have s₁ : CommSq cN.hom a b cM.hom := ⟨hc.symm⟩
  have s₂ : CommSq eN.hom b d eM.hom := ⟨he.symm⟩
  have hCore : a ≫ (cM.hom ≫ eM.hom) = (cN.hom ≫ eN.hom) ≫ d :=
    (s₁.horiz_comp s₂).w.symm
  have h : a ≫ (rightDerivedLinearCoyonedaForgetIso R M n).hom =
      (rightDerivedLinearCoyonedaForgetIso R N n).hom ≫ d := by
    change a ≫ (cM.hom ≫ eM.hom) = (cN.hom ≫ eN.hom) ≫ d
    exact hCore
  exact h

/-- Let `R` be a commutative ring and `C` an `R`-linear abelian
category with hom-set universe `v`, injective resolutions, and
Ext in universe `v`. For `f : M → N`, the canonical linear comparisons commute
with the derived map `R^nHom(N,-) → R^nHom(M,-)` and Ext
precomposition `Ext^n(N,-) → Ext^n(M,-)`. -/
theorem rightDerivedLinearCoyonedaIsoExtFunctorObj_hom_naturality_first
    {M N : C} (f : M ⟶ N) (n : ℕ) :
    NatTrans.rightDerived ((linearCoyoneda R C).map f.op) n ≫
        (rightDerivedLinearCoyonedaIsoExtFunctorObj R M n).hom =
      (rightDerivedLinearCoyonedaIsoExtFunctorObj R N n).hom ≫
        (linearExtFunctor R C n).map f.op := by
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have h := congrArg (fun η => η.app Y) (forgetComparison_hom_naturality_first R f n)
  have hv := ConcreteCategory.congr_hom h z
  change rightDerivedLinearCoyonedaObjEquiv R M Y n
      (((NatTrans.rightDerived ((linearCoyoneda R C).map f.op) n).app Y).hom z) =
    (Ext.mk₀ f).comp (rightDerivedLinearCoyonedaObjEquiv R N Y n z) (zero_add n)
  rw [rightDerivedLinearCoyonedaObjEquiv_apply, rightDerivedLinearCoyonedaObjEquiv_apply]
  exact hv

end CategoryTheory.Abelian

namespace CategoryTheory.ProjectiveResolution
variable (R : Type t) [CommRing R] [Linear R C] [HasExt.{v} C]

private def sourceLinearYonedaMap {M N : C} {P : ProjectiveResolution M}
    {Q : ProjectiveResolution N} {f : M ⟶ N} (φ : Hom P Q f) (Y : C) :
    Q.linearYonedaComplex R Y ⟶ P.linearYonedaComplex R Y :=
  (HomologicalComplex.unopFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op ((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map φ.hom))

private def sourceLinearYonedaCyclesMap {M N : C} {P : ProjectiveResolution M}
    {Q : ProjectiveResolution N} {f : M ⟶ N} (φ : Hom P Q f) (Y : C) (n : ℕ) :
    ModuleCat.of R (((Q.linearYonedaComplex R Y).sc n).g.hom).ker ⟶
      ModuleCat.of R (((P.linearYonedaComplex R Y).sc n).g.hom).ker :=
  ModuleCat.ofHom
    ((((sourceLinearYonedaMap R φ Y).f n).hom.comp
      (((Q.linearYonedaComplex R Y).sc n).g.hom).ker.subtype).codRestrict
        (((P.linearYonedaComplex R Y).sc n).g.hom).ker (fun c => by
          let χ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
            (ComplexShape.up ℕ) n).map (sourceLinearYonedaMap R φ Y)
          have hc : ((Q.linearYonedaComplex R Y).sc n).g.hom c.val = 0 :=
            c.property
          have hcomm : ((P.linearYonedaComplex R Y).sc n).g.hom
                (((sourceLinearYonedaMap R φ Y).f n).hom c.val) =
              χ.τ₃.hom (((Q.linearYonedaComplex R Y).sc n).g.hom c.val) :=
            ConcreteCategory.congr_hom χ.comm₂₃ c.val
          change ((P.linearYonedaComplex R Y).sc n).g.hom
            (((sourceLinearYonedaMap R φ Y).f n).hom c.val) = 0
          exact hcomm.trans ((congrArg χ.τ₃.hom hc).trans (map_zero χ.τ₃.hom))))

private def sourceLinearYonedaHomologyMapData {M N : C} {P : ProjectiveResolution M}
    {Q : ProjectiveResolution N} {f : M ⟶ N} (φ : Hom P Q f) (Y : C) (n : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
        (ComplexShape.up ℕ) n).map (sourceLinearYonedaMap R φ Y))
      (Q.linearYonedaHomologyDataExt R Y n) (P.linearYonedaHomologyDataExt R Y n) where
  φK := sourceLinearYonedaCyclesMap R φ Y n
  φH := ((Abelian.linearExtFunctor R C n).map f.op).app Y
  commi := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    rfl
  commf' := by
    let hQ := Q.linearYonedaHomologyDataExt R Y n
    let hP := P.linearYonedaHomologyDataExt R Y n
    let χ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
      (ComplexShape.up ℕ) n).map (sourceLinearYonedaMap R φ Y)
    have hfQ : hQ.f' ≫ hQ.i = ((Q.linearYonedaComplex R Y).sc n).f :=
      ShortComplex.LeftHomologyData.f'_i hQ
    have hfP : hP.f' ≫ hP.i = ((P.linearYonedaComplex R Y).sc n).f :=
      ShortComplex.LeftHomologyData.f'_i hP
    have hi : sourceLinearYonedaCyclesMap R φ Y n ≫ hP.i = hQ.i ≫ χ.τ₂ := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      rfl
    have hm : Mono hP.i := inferInstance
    have hpost : (hQ.f' ≫ sourceLinearYonedaCyclesMap R φ Y n) ≫ hP.i =
        (χ.τ₁ ≫ hP.f') ≫ hP.i :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun g => hQ.f' ≫ g) hi).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun g => g ≫ χ.τ₂) hfQ).trans
              (χ.comm₁₂.symm.trans
                ((congrArg (fun g => χ.τ₁ ≫ g) hfP.symm).trans
                  (Category.assoc _ _ _).symm)))))
    exact hm.right_cancellation _ _ hpost
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    let c₀ : Q.complex.X n ⟶ Y := c.val
    have hc : Q.complex.d (n + 1) n ≫ c₀ = 0 :=
      Q.linearYonedaCocycle_closed R Y n c
    have hcP : P.complex.d (n + 1) n ≫ (φ.hom.f n ≫ c₀) = 0 :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ c₀) (φ.hom.comm (n + 1) n).symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun g => φ.hom.f (n + 1) ≫ g) hc).trans comp_zero)))
    change (Abelian.Ext.mk₀ f).comp (Q.extMk c₀ (n + 1) rfl hc) (zero_add n) =
      P.extMk (φ.hom.f n ≫ c₀) (n + 1) rfl hcP
    exact Q.mk₀_comp_extMk c₀ (n + 1) rfl hc φ

private theorem sourceLinearYoneda_homology_naturality {M N : C}
    {P : ProjectiveResolution M} {Q : ProjectiveResolution N} {f : M ⟶ N}
    (φ : Hom P Q f) (Y : C) (n : ℕ) :
    HomologicalComplex.homologyMap (sourceLinearYonedaMap R φ Y) n ≫
        (P.linearYonedaHomologyIsoExt R Y n).hom =
      (Q.linearYonedaHomologyIsoExt R Y n).hom ≫
        ((Abelian.linearExtFunctor R C n).map f.op).app Y :=
  (sourceLinearYonedaHomologyMapData R φ Y n).homologyMap_comm

omit [HasExt.{v} C] in
private theorem sourceIsoExt_naturality [EnoughProjectives C] {M N : C}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (f : M ⟶ N) (φ : Hom P Q f) (Y : C) (n : ℕ) :
    ((_root_.Ext R C n).map f.op).app Y ≫ (P.isoExt (R := R) n Y).hom =
      (Q.isoExt (R := R) n Y).hom ≫
        HomologicalComplex.homologyMap (sourceLinearYonedaMap R φ Y) n := by
  let F := ((linearYoneda R C).obj Y).rightOp
  let KP := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let KQ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  let χ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.hom
  let ψ := sourceLinearYonedaMap R φ Y
  let iP := P.isoLeftDerivedObj F n
  let iQ := Q.isoLeftDerivedObj F n
  let uP := HomologicalComplex.homologyUnop KP n
  let uQ := HomologicalComplex.homologyUnop KQ n
  let a := (F.leftDerived n).map f
  have hI : iP.inv ≫ a = HomologicalComplex.homologyMap χ n ≫ iQ.inv := by
    let s : M ⟶ N := ((ChainComplex.single₀ C).map f).f 0
    have hs : s = f := ChainComplex.single₀_map_f_zero f
    have hπ : φ.hom.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ s :=
      φ.hom_f_zero_comp_π_f_zero
    exact ProjectiveResolution.isoLeftDerivedObj_inv_naturality f P Q φ.hom
      (hπ.trans (congrArg (fun g => P.π.f 0 ≫ g) hs)) F n
  have hIu : a.unop ≫ iP.inv.unop =
      iQ.inv.unop ≫ (HomologicalComplex.homologyMap χ n).unop := by
    have h := congrArg
      (fun (g : KP.homology n ⟶ (F.leftDerived n).obj N) => Quiver.Hom.unop g) hI
    exact (CategoryTheory.unop_comp (f := iP.inv) (g := a)).symm.trans
      (h.trans (CategoryTheory.unop_comp
        (f := HomologicalComplex.homologyMap χ n) (g := iQ.inv)))
  have hχ : (HomologicalComplex.opFunctor (ModuleCat.{v} R)
        (ComplexShape.up ℕ)).map ψ.op = χ := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  have hU : uQ.hom ≫ (HomologicalComplex.homologyMap χ n).unop =
      HomologicalComplex.homologyMap ψ n ≫ uP.hom := by
    have hOp := HomologicalComplex.homologyOp_hom_naturality ψ n
    rw [hχ] at hOp
    have h := congrArg
      (fun (g : KP.homology n ⟶ op ((Q.linearYonedaComplex R Y).homology n)) =>
        Quiver.Hom.unop g) hOp
    exact (CategoryTheory.unop_comp (f := HomologicalComplex.homologyMap χ n)
      (g := (HomologicalComplex.homologyOp (Q.linearYonedaComplex R Y) n).hom)).symm.trans
        (h.trans (CategoryTheory.unop_comp
          (f := (HomologicalComplex.homologyOp (P.linearYonedaComplex R Y) n).hom)
          (g := (HomologicalComplex.homologyMap ψ n).op)))
  have hUi : (HomologicalComplex.homologyMap χ n).unop ≫ uP.inv =
      uQ.inv ≫ HomologicalComplex.homologyMap ψ n := by
    exact (Iso.comp_inv_eq uP).2
      (((Iso.eq_inv_comp uQ).2 hU).trans
        (Category.assoc uQ.inv (HomologicalComplex.homologyMap ψ n) uP.hom).symm)
  have hA : ((_root_.Ext R C n).map f.op).app Y = a.unop := rfl
  have hP : (P.isoExt (R := R) n Y).hom = iP.inv.unop ≫ uP.inv := rfl
  have hQ : (Q.isoExt (R := R) n Y).hom = iQ.inv.unop ≫ uQ.inv := rfl
  have s₁ : CommSq iQ.inv.unop a.unop
      (HomologicalComplex.homologyMap χ n).unop iP.inv.unop := ⟨hIu.symm⟩
  have s₂ : CommSq uQ.inv (HomologicalComplex.homologyMap χ n).unop
      (HomologicalComplex.homologyMap ψ n) uP.inv := ⟨hUi.symm⟩
  have hCore : a.unop ≫ (iP.inv.unop ≫ uP.inv) =
      (iQ.inv.unop ≫ uQ.inv) ≫ HomologicalComplex.homologyMap ψ n :=
    (s₁.horiz_comp s₂).w.symm
  exact (congrArg (fun g => g ≫ (P.isoExt (R := R) n Y).hom) hA).trans
    ((congrArg (fun g => a.unop ≫ g) hP).trans
      (hCore.trans (congrArg (fun g => g ≫ HomologicalComplex.homologyMap ψ n) hQ.symm)))

end CategoryTheory.ProjectiveResolution

namespace CategoryTheory.Abelian
variable (R : Type t) [CommRing R] [Linear R C] [HasExt.{v} C]
  [EnoughProjectives C]

/-- Let `R` be a commutative ring and `C` an `R`-linear abelian
category with enough projectives, hom-set universe `v`, and Ext
in universe `v`. For `f : M → N`, the comparison from projective first-variable
Ext to native linear Ext commutes with the contravariant
precomposition maps induced by `f`. -/
theorem firstVariableLinearExtIso_hom_naturality_first {M N : C} (f : M ⟶ N) (n : ℕ) :
    (_root_.Ext R C n).map f.op ≫ (firstVariableLinearExtIso R M n).hom =
      (firstVariableLinearExtIso R N n).hom ≫ (linearExtFunctor R C n).map f.op := by
  apply NatTrans.ext
  funext Y
  let P := projectiveResolution M
  let Q := projectiveResolution N
  let φ := ProjectiveResolution.liftHom f P Q
  let ψ := ProjectiveResolution.sourceLinearYonedaMap R φ Y
  have hP : (firstVariableLinearExtIso R M n).hom.app Y =
      (P.isoExt (R := R) n Y).hom ≫ (P.linearYonedaHomologyIsoExt R Y n).hom := rfl
  have hQ : (firstVariableLinearExtIso R N n).hom.app Y =
      (Q.isoExt (R := R) n Y).hom ≫ (Q.linearYonedaHomologyIsoExt R Y n).hom := rfl
  have hi := ProjectiveResolution.sourceIsoExt_naturality R P Q f φ Y n
  have hh := ProjectiveResolution.sourceLinearYoneda_homology_naturality R φ Y n
  have s₁ : CommSq (Q.isoExt (R := R) n Y).hom
      (((_root_.Ext R C n).map f.op).app Y)
      (HomologicalComplex.homologyMap ψ n) (P.isoExt (R := R) n Y).hom := ⟨hi.symm⟩
  have s₂ : CommSq (Q.linearYonedaHomologyIsoExt R Y n).hom
      (HomologicalComplex.homologyMap ψ n)
      (((linearExtFunctor R C n).map f.op).app Y)
      (P.linearYonedaHomologyIsoExt R Y n).hom := ⟨hh.symm⟩
  have hCore : ((_root_.Ext R C n).map f.op).app Y ≫
        ((P.isoExt (R := R) n Y).hom ≫ (P.linearYonedaHomologyIsoExt R Y n).hom) =
      ((Q.isoExt (R := R) n Y).hom ≫ (Q.linearYonedaHomologyIsoExt R Y n).hom) ≫
        ((linearExtFunctor R C n).map f.op).app Y := (s₁.horiz_comp s₂).w.symm
  change ((_root_.Ext R C n).map f.op).app Y ≫ (firstVariableLinearExtIso R M n).hom.app Y =
    (firstVariableLinearExtIso R N n).hom.app Y ≫ ((linearExtFunctor R C n).map f.op).app Y
  exact (congrArg (fun g => ((_root_.Ext R C n).map f.op).app Y ≫ g) hP).trans
    (hCore.trans (congrArg
      (fun g => g ≫ ((linearExtFunctor R C n).map f.op).app Y) hQ.symm))

variable [HasInjectiveResolutions C]

/-- Let `R` be a commutative ring and `C` an `R`-linear abelian
category with enough projectives, hom-set universe `v`, and Ext
in universe `v`. Suppose `C` also has injective resolutions. For `f : M → N`, the forward bridge from right-derived linear
Hom to projective first-variable Ext commutes with the derived
precomposition map and the first-variable Ext map. -/
theorem rightDerivedLinearCoyonedaIsoFirstVariableExt_hom_naturality_first
    {M N : C} (f : M ⟶ N) (n : ℕ) :
    NatTrans.rightDerived ((linearCoyoneda R C).map f.op) n ≫
        (rightDerivedLinearCoyonedaIsoFirstVariableExt R M n).hom =
      (rightDerivedLinearCoyonedaIsoFirstVariableExt R N n).hom ≫
        (_root_.Ext R C n).map f.op := by
  let aM := rightDerivedLinearCoyonedaIsoExtFunctorObj R M n
  let aN := rightDerivedLinearCoyonedaIsoExtFunctorObj R N n
  let bM := firstVariableLinearExtIso R M n
  let bN := firstVariableLinearExtIso R N n
  let d := NatTrans.rightDerived ((linearCoyoneda R C).map f.op) n
  let h := (_root_.Ext R C n).map f.op
  let e := (linearExtFunctor R C n).map f.op
  have ha : d ≫ aM.hom = aN.hom ≫ e :=
    rightDerivedLinearCoyonedaIsoExtFunctorObj_hom_naturality_first R f n
  have hb : h ≫ bM.hom = bN.hom ≫ e :=
    firstVariableLinearExtIso_hom_naturality_first R f n
  have hbi : e ≫ bM.inv = bN.inv ≫ h := by
    exact (Iso.comp_inv_eq bM).2
      (((Iso.eq_inv_comp bN).2 hb.symm).trans (Category.assoc bN.inv h bM.hom).symm)
  calc
    d ≫ (aM.hom ≫ bM.inv) = (d ≫ aM.hom) ≫ bM.inv := (Category.assoc _ _ _).symm
    _ = (aN.hom ≫ e) ≫ bM.inv := congrArg (fun k => k ≫ bM.inv) ha
    _ = aN.hom ≫ (e ≫ bM.inv) := Category.assoc _ _ _
    _ = aN.hom ≫ (bN.inv ≫ h) := congrArg (fun k => aN.hom ≫ k) hbi
    _ = (aN.hom ≫ bN.inv) ≫ h := (Category.assoc _ _ _).symm

/-- Let `R` be a commutative ring and `C` an `R`-linear abelian
category with enough projectives, hom-set universe `v`, and Ext
in universe `v`. Suppose `C` also has injective resolutions. For `f : M → N`, the inverse projective-Ext-to-derived-Hom
bridge commutes with the same contravariant first-argument maps. -/
theorem rightDerivedLinearCoyonedaIsoFirstVariableExt_inv_naturality_first
    {M N : C} (f : M ⟶ N) (n : ℕ) :
    (_root_.Ext R C n).map f.op ≫
        (rightDerivedLinearCoyonedaIsoFirstVariableExt R M n).inv =
      (rightDerivedLinearCoyonedaIsoFirstVariableExt R N n).inv ≫
        NatTrans.rightDerived ((linearCoyoneda R C).map f.op) n := by
  let eM := rightDerivedLinearCoyonedaIsoFirstVariableExt R M n
  let eN := rightDerivedLinearCoyonedaIsoFirstVariableExt R N n
  have h := rightDerivedLinearCoyonedaIsoFirstVariableExt_hom_naturality_first R f n
  exact (Iso.comp_inv_eq eM).2
    (((Iso.eq_inv_comp eN).2 h.symm).trans
      (Category.assoc eN.inv (NatTrans.rightDerived ((linearCoyoneda R C).map f.op) n)
        eM.hom).symm)

/-- Let `R` be a commutative ring and `C` an `R`-linear abelian
category with hom-set universe `v`, injective resolutions, and
Ext in universe `v`. For fixed degree `n`, the assignment
`X ↦ R^nHom_C(X,-)` is a functor from `Cᵒᵖ` to module-valued
functors on `C`, with maps given by derived precomposition. -/
def rightDerivedLinearCoyonedaFamily (n : ℕ) : Cᵒᵖ ⥤ (C ⥤ ModuleCat.{v} R) :=
  (additiveFunctor C (ModuleCat.{v} R)).lift (linearCoyoneda R C)
      (fun X => by
        change ((linearCoyoneda R C).obj X).Additive
        infer_instance) ⋙
    rightDerivedDeltaFunctorFamily C (ModuleCat.{v} R) ⋙
      CohomologicalDeltaFunctor.evaluation C (ModuleCat.{v} R) n

/-- Let `R` be a commutative ring and `C` an `R`-linear abelian
category with enough projectives, hom-set universe `v`, and Ext
in universe `v`. Suppose `C` also has injective resolutions. The pointwise bridge comparisons form a natural isomorphism
from the contravariant family of right-derived linear Hom functors
to the projective first-variable Ext bifunctor in degree `n`. -/
def rightDerivedLinearCoyonedaFamilyIsoFirstVariableExt (n : ℕ) :
    rightDerivedLinearCoyonedaFamily R n ≅ _root_.Ext R C n :=
  NatIso.ofComponents
    (fun X => by
      change ((linearCoyoneda R C).obj X).rightDerived n ≅ (_root_.Ext R C n).obj X
      simpa only [Opposite.op_unop] using
        rightDerivedLinearCoyonedaIsoFirstVariableExt R X.unop n)
    (by
      intro X Y f
      change NatTrans.rightDerived ((linearCoyoneda R C).map f) n ≫
          (rightDerivedLinearCoyonedaIsoFirstVariableExt R Y.unop n).hom =
        (rightDerivedLinearCoyonedaIsoFirstVariableExt R X.unop n).hom ≫ (_root_.Ext R C n).map f
      simpa only [Quiver.Hom.op_unop, Opposite.op_unop] using
        rightDerivedLinearCoyonedaIsoFirstVariableExt_hom_naturality_first R f.unop n)

/-- Let `R` be a commutative ring and `C` an `R`-linear abelian
category with enough projectives, hom-set universe `v`, and Ext
in universe `v`. Suppose `C` also has injective resolutions. At the opposite object `Mᵒᵖ`, the family isomorphism is the
canonical degree-`n` bridge from `R^nHom_C(M,-)` to projective
first-variable Ext. -/
lemma rightDerivedLinearCoyonedaFamilyIsoFirstVariableExt_app (M : C) (n : ℕ) :
    (rightDerivedLinearCoyonedaFamilyIsoFirstVariableExt R n).app (op M) =
      rightDerivedLinearCoyonedaIsoFirstVariableExt R M n := rfl

end CategoryTheory.Abelian
