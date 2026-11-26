/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Projective linear Ext and derived-category Ext

The linear Yoneda complex of a projective resolution computes
derived-category Ext. Its map sends a cocycle to
`ProjectiveResolution.extMk`. Composing with `ProjectiveResolution.isoExt`
compares the first-variable `_root_.Ext` functor with `Abelian.Ext`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe r v u

namespace CategoryTheory.ProjectiveResolution

variable (R : Type r) [Ring R]
variable {C : Type u} [Category.{v} C] [Abelian C] [CategoryTheory.Linear R C]
variable [HasExt.{v} C] {X : C} (P : ProjectiveResolution X) (Y : C) (n : ℕ)

/-- The linear Yoneda complex of the resolution. -/
noncomputable abbrev linearYonedaComplex : CochainComplex (ModuleCat.{v} R) ℕ :=
  P.complex.linearYonedaObj R Y

omit [HasExt.{v} C] in
/-- The outgoing differential is precomposition with the resolution differential. -/
theorem linearYonedaComplex_g_apply
    (f : ↥((P.linearYonedaComplex R Y).sc n).X₂) :
    ((P.linearYonedaComplex R Y).sc n).g.hom f =
      P.complex.d ((ComplexShape.up ℕ).next n) n ≫
        (f : P.complex.X n ⟶ Y) :=
  rfl

omit [HasExt.{v} C] in
/-- The incoming differential is precomposition with the resolution differential. -/
theorem linearYonedaComplex_f_apply
    (f : ↥((P.linearYonedaComplex R Y).sc n).X₁) :
    ((P.linearYonedaComplex R Y).sc n).f.hom f =
      P.complex.d n ((ComplexShape.up ℕ).prev n) ≫
        (f : P.complex.X ((ComplexShape.up ℕ).prev n) ⟶ Y) :=
  rfl

omit [HasExt.{v} C] in
/-- The kernel condition in the mapped complex is the usual cocycle equation. -/
theorem linearYonedaCocycle_closed
    (f : (((P.linearYonedaComplex R Y).sc n).g.hom).ker) :
    P.complex.d (n + 1) n ≫ (f.val : P.complex.X n ⟶ Y) = 0 := by
  have hf : P.complex.d ((ComplexShape.up ℕ).next n) n ≫
      (f.val : P.complex.X n ⟶ Y) = 0 :=
    f.property
  have hnext : (ComplexShape.up ℕ).next n = n + 1 :=
    ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)
  rw [hnext] at hf
  exact hf

/-- A usual cocycle, as an element of the kernel. -/
def linearYonedaCocycleMk (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n + 1) n ≫ f = 0) :
    (((P.linearYonedaComplex R Y).sc n).g.hom).ker := by
  refine ⟨f, ?_⟩
  change P.complex.d ((ComplexShape.up ℕ).next n) n ≫ f = 0
  have hnext : (ComplexShape.up ℕ).next n = n + 1 :=
    ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)
  rw [hnext]
  exact hf

omit [HasExt.{v} C] in
@[simp]
theorem linearYonedaCocycleMk_val (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n + 1) n ≫ f = 0) :
    (P.linearYonedaCocycleMk R Y n f hf).val = f :=
  rfl

/-- The Ext class represented by a cocycle of the linear Yoneda complex. -/
def linearYonedaCocyclesToExt :
    (((P.linearYonedaComplex R Y).sc n).g.hom).ker →ₗ[R]
      Abelian.Ext X Y n where
  toFun f := P.extMk f.val (n + 1) rfl (P.linearYonedaCocycle_closed R Y n f)
  map_add' f g :=
    (P.add_extMk f.val g.val (n + 1) rfl
      (P.linearYonedaCocycle_closed R Y n f)
      (P.linearYonedaCocycle_closed R Y n g)).symm
  map_smul' r f :=
    (P.smul_extMk r f.val (n + 1) rfl
      (P.linearYonedaCocycle_closed R Y n f)).symm

@[simp]
theorem linearYonedaCocyclesToExt_apply
    (f : (((P.linearYonedaComplex R Y).sc n).g.hom).ker) :
    P.linearYonedaCocyclesToExt R Y n f =
      P.extMk f.val (n + 1) rfl (P.linearYonedaCocycle_closed R Y n f) :=
  rfl

/-- There are no nonzero zero-degree cocycles representing zero Ext classes. -/
theorem extMk_zero_eq_zero (f : P.complex.X 0 ⟶ Y)
    (hf : P.complex.d 1 0 ≫ f = 0)
    (h0 : P.extMk f 1 rfl hf = 0) : f = 0 := by
  have h1 : P.extEquivCohomologyClass (P.extMk f 1 rfl hf) = 0 := by
    rw [h0]
    exact P.extEquivCohomologyClass_zero X 0
  rw [P.extEquivCohomologyClass_extMk,
    CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff] at h1
  rw [CochainComplex.HomComplex.Cocycle.toSingleMk_mem_coboundaries_iff
    _ _ _ _ _ (1 : ℤ) (by norm_num)] at h1
  obtain ⟨g, hg⟩ := h1
  have hX : IsZero (P.cochainComplex.X 1) :=
    CochainComplex.isZero_of_isStrictlyLE _ 0 _ (by norm_num)
  have hg0 : g = 0 := hX.eq_of_src g 0
  rw [hg0, comp_zero] at hg
  have hfi : (P.cochainComplexXIso (0 : ℤ) 0 rfl).hom ≫ f = 0 :=
    hg.symm
  apply (cancel_epi (P.cochainComplexXIso (0 : ℤ) 0 rfl).hom).1
  simpa only [comp_zero] using hfi

/-- The incoming cycles map and the Ext projection form an exact pair. -/
theorem linearYonedaCocyclesToExt_exact :
    Function.Exact ((P.linearYonedaComplex R Y).sc n).moduleCatToCycles
      (P.linearYonedaCocyclesToExt R Y n) := by
  intro f
  cases n with
  | zero =>
    constructor
    · intro h
      have hf : (f.val : P.complex.X 0 ⟶ Y) = 0 :=
        P.extMk_zero_eq_zero Y f.val
          (P.linearYonedaCocycle_closed R Y 0 f) h
      have hf0 : f = 0 := Subtype.ext hf
      exact ⟨0, by simp only [hf0, map_zero]⟩
    · rintro ⟨g, rfl⟩
      let g₀ : P.complex.X ((ComplexShape.up ℕ).prev 0) ⟶ Y := g
      have hd : P.complex.d 0 ((ComplexShape.up ℕ).prev 0) = 0 :=
        P.complex.shape _ _ (fun h ↦ Nat.succ_ne_zero _ h)
      have hval :
          (((P.linearYonedaComplex R Y).sc 0).moduleCatToCycles g).val = 0 := by
        change P.complex.d 0 ((ComplexShape.up ℕ).prev 0) ≫
          g₀ = 0
        rw [hd]
        exact zero_comp
      have hz : ((P.linearYonedaComplex R Y).sc 0).moduleCatToCycles g = 0 :=
        Subtype.ext hval
      rw [hz, map_zero]
  | succ k =>
    have hprev : (ComplexShape.up ℕ).prev (k + 1) = k :=
      ComplexShape.prev_eq' _ (ComplexShape.up_mk _ _ rfl)
    let f₀ : P.complex.X (k + 1) ⟶ Y := f.val
    have hf₀ : P.complex.d (k + 2) (k + 1) ≫ f₀ = 0 :=
      P.linearYonedaCocycle_closed R Y (k + 1) f
    have hExt : P.extMk f₀ (k + 2) rfl hf₀ = 0 ↔
        ∃ g : P.complex.X k ⟶ Y, P.complex.d (k + 1) k ≫ g = f₀ :=
      P.extMk_eq_zero_iff f₀ (k + 2) rfl hf₀ k rfl
    constructor
    · intro h
      have h₀ : P.extMk f₀ (k + 2) rfl hf₀ = 0 := h
      obtain ⟨g, hg⟩ := hExt.mp h₀
      let g₁ : ((P.linearYonedaComplex R Y).sc (k + 1)).X₁ :=
        (P.complex.XIsoOfEq hprev).hom ≫ g
      refine ⟨g₁, Subtype.ext ?_⟩
      change P.complex.d (k + 1) ((ComplexShape.up ℕ).prev (k + 1)) ≫
        ((P.complex.XIsoOfEq hprev).hom ≫ g) = f₀
      rw [← Category.assoc, P.complex.d_comp_XIsoOfEq_hom]
      exact hg
    · rintro ⟨g, hg⟩
      let g₀ : P.complex.X ((ComplexShape.up ℕ).prev (k + 1)) ⟶ Y := g
      have hg₀ :
          P.complex.d (k + 1) ((ComplexShape.up ℕ).prev (k + 1)) ≫ g₀ = f₀ := by
        have h := congrArg Subtype.val hg
        change P.complex.d (k + 1) ((ComplexShape.up ℕ).prev (k + 1)) ≫ g₀ = f₀ at h
        exact h
      have h₀ : P.extMk f₀ (k + 2) rfl hf₀ = 0 := hExt.mpr
        ⟨(P.complex.XIsoOfEq hprev).inv ≫ g₀, by
          rw [← Category.assoc, P.complex.d_comp_XIsoOfEq_inv]
          exact hg₀⟩
      exact h₀

/-- Every Ext class has a representative in the mapped-complex kernel. -/
theorem linearYonedaCocyclesToExt_surjective :
    Function.Surjective (P.linearYonedaCocyclesToExt R Y n) := by
  intro e
  obtain ⟨f, hf, he⟩ := P.extMk_surjective e (n + 1) rfl
  exact ⟨P.linearYonedaCocycleMk R Y n f hf, he⟩

/-- Kernel/cokernel data exhibiting derived-category Ext as the homology
of the linear Yoneda complex. -/
def linearYonedaHomologyDataExt :
    ((P.linearYonedaComplex R Y).sc n).LeftHomologyData where
  K := ((P.linearYonedaComplex R Y).sc n).moduleCatLeftHomologyData.K
  H := ModuleCat.of R (Abelian.Ext X Y n)
  i := ((P.linearYonedaComplex R Y).sc n).moduleCatLeftHomologyData.i
  π := ModuleCat.ofHom (P.linearYonedaCocyclesToExt R Y n)
  wi := ((P.linearYonedaComplex R Y).sc n).moduleCatLeftHomologyData.wi
  hi := ((P.linearYonedaComplex R Y).sc n).moduleCatLeftHomologyData.hi
  wπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (P.linearYonedaCocyclesToExt_exact R Y n).apply_apply_eq_zero f
  hπ := ModuleCat.isColimitCokernelCofork
    (ModuleCat.ofHom ((P.linearYonedaComplex R Y).sc n).moduleCatToCycles)
    (ModuleCat.ofHom (P.linearYonedaCocyclesToExt R Y n))
    (P.linearYonedaCocyclesToExt_exact R Y n)
    (P.linearYonedaCocyclesToExt_surjective R Y n)

/-- The Hom-cochain homology is the derived-category Ext module. -/
def linearYonedaHomologyIsoExt :
    (P.linearYonedaComplex R Y).homology n ≅
      ModuleCat.of R (Abelian.Ext X Y n) :=
  (P.linearYonedaHomologyDataExt R Y n).homologyIso

/-- The comparison sends the homology class of an cocycle to its Ext class. -/
@[reassoc]
theorem linearYonedaHomologyIsoExt_cycles :
    (P.linearYonedaHomologyDataExt R Y n).cyclesIso.inv ≫
      (P.linearYonedaComplex R Y).homologyπ n ≫
        (P.linearYonedaHomologyIsoExt R Y n).hom =
      ModuleCat.ofHom (P.linearYonedaCocyclesToExt R Y n) := by
  let K := P.linearYonedaComplex R Y
  let hK : (K.sc n).LeftHomologyData := P.linearYonedaHomologyDataExt R Y n
  change hK.cyclesIso.inv ≫ (K.sc n).homologyπ ≫ hK.homologyIso.hom = hK.π
  have hπ : hK.π ≫ hK.homologyIso.inv = hK.cyclesIso.inv ≫ (K.sc n).homologyπ :=
    hK.π_comp_homologyIso_inv
  have hpost := congrArg
    (fun q : hK.K ⟶ (K.sc n).homology => q ≫ hK.homologyIso.hom) hπ
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hpost.symm

section EnoughProjectives

variable [EnoughProjectives C]

/-- The existing first-variable linear Ext model is the Ext module. -/
def isoFirstVariableLinearExt (n : ℕ) (Y : C) :
    ((_root_.Ext R C n).obj (op X)).obj Y ≅
      ModuleCat.of R (Abelian.Ext X Y n) :=
  P.isoExt n Y ≪≫ P.linearYonedaHomologyIsoExt R Y n

end EnoughProjectives

end CategoryTheory.ProjectiveResolution

namespace CategoryTheory.ProjectiveResolution

variable (R : Type r) [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [CategoryTheory.Linear R C]
variable [HasExt.{v} C] {X : C} (P : ProjectiveResolution X)
variable {Y Z : C} (g : Y ⟶ Z) (n : ℕ)

/-- Postcomposition on the linear Yoneda complex. -/
def linearYonedaCoefficientMap (g : Y ⟶ Z) :
    P.linearYonedaComplex R Y ⟶ P.linearYonedaComplex R Z :=
  (HomologicalComplex.unopFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op ((NatTrans.mapHomologicalComplex
      (((linearYoneda R C).map g).rightOp) (ComplexShape.down ℕ)).app P.complex))

omit [HasExt.{v} C] in
@[simp]
theorem linearYonedaCoefficientMap_f_apply (g : Y ⟶ Z) (n : ℕ)
    (f : P.complex.X n ⟶ Y) :
    ((P.linearYonedaCoefficientMap R g).f n).hom f = f ≫ g :=
  rfl

/-- The coefficient map restricted to the kernel of the differential. -/
def linearYonedaCoefficientCyclesMap (g : Y ⟶ Z) (n : ℕ) :
    ModuleCat.of R (((P.linearYonedaComplex R Y).sc n).g.hom).ker ⟶
      ModuleCat.of R (((P.linearYonedaComplex R Z).sc n).g.hom).ker :=
  ModuleCat.ofHom
    ((((P.linearYonedaCoefficientMap R g).f n).hom.comp
      (((P.linearYonedaComplex R Y).sc n).g.hom).ker.subtype).codRestrict
        (((P.linearYonedaComplex R Z).sc n).g.hom).ker (fun f ↦ by
      let f₀ : P.complex.X n ⟶ Y := f.val
      have hf : P.complex.d ((ComplexShape.up ℕ).next n) n ≫
          f₀ = 0 := f.property
      change P.complex.d ((ComplexShape.up ℕ).next n) n ≫
        (f₀ ≫ g) = 0
      rw [← Category.assoc, hf]
      exact zero_comp))

omit [HasExt.{v} C] in
@[simp]
theorem linearYonedaCoefficientCyclesMap_apply (g : Y ⟶ Z) (n : ℕ)
    (f : (((P.linearYonedaComplex R Y).sc n).g.hom).ker) :
    ((P.linearYonedaCoefficientCyclesMap R g n).hom f).val =
      (f.val : P.complex.X n ⟶ Y) ≫ g :=
  rfl

/-- Coefficient naturality as left homology map data. -/
def linearYonedaCoefficientHomologyMapData (g : Y ⟶ Z) (n : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
        (ComplexShape.up ℕ) n).map (P.linearYonedaCoefficientMap R g))
      (P.linearYonedaHomologyDataExt R Y n)
      (P.linearYonedaHomologyDataExt R Z n) where
  φK := P.linearYonedaCoefficientCyclesMap R g n
  φH := (Abelian.linearExtFunctorObj R X n).map g
  commi := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    rfl
  commf' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    let f₀ : P.complex.X ((ComplexShape.up ℕ).prev n) ⟶ Y := f
    apply Subtype.ext
    change (P.complex.d n ((ComplexShape.up ℕ).prev n) ≫ f₀) ≫ g =
      P.complex.d n ((ComplexShape.up ℕ).prev n) ≫ (f₀ ≫ g)
    exact Category.assoc _ _ _
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    let f₀ : P.complex.X n ⟶ Y := f.val
    exact P.extMk_comp_mk₀ f₀ (n + 1) rfl
      (P.linearYonedaCocycle_closed R Y n f) g

/-- The Hom-cochain comparison is covariantly natural in the coefficient object. -/
@[reassoc]
theorem linearYonedaHomologyIsoExt_naturality (g : Y ⟶ Z) (n : ℕ) :
    HomologicalComplex.homologyMap (P.linearYonedaCoefficientMap R g) n ≫
        (P.linearYonedaHomologyIsoExt R Z n).hom =
      (P.linearYonedaHomologyIsoExt R Y n).hom ≫
        (Abelian.linearExtFunctorObj R X n).map g :=
  (P.linearYonedaCoefficientHomologyMapData R g n).homologyMap_comm

section EnoughProjectives

variable [EnoughProjectives C]

omit [HasExt.{v} C] in
/-- Coefficient naturality of `ProjectiveResolution.isoExt`.
The transport through opposite homology is retained explicitly. -/
@[reassoc]
theorem isoExt_naturality_coefficient (g : Y ⟶ Z) (n : ℕ) :
    ((_root_.Ext R C n).obj (op X)).map g ≫ (P.isoExt (R := R) n Z).hom =
      (P.isoExt (R := R) n Y).hom ≫
        HomologicalComplex.homologyMap (P.linearYonedaCoefficientMap R g) n := by
  let FY := ((linearYoneda R C).obj Y).rightOp
  let FZ := ((linearYoneda R C).obj Z).rightOp
  let α : FZ ⟶ FY := ((linearYoneda R C).map g).rightOp
  let KY := (FY.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let KZ := (FZ.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let φ : KZ ⟶ KY := (NatTrans.mapHomologicalComplex α _).app P.complex
  let eY : (FY.leftDerived n).obj X ≅ KY.homology n := P.isoLeftDerivedObj FY n
  let eZ : (FZ.leftDerived n).obj X ≅ KZ.homology n := P.isoLeftDerivedObj FZ n
  let uY : (P.linearYonedaComplex R Y).homology n ≅ unop (KY.homology n) :=
    HomologicalComplex.homologyUnop KY n
  let uZ : (P.linearYonedaComplex R Z).homology n ≅ unop (KZ.homology n) :=
    HomologicalComplex.homologyUnop KZ n
  let ψ := P.linearYonedaCoefficientMap R g
  have hLD₀ : (NatTrans.leftDerived α n).app X =
      eZ.hom ≫ HomologicalComplex.homologyMap φ n ≫ eY.inv := by
    change (NatTrans.leftDerived α n).app X =
      (P.isoLeftDerivedObj FZ n).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} R)ᵒᵖ
          (ComplexShape.down ℕ) n).map φ ≫ (P.isoLeftDerivedObj FY n).inv
    exact P.leftDerived_app_eq α n
  have hLD :
      ((NatTrans.leftDerived α n).app X).unop =
        eY.inv.unop ≫ (HomologicalComplex.homologyMap φ n).unop ≫ eZ.hom.unop := by
    simpa only [unop_comp, Category.assoc] using
      congrArg (fun f : (FZ.leftDerived n).obj X ⟶ (FY.leftDerived n).obj X ↦
        Quiver.Hom.unop f) hLD₀
  have hU :
      uY.hom ≫ (HomologicalComplex.homologyMap φ n).unop =
        HomologicalComplex.homologyMap ψ n ≫ uZ.hom := by
    exact congrArg Quiver.Hom.unop
      (HomologicalComplex.homologyOp_hom_naturality ψ n)
  have hUinv :
      (HomologicalComplex.homologyMap φ n).unop ≫ uZ.inv =
        uY.inv ≫ HomologicalComplex.homologyMap ψ n := by
    have h := congrArg
      (fun q : (P.linearYonedaComplex R Y).homology n ⟶ unop (KZ.homology n) =>
        uY.inv ≫ q ≫ uZ.inv) hU
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using h
  have hcancel : eZ.hom.unop ≫ eZ.inv.unop = 𝟙 _ :=
    Iso.hom_inv_id eZ.unop
  have hcancelTail : eZ.hom.unop ≫ eZ.inv.unop ≫ uZ.inv = uZ.inv := by
    have h := congrArg
      (fun q : unop (KZ.homology n) ⟶ unop (KZ.homology n) => q ≫ uZ.inv) hcancel
    simpa only [Category.assoc, Category.id_comp] using h
  change ((NatTrans.leftDerived α n).app X).unop ≫
      (eZ.inv.unop ≫ uZ.inv) =
    (eY.inv.unop ≫ uY.inv) ≫ HomologicalComplex.homologyMap ψ n
  have hpost := congrArg
    (fun q : unop ((FY.leftDerived n).obj X) ⟶ unop ((FZ.leftDerived n).obj X) =>
      q ≫ eZ.inv.unop ≫ uZ.inv) hLD
  have h₁ : ((NatTrans.leftDerived α n).app X).unop ≫ (eZ.inv.unop ≫ uZ.inv) =
      eY.inv.unop ≫ (HomologicalComplex.homologyMap φ n).unop ≫ uZ.inv := by
    simpa only [Category.assoc, hcancelTail] using hpost
  have hpre := congrArg
    (fun q : unop (KY.homology n) ⟶ (P.linearYonedaComplex R Z).homology n =>
      eY.inv.unop ≫ q) hUinv
  have h₂ : eY.inv.unop ≫ (HomologicalComplex.homologyMap φ n).unop ≫ uZ.inv =
      (eY.inv.unop ≫ uY.inv) ≫ HomologicalComplex.homologyMap ψ n := by
    simpa only [Category.assoc] using hpre
  exact h₁.trans h₂

/-- The first-variable Ext comparison is natural in coefficients. -/
@[reassoc]
theorem isoFirstVariableLinearExt_naturality (g : Y ⟶ Z) (n : ℕ) :
    ((_root_.Ext R C n).obj (op X)).map g ≫
        (P.isoFirstVariableLinearExt R n Z).hom =
      (P.isoFirstVariableLinearExt R n Y).hom ≫
        (Abelian.linearExtFunctorObj R X n).map g := by
  change ((_root_.Ext R C n).obj (op X)).map g ≫
      ((P.isoExt (R := R) n Z).hom ≫ (P.linearYonedaHomologyIsoExt R Z n).hom) =
    ((P.isoExt (R := R) n Y).hom ≫ (P.linearYonedaHomologyIsoExt R Y n).hom) ≫
      (Abelian.linearExtFunctorObj R X n).map g
  rw [← Category.assoc, P.isoExt_naturality_coefficient R g n,
    Category.assoc, P.linearYonedaHomologyIsoExt_naturality R g n, ← Category.assoc]

end EnoughProjectives

end CategoryTheory.ProjectiveResolution

namespace CategoryTheory.Abelian

variable (R : Type r) [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [CategoryTheory.Linear R C]
variable [EnoughProjectives C] [HasExt.{v} C]

/-- The old first-variable linear Ext functor computes derived-category
Ext, naturally in the coefficient object. The chosen projective resolution is
proof machinery and is absent from this public interface. -/
def firstVariableLinearExtIso (X : C) (n : ℕ) :
    (_root_.Ext R C n).obj (op X) ≅ linearExtFunctorObj R X n :=
  NatIso.ofComponents
    (fun Y ↦ (projectiveResolution X).isoFirstVariableLinearExt R n Y)
    (fun g ↦ (projectiveResolution X).isoFirstVariableLinearExt_naturality R g n)

end CategoryTheory.Abelian
