/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Module.Hom
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.TransferInstance
public import MathlibExt.Algebra.Homology.ChainComplex.HomCochainComplex

/-!
# The right-module action on Hom cochains

Domain precomposition gives the `DomMulAct` module structure on additive
Hom. Transport through the Hom equivalence and product instances gives
the right-ring action on total-Hom cochains. The differential is linear
because the source differential is linear; the target remains a cochain
complex of abelian groups.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite

namespace ChainComplex

universe u v

variable (R : Type u) [Ring R]
  (Q : ChainComplex (ModuleCat.{v} R) ℤ) (I : CochainComplex AddCommGrpCat.{v} ℤ)

/-- The module chain complex after forgetting its scalar action. -/
abbrev moduleHomUnderlyingChain : ChainComplex AddCommGrpCat.{v} ℤ :=
  ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex
    (ComplexShape.down ℤ)).obj Q

/-- The negative-index cochain view of the Hom domain. -/
abbrev moduleHomDomainCochain : CochainComplex AddCommGrpCat.{v} ℤ :=
  (cochainComplexEquivalence AddCommGrpCat.{v}).functor.obj
    (moduleHomUnderlyingChain R Q)

/-- Domain action, transported to the categorical additive Hom group. -/
def homGroupModule (B : ModuleCat.{v} R) (C : AddCommGrpCat.{v}) :
    Module Rᵐᵒᵖ ((forget₂ (ModuleCat R) AddCommGrpCat).obj B ⟶ C) := by
  letI : Module R ((forget₂ (ModuleCat R) AddCommGrpCat).obj B) := B.isModule
  letI : Module Rᵈᵐᵃ
      (((forget₂ (ModuleCat R) AddCommGrpCat).obj B) →+ C) := inferInstance
  let ρ : Rᵐᵒᵖ →+* Rᵈᵐᵃ :=
    { toFun := fun r => show Rᵈᵐᵃ from r
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Module Rᵐᵒᵖ
      (((forget₂ (ModuleCat R) AddCommGrpCat).obj B) →+ C) :=
    Module.compHom _ ρ
  exact (AddCommGrpCat.homAddEquiv
    (M := (forget₂ (ModuleCat R) AddCommGrpCat).obj B) (N := C)).module Rᵐᵒᵖ

/-- The computed categorical Hom action is literal original-domain precomposition. -/
theorem homGroupModule_smul_apply (B : ModuleCat.{v} R) (C : AddCommGrpCat.{v})
    (r : Rᵐᵒᵖ) (f : (forget₂ (ModuleCat R) AddCommGrpCat).obj B ⟶ C) (x : B) :
    letI := homGroupModule R B C
    (r • f).hom x = f.hom (r.unop • x) := by
  let := homGroupModule R B C
  let : Module R ((forget₂ (ModuleCat R) AddCommGrpCat).obj B) := B.isModule
  let : Module Rᵈᵐᵃ
      (((forget₂ (ModuleCat R) AddCommGrpCat).obj B) →+ C) := inferInstance
  let ρ : Rᵐᵒᵖ →+* Rᵈᵐᵃ :=
    { toFun := fun r => show Rᵈᵐᵃ from r
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let : Module Rᵐᵒᵖ
      (((forget₂ (ModuleCat R) AddCommGrpCat).obj B) →+ C) :=
    Module.compHom _ ρ
  let e := AddCommGrpCat.homAddEquiv
    (M := (forget₂ (ModuleCat R) AddCommGrpCat).obj B) (N := C)
  have hs : (r • f).hom = (ρ r) • f.hom := by
    change e (e.symm ((ρ r) • f.hom)) = (ρ r) • f.hom
    exact e.apply_symm_apply ((ρ r) • f.hom)
  exact (congrArg (fun g :
      (((forget₂ (ModuleCat R) AddCommGrpCat).obj B) →+ C) => g x) hs).trans
    (DomMulAct.smul_addMonoidHom_apply (ρ r) f.hom x)

/-- The Hom products carry the right-R precomposition action. -/
def homCochainModule (n : ℤ) :
    Module Rᵐᵒᵖ (CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I n) := by
  let homModules : ∀ T : CochainComplex.HomComplex.Triplet n,
      Module Rᵐᵒᵖ ((moduleHomDomainCochain R Q).X T.p ⟶ I.X T.q) := fun T => by
    exact homGroupModule R (Q.X (-T.p)) (I.X T.q)
  letI := homModules
  change Module Rᵐᵒᵖ (∀ T : CochainComplex.HomComplex.Triplet n, (moduleHomDomainCochain R Q).X T.p ⟶ I.X T.q)
  exact Pi.module _ _ _

/-- The product action is literal domain precomposition on each component. -/
theorem homCochainModule_smul_v (n : ℤ) (r : Rᵐᵒᵖ)
    (z : CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I n)
    (p q : ℤ) (hpq : p + n = q) (x : Q.X (-p)) :
    letI := homCochainModule R Q I n
    ((r • z).v p q hpq).hom x = (z.v p q hpq).hom (r.unop • x) := by
  let := homCochainModule R Q I n
  let : Module R ((moduleHomDomainCochain R Q).X p) := (Q.X (-p)).isModule
  change ((show Rᵈᵐᵃ from r) • (z.v p q hpq).hom) x = _
  exact DomMulAct.smul_addMonoidHom_apply (show Rᵈᵐᵃ from r) (z.v p q hpq).hom x

/-- The product component, with its right-R linearity. -/
def homCochainEval (n p q : ℤ) (hpq : p + n = q) :
    letI := homCochainModule R Q I n
    letI : Module Rᵐᵒᵖ ((moduleHomDomainCochain R Q).X p ⟶ I.X q) :=
      homGroupModule R (Q.X (-p)) (I.X q)
    CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I n →ₗ[Rᵐᵒᵖ] ((moduleHomDomainCochain R Q).X p ⟶ I.X q) := by
  letI := homCochainModule R Q I n
  letI : Module Rᵐᵒᵖ ((moduleHomDomainCochain R Q).X p ⟶ I.X q) :=
    homGroupModule R (Q.X (-p)) (I.X q)
  refine { toFun := fun z => z.v p q hpq, map_add' := ?_, map_smul' := ?_ }
  · intro z z'
    exact CochainComplex.HomComplex.Cochain.add_v z z' p q hpq
  · intro r z
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact homCochainModule_smul_v R Q I n r z p q hpq x

@[simp]
theorem homCochainEval_apply (n p q : ℤ) (hpq : p + n = q)
    (z : CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I n) :
    letI := homCochainModule R Q I n
    letI : Module Rᵐᵒᵖ ((moduleHomDomainCochain R Q).X p ⟶ I.X q) :=
      homGroupModule R (Q.X (-p)) (I.X q)
    homCochainEval R Q I n p q hpq z = z.v p q hpq := rfl

/-- Linearity of the original-group total Hom differential. -/
theorem homCochainDifferential_smul (n m : ℤ) (r : Rᵐᵒᵖ)
    (z : CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I n) :
    letI := homCochainModule R Q I n
    letI : Module Rᵐᵒᵖ
        ((homCochainComplex (moduleHomUnderlyingChain R Q) I).X m) :=
      homCochainModule R Q I m
    ((homCochainComplex (moduleHomUnderlyingChain R Q) I).d n m).hom (r • z) =
      r • (((homCochainComplex (moduleHomUnderlyingChain R Q) I).d n m).hom z) := by
  let := homCochainModule R Q I n
  let : Module Rᵐᵒᵖ
      ((homCochainComplex (moduleHomUnderlyingChain R Q) I).X m) :=
    homCochainModule R Q I m
  by_cases hnm : n + 1 = m
  · apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    let : Module R ((moduleHomDomainCochain R Q).X p) := (Q.X (-p)).isModule
    let : Module R ((moduleHomDomainCochain R Q).X (p + 1)) := (Q.X (-(p + 1))).isModule
    have hL := congrArg (fun a : (moduleHomDomainCochain R Q).X p ⟶ I.X q => a.hom x)
      (homCochainComplex_d_v (moduleHomUnderlyingChain R Q) I n m hnm (r • z) p q hpq)
    have hR := congrArg (fun a : (moduleHomDomainCochain R Q).X p ⟶ I.X q => a.hom (r.unop • x))
      (homCochainComplex_d_v (moduleHomUnderlyingChain R Q) I n m hnm z p q hpq)
    have hA := homCochainModule_smul_v R Q I m r
      (((homCochainComplex (moduleHomUnderlyingChain R Q) I).d n m).hom z) p q hpq x
    have hQ : ((moduleHomDomainCochain R Q).d p (p + 1)).hom (r.unop • x) =
        r.unop • ((moduleHomDomainCochain R Q).d p (p + 1)).hom x := by
      change (Q.d (-p) (-(p + 1))).hom (r.unop • x) =
        r.unop • (Q.d (-p) (-(p + 1))).hom x
      exact (Q.d (-p) (-(p + 1))).hom.map_smul r.unop x
    have hc :
        ((moduleHomDomainCochain R Q).d p (p + 1) ≫ (r • z).v (p + 1) q (by omega) +
          m.negOnePow • ((r • z).v p (q - 1) (by omega) ≫ I.d (q - 1) q)).hom x =
        ((moduleHomDomainCochain R Q).d p (p + 1) ≫ z.v (p + 1) q (by omega) +
          m.negOnePow • (z.v p (q - 1) (by omega) ≫ I.d (q - 1) q)).hom (r.unop • x) := by
      simp only [AddCommGrpCat.hom_add, AddMonoidHom.add_apply, AddCommGrpCat.hom_comp,
        AddMonoidHom.comp_apply, Units.smul_def, AddCommGrpCat.hom_zsmul,
        AddMonoidHom.zsmul_apply]
      let dx : Q.X (-(p + 1)) :=
        ((moduleHomDomainCochain R Q).d p (p + 1)).hom x
      have hPre := homCochainModule_smul_v R Q I n r z
        (p + 1) q (by omega) dx
      have hFirst := hPre.trans
        (congrArg (fun y : Q.X (-(p + 1)) =>
          (z.v (p + 1) q (by omega)).hom y) hQ.symm)
      have hComponent := homCochainModule_smul_v R Q I n r z
        p (q - 1) (by omega) (show Q.X (-p) from x)
      have hSecond := congrArg (fun y : I.X (q - 1) =>
        m.negOnePow • (I.d (q - 1) q).hom y) hComponent
      exact congrArg₂ (fun a b : I.X q => a + b) hFirst hSecond
    exact hL.trans (hc.trans (hR.symm.trans hA.symm))
  · have hd := (homCochainComplex (moduleHomUnderlyingChain R Q) I).shape n m hnm
    rw [hd]
    let := homCochainModule R Q I m
    change (0 : CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I m) = r • 0
    exact (smul_zero r).symm

/-- The full total Hom, now bundled with its right-R module structure. -/
def moduleHomCochainComplex : CochainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ where
  X n :=
    letI := homCochainModule R Q I n
    ModuleCat.of Rᵐᵒᵖ (CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I n)
  d n m := by
    letI := homCochainModule R Q I n
    letI := homCochainModule R Q I m
    exact ModuleCat.ofHom
      { toFun := ((homCochainComplex (moduleHomUnderlyingChain R Q) I).d n m).hom
        map_add' := ((homCochainComplex (moduleHomUnderlyingChain R Q) I).d n m).hom.map_add
        map_smul' := homCochainDifferential_smul R Q I n m }
  shape n m hnm := by
    let : Module Rᵐᵒᵖ
      (CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I n) :=
      homCochainModule R Q I n
    let : Module Rᵐᵒᵖ
      (CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I m) :=
      homCochainModule R Q I m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have hd := (homCochainComplex (moduleHomUnderlyingChain R Q) I).shape n m hnm
    change ((homCochainComplex (moduleHomUnderlyingChain R Q) I).d n m).hom z = 0
    rw [hd]
    rfl
  d_comp_d' n m l hnm hml := by
    let : Module Rᵐᵒᵖ
      (CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I n) :=
      homCochainModule R Q I n
    let : Module Rᵐᵒᵖ
      (CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I m) :=
      homCochainModule R Q I m
    let : Module Rᵐᵒᵖ
      (CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I l) :=
      homCochainModule R Q I l
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    let C : CochainComplex AddCommGrpCat.{v} ℤ :=
      homCochainComplex (moduleHomUnderlyingChain R Q) I
    let dnm : C.X n →+ C.X m := (C.d n m).hom
    let dml : C.X m →+ C.X l := (C.d m l).hom
    let z₀ : C.X n := z
    have hMaps : dml.comp dnm = (0 : C.X n →+ C.X l) :=
      (AddCommGrpCat.hom_comp (C.d n m) (C.d m l)).symm.trans
        ((congrArg (fun a : C.X n ⟶ C.X l => a.hom) (C.d_comp_d n m l)).trans
          AddCommGrpCat.hom_zero)
    have hValue := DFunLike.congr_fun hMaps z₀
    have hZero : (0 : C.X n →+ C.X l) z₀ = 0 := rfl
    change dml (dnm z₀) = 0
    exact (AddMonoidHom.comp_apply dml dnm z₀).symm.trans (hValue.trans hZero)

@[simp]
theorem moduleHomCochainComplex_X (n : ℤ) :
    letI := homCochainModule R Q I n
    (moduleHomCochainComplex R Q I).X n =
      ModuleCat.of Rᵐᵒᵖ (CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I n) := rfl

/-- The module differential has exactly the original-group evaluation. -/
@[simp]
theorem moduleHomCochainComplex_d_apply (n m : ℤ)
    (z : CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I n) :
    letI := homCochainModule R Q I n
    letI := homCochainModule R Q I m
    (show CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I n →ₗ[Rᵐᵒᵖ]
        CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I m from
      ((moduleHomCochainComplex R Q I).d n m).hom) z =
      ((homCochainComplex (moduleHomUnderlyingChain R Q) I).d n m).hom z := rfl

/-- Forgetting the action retains the total-Hom objects and maps. -/
def moduleHomCochainForgetIso :
    ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (moduleHomCochainComplex R Q I) ≅ homCochainComplex (moduleHomUnderlyingChain R Q) I :=
  HomologicalComplex.Hom.isoOfComponents
    (C₁ := ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (moduleHomCochainComplex R Q I))
    (C₂ := homCochainComplex (moduleHomUnderlyingChain R Q) I)
    (fun n => Iso.refl _) (by
    intro i j hij
    simp only [Iso.refl_hom]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    rfl)

section Maps

variable {Q I}
  {Q' : ChainComplex (ModuleCat.{v} R) ℤ} {I' : CochainComplex AddCommGrpCat.{v} ℤ}

/-- The Hom map is right-R-linear; the target map g needs no R action. -/
theorem homCochainMap_smul (f : Q' ⟶ Q) (g : I ⟶ I') (n : ℤ) (r : Rᵐᵒᵖ)
    (z : CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I n) :
    letI := homCochainModule R Q I n
    letI : Module Rᵐᵒᵖ
        ((homCochainComplex (moduleHomUnderlyingChain R Q') I').X n) :=
      homCochainModule R Q' I' n
    ((homCochainComplexMap
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.down ℤ)).map f) g).f n).hom (r • z) =
      r • (((homCochainComplexMap
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.down ℤ)).map f) g).f n).hom z) := by
  let := homCochainModule R Q I n
  let : Module Rᵐᵒᵖ
      ((homCochainComplex (moduleHomUnderlyingChain R Q') I').X n) :=
    homCochainModule R Q' I' n
  let f₀ := ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.down ℤ)).map f
  let f₁ := (cochainComplexEquivalence AddCommGrpCat).functor.map f₀
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  let : Module R
      (((cochainComplexEquivalence AddCommGrpCat).functor.obj
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.down ℤ)).obj Q')).X p) := (Q'.X (-p)).isModule
  let : Module R ((moduleHomDomainCochain R Q).X p) := (Q.X (-p)).isModule
  have hL := congrArg (fun a :
      ((cochainComplexEquivalence AddCommGrpCat).functor.obj
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.down ℤ)).obj Q')).X p ⟶ I'.X q => a.hom x)
    (homCochainComplexMap_v f₀ g n p q hpq (r • z))
  have hR := congrArg (fun a :
      ((cochainComplexEquivalence AddCommGrpCat).functor.obj
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.down ℤ)).obj Q')).X p ⟶ I'.X q => a.hom (r.unop • x))
    (homCochainComplexMap_v f₀ g n p q hpq z)
  have hA := homCochainModule_smul_v R Q' I' n r
    (((homCochainComplexMap f₀ g).f n).hom z) p q hpq x
  have hf : (f₁.f p).hom (r.unop • x) = r.unop • (f₁.f p).hom x := by
    change (f.f (-p)).hom (r.unop • x) = r.unop • (f.f (-p)).hom x
    exact (f.f (-p)).hom.map_smul r.unop x
  have hc : (f₁.f p ≫ (r • z).v p q hpq ≫ g.f q).hom x =
      (f₁.f p ≫ z.v p q hpq ≫ g.f q).hom (r.unop • x) := by
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
    let y : Q.X (-p) := (f₁.f p).hom x
    have hComponent := homCochainModule_smul_v R Q I n r z p q hpq y
    have hInput := congrArg (fun t : Q.X (-p) => (z.v p q hpq).hom t) hf.symm
    exact congrArg (g.f q).hom (hComponent.trans hInput)
  exact hL.trans (hc.trans (hR.symm.trans hA.symm))

/-- The Hom component with its right-R linearity. -/
def homCochainMapLinear (f : Q' ⟶ Q) (g : I ⟶ I') (n : ℤ) :
    letI := homCochainModule R Q I n
    letI := homCochainModule R Q' I' n
    CochainComplex.HomComplex.Cochain (moduleHomDomainCochain R Q) I n →ₗ[Rᵐᵒᵖ]
      CochainComplex.HomComplex.Cochain
        ((cochainComplexEquivalence AddCommGrpCat).functor.obj
          (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
            (ComplexShape.down ℤ)).obj Q')) I' n := by
  letI := homCochainModule R Q I n
  letI := homCochainModule R Q' I' n
  let h := ((homCochainComplexMap
    (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.down ℤ)).map f) g).f n).hom
  exact
    { toFun := h
      map_add' := h.map_add
      map_smul' := homCochainMap_smul R f g n }

/-- The enriched Hom map in the two variables. -/
def moduleHomCochainComplexMap (f : Q' ⟶ Q) (g : I ⟶ I') :
    moduleHomCochainComplex R Q I ⟶ moduleHomCochainComplex R Q' I' where
  f n := by
    letI := homCochainModule R Q I n
    letI := homCochainModule R Q' I' n
    exact ModuleCat.ofHom (homCochainMapLinear R f g n)
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    let A : CochainComplex AddCommGrpCat.{v} ℤ :=
      homCochainComplex (moduleHomUnderlyingChain R Q) I
    let B : CochainComplex AddCommGrpCat.{v} ℤ :=
      homCochainComplex (moduleHomUnderlyingChain R Q') I'
    let h : A ⟶ B := homCochainComplexMap
      (((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.down ℤ)).map f) g
    let dA : A.X i →+ A.X j := (A.d i j).hom
    let dB : B.X i →+ B.X j := (B.d i j).hom
    let hi : A.X i →+ B.X i := (h.f i).hom
    let hj : A.X j →+ B.X j := (h.f j).hom
    let z₀ : A.X i := z
    have hmaps : dB.comp hi = hj.comp dA :=
      (AddCommGrpCat.hom_comp (h.f i) (B.d i j)).symm.trans
        ((congrArg (fun a : A.X i ⟶ B.X j => a.hom) (h.comm i j)).trans
          (AddCommGrpCat.hom_comp (A.d i j) (h.f j)))
    have hvalue := DFunLike.congr_fun hmaps z₀
    change dB (hi z₀) = hj (dA z₀)
    exact (AddMonoidHom.comp_apply dB hi z₀).symm.trans
      (hvalue.trans (AddMonoidHom.comp_apply hj dA z₀))

@[simp]
theorem moduleHomCochainComplexMap_f (f : Q' ⟶ Q) (g : I ⟶ I') (n : ℤ) :
    letI := homCochainModule R Q I n
    letI := homCochainModule R Q' I' n
    ((moduleHomCochainComplexMap R f g).f n).hom = homCochainMapLinear R f g n := rfl

/-- Forgetting the enriched map retains the Hom-complex map. -/
theorem moduleHomCochainForgetIso_naturality (f : Q' ⟶ Q) (g : I ⟶ I') :
    ((forget₂ (ModuleCat Rᵐᵒᵖ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (moduleHomCochainComplexMap R f g) ≫
      (moduleHomCochainForgetIso R Q' I').hom =
    (moduleHomCochainForgetIso R Q I).hom ≫ homCochainComplexMap
      (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.down ℤ)).map f) g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  rfl

end Maps

end ChainComplex
