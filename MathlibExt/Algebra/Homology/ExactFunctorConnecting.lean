/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

public section

namespace HomologicalComplex

variable {C D ι : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {c : ComplexShape ι} (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The canonical exact-functor homology comparison carries the class of
an actual cycle to the image of its original cycle class. -/
theorem mapCycleClass_homologyIso (K : HomologicalComplex C c) {A : C} (i j : ι)
    (hij : c.next i = j) (a : A ⟶ K.X i) (ha : a ≫ K.d i j = 0) :
    let KF := (F.mapHomologicalComplex c).obj K
    let haF : F.map a ≫ KF.d i j = 0 :=
      (F.map_comp a (K.d i j)).symm.trans
        ((congrArg F.map ha).trans (F.map_zero _ _))
    KF.liftCycles (F.map a) j hij haF ≫ KF.homologyπ i ≫
      ((mapHomologyFunctorIso i F).app K).hom =
        F.map (K.liftCycles a j hij ha ≫ K.homologyπ i) := by
  dsimp only
  let KF := (F.mapHomologicalComplex c).obj K
  let z := K.liftCycles a j hij ha
  let haF : F.map a ≫ KF.d i j = 0 :=
    (F.map_comp a (K.d i j)).symm.trans
      ((congrArg F.map ha).trans (F.map_zero _ _))
  let zF := KF.liftCycles (F.map a) j hij haF
  let e := (K.sc i).mapCyclesIso F
  let h : KF.homology i ≅ F.obj (K.homology i) := (K.sc i).mapHomologyIso F
  have hComponent : h.hom = ((mapHomologyFunctorIso i F).app K).hom := by rfl
  have hE : e.hom ≫ F.map (K.iCycles i) = KF.iCycles i :=
    (K.sc i).mapCyclesIso_hom_iCycles F
  have hZ : zF ≫ e.hom = F.map z := by
    apply (cancel_mono (F.map (K.iCycles i))).mp
    have hL : (zF ≫ e.hom) ≫ F.map (K.iCycles i) = F.map a :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f => zF ≫ f) hE).trans (KF.liftCycles_i _ _ _ _))
    have hR : F.map z ≫ F.map (K.iCycles i) = F.map a :=
      (F.map_comp z (K.iCycles i)).symm.trans (congrArg F.map (K.liftCycles_i _ _ _ _))
    exact hL.trans hR.symm
  have hProjection : KF.homologyπ i ≫ h.hom = e.hom ≫ F.map (K.homologyπ i) :=
    CategoryTheory.ShortComplex.homologyπ_comp_mapHomologyIso_hom (K.sc i) F
  have hcalc : (zF ≫ KF.homologyπ i) ≫ h.hom = F.map (z ≫ K.homologyπ i) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => zF ≫ f) hProjection).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ F.map (K.homologyπ i)) hZ).trans (F.map_comp _ _).symm)))
  change zF ≫ (KF.homologyπ i ≫ h.hom) = F.map (z ≫ K.homologyπ i)
  exact (Category.assoc zF (KF.homologyπ i) h.hom).symm.trans hcalc

end HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

variable {C D ι : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {c : ComplexShape ι} {S : ShortComplex (HomologicalComplex C c)}

/-- An exact additive functor preserves the ORIGINAL connecting morphism
through its canonical homology comparisons. The proof uses the actual
quotient/cycle pullback, original kernel lift and the stock boundary calculation. -/
theorem delta_mapFunctor (hS : S.ShortExact) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (i j : ι) (hij : c.Rel i j) :
    ((HomologicalComplex.mapHomologyFunctorIso i F).app S.X₃).inv ≫
      (hS.map_of_exact (F.mapHomologicalComplex c)).δ i j hij ≫
        ((HomologicalComplex.mapHomologyFunctorIso j F).app S.X₁).hom = F.map (hS.δ i j hij) := by
  let FF := F.mapHomologicalComplex c
  let T := S.map FF
  let hT : T.ShortExact := hS.map_of_exact FF
  let e3 : T.X₃.homology i ≅ F.obj (S.X₃.homology i) := (S.X₃.sc i).mapHomologyIso F
  let e1 : T.X₁.homology j ≅ F.obj (S.X₁.homology j) := (S.X₁.sc j).mapHomologyIso F
  have e3Component : e3.hom =
      ((HomologicalComplex.mapHomologyFunctorIso i F).app S.X₃).hom := by rfl
  have e1Component : e1.hom =
      ((HomologicalComplex.mapHomologyFunctorIso j F).app S.X₁).hom := by rfl
  let u := S.g.f i
  let z := S.X₃.iCycles i
  let A := pullback u z
  let x₂ : A ⟶ S.X₂.X i := pullback.fst u z
  let v : A ⟶ S.X₃.cycles i := pullback.snd u z
  let x₃ : A ⟶ S.X₃.X i := v ≫ z
  have hx₂ : x₂ ≫ S.g.f i = x₃ := pullback.condition (f := u) (g := z)
  have hx₃ : x₃ ≫ S.X₃.d i j = 0 := by
    simp only [x₃, z, Category.assoc, HomologicalComplex.iCycles_d, CategoryTheory.Limits.comp_zero]
  let Sj := S.map (HomologicalComplex.eval C c j)
  have hSj : Sj.ShortExact := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS j
  let : Mono Sj.f := hSj.mono_f
  have hz : (x₂ ≫ S.X₂.d i j) ≫ Sj.g = 0 :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => x₂ ≫ f) (S.g.comm i j).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ S.X₃.d i j) hx₂).trans hx₃)))
  let x₁ : A ⟶ S.X₁.X j := hSj.exact.lift (x₂ ≫ S.X₂.d i j) hz
  have hx₁ : x₁ ≫ S.f.f j = x₂ ≫ S.X₂.d i j := hSj.exact.lift_f _ _
  let k := c.next j
  have hSk : (S.map (HomologicalComplex.eval C c k)).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS k
  let : Mono (S.f.f k) := hSk.mono_f
  have hc₁ : x₁ ≫ S.X₁.d j k = 0 := by
    apply (cancel_mono (S.f.f k)).mp
    rw [Category.assoc, ← S.f.comm j k, ← Category.assoc, hx₁, Category.assoc,
      HomologicalComplex.d_comp_d, CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]
  let q := S.X₃.liftCycles x₃ j (c.next_eq' hij) hx₃ ≫ S.X₃.homologyπ i
  let q₁ := S.X₁.liftCycles x₁ k rfl hc₁ ≫ S.X₁.homologyπ j
  have hδ : q ≫ hS.δ i j hij = q₁ := by
    dsimp only [q, q₁]
    simpa only [Category.assoc] using hS.δ_eq i j hij x₃ hx₃ x₂ hx₂ x₁ hx₁ k rfl
  have hv : S.X₃.liftCycles x₃ j (c.next_eq' hij) hx₃ = v := by
    apply (cancel_mono (S.X₃.iCycles i)).mp
    exact (S.X₃.liftCycles_i _ _ _ _).trans rfl
  have hq : q = v ≫ S.X₃.homologyπ i := congrArg (fun f => f ≫ S.X₃.homologyπ i) hv
  let : Epi u := ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS i).epi_g
  let : Epi v := inferInstance
  let : Epi q := by
    rw [hq]
    infer_instance
  let hx₃F : F.map x₃ ≫ T.X₃.d i j = 0 :=
    (F.map_comp x₃ (S.X₃.d i j)).symm.trans
      ((congrArg F.map hx₃).trans (F.map_zero _ _))
  let hc₁F : F.map x₁ ≫ T.X₁.d j k = 0 :=
    (F.map_comp x₁ (S.X₁.d j k)).symm.trans
      ((congrArg F.map hc₁).trans (F.map_zero _ _))
  let qF := T.X₃.liftCycles (F.map x₃) j (c.next_eq' hij) hx₃F ≫ T.X₃.homologyπ i
  let q₁F := T.X₁.liftCycles (F.map x₁) k rfl hc₁F ≫ T.X₁.homologyπ j
  have hx₂F : F.map x₂ ≫ T.g.f i = F.map x₃ :=
    (F.map_comp x₂ (S.g.f i)).symm.trans (congrArg F.map hx₂)
  have hx₁F : F.map x₁ ≫ T.f.f j = F.map x₂ ≫ T.X₂.d i j :=
    (F.map_comp x₁ (S.f.f j)).symm.trans
      ((congrArg F.map hx₁).trans (F.map_comp x₂ (S.X₂.d i j)))
  have hδF : qF ≫ hT.δ i j hij = q₁F := by
    dsimp only [qF, q₁F]
    simpa only [Category.assoc] using
      hT.δ_eq i j hij (F.map x₃) hx₃F (F.map x₂) hx₂F (F.map x₁) hx₁F k rfl
  have hClass₃ : qF ≫ e3.hom = F.map q := by
    let KF := (F.mapHomologicalComplex c).obj S.X₃
    let zF := KF.liftCycles (F.map x₃) j (c.next_eq' hij) hx₃F
    let zC := S.X₃.liftCycles x₃ j (c.next_eq' hij) hx₃
    have hRaw : zF ≫ (KF.homologyπ i ≫ e3.hom) = F.map (zC ≫ S.X₃.homologyπ i) :=
      HomologicalComplex.mapCycleClass_homologyIso F S.X₃ i j (c.next_eq' hij) x₃ hx₃
    change (zF ≫ KF.homologyπ i) ≫ e3.hom = F.map (zC ≫ S.X₃.homologyπ i)
    exact (Category.assoc zF (KF.homologyπ i) e3.hom).trans hRaw
  have hClass₁ : q₁F ≫ e1.hom = F.map q₁ := by
    let KF := (F.mapHomologicalComplex c).obj S.X₁
    let zF := KF.liftCycles (F.map x₁) k rfl hc₁F
    let zC := S.X₁.liftCycles x₁ k rfl hc₁
    have hRaw : zF ≫ (KF.homologyπ j ≫ e1.hom) = F.map (zC ≫ S.X₁.homologyπ j) :=
      HomologicalComplex.mapCycleClass_homologyIso F S.X₁ j k rfl x₁ hc₁
    change (zF ≫ KF.homologyπ j) ≫ e1.hom = F.map (zC ≫ S.X₁.homologyπ j)
    exact (Category.assoc zF (KF.homologyπ j) e1.hom).trans hRaw
  have hPre : F.map q ≫ e3.inv = qF :=
    (congrArg (fun f => f ≫ e3.inv) hClass₃.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => qF ≫ f) e3.hom_inv_id).trans (Category.comp_id _)))
  apply (cancel_epi (F.map q)).mp
  have hL : F.map q ≫ (e3.inv ≫ (hT.δ i j hij ≫ e1.hom)) = F.map q₁ :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ (hT.δ i j hij ≫ e1.hom)) hPre).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ e1.hom) hδF).trans hClass₁)))
  have hR : F.map q ≫ F.map (hS.δ i j hij) = F.map q₁ :=
    (F.map_comp q (hS.δ i j hij)).symm.trans (congrArg F.map hδ)
  exact hL.trans hR.symm

end CategoryTheory.ShortComplex.ShortExact

end
