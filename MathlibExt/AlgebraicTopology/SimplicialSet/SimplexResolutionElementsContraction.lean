/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolution
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveDiscreteIso
public import MathlibExt.CategoryTheory.CategoryBar.ElementsNaturality
public import MathlibExt.CategoryTheory.NerveHomotopy
public import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Fixed-degree Elements contraction for the simplex resolution

In each inner simplicial degree, the simplex-pullback coefficient functor has
an Elements category which retracts onto the discrete set of source
simplices.  The section uses the represented simplex of `p(x)` and the
literal pullback element `(x, id)`; the contraction morphism is the decoded
simplex map `alpha`.

Via the simplicial-replacement/Elements-nerve comparison this gives a
homotopy equivalence in every fixed inner degree.  The sections are only
oplax natural as the inner degree varies, so this file makes no diagonal
section, realized weak-equivalence, Theorem A, or additivity claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open scoped Simplicial

universe u

namespace SSet

/-- The simplex-pullback diagram evaluated in one fixed inner simplicial
degree. -/
noncomputable def simplexPullbackDegree {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (a : SimplexCategoryᵒᵖ) : SimplexIndex Y ⥤ Type u :=
  simplexPullbackDiagram p ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj a

@[simp]
theorem simplexPullbackDegree_obj {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (a : SimplexCategoryᵒᵖ) (s : SimplexIndex Y) :
    (simplexPullbackDegree p a).obj s = (pullback p s.hom).obj a :=
  rfl

@[simp↓]
theorem simplexPullbackDegree_map_apply {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (a : SimplexCategoryᵒᵖ) {s t : SimplexIndex Y} (u : s ⟶ t)
    (z : (simplexPullbackDegree p a).obj s) :
    (simplexPullbackDegree p a).map u z =
      (simplexPullbackMap p u).app a z :=
  rfl

/-- Inner simplicial reindexing of the evaluated pullback coefficient
functor. -/
def simplexPullbackDegreeMap {Z Y : SSet.{u}} (p : Z ⟶ Y)
    {a b : SimplexCategoryᵒᵖ} (k : a ⟶ b) :
    simplexPullbackDegree p a ⟶ simplexPullbackDegree p b where
  app s := ((simplexPullbackDiagram p).obj s).map k
  naturality {s t} u := by
    change (simplexPullbackMap p u).app a ≫
        ((simplexPullbackDiagram p).obj t).map k =
      ((simplexPullbackDiagram p).obj s).map k ≫
        (simplexPullbackMap p u).app b
    exact ((simplexPullbackMap p u).naturality k).symm

/-- Decode a simplex of a pullback over a represented simplex into its source
coordinate and its simplex-category map. -/
noncomputable def simplexPullbackObjEquiv {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (s : SimplexIndex Y) (a : SimplexCategoryᵒᵖ) :
    (pullback p s.hom).obj a ≃
      {q : Z.obj a × (a.unop ⟶ s.left) //
        p.app a q.1 = Y.map q.2.op (SSet.yonedaEquiv s.hom)} := by
  let ePullback :
      (pullback p s.hom).obj a ≃
        Types.PullbackObj (p.app a) (s.hom.app a) :=
    ((pullbackObjIso p s.hom a).trans
      (Types.pullbackIsoPullback (p.app a) (s.hom.app a))).toEquiv
  let eProd :
      Z.obj a × (SSet.stdSimplex.obj s.left).obj a ≃
        Z.obj a × (a.unop ⟶ s.left) :=
    Equiv.prodCongr (Equiv.refl _) SSet.stdSimplex.objEquiv
  exact ePullback.trans (eProd.subtypeEquiv (fun q => by
    change
      (p.app a q.1 = s.hom.app a q.2) ↔
        p.app a q.1 = Y.map (SSet.stdSimplex.objEquiv q.2).op
          (SSet.yonedaEquiv s.hom)
    simp only [SSet.stdSimplex.map_objEquiv_op_apply,
      Equiv.symm_apply_apply]))

@[simp]
theorem simplexPullbackObjEquiv_fst {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (s : SimplexIndex Y) (a : SimplexCategoryᵒᵖ)
    (z : (pullback p s.hom).obj a) :
    ((simplexPullbackObjEquiv p s a z).1).1 =
      (pullback.fst p s.hom).app a z := by
  unfold simplexPullbackObjEquiv
  change
    (((Types.pullbackIsoPullback (p.app a) (s.hom.app a)).hom
      ((pullbackObjIso p s.hom a).hom z)).1 :
        Z.obj a × (SSet.stdSimplex.obj s.left).obj a).1 = _
  rw [Types.pullbackIsoPullback_hom_fst]
  exact ConcreteCategory.congr_hom
    (pullbackObjIso_hom_comp_fst p s.hom a) z

@[simp]
theorem simplexPullbackObjEquiv_snd {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (s : SimplexIndex Y) (a : SimplexCategoryᵒᵖ)
    (z : (pullback p s.hom).obj a) :
    ((simplexPullbackObjEquiv p s a z).1).2 =
      SSet.stdSimplex.objEquiv ((pullback.snd p s.hom).app a z) := by
  unfold simplexPullbackObjEquiv
  change SSet.stdSimplex.objEquiv
    ((((Types.pullbackIsoPullback (p.app a) (s.hom.app a)).hom
      ((pullbackObjIso p s.hom a).hom z)).1 :
        Z.obj a × (SSet.stdSimplex.obj s.left).obj a).2) = _
  apply congrArg SSet.stdSimplex.objEquiv
  rw [Types.pullbackIsoPullback_hom_snd]
  exact ConcreteCategory.congr_hom
    (pullbackObjIso_hom_comp_snd p s.hom a) z

theorem simplexPullbackObjEquiv_condition {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (s : SimplexIndex Y) (a : SimplexCategoryᵒᵖ)
    (z : (pullback p s.hom).obj a) :
    p.app a ((simplexPullbackObjEquiv p s a z).1.1) =
      Y.map ((simplexPullbackObjEquiv p s a z).1.2).op
        (SSet.yonedaEquiv s.hom) :=
  (simplexPullbackObjEquiv p s a z).2

/-- Reindexing a pullback element preserves its source coordinate. -/
@[simp↓]
theorem simplexPullbackObjEquiv_map_fst {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (a : SimplexCategoryᵒᵖ) {s t : SimplexIndex Y} (u : s ⟶ t)
    (z : (pullback p s.hom).obj a) :
    ((simplexPullbackObjEquiv p t a
      ((simplexPullbackMap p u).app a z)).1).1 =
        ((simplexPullbackObjEquiv p s a z).1).1 := by
  rw [simplexPullbackObjEquiv_fst, simplexPullbackObjEquiv_fst]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (simplexPullbackMap_fst p u) a) z

/-- Reindexing a pullback element postcomposes its decoded simplex map. -/
@[simp↓]
theorem simplexPullbackObjEquiv_map_snd {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (a : SimplexCategoryᵒᵖ) {s t : SimplexIndex Y} (u : s ⟶ t)
    (z : (pullback p s.hom).obj a) :
    ((simplexPullbackObjEquiv p t a
      ((simplexPullbackMap p u).app a z)).1).2 =
        (simplexPullbackObjEquiv p s a z).1.2 ≫ u.left := by
  rw [simplexPullbackObjEquiv_snd, simplexPullbackObjEquiv_snd]
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (simplexPullbackMap_snd p u) a) z
  change (pullback.snd p t.hom).app a ((simplexPullbackMap p u).app a z) =
    (SSet.stdSimplex.map u.left).app a ((pullback.snd p s.hom).app a z) at h
  rw [h]
  let x := (pullback.snd p s.hom).app a z
  change SSet.stdSimplex.objEquiv ((SSet.stdSimplex.map u.left).app a x) =
    SSet.stdSimplex.objEquiv x ≫ u.left
  rw [← Equiv.symm_apply_apply SSet.stdSimplex.objEquiv x,
    ← SSet.stdSimplex.objEquiv_symm_comp, Equiv.apply_symm_apply]
  rw [Equiv.apply_symm_apply]

/-- Projection from the Elements category to the discrete source-simplex
set. -/
noncomputable def simplexResolutionPi {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (a : SimplexCategoryᵒᵖ) :
    (simplexPullbackDegree p a).Elements ⥤ Discrete (Z.obj a) where
  obj e := Discrete.mk ((pullback.fst p e.obj.hom).app a e.val)
  map {e e'} f := Discrete.eqToHom (by
    calc
      (pullback.fst p e.obj.hom).app a e.val =
          (pullback.fst p e'.obj.hom).app a
            ((simplexPullbackDegree p a).map f.hom e.val) := by
        symm
        exact ConcreteCategory.congr_hom
          (NatTrans.congr_app (simplexPullbackMap_fst p f.hom) a) e.val
      _ = (pullback.fst p e'.obj.hom).app a e'.val :=
        congrArg (fun z => (pullback.fst p e'.obj.hom).app a z) f.map_val)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
theorem simplexResolutionPi_obj_as {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (a : SimplexCategoryᵒᵖ) (e : (simplexPullbackDegree p a).Elements) :
    ((simplexResolutionPi p a).obj e).as =
      (pullback.fst p e.obj.hom).app a e.val :=
  rfl

/-- Canonical Elements object over `x`, represented by `p(x)` with pullback
coordinate `(x, id)`. -/
noncomputable def simplexResolutionSigmaObj {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (a : SimplexCategoryᵒᵖ) (x : Z.obj a) :
    (simplexPullbackDegree p a).Elements := by
  refine { obj := leftFiberSimplexIndex (p.app a x), val := ?_ }
  change (SSet.leftFiber p (p.app a x)).obj a
  exact (SSet.leftFiber.objEquiv p (p.app a x) a).symm
    ⟨⟨x, 𝟙 a.unop⟩, by simp⟩

/-- The canonical section from source simplices to pullback Elements. -/
noncomputable def simplexResolutionSigma {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (a : SimplexCategoryᵒᵖ) :
    Discrete (Z.obj a) ⥤ (simplexPullbackDegree p a).Elements :=
  Discrete.functor (simplexResolutionSigmaObj p a)

private theorem simplexResolutionSigma_map_hom_left_comp
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ)
    {x y : Discrete (Z.obj a)} (f : x ⟶ y)
    {s : SimplexCategory}
    (g : ((simplexResolutionSigma p a).obj y).obj.left ⟶ s) :
    (((simplexResolutionSigma p a).map f).hom).left ≫ g = g := by
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  rcases f with ⟨h⟩
  change x = y at h
  subst y
  exact Category.id_comp g

@[simp]
theorem simplexResolutionSigmaObj_obj {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (a : SimplexCategoryᵒᵖ) (x : Z.obj a) :
    (simplexResolutionSigmaObj p a x).obj =
      leftFiberSimplexIndex (p.app a x) :=
  rfl

@[simp↓]
theorem simplexResolutionSigmaObj_decoded_fst {Z Y : SSet.{u}}
    (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ) (x : Z.obj a) :
    ((simplexPullbackObjEquiv p
      (simplexResolutionSigmaObj p a x).obj a
      (simplexResolutionSigmaObj p a x).val).1).1 = x := by
  change (((SSet.leftFiber.objEquiv p (p.app a x) a)
    ((SSet.leftFiber.objEquiv p (p.app a x) a).symm
      ⟨⟨x, 𝟙 a.unop⟩, by simp⟩)).1).1 = x
  rw [Equiv.apply_symm_apply]

@[simp↓]
theorem simplexResolutionSigmaObj_decoded_snd {Z Y : SSet.{u}}
    (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ) (x : Z.obj a) :
    ((simplexPullbackObjEquiv p
      (simplexResolutionSigmaObj p a x).obj a
      (simplexResolutionSigmaObj p a x).val).1).2 = 𝟙 a.unop := by
  change (((SSet.leftFiber.objEquiv p (p.app a x) a)
    ((SSet.leftFiber.objEquiv p (p.app a x) a).symm
      ⟨⟨x, 𝟙 a.unop⟩, by simp⟩)).1).2 = 𝟙 a.unop
  rw [Equiv.apply_symm_apply]

/-- The canonical section followed by the source projection is strictly the
identity. -/
@[simp]
theorem simplexResolutionSigma_comp_pi {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (a : SimplexCategoryᵒᵖ) :
    simplexResolutionSigma p a ⋙ simplexResolutionPi p a =
      𝟭 (Discrete (Z.obj a)) := by
  apply Discrete.functor_ext
  intro x
  have hfst :
      (pullback.fst p (simplexResolutionSigmaObj p a x).obj.hom).app a
        (simplexResolutionSigmaObj p a x).val = x :=
    (simplexPullbackObjEquiv_fst p
        (simplexResolutionSigmaObj p a x).obj a
        (simplexResolutionSigmaObj p a x).val).symm.trans
      (simplexResolutionSigmaObj_decoded_fst p a x)
  apply Discrete.ext
  simpa only [Functor.comp_obj, Functor.id_obj,
    simplexResolutionSigma, Discrete.functor_obj_eq_as,
    simplexResolutionPi_obj_as] using hfst

/-- The simplex-index arrow from the simplex representing the image under `p`
of the source coordinate of `e` to `e.obj`, induced by the simplex-category map
decoded from the pullback element `e.val`. -/
noncomputable def simplexResolutionSigmaPiArrow
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ)
    (e : (simplexPullbackDegree p a).Elements) :
    (simplexResolutionSigmaObj p a
      ((simplexResolutionPi p a).obj e).as).obj ⟶
      e.obj := by
  let d := simplexPullbackObjEquiv p e.obj a e.val
  let alpha : a.unop ⟶ e.obj.left := d.1.2
  refine CostructuredArrow.homMk alpha ?_
  have hx : ((simplexResolutionPi p a).obj e).as = d.1.1 := by
    exact (simplexPullbackObjEquiv_fst p e.obj a e.val).symm
  change SSet.stdSimplex.map alpha ≫ e.obj.hom =
    SSet.yonedaEquiv.symm
      (p.app a ((simplexResolutionPi p a).obj e).as)
  calc
    SSet.stdSimplex.map alpha ≫ e.obj.hom =
        SSet.yonedaEquiv.symm
          (Y.map alpha.op (SSet.yonedaEquiv e.obj.hom)) := by
      simpa only [Equiv.symm_apply_apply] using
        SSet.yonedaEquiv_symm_naturality_left alpha
          (SSet.yonedaEquiv e.obj.hom)
    _ = SSet.yonedaEquiv.symm (p.app a d.1.1) :=
      congrArg SSet.yonedaEquiv.symm d.2.symm
    _ = SSet.yonedaEquiv.symm
        (p.app a ((simplexResolutionPi p a).obj e).as) := by rw [hx]

/-- The contraction component from the source projection of `e` followed by
the canonical section back to `e` in the Elements category. Its underlying
simplex-index arrow is `simplexResolutionSigmaPiArrow p a e`. -/
noncomputable def simplexResolutionSigmaPiToIdApp
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ)
    (e : (simplexPullbackDegree p a).Elements) :
    (simplexResolutionPi p a ⋙ simplexResolutionSigma p a).obj e ⟶ e := by
  refine Functor.Elements.homMk (simplexResolutionSigmaPiArrow p a e) ?_
  change (simplexPullbackMap p (simplexResolutionSigmaPiArrow p a e)).app a
      (simplexResolutionSigmaObj p a
        ((simplexResolutionPi p a).obj e).as).val = e.val
  apply (simplexPullbackObjEquiv p e.obj a).injective
  apply Subtype.ext
  apply Prod.ext
  · calc
      _ = (simplexPullbackObjEquiv p
          (simplexResolutionSigmaObj p a
            ((simplexResolutionPi p a).obj e).as).obj a
          (simplexResolutionSigmaObj p a
            ((simplexResolutionPi p a).obj e).as).val).1.1 :=
        simplexPullbackObjEquiv_map_fst p a
          (simplexResolutionSigmaPiArrow p a e) _
      _ = ((simplexResolutionPi p a).obj e).as :=
        simplexResolutionSigmaObj_decoded_fst p a _
      _ = (simplexPullbackObjEquiv p e.obj a e.val).1.1 :=
        (simplexPullbackObjEquiv_fst p e.obj a e.val).symm
  · calc
      _ = (simplexPullbackObjEquiv p
          (simplexResolutionSigmaObj p a
            ((simplexResolutionPi p a).obj e).as).obj a
          (simplexResolutionSigmaObj p a
            ((simplexResolutionPi p a).obj e).as).val).1.2 ≫
            (simplexResolutionSigmaPiArrow p a e).left :=
        simplexPullbackObjEquiv_map_snd p a
          (simplexResolutionSigmaPiArrow p a e) _
      _ = 𝟙 a.unop ≫
          (simplexPullbackObjEquiv p e.obj a e.val).1.2 := by
        rw [simplexResolutionSigmaObj_decoded_snd]
        rfl
      _ = _ := Category.id_comp _

/-- The decoded simplex map is the underlying simplex-category component of
the contraction arrow. -/
@[simp]
theorem simplexResolutionSigmaPiToIdApp_left
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ)
    (e : (simplexPullbackDegree p a).Elements) :
    (simplexResolutionSigmaPiToIdApp p a e).hom.left =
      (simplexPullbackObjEquiv p e.obj a e.val).1.2 :=
  by
    unfold simplexResolutionSigmaPiToIdApp simplexResolutionSigmaPiArrow
    rfl

/-- The canonicalization endofunctor contracts naturally to the identity
through the decoded simplex map. -/
noncomputable def simplexResolutionSigmaPiToId
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ) :
    simplexResolutionPi p a ⋙ simplexResolutionSigma p a ⟶
      𝟭 (simplexPullbackDegree p a).Elements where
  app e := simplexResolutionSigmaPiToIdApp p a e
  naturality {e e'} f := by
    apply Functor.Elements.hom_ext
    apply CostructuredArrow.hom_ext
    have hAlpha := simplexPullbackObjEquiv_map_snd p a f.hom e.val
    have hf : (simplexPullbackMap p f.hom).app a e.val = e'.val := by
      exact f.map_val
    rw [hf] at hAlpha
    have hLeftComp :
        (((simplexResolutionSigma p a).map
          ((simplexResolutionPi p a).map f)).hom).left ≫
            (simplexResolutionSigmaPiToIdApp p a e').hom.left =
          (simplexResolutionSigmaPiToIdApp p a e').hom.left :=
      simplexResolutionSigma_map_hom_left_comp p a _ _
    have hApp :
        (simplexResolutionSigmaPiToIdApp p a e').hom.left =
          (simplexResolutionSigmaPiToIdApp p a e).hom.left ≫
            f.hom.left := by
      rw [simplexResolutionSigmaPiToIdApp_left,
        simplexResolutionSigmaPiToIdApp_left]
      exact hAlpha
    simpa only [Functor.comp_map, Functor.id_map,
      Functor.Elements.comp_hom, CostructuredArrow.comp_left] using
        hLeftComp.trans hApp

private abbrev simplexResolutionSmallDiscrete (X : Type u) :=
  ShrinkHoms (Discrete X)

private abbrev simplexResolutionSmallNerve (X : Type u) : SSet.{u} :=
  nerve.{0, u} (simplexResolutionSmallDiscrete X)

private noncomputable def simplexResolutionPiSmall
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ) :
    (simplexPullbackDegree p a).Elements ⥤
      simplexResolutionSmallDiscrete (Z.obj a) :=
  simplexResolutionPi p a ⋙
    ShrinkHoms.functor.{0} (Discrete (Z.obj a))

private noncomputable def simplexResolutionSigmaSmall
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ) :
    simplexResolutionSmallDiscrete (Z.obj a) ⥤
      (simplexPullbackDegree p a).Elements :=
  ShrinkHoms.inverse.{0} (Discrete (Z.obj a)) ⋙
    simplexResolutionSigma p a

private theorem simplexResolutionSigmaSmall_comp_piSmall
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ) :
    simplexResolutionSigmaSmall p a ⋙ simplexResolutionPiSmall p a =
      𝟭 (simplexResolutionSmallDiscrete (Z.obj a)) := by
  calc
    simplexResolutionSigmaSmall p a ⋙ simplexResolutionPiSmall p a =
        ShrinkHoms.inverse.{0} (Discrete (Z.obj a)) ⋙
          (simplexResolutionSigma p a ⋙ simplexResolutionPi p a) ⋙
            ShrinkHoms.functor.{0} (Discrete (Z.obj a)) := by
      simp only [simplexResolutionSigmaSmall, simplexResolutionPiSmall,
        Functor.assoc]
    _ = ShrinkHoms.inverse.{0} (Discrete (Z.obj a)) ⋙
          ShrinkHoms.functor.{0} (Discrete (Z.obj a)) := by
      rw [simplexResolutionSigma_comp_pi]
      rfl
    _ = 𝟭 (simplexResolutionSmallDiscrete (Z.obj a)) := by
      refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
      intro x y f
      exact Shrink.ext (Subsingleton.elim _ _)

private noncomputable def simplexResolutionShrinkUnitInv (X : Type u) :
    ShrinkHoms.functor.{0} (Discrete X) ⋙
        ShrinkHoms.inverse.{0} (Discrete X) ⟶
      𝟭 (Discrete X) :=
  (ShrinkHoms.equivalence.{0} (Discrete X)).unitIso.inv

private noncomputable def simplexResolutionSigmaPiSmallToId
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ) :
    simplexResolutionPiSmall p a ⋙ simplexResolutionSigmaSmall p a ⟶
      𝟭 (simplexPullbackDegree p a).Elements := by
  let α := Functor.whiskerRight
    (Functor.whiskerLeft (simplexResolutionPi p a)
      (simplexResolutionShrinkUnitInv (Z.obj a)))
    (simplexResolutionSigma p a)
  have h := α ≫ simplexResolutionSigmaPiToId p a
  simpa only [simplexResolutionPiSmall, simplexResolutionSigmaSmall,
    Functor.assoc, Functor.comp_id] using h

private noncomputable def simplexResolutionSmallNerveObjEquiv (X : Type u)
    (a : SimplexCategoryᵒᵖ) :
    (simplexResolutionSmallNerve X).obj a ≃ X where
  toFun F := (ShrinkHoms.fromShrinkHoms (F.obj 0)).as
  invFun x := (Functor.const (Fin (a.unop.len + 1))).obj
    (ShrinkHoms.toShrinkHoms (Discrete.mk x))
  left_inv F := by
    fapply CategoryTheory.Functor.ext
    · intro i
      apply Discrete.ext
      let f : ShrinkHoms.fromShrinkHoms (F.obj 0) ⟶
          ShrinkHoms.fromShrinkHoms (F.obj i) :=
        (equivShrink _).symm (F.map (homOfLE (Fin.zero_le i)))
      exact f.eq
    · intro i j f
      exact Shrink.ext (Subsingleton.elim _ _)
  right_inv _ := rfl

private noncomputable def simplexResolutionSmallNerveIso (X : Type u) :
    simplexResolutionSmallNerve X ≅
      (Functor.const SimplexCategoryᵒᵖ).obj X :=
  NatIso.ofComponents
    (fun a => (simplexResolutionSmallNerveObjEquiv X a).toIso) (by
      intro a b k
      apply ConcreteCategory.hom_ext
      intro F
      let f : ShrinkHoms.fromShrinkHoms (F.obj 0) ⟶
          ShrinkHoms.fromShrinkHoms (F.obj (k.unop.toOrderHom 0)) :=
        (equivShrink _).symm
          (F.map (homOfLE (Fin.zero_le (k.unop.toOrderHom 0))))
      exact f.eq.symm)

/-- Fixed-inner replacement-row augmentation obtained from the Elements
projection. -/
@[no_expose]
noncomputable def simplexResolutionDegreeAugmentation
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ) :
    CategoryBar.simplicialReplacement (simplexPullbackDegree p a) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (Z.obj a) :=
  (CategoryBar.replNerveSimplicialIso (simplexPullbackDegree p a)).hom ≫
    nerveMap (simplexResolutionPiSmall p a) ≫
      (simplexResolutionSmallNerveIso (Z.obj a)).hom

/-- The fixed-inner augmentation sends a replacement simplex to its source
coefficient, then projects that coefficient to the source simplicial set. -/
@[simp↓]
theorem simplexResolutionDegreeAugmentation_app_apply
    {Z Y : SSet.{u}} (p : Z ⟶ Y)
    (a : SimplexCategoryᵒᵖ) (n : ℕ)
    (s : ComposableArrows (SimplexIndex Y) n)
    (x : (simplexPullbackDegree p a).obj s.left) (w : PUnit) :
    (simplexResolutionDegreeAugmentation p a).app (op ⦋n⦌)
        ⟨s, x, w⟩ =
      (pullback.fst p s.left.hom).app a x := by
  change
    ((simplexResolutionPi p a).obj
      ((CategoryBar.replElementsEquiv (SimplexIndex Y)
        (simplexPullbackDegree p a) n ⟨s, x, w⟩).obj 0)).as = _
  have he :
      (CategoryBar.replElementsEquiv (SimplexIndex Y)
          (simplexPullbackDegree p a) n ⟨s, x, w⟩).obj 0 =
        (simplexPullbackDegree p a).elementsMk s.left x := by
    refine Functor.Elements.ext _ _ rfl ?_
    change
      (simplexPullbackDegree p a).map (eqToHom rfl)
          ((simplexPullbackDegree p a).map (s.map' 0 0) x) = x
    simp only [eqToHom_refl, s.map'_self 0 (Nat.zero_le n)]
    have hId (y : (simplexPullbackDegree p a).obj s.left) :
        (simplexPullbackDegree p a).map (𝟙 s.left) y = y :=
      ConcreteCategory.congr_hom
        ((simplexPullbackDegree p a).map_id s.left) y
    exact (hId _).trans (hId x)
  rw [he]
  rfl

/-- Fixed-inner replacement-row section obtained from the canonical
`(x,id)` Elements object. -/
@[no_expose]
noncomputable def simplexResolutionDegreeSection
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ) :
    (Functor.const SimplexCategoryᵒᵖ).obj (Z.obj a) ⟶
      CategoryBar.simplicialReplacement (simplexPullbackDegree p a) :=
  (simplexResolutionSmallNerveIso (Z.obj a)).inv ≫
    nerveMap (simplexResolutionSigmaSmall p a) ≫
      (CategoryBar.replNerveSimplicialIso (simplexPullbackDegree p a)).inv

/-- The fixed-inner section followed by augmentation is strictly the
identity. -/
@[simp]
theorem simplexResolutionDegreeSection_comp_augmentation
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ) :
    simplexResolutionDegreeSection p a ≫
        simplexResolutionDegreeAugmentation p a =
      𝟙 ((Functor.const SimplexCategoryᵒᵖ).obj (Z.obj a)) := by
  have hN : nerveMap (simplexResolutionSigmaSmall p a) ≫
      nerveMap (simplexResolutionPiSmall p a) = 𝟙 _ := by
    rw [nerveMap_comp, simplexResolutionSigmaSmall_comp_piSmall, nerveMap_id]
  let d := simplexResolutionSmallNerveIso (Z.obj a)
  change (d.inv ≫ nerveMap (simplexResolutionSigmaSmall p a) ≫
      (CategoryBar.replNerveSimplicialIso
        (simplexPullbackDegree p a)).inv) ≫
    ((CategoryBar.replNerveSimplicialIso
        (simplexPullbackDegree p a)).hom ≫
      nerveMap (simplexResolutionPiSmall p a) ≫ d.hom) = 𝟙 _
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id, Category.id_comp] using
      congrArg (fun q => d.inv ≫ q ≫ d.hom) hN

/-- Fixed-inner augmentation followed by its section is homotopic to the
identity. -/
@[no_expose]
noncomputable def simplexResolutionDegreeAugmentationSectionHomotopy
    {Z Y : SSet.{u}} (p : Z ⟶ Y) (a : SimplexCategoryᵒᵖ) :
    SSet.Homotopy
      (simplexResolutionDegreeAugmentation p a ≫
        simplexResolutionDegreeSection p a)
      (𝟙 (CategoryBar.simplicialReplacement (simplexPullbackDegree p a))) := by
  let e := CategoryBar.replNerveSimplicialIso (simplexPullbackDegree p a)
  let H := CategoryTheory.NatTrans.nerveHomotopy
    (simplexResolutionSigmaPiSmallToId p a)
  change SSet.RelativeMorphism.Homotopy
    (SSet.RelativeMorphism.botEquiv.symm _)
    (SSet.RelativeMorphism.botEquiv.symm _)
  refine
    { h := (e.hom ▷ (Δ[1] : SSet.{u})) ≫ H.h ≫ e.inv
      h₀ := ?_
      h₁ := ?_
      rel := by
        ext b ⟨⟨x, hx⟩, t⟩
        cases hx }
  · calc
      SSet.ι₀ ≫ ((e.hom ▷ (Δ[1] : SSet.{u})) ≫ H.h ≫ e.inv) =
          e.hom ≫ (SSet.ι₀ ≫ H.h) ≫ e.inv := by
            rw [← Category.assoc, SSet.ι₀_comp]
            simp only [Category.assoc]
      _ = e.hom ≫
          CategoryTheory.nerveMap
            (simplexResolutionPiSmall p a ⋙
              simplexResolutionSigmaSmall p a) ≫
          e.inv :=
            congrArg (fun q => e.hom ≫ q ≫ e.inv) H.h₀
      _ = simplexResolutionDegreeAugmentation p a ≫
          simplexResolutionDegreeSection p a := by
            simp [simplexResolutionDegreeAugmentation,
              simplexResolutionDegreeSection, e, ← nerveMap_comp,
              Category.assoc]
  · calc
      SSet.ι₁ ≫ ((e.hom ▷ (Δ[1] : SSet.{u})) ≫ H.h ≫ e.inv) =
          e.hom ≫ (SSet.ι₁ ≫ H.h) ≫ e.inv := by
            rw [← Category.assoc, SSet.ι₁_comp]
            simp only [Category.assoc]
      _ = e.hom ≫ 𝟙 _ ≫ e.inv :=
        congrArg (fun q => e.hom ≫ q ≫ e.inv) H.h₁
      _ = 𝟙 _ := by simp [e]

end SSet

end
