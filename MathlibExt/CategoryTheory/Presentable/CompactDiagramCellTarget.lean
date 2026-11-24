/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Presentable.CompactDiagramRoot
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.RelativePresentability
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramActionConstraintBounds

/-!
# Compact whole-diagram cell targets

A regular cardinal and the actual bounded original index suffice to capture
compact component attachments and their actions at a common stage of the
original source presentation. Native pushout descents recover the whole target
functor and the original whole pushout.

This is the ordinary finite-refinement core of Jacob Lurie's *Higher Topos
Theory*, author version dated April 9, 2017, Lemma A.3.3.17, printed pages
883–884 (PDF pages 901–902). The later countable slice constructions use the
source application's uncountable rank; this finite core uses regularity.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SmallObject.CompactRootBaseChange
open CategoryTheory.Presentable

universe w uD vD uC vC uI vI uE uK

namespace CategoryTheory.Presentable

-- A bounded family of maps from compact objects factors through one common stage.
private theorem commonCoconeFactors {I : Type uI} [Category.{vI} I] {E : Type uE} {K : Type uK}
    {C : Type uC} [Category.{vC} C]
    (chi : Cardinal.{w}) [Fact chi.IsRegular]
    [EssentiallySmall.{w} I] [IsCardinalFiltered I chi]
    (H : E → I ⥤ C) (c : ∀ e, Cocone (H e)) (hc : ∀ e, IsColimit (c e))
    (target : K → E) (Z : K → C)
    (hK : HasCardinalLT K chi) (hZ : ∀ k, IsCardinalPresentable (Z k) chi)
    (f : ∀ k, Z k ⟶ (c (target k)).pt) :
    ∃ (i : I) (g : ∀ k, Z k ⟶ (H (target k)).obj i),
      ∀ k, g k ≫ (c (target k)).ι.app i = f k := by
  have h (k : K) :
      ∃ i : I, ∃ g : Z k ⟶ (H (target k)).obj i,
        g ≫ (c (target k)).ι.app i = f k := by
    let : IsCardinalPresentable (Z k) chi := hZ k
    exact IsCardinalPresentable.exists_hom_of_isColimit chi (hc (target k)) (f k)
  choose stage factor hfactor using h
  let i := IsCardinalFiltered.max stage hK
  let trans (k : K) : stage k ⟶ i := IsCardinalFiltered.toMax stage hK k
  refine ⟨i, fun k => factor k ≫ (H (target k)).map (trans k), ?_⟩
  intro k
  rw [Category.assoc, (c (target k)).w (trans k)]
  exact hfactor k

-- Uniform actual later-stage equality, including empty constraint families.
-- Thinness belongs to the genuine compact presentation/Under-stage index.
private theorem commonCoconeEqualities {I : Type uI} [Category.{vI} I] [Quiver.IsThin I]
    {E : Type uE} {K : Type uK} {C : Type uC} [Category.{vC} C]
    (chi : Cardinal.{w}) [Fact chi.IsRegular]
    [EssentiallySmall.{w} I] [IsCardinalFiltered I chi]
    (H : E → I ⥤ C) (c : ∀ e, Cocone (H e)) (hc : ∀ e, IsColimit (c e))
    (target : K → E) (Z : K → C)
    (hK : HasCardinalLT K chi) (hZ : ∀ k, IsCardinalPresentable (Z k) chi)
    (i : I) (f g : ∀ k, Z k ⟶ (H (target k)).obj i)
    (he : ∀ k, f k ≫ (c (target k)).ι.app i = g k ≫ (c (target k)).ι.app i) :
    ∃ (j : I) (t : i ⟶ j),
      ∀ k, f k ≫ (H (target k)).map t = g k ≫ (H (target k)).map t := by
  let : IsFiltered I := isFiltered_of_isCardinalFiltered I chi
  have h (k : K) : ∃ (j : I) (t : i ⟶ j),
      f k ≫ (H (target k)).map t = g k ≫ (H (target k)).map t := by
    let : IsCardinalPresentable (Z k) chi := hZ k
    exact IsCardinalPresentable.exists_eq_of_isColimit' chi
      (hc (target k)) (f k) (g k) (he k)
  choose stage trans hstage using h
  let upper := IsCardinalFiltered.max stage hK
  let j := IsFiltered.max i upper
  let left : i ⟶ j := IsFiltered.leftToMax i upper
  let right : upper ⟶ j := IsFiltered.rightToMax i upper
  let extra (k : K) : stage k ⟶ j := IsCardinalFiltered.toMax stage hK k ≫ right
  have path (k : K) : trans k ≫ extra k = left := Subsingleton.elim _ _
  refine ⟨j, left, ?_⟩
  intro k
  have hh := congrArg (fun z => z ≫ (H (target k)).map (extra k)) (hstage k)
  simpa only [Category.assoc, ← Functor.map_comp, path k] using hh


private noncomputable abbrev evaluatedApproximation
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
    (hD : HasCardinalLT (Arrow D) chi) (F : D ⥤ C)
    (A : CompactApproximation chi F) (d : D) : CompactApproximation chi (F.obj d) := by
  let : Small.{w} (Arrow D) := hD.small
  let : Small.{w} D := small_of_small_arrow D
  let : LocallySmall.{w} D := locallySmall_of_small_arrow D
  let idx := equivSmallModel.{w} D
  let ev := (evaluation D C).obj d
  refine
    { index := A.index
      partialOrder := A.partialOrder
      filtered := A.filtered
      presentation :=
        { diag := A.presentation.diag ⋙ ev
          ι := (ev.mapCocone A.presentation.cocone).ι
          isColimit := isColimitOfPreserves ev A.presentation.isColimit }
      presentable := ?_ }
  intro j
  let : IsCardinalPresentable (A.presentation.diag.obj j) chi := A.presentable j
  let : (Completeness.cofree C chi idx d).IsCardinalAccessible chi :=
    HomPowerAccessibility.cofree_isCardinalAccessible_of_hom_bounds
      C chi idx d chi le_rfl
      (fun e => Functor.OriginalArrowBounds.homLt hD e d)
  exact Adjunction.isCardinalPresentable_leftAdjoint_obj
    (Completeness.evaluationCofreeAdjunction C chi idx d) chi
    (A.presentation.diag.obj j)

private noncomputable abbrev originalTargetPresentation
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
    (hD : HasCardinalLT (Arrow D) chi) (F G : D ⥤ C) (f : F ⟶ G)
    (A : CompactApproximation chi F) (i : A.index) (d : D)
    (U : Under ((A.presentation.diag.obj i).obj d)) (q : U.right ⟶ G.obj d)
    (H : IsPushout U.hom ((A.presentation.ι.app i).app d) q (f.app d)) :
    ColimitPresentation (Under i) (G.obj d) :=
  (rootPushoutPresentation chi (evaluatedApproximation chi hD F A d) i U).ofIso
    H.isoPushout.symm

-- The original scalar chart-target leg, including its actual point in G.
private theorem originalTargetPresentation_inl
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
    (hD : HasCardinalLT (Arrow D) chi) (F G : D ⥤ C) (f : F ⟶ G)
    (A : CompactApproximation chi F) (i : A.index) (d : D)
    (U : Under ((A.presentation.diag.obj i).obj d)) (q : U.right ⟶ G.obj d)
    (H : IsPushout U.hom ((A.presentation.ι.app i).app d) q (f.app d))
    (j : Under i) :
    pushout.inl U.hom ((A.presentation.diag.map j.hom).app d) ≫
      (originalTargetPresentation chi hD F G f A i d U q H).ι.app j = q := by
  let E := evaluatedApproximation chi hD F A d
  have h := congrArg (fun z => z ≫ H.isoPushout.inv)
    (rootPushoutPresentation_inl chi E i U j)
  exact (Category.assoc _ _ _).symm.trans (h.trans H.inl_isoPushout_inv)


-- The original scalar source leg through the same target cocone.
private theorem originalTargetPresentation_inr
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
    (hD : HasCardinalLT (Arrow D) chi) (F G : D ⥤ C) (f : F ⟶ G)
    (A : CompactApproximation chi F) (i : A.index) (d : D)
    (U : Under ((A.presentation.diag.obj i).obj d)) (q : U.right ⟶ G.obj d)
    (H : IsPushout U.hom ((A.presentation.ι.app i).app d) q (f.app d))
    (j : Under i) :
    pushout.inr U.hom ((A.presentation.diag.map j.hom).app d) ≫
      (originalTargetPresentation chi hD F G f A i d U q H).ι.app j =
        (A.presentation.ι.app j.right).app d ≫ f.app d := by
  let E := evaluatedApproximation chi hD F A d
  have h := congrArg (fun z => z ≫ H.isoPushout.inv)
    (rootPushoutPresentation_inr chi E i U j)
  exact (Category.assoc _ _ _).symm.trans
    (h.trans ((Category.assoc _ _ _).trans
      (congrArg (fun z => (A.presentation.ι.app j.right).app d ≫ z)
        H.inr_isoPushout_inv)))


-- Every original compact chart action is captured at one original receiving root stage.
private theorem firstTargetActions
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
    (hD : HasCardinalLT (Arrow D) chi) (F G : D ⥤ C) (f : F ⟶ G)
    (A : CompactApproximation chi F) (i : A.index)
    (B : D → C) (g : ∀ d, (A.presentation.diag.obj i).obj d ⟶ B d)
    (q : ∀ d, B d ⟶ G.obj d)
    (hB : ∀ d, IsCardinalPresentable (B d) chi)
    (H : ∀ d, IsPushout (g d) ((A.presentation.ι.app i).app d) (q d) (f.app d)) :
    ∃ (j : Under i)
      (actions : ∀ a : Arrow D, B a.left ⟶
        (originalTargetPresentation chi hD F G f A i a.right
          (Under.mk (g a.right)) (q a.right) (H a.right)).diag.obj j),
      ∀ a : Arrow D, actions a ≫
        (originalTargetPresentation chi hD F G f A i a.right
          (Under.mk (g a.right)) (q a.right) (H a.right)).ι.app j =
        q a.left ≫ G.map a.hom := by
  let P (d : D) := originalTargetPresentation chi hD F G f A i d
    (Under.mk (g d)) (q d) (H d)
  exact commonCoconeFactors chi (fun d => (P d).diag) (fun d => (P d).cocone)
    (fun d => (P d).isColimit) (fun a : Arrow D => a.right)
    (fun a : Arrow D => B a.left) hD (fun a => hB a.left)
    (fun a => q a.left ≫ G.map a.hom)


-- Source compatibility is forced on the ORIGINAL compact source components.
private theorem firstTargetActionsWithRoots
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
    (hD : HasCardinalLT (Arrow D) chi) (F G : D ⥤ C) (f : F ⟶ G)
    (A : CompactApproximation chi F) (i : A.index)
    (B : D → C) (g : ∀ d, (A.presentation.diag.obj i).obj d ⟶ B d)
    (q : ∀ d, B d ⟶ G.obj d)
    (hB : ∀ d, IsCardinalPresentable (B d) chi)
    (H : ∀ d, IsPushout (g d) ((A.presentation.ι.app i).app d) (q d) (f.app d)) :
    ∃ (j : Under i)
      (actions : ∀ a : Arrow D, B a.left ⟶
        (originalTargetPresentation chi hD F G f A i a.right
          (Under.mk (g a.right)) (q a.right) (H a.right)).diag.obj j),
      ∀ a : Arrow D,
        actions a ≫
          (originalTargetPresentation chi hD F G f A i a.right
            (Under.mk (g a.right)) (q a.right) (H a.right)).ι.app j =
          q a.left ≫ G.map a.hom ∧
        g a.left ≫ actions a =
          (A.presentation.diag.obj i).map a.hom ≫
            (A.presentation.diag.map j.hom).app a.right ≫
              pushout.inr (g a.right) ((A.presentation.diag.map j.hom).app a.right) := by
  let P (d : D) := originalTargetPresentation chi hD F G f A i d
    (Under.mk (g d)) (q d) (H d)
  obtain ⟨j, act, hact⟩ := firstTargetActions chi hD F G f A i B g q hB H
  let : Quiver.IsThin (Under i) := fun _ _ =>
    ⟨fun s t => Under.UnderMorphism.ext (Subsingleton.elim s.right t.right)⟩
  let lhs (a : Arrow D) := g a.left ≫ act a
  let rhs (a : Arrow D) :=
    (A.presentation.diag.obj i).map a.hom ≫
      (A.presentation.diag.map j.hom).app a.right ≫
        pushout.inr (g a.right) ((A.presentation.diag.map j.hom).app a.right)
  let v (d : D) : pushout (g d) ((A.presentation.diag.map j.hom).app d) ⟶ G.obj d :=
    (P d).ι.app j
  have hv (d : D) :
      pushout.inr (g d) ((A.presentation.diag.map j.hom).app d) ≫ v d =
        (A.presentation.ι.app j.right).app d ≫ f.app d :=
    originalTargetPresentation_inr chi hD F G f A i d
      (Under.mk (g d)) (q d) (H d) j
  have he (a : Arrow D) :
      lhs a ≫ (P a.right).ι.app j = rhs a ≫ (P a.right).ι.app j := by
    change (g a.left ≫ act a) ≫ v a.right =
      ((A.presentation.diag.obj i).map a.hom ≫
        (A.presentation.diag.map j.hom).app a.right ≫
          pushout.inr (g a.right) ((A.presentation.diag.map j.hom).app a.right)) ≫ v a.right
    have ha : act a ≫ v a.right = q a.left ≫ G.map a.hom := hact a
    rw [Category.assoc, ha]
    rw [← Category.assoc, (H a.left).w, Category.assoc, ← f.naturality a.hom]
    rw [Category.assoc, Category.assoc, hv]
    have hj : (A.presentation.diag.map j.hom).app a.right ≫
        (A.presentation.ι.app j.right).app a.right =
          (A.presentation.ι.app i).app a.right :=
      NatTrans.congr_app (A.presentation.w j.hom) a.right
    rw [← Category.assoc ((A.presentation.diag.map j.hom).app a.right), hj]
    rw [← Category.assoc]
    have hi : (A.presentation.diag.obj i).map a.hom ≫
        (A.presentation.ι.app i).app a.right =
          (A.presentation.ι.app i).app a.left ≫ F.map a.hom :=
      (A.presentation.ι.app i).naturality a.hom
    exact (congrArg (fun z => z ≫ f.app a.right) hi).symm.trans (Category.assoc _ _ _)
  have hSource (a : Arrow D) :
      IsCardinalPresentable ((A.presentation.diag.obj i).obj a.left) chi :=
    (evaluatedApproximation chi hD F A a.left).presentable i
  obtain ⟨k, t, heq⟩ := commonCoconeEqualities chi (fun d => (P d).diag)
    (fun d => (P d).cocone) (fun d => (P d).isColimit)
    (fun a : Arrow D => a.right) (fun a : Arrow D => (A.presentation.diag.obj i).obj a.left)
    hD hSource j lhs rhs he
  let T (d : D) :
      pushout (g d) ((A.presentation.diag.map j.hom).app d) ⟶
        pushout (g d) ((A.presentation.diag.map k.hom).app d) :=
    (P d).diag.map t
  have hT (d : D) :
      pushout.inr (g d) ((A.presentation.diag.map j.hom).app d) ≫ T d =
        (A.presentation.diag.map t.right).app d ≫
          pushout.inr (g d) ((A.presentation.diag.map k.hom).app d) := by
    exact pushout.inr_desc _ _ _
  refine ⟨k, fun a => act a ≫ (P a.right).diag.map t, ?_⟩
  intro a
  constructor
  · rw [Category.assoc, (P a.right).w t]
    exact hact a
  · have hh : g a.left ≫ (act a ≫ T a.right) = rhs a ≫ T a.right :=
      (Category.assoc _ _ _).symm.trans (heq a)
    have hjk : (A.presentation.diag.map j.hom).app a.right ≫
        (A.presentation.diag.map t.right).app a.right =
          (A.presentation.diag.map k.hom).app a.right := by
      rw [← NatTrans.comp_app, ← Functor.map_comp, Under.w t]
    have hr : rhs a ≫ T a.right =
        (A.presentation.diag.obj i).map a.hom ≫
          (A.presentation.diag.map k.hom).app a.right ≫
            pushout.inr (g a.right) ((A.presentation.diag.map k.hom).app a.right) := by
      dsimp only [rhs]
      rw [Category.assoc, Category.assoc, hT,
        ← Category.assoc ((A.presentation.diag.map j.hom).app a.right), hjk]
    exact hh.trans hr


-- A finite-stage action is an actual native pushout descent.
private noncomputable def pushoutAction
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    [HasPushouts C] (S T : D ⥤ C) (t : S ⟶ T)
    (B : D → C) (g : ∀ d, S.obj d ⟶ B d)
    (a : Arrow D)
    (L : B a.left ⟶ pushout (g a.right) (t.app a.right))
    (h : g a.left ≫ L = S.map a.hom ≫ t.app a.right ≫
      pushout.inr (g a.right) (t.app a.right)) :
    pushout (g a.left) (t.app a.left) ⟶ pushout (g a.right) (t.app a.right) :=
  pushout.desc L (T.map a.hom ≫ pushout.inr (g a.right) (t.app a.right))
    (h.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ pushout.inr (g a.right) (t.app a.right))
        (t.naturality a.hom)).trans (Category.assoc _ _ _))))

private theorem pushoutAction_inl
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    [HasPushouts C] (S T : D ⥤ C) (t : S ⟶ T)
    (B : D → C) (g : ∀ d, S.obj d ⟶ B d) (a : Arrow D)
    (L : B a.left ⟶ pushout (g a.right) (t.app a.right))
    (h : g a.left ≫ L = S.map a.hom ≫ t.app a.right ≫
      pushout.inr (g a.right) (t.app a.right)) :
    pushout.inl (g a.left) (t.app a.left) ≫ pushoutAction S T t B g a L h = L :=
  pushout.inl_desc _ _ _

private theorem pushoutAction_inr
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    [HasPushouts C] (S T : D ⥤ C) (t : S ⟶ T)
    (B : D → C) (g : ∀ d, S.obj d ⟶ B d) (a : Arrow D)
    (L : B a.left ⟶ pushout (g a.right) (t.app a.right))
    (h : g a.left ≫ L = S.map a.hom ≫ t.app a.right ≫
      pushout.inr (g a.right) (t.app a.right)) :
    pushout.inr (g a.left) (t.app a.left) ≫ pushoutAction S T t B g a L h =
      T.map a.hom ≫ pushout.inr (g a.right) (t.app a.right) :=
  pushout.inr_desc _ _ _


-- The descended entire action has its actual original target equation.
private theorem pushoutAction_endpoint
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    [HasPushouts C] (S T F G : D ⥤ C) (t : S ⟶ T) (u : T ⟶ F) (f : F ⟶ G)
    (B : D → C) (g : ∀ d, S.obj d ⟶ B d)
    (q : ∀ d, B d ⟶ G.obj d)
    (V : ∀ d, pushout (g d) (t.app d) ⟶ G.obj d)
    (hVL : ∀ d, pushout.inl (g d) (t.app d) ≫ V d = q d)
    (hVR : ∀ d, pushout.inr (g d) (t.app d) ≫ V d = u.app d ≫ f.app d)
    (a : Arrow D) (L : B a.left ⟶ pushout (g a.right) (t.app a.right))
    (h : g a.left ≫ L = S.map a.hom ≫ t.app a.right ≫
      pushout.inr (g a.right) (t.app a.right))
    (hL : L ≫ V a.right = q a.left ≫ G.map a.hom) :
    pushoutAction S T t B g a L h ≫ V a.right = V a.left ≫ G.map a.hom := by
  apply pushout.hom_ext
  · rw [← Category.assoc, pushoutAction_inl, hL, ← Category.assoc, hVL]
  · rw [← Category.assoc, pushoutAction_inr, Category.assoc, hVR]
    rw [← Category.assoc (pushout.inr (g a.left) (t.app a.left)), hVR,
      Category.assoc, ← f.naturality a.hom]
    rw [← Category.assoc, u.naturality a.hom]
    simp only [Category.assoc]


-- Actual stage transitions commute with the entire descended actions.
private theorem pushoutAction_transition
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    [HasPushouts C] (S T U : D ⥤ C) (t : S ⟶ T) (s : S ⟶ U) (r : T ⟶ U)
    (B : D → C) (g : ∀ d, S.obj d ⟶ B d)
    (V : ∀ d, pushout (g d) (t.app d) ⟶ pushout (g d) (s.app d))
    (hVL : ∀ d, pushout.inl (g d) (t.app d) ≫ V d = pushout.inl (g d) (s.app d))
    (hVR : ∀ d, pushout.inr (g d) (t.app d) ≫ V d =
      r.app d ≫ pushout.inr (g d) (s.app d))
    (a : Arrow D)
    (L : B a.left ⟶ pushout (g a.right) (t.app a.right))
    (K : B a.left ⟶ pushout (g a.right) (s.app a.right))
    (hL : g a.left ≫ L = S.map a.hom ≫ t.app a.right ≫
      pushout.inr (g a.right) (t.app a.right))
    (hK : g a.left ≫ K = S.map a.hom ≫ s.app a.right ≫
      pushout.inr (g a.right) (s.app a.right))
    (hLK : L ≫ V a.right = K) :
    V a.left ≫ pushoutAction S U s B g a K hK =
      pushoutAction S T t B g a L hL ≫ V a.right := by
  apply pushout.hom_ext
  · rw [← Category.assoc, hVL, pushoutAction_inl,
      ← Category.assoc, pushoutAction_inl, hLK]
  · rw [← Category.assoc, hVR, Category.assoc, pushoutAction_inr,
      ← Category.assoc (pushout.inr (g a.left) (t.app a.left)),
      pushoutAction_inr, Category.assoc, hVR]
    simpa only [Category.assoc] using
      (congrArg (fun z => z ≫ pushout.inr (g a.right) (s.app a.right))
        (r.naturality a.hom)).symm


-- The finite chart laws produce an actual functor, not an action dictionary input to the result.
private noncomputable def chartFunctor
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    [HasPushouts C] (S T : D ⥤ C) (t : S ⟶ T)
    (B : D → C) (g : ∀ d, S.obj d ⟶ B d)
    (L : ∀ a : Arrow D, B a.left ⟶ pushout (g a.right) (t.app a.right))
    (hL : ∀ a, g a.left ≫ L a = S.map a.hom ≫ t.app a.right ≫
      pushout.inr (g a.right) (t.app a.right))
    (hid : ∀ d, L (Arrow.mk (𝟙 d)) = pushout.inl (g d) (t.app d))
    (hcomp : ∀ {d e z : D} (a : d ⟶ e) (b : e ⟶ z),
      L (Arrow.mk (a ≫ b)) = L (Arrow.mk a) ≫
        pushoutAction S T t B g (Arrow.mk b) (L (Arrow.mk b)) (hL (Arrow.mk b))) :
    D ⥤ C := by
  let α (a : Arrow D) : pushout (g a.left) (t.app a.left) ⟶
      pushout (g a.right) (t.app a.right) := pushoutAction S T t B g a (L a) (hL a)
  have hαL (a : Arrow D) : pushout.inl (g a.left) (t.app a.left) ≫ α a = L a :=
    pushoutAction_inl S T t B g a (L a) (hL a)
  have hαR (a : Arrow D) : pushout.inr (g a.left) (t.app a.left) ≫ α a =
      T.map a.hom ≫ pushout.inr (g a.right) (t.app a.right) :=
    pushoutAction_inr S T t B g a (L a) (hL a)
  exact
    { obj := fun d => pushout (g d) (t.app d)
      map := fun a => α (Arrow.mk a)
      map_id := fun d => by
        apply pushout.hom_ext
        · simpa only [Arrow.mk_left, Arrow.mk_right, Category.comp_id] using
            (hαL (Arrow.mk (𝟙 d))).trans (hid d)
        · simpa only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom,
            T.map_id, Category.id_comp, Category.comp_id] using hαR (Arrow.mk (𝟙 d))
      map_comp := fun {d e z} a b => by
        apply pushout.hom_ext
        · calc
            pushout.inl (g d) (t.app d) ≫ α (Arrow.mk (a ≫ b)) =
                L (Arrow.mk (a ≫ b)) := hαL (Arrow.mk (a ≫ b))
            _ = L (Arrow.mk a) ≫ α (Arrow.mk b) := hcomp a b
            _ = (pushout.inl (g d) (t.app d) ≫ α (Arrow.mk a)) ≫ α (Arrow.mk b) :=
              congrArg (fun h => h ≫ α (Arrow.mk b)) (hαL (Arrow.mk a)).symm
            _ = pushout.inl (g d) (t.app d) ≫ (α (Arrow.mk a) ≫ α (Arrow.mk b)) :=
              Category.assoc _ _ _
        · calc
            pushout.inr (g d) (t.app d) ≫ α (Arrow.mk (a ≫ b)) =
                T.map (a ≫ b) ≫ pushout.inr (g z) (t.app z) := hαR (Arrow.mk (a ≫ b))
            _ = T.map a ≫ (T.map b ≫ pushout.inr (g z) (t.app z)) := by
              rw [T.map_comp, Category.assoc]
            _ = T.map a ≫ (pushout.inr (g e) (t.app e) ≫ α (Arrow.mk b)) :=
              congrArg (fun h => T.map a ≫ h) (hαR (Arrow.mk b)).symm
            _ = (T.map a ≫ pushout.inr (g e) (t.app e)) ≫ α (Arrow.mk b) :=
              (Category.assoc _ _ _).symm
            _ = (pushout.inr (g d) (t.app d) ≫ α (Arrow.mk a)) ≫ α (Arrow.mk b) :=
              congrArg (fun h => h ≫ α (Arrow.mk b)) (hαR (Arrow.mk a)).symm
            _ = pushout.inr (g d) (t.app d) ≫ (α (Arrow.mk a) ≫ α (Arrow.mk b)) :=
              Category.assoc _ _ _ }


-- Both finite families of genuine chart equalities are forced at one later stage.
private theorem coherentChartStage
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
    (hD : HasCardinalLT (Arrow D) chi) (F G : D ⥤ C) (f : F ⟶ G)
    (A : CompactApproximation chi F) (i : A.index)
    (B : D → C) (g : ∀ d, (A.presentation.diag.obj i).obj d ⟶ B d)
    (q : ∀ d, B d ⟶ G.obj d) (hB : ∀ d, IsCardinalPresentable (B d) chi)
    (H : ∀ d, IsPushout (g d) ((A.presentation.ι.app i).app d) (q d) (f.app d)) :
    ∃ (k : Under i)
      (L : ∀ a : Arrow D, B a.left ⟶
        pushout (g a.right) ((A.presentation.diag.map k.hom).app a.right))
      (hRoot : ∀ a, g a.left ≫ L a =
        (A.presentation.diag.obj i).map a.hom ≫ (A.presentation.diag.map k.hom).app a.right ≫
          pushout.inr (g a.right) ((A.presentation.diag.map k.hom).app a.right)),
      (∀ a, L a ≫
        (originalTargetPresentation chi hD F G f A i a.right
          (Under.mk (g a.right)) (q a.right) (H a.right)).ι.app k =
          q a.left ≫ G.map a.hom) ∧
      (∀ d, L (Arrow.mk (𝟙 d)) =
        pushout.inl (g d) ((A.presentation.diag.map k.hom).app d)) ∧
      (∀ {d e z : D} (a : d ⟶ e) (b : e ⟶ z),
        L (Arrow.mk (a ≫ b)) = L (Arrow.mk a) ≫
          pushoutAction (A.presentation.diag.obj i) (A.presentation.diag.obj k.right)
            (A.presentation.diag.map k.hom) B g (Arrow.mk b) (L (Arrow.mk b))
            (hRoot (Arrow.mk b))) := by
  let P (d : D) := originalTargetPresentation chi hD F G f A i d
    (Under.mk (g d)) (q d) (H d)
  obtain ⟨j, Lraw, hj⟩ := firstTargetActionsWithRoots chi hD F G f A i B g q hB H
  let S := A.presentation.diag.obj i
  let T := A.presentation.diag.obj j.right
  let tj := A.presentation.diag.map j.hom
  let Lj (a : Arrow D) : B a.left ⟶ pushout (g a.right) (tj.app a.right) := Lraw a
  let Vj (d : D) : pushout (g d) (tj.app d) ⟶ G.obj d := (P d).ι.app j
  have hLj (a : Arrow D) : Lj a ≫ Vj a.right = q a.left ≫ G.map a.hom := (hj a).1
  have hRootj (a : Arrow D) : g a.left ≫ Lj a =
      S.map a.hom ≫ tj.app a.right ≫ pushout.inr (g a.right) (tj.app a.right) := (hj a).2
  have hVjL (d : D) : pushout.inl (g d) (tj.app d) ≫ Vj d = q d :=
    originalTargetPresentation_inl chi hD F G f A i d (Under.mk (g d)) (q d) (H d) j
  have hVjR (d : D) : pushout.inr (g d) (tj.app d) ≫ Vj d =
      (A.presentation.ι.app j.right).app d ≫ f.app d :=
    originalTargetPresentation_inr chi hD F G f A i d (Under.mk (g d)) (q d) (H d) j
  let Rj (a : Arrow D) : pushout (g a.left) (tj.app a.left) ⟶
      pushout (g a.right) (tj.app a.right) :=
    pushoutAction S T tj B g a (Lj a) (hRootj a)
  have hRj (a : Arrow D) : Rj a ≫ Vj a.right = Vj a.left ≫ G.map a.hom :=
    pushoutAction_endpoint S T F G tj (A.presentation.ι.app j.right) f
      B g q Vj hVjL hVjR a (Lj a) (hRootj a) (hLj a)
  let K := D ⊕ ComposableArrows D 2
  let src : K → D := fun c => match c with
    | .inl d => d
    | .inr p => p.obj 0
  let dst : K → D := fun c => match c with
    | .inl d => d
    | .inr p => p.obj 2
  let Z (c : K) := B (src c)
  let leftSide : ∀ c : K, Z c ⟶ (P (dst c)).diag.obj j := fun c => match c with
    | .inl d => Lj (Arrow.mk (𝟙 d))
    | .inr p => Lj (Arrow.mk (p.map' 0 1 ≫ p.map' 1 2))
  let rightSide : ∀ c : K, Z c ⟶ (P (dst c)).diag.obj j := fun c => match c with
    | .inl d => pushout.inl (g d) (tj.app d)
    | .inr p => Lj (Arrow.mk (p.map' 0 1)) ≫ Rj (Arrow.mk (p.map' 1 2))
  have he (c : K) :
      leftSide c ≫ (P (dst c)).ι.app j = rightSide c ≫ (P (dst c)).ι.app j := by
    cases c with
    | inl d =>
      change Lj (Arrow.mk (𝟙 d)) ≫ Vj d = pushout.inl (g d) (tj.app d) ≫ Vj d
      have hu : Lj (Arrow.mk (𝟙 d)) ≫ Vj d = q d := by
        simpa only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, G.map_id, Category.comp_id]
          using hLj (Arrow.mk (𝟙 d))
      exact hu.trans (hVjL d).symm
    | inr p =>
      let a := p.map' 0 1
      let b := p.map' 1 2
      change Lj (Arrow.mk (a ≫ b)) ≫ Vj (p.obj 2) =
        (Lj (Arrow.mk a) ≫ Rj (Arrow.mk b)) ≫ Vj (p.obj 2)
      calc
        Lj (Arrow.mk (a ≫ b)) ≫ Vj (p.obj 2) = q (p.obj 0) ≫ G.map (a ≫ b) :=
          hLj (Arrow.mk (a ≫ b))
        _ = (q (p.obj 0) ≫ G.map a) ≫ G.map b := by rw [G.map_comp, Category.assoc]
        _ = (Lj (Arrow.mk a) ≫ Vj (p.obj 1)) ≫ G.map b :=
          congrArg (fun z => z ≫ G.map b) (hLj (Arrow.mk a)).symm
        _ = Lj (Arrow.mk a) ≫ (Rj (Arrow.mk b) ≫ Vj (p.obj 2)) :=
          (Category.assoc _ _ _).trans
            (congrArg (fun z => Lj (Arrow.mk a) ≫ z) (hRj (Arrow.mk b)).symm)
        _ = (Lj (Arrow.mk a) ≫ Rj (Arrow.mk b)) ≫ Vj (p.obj 2) :=
          (Category.assoc _ _ _).symm
  have hK : HasCardinalLT K chi :=
    (hasCardinalLT_sum_iff D (ComposableArrows D 2) chi (Fact.out : chi.IsRegular).aleph0_le).2
      ⟨hasCardinalLT_of_hasCardinalLT_arrow hD,
        SmallObject.DiagramActionConstraintBounds.nativePairsLt chi hD⟩
  let : Quiver.IsThin (Under i) := fun _ _ =>
    ⟨fun s t => Under.UnderMorphism.ext (Subsingleton.elim s.right t.right)⟩
  obtain ⟨k, η, heq⟩ := commonCoconeEqualities chi (fun d => (P d).diag)
    (fun d => (P d).cocone) (fun d => (P d).isColimit) dst Z hK
    (fun c => hB (src c)) j leftSide rightSide he
  let U := A.presentation.diag.obj k.right
  let tk := A.presentation.diag.map k.hom
  let r := A.presentation.diag.map η.right
  let Tk (d : D) : pushout (g d) (tj.app d) ⟶ pushout (g d) (tk.app d) :=
    (P d).diag.map η
  let Vk (d : D) : pushout (g d) (tk.app d) ⟶ G.obj d := (P d).ι.app k
  have hTkV (d : D) : Tk d ≫ Vk d = Vj d := (P d).w η
  have hTkL (d : D) : pushout.inl (g d) (tj.app d) ≫ Tk d = pushout.inl (g d) (tk.app d) :=
    pushout.inl_desc _ _ _
  have hTkR (d : D) : pushout.inr (g d) (tj.app d) ≫ Tk d =
      r.app d ≫ pushout.inr (g d) (tk.app d) := pushout.inr_desc _ _ _
  have htr (d : D) : tj.app d ≫ r.app d = tk.app d := by
    change (A.presentation.diag.map j.hom).app d ≫
      (A.presentation.diag.map η.right).app d = (A.presentation.diag.map k.hom).app d
    rw [← NatTrans.comp_app, ← Functor.map_comp, Under.w η]
  let Lk (a : Arrow D) : B a.left ⟶ pushout (g a.right) (tk.app a.right) :=
    Lj a ≫ Tk a.right
  have hRootk (a : Arrow D) : g a.left ≫ Lk a =
      S.map a.hom ≫ tk.app a.right ≫ pushout.inr (g a.right) (tk.app a.right) := by
    change g a.left ≫ (Lj a ≫ Tk a.right) = _
    rw [← Category.assoc, hRootj a, Category.assoc, Category.assoc, hTkR a.right,
      ← Category.assoc (tj.app a.right), htr a.right]
  let Rk (a : Arrow D) : pushout (g a.left) (tk.app a.left) ⟶
      pushout (g a.right) (tk.app a.right) :=
    pushoutAction S U tk B g a (Lk a) (hRootk a)
  have hRjk (a : Arrow D) : Tk a.left ≫ Rk a = Rj a ≫ Tk a.right :=
    pushoutAction_transition S T U tj tk r B g Tk hTkL hTkR a
      (Lj a) (Lk a) (hRootj a) (hRootk a) rfl
  refine ⟨k, Lk, hRootk, ?_, ?_, ?_⟩
  · intro a
    change (Lj a ≫ Tk a.right) ≫ Vk a.right = _
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => Lj a ≫ z) (hTkV a.right)).trans (hLj a))
  · intro d
    have hh := heq (Sum.inl d)
    change Lj (Arrow.mk (𝟙 d)) ≫ Tk d = pushout.inl (g d) (tj.app d) ≫ Tk d at hh
    exact hh.trans (hTkL d)
  · intro d e z a b
    have hh := heq (Sum.inr (ComposableArrows.mk₂ a b))
    change Lj (Arrow.mk (a ≫ b)) ≫ Tk z = (Lj (Arrow.mk a) ≫ Rj (Arrow.mk b)) ≫ Tk z at hh
    calc
      Lk (Arrow.mk (a ≫ b)) = (Lj (Arrow.mk a) ≫ Rj (Arrow.mk b)) ≫ Tk z := hh
      _ = Lj (Arrow.mk a) ≫ (Rj (Arrow.mk b) ≫ Tk z) := Category.assoc _ _ _
      _ = Lj (Arrow.mk a) ≫ (Tk e ≫ Rk (Arrow.mk b)) :=
        congrArg (fun t => Lj (Arrow.mk a) ≫ t) (hRjk (Arrow.mk b)).symm
      _ = Lk (Arrow.mk a) ≫ Rk (Arrow.mk b) := (Category.assoc _ _ _).symm

private theorem wholePushoutOfComponents
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    {S T U V : D ⥤ C} (a : S ⟶ T) (b : S ⟶ U) (f : T ⟶ V) (g : U ⟶ V)
    (H : ∀ d, IsPushout (a.app d) (b.app d) (f.app d) (g.app d)) :
    IsPushout a b f g := by
  have w : a ≫ f = b ≫ g := NatTrans.ext (funext (fun d => (H d).w))
  let sq : CommSq a b f g := ⟨w⟩
  apply IsPushout.of_isColimit' sq
  apply evaluationJointlyReflectsColimits
  intro d
  let ev := (evaluation D C).obj d
  refine (IsColimit.equivOfNatIsoOfIso (spanCompIso ev a b) _ _
    (WalkingSpan.ext ?_ ?_ ?_)).symm (H d).isColimit
  exacts [Iso.refl _, (Category.comp_id _).trans (Category.id_comp _),
    (Category.comp_id _).trans (Category.id_comp _)]

private theorem wholeDiagramPresentable
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
    (hD : HasCardinalLT (Arrow D) chi) (F : D ⥤ C)
    (hF : ∀ d, IsCardinalPresentable (F.obj d) chi) :
    IsCardinalPresentable F chi := by
  let : Small.{w} (Arrow D) := hD.small
  let : Small.{w} D := small_of_small_arrow D
  let : LocallySmall.{w} D := locallySmall_of_small_arrow D
  let : Small.{w} (ShrinkHoms D) := inferInstanceAs (Small.{w} D)
  let idx : D ≌ Shrink.{w} (ShrinkHoms D) :=
    (ShrinkHoms.equivalence D).trans (Shrink.equivalence (ShrinkHoms D))
  have hb : HasCardinalLT (Arrow (Shrink.{w} (ShrinkHoms D))) chi :=
    (hasCardinalLT_arrow_shrink_iff (ShrinkHoms D) chi).2
      ((hasCardinalLT_arrow_shrinkHoms_iff D chi).2 hD)
  exact FunctorPresentability.diagram_presentable C chi idx chi hb F hF


-- Whole target, natural maps, compactness and the original pushout, all constructed from the chart.
private theorem compactTargetOverRoot
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
    (hD : HasCardinalLT (Arrow D) chi) (F G : D ⥤ C) (f : F ⟶ G)
    (A : CompactApproximation chi F) (i : A.index)
    (B : D → C) (g : ∀ d, (A.presentation.diag.obj i).obj d ⟶ B d)
    (q : ∀ d, B d ⟶ G.obj d) (hB : ∀ d, IsCardinalPresentable (B d) chi)
    (H : ∀ d, IsPushout (g d) ((A.presentation.ι.app i).app d) (q d) (f.app d)) :
    ∃ (k : Under i) (G0 : D ⥤ C)
      (f0 : A.presentation.diag.obj k.right ⟶ G0) (v : G0 ⟶ G)
      (b0 : ∀ d, B d ⟶ G0.obj d),
      IsCardinalPresentable G0 chi ∧
      (∀ d, IsCardinalPresentable (G0.obj d) chi) ∧
      IsPushout (A.presentation.ι.app k.right) f0 f v ∧
      ∀ d, IsPushout ((A.presentation.diag.map k.hom).app d) (g d) (f0.app d) (b0 d) ∧
        b0 d ≫ v.app d = q d := by
  obtain ⟨k, L, hRoot, hEnd, hid, hcomp⟩ := coherentChartStage chi hD F G f A i B g q hB H
  let S := A.presentation.diag.obj i
  let T := A.presentation.diag.obj k.right
  let t := A.presentation.diag.map k.hom
  let u : T ⟶ F := A.presentation.ι.app k.right
  let P (d : D) := originalTargetPresentation chi hD F G f A i d
    (Under.mk (g d)) (q d) (H d)
  let V (d : D) : pushout (g d) (t.app d) ⟶ G.obj d := (P d).ι.app k
  have hVL (d : D) : pushout.inl (g d) (t.app d) ≫ V d = q d :=
    originalTargetPresentation_inl chi hD F G f A i d (Under.mk (g d)) (q d) (H d) k
  have hVR (d : D) : pushout.inr (g d) (t.app d) ≫ V d = u.app d ≫ f.app d :=
    originalTargetPresentation_inr chi hD F G f A i d (Under.mk (g d)) (q d) (H d) k
  let G0 := chartFunctor S T t B g L hRoot hid hcomp
  let f0 : T ⟶ G0 :=
    { app := fun d => pushout.inr (g d) (t.app d)
      naturality := fun d e a =>
        (pushoutAction_inr S T t B g (Arrow.mk a) (L (Arrow.mk a))
          (hRoot (Arrow.mk a))).symm }
  let v : G0 ⟶ G :=
    { app := V
      naturality := fun d e a => pushoutAction_endpoint S T F G t u f
        B g q V hVL hVR (Arrow.mk a) (L (Arrow.mk a)) (hRoot (Arrow.mk a))
          (hEnd (Arrow.mk a)) }
  let b0 (d : D) : B d ⟶ G0.obj d := pushout.inl (g d) (t.app d)
  have hValue (d : D) : IsCardinalPresentable (G0.obj d) chi := by
    let : IsCardinalPresentable (S.obj d) chi := (evaluatedApproximation chi hD F A d).presentable i
    let : IsCardinalPresentable (B d) chi := hB d
    let : IsCardinalPresentable (T.obj d) chi :=
      (evaluatedApproximation chi hD F A d).presentable k.right
    exact SmallObject.RelativeCellPresentability.ofPushout chi
      (IsPushout.of_hasPushout (g d) (t.app d))
  have hWhole : IsCardinalPresentable G0 chi := wholeDiagramPresentable chi hD G0 hValue
  have hOriginal (d : D) :
      IsPushout (u.app d) (f0.app d) (f.app d) (v.app d) := by
    have hw : t.app d ≫ u.app d = (A.presentation.ι.app i).app d :=
      NatTrans.congr_app (A.presentation.w k.hom) d
    have hout : IsPushout (g d) (t.app d ≫ u.app d) (b0 d ≫ v.app d) (f.app d) := by
      have hl : b0 d ≫ v.app d = q d := hVL d
      rw [hw, hl]
      exact H d
    exact (hout.of_top (hVR d) (IsPushout.of_hasPushout (g d) (t.app d))).flip
  refine ⟨k, G0, f0, v, b0, hWhole, hValue,
    wholePushoutOfComponents u f0 f v hOriginal, ?_⟩
  intro d
  exact ⟨(IsPushout.of_hasPushout (g d) (t.app d)).flip, hVL d⟩


/-- The original compact component cell charts are recovered by one compact
whole-diagram pushout. -/
theorem existsCompactDiagramCellTarget
    {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
    (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
    (hD : HasCardinalLT (Arrow D) chi) (F G : D ⥤ C) (f : F ⟶ G)
    (X Y : D → C) (g : ∀ d, X d ⟶ Y d)
    (a : ∀ d, X d ⟶ F.obj d) (b : ∀ d, Y d ⟶ G.obj d)
    (hX : ∀ d, IsCardinalPresentable (X d) chi)
    (hY : ∀ d, IsCardinalPresentable (Y d) chi)
    (H : ∀ d, IsPushout (a d) (g d) (f.app d) (b d)) :
    ∃ (F0 G0 : D ⥤ C) (u : F0 ⟶ F) (v : G0 ⟶ G) (f0 : F0 ⟶ G0)
      (a0 : ∀ d, X d ⟶ F0.obj d) (b0 : ∀ d, Y d ⟶ G0.obj d),
      IsCardinalPresentable F0 chi ∧ IsCardinalPresentable G0 chi ∧
      (∀ d, IsCardinalPresentable (F0.obj d) chi ∧ IsCardinalPresentable (G0.obj d) chi) ∧
      IsPushout u f0 f v ∧
      ∀ d, IsPushout (a0 d) (g d) (f0.app d) (b0 d) ∧
        a0 d ≫ u.app d = a d ∧ b0 d ≫ v.app d = b d := by
  obtain ⟨Froot, uRoot, aRoot, hFroot, _, hAttach⟩ :=
    existsCompactDiagramRoot chi hD F X hX a
  let : Small.{w} (Arrow D) := hD.small
  let : Small.{w} D := small_of_small_arrow D
  let : LocallySmall.{w} D := locallySmall_of_small_arrow D
  let : IsCardinalLocallyPresentable (D ⥤ C) chi :=
    HomPowerAccessibility.diagramLocallyPresentable C chi (equivSmallModel.{w} D)
  let A := compactApproximation chi F
  let : IsCardinalPresentable Froot chi := hFroot
  obtain ⟨i, e, he⟩ :=
    IsCardinalPresentable.exists_hom_of_isColimit chi A.presentation.isColimit uRoot
  let ui : A.presentation.diag.obj i ⟶ F := A.presentation.ι.app i
  let x0 (d : D) : X d ⟶ (A.presentation.diag.obj i).obj d := aRoot d ≫ e.app d
  have hx0 (d : D) : x0 d ≫ ui.app d = a d := by
    change (aRoot d ≫ e.app d) ≫ ui.app d = _
    rw [Category.assoc]
    have hc : e.app d ≫ ui.app d = uRoot.app d := NatTrans.congr_app he d
    rw [hc]
    exact hAttach d
  let B (d : D) := pushout (g d) (x0 d)
  let gStage (d : D) : (A.presentation.diag.obj i).obj d ⟶ B d := pushout.inr (g d) (x0 d)
  let q (d : D) : B d ⟶ G.obj d :=
    pushout.desc (b d) (ui.app d ≫ f.app d)
      ((H d).w.symm.trans
        ((congrArg (fun z => z ≫ f.app d) (hx0 d)).symm.trans (Category.assoc _ _ _)))
  have hqL (d : D) : pushout.inl (g d) (x0 d) ≫ q d = b d := pushout.inl_desc _ _ _
  have hqR (d : D) : gStage d ≫ q d = ui.app d ≫ f.app d := pushout.inr_desc _ _ _
  have hB (d : D) : IsCardinalPresentable (B d) chi := by
    let : IsCardinalPresentable (X d) chi := hX d
    let : IsCardinalPresentable (Y d) chi := hY d
    let : IsCardinalPresentable ((A.presentation.diag.obj i).obj d) chi :=
      (evaluatedApproximation chi hD F A d).presentable i
    exact SmallObject.RelativeCellPresentability.ofPushout chi
      (IsPushout.of_hasPushout (g d) (x0 d))
  have hStage (d : D) : IsPushout (gStage d) (ui.app d) (q d) (f.app d) := by
    have hout : IsPushout (g d) (x0 d ≫ ui.app d)
        (pushout.inl (g d) (x0 d) ≫ q d) (f.app d) := by
      rw [hx0 d, hqL d]
      exact (H d).flip
    exact hout.of_top (hqR d) (IsPushout.of_hasPushout (g d) (x0 d))
  obtain ⟨k, G0, f0, v, bStage, hG0, hG0Values, hWhole, hCharts⟩ :=
    compactTargetOverRoot chi hD F G f A i B gStage q hB hStage
  let F0 := A.presentation.diag.obj k.right
  let u : F0 ⟶ F := A.presentation.ι.app k.right
  let a0 (d : D) : X d ⟶ F0.obj d := x0 d ≫ (A.presentation.diag.map k.hom).app d
  let b0 (d : D) : Y d ⟶ G0.obj d := pushout.inl (g d) (x0 d) ≫ bStage d
  refine ⟨F0, G0, u, v, f0, a0, b0, A.presentable k.right, hG0, ?_, hWhole, ?_⟩
  · intro d
    exact ⟨(evaluatedApproximation chi hD F A d).presentable k.right, hG0Values d⟩
  · intro d
    refine ⟨((IsPushout.of_hasPushout (g d) (x0 d)).paste_vert (hCharts d).1.flip).flip, ?_, ?_⟩
    · change (x0 d ≫ (A.presentation.diag.map k.hom).app d) ≫ u.app d = _
      have hc : (A.presentation.diag.map k.hom).app d ≫ u.app d = ui.app d :=
        NatTrans.congr_app (A.presentation.w k.hom) d
      rw [Category.assoc, hc]
      exact hx0 d
    · change (pushout.inl (g d) (x0 d) ≫ bStage d) ≫ v.app d = _
      rw [Category.assoc, (hCharts d).2]
      exact hqL d

end CategoryTheory.Presentable
