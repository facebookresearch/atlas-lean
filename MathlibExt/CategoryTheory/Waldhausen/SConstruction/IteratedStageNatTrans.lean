/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageReindex
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenNatTrans
import MathlibExt.CategoryTheory.Functor.WholeArrowRetyping

/-!
# Original natural transformations through all iterated Stage directions

Every original transformation between exact functors lifts through the
actual Nil and Cons charts. The finite-stage transformation and both
whole endpoint transports retain the original ordered Stage degrees.
Identity, composition and every tuple operator act on these complete
transformations. The four source and target universe roles are independent.

These are the original arrows needed to iterate admissible cofiber
functor sequences before applying additivity in additional directions.
-/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe uC vC uD vD
universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ uE vE

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type (max uC vC)} [Category.{vC} C] [HasZeroObject C]
    [WaldhausenCategoryWithoutGluing C]
variable {D : Type (max uD vD)} [Category.{vD} D] [HasZeroObject D]
    [WaldhausenCategoryWithoutGluing D]
variable {F G K : C ⥤ D}

/-- The finite-stage isomorphism and transformation lifts have the same whole forward map. -/
theorem stageNatIso_hom_eq_natTrans
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G) (n : ℕ) :
    (hF.mapStageNatIso hG e n).hom = hF.mapStageNatTrans hG e.hom n := by
  apply ((fullyFaithfulForget D n).whiskeringRight (Stage C n)).map_injective
  exact (hF.mapStageNatIso_hom_forget hG e n).trans
    (hF.mapStageNatTrans_forget hG e.hom n).symm

/-- The finite-stage inverse is the transformation lift of the original inverse. -/
theorem stageNatIso_inv_eq_natTrans
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (e : F ≅ G) (n : ℕ) :
    (hF.mapStageNatIso hG e n).inv = hG.mapStageNatTrans hF e.inv n := by
  apply ((fullyFaithfulForget D n).whiskeringRight (Stage C n)).map_injective
  exact (hF.mapStageNatIso_inv_forget hG e n).trans
    (hG.mapStageNatTrans_forget hF e.inv n).symm

private def nilNatTransChart (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (η : F ⟶ G) :
    mapIteratedStage hF [] ⋙ (iteratedStageNilEquivalence D).functor ⟶
      mapIteratedStage hG [] ⋙ (iteratedStageNilEquivalence D).functor :=
  eqToHom (mapIteratedStage_nil_chart hF) ≫
    Functor.whiskerLeft (iteratedStageNilEquivalence C).functor η ≫
      eqToHom (mapIteratedStage_nil_chart hG).symm

private def consNatTransChart (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (n : ℕ) (ns : List ℕ) (η : mapIteratedStage hF ns ⟶ mapIteratedStage hG ns) :
    mapIteratedStage hF (n :: ns) ⋙ (iteratedStageConsEquivalence D n ns).functor ⟶
      mapIteratedStage hG (n :: ns) ⋙ (iteratedStageConsEquivalence D n ns).functor :=
  eqToHom (mapIteratedStage_cons_chart hF n ns) ≫
    Functor.whiskerLeft (iteratedStageConsEquivalence C n ns).functor
      ((mapIteratedStage_isWaldhausenExact hF ns).mapStageNatTrans
        (mapIteratedStage_isWaldhausenExact hG ns) η n) ≫
      eqToHom (mapIteratedStage_cons_chart hG n ns).symm

/-- The original transformation lifts through every actual iterated Stage chart. -/
def mapIteratedStageNatTrans (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (η : F ⟶ G) : (ns : List ℕ) → mapIteratedStage hF ns ⟶ mapIteratedStage hG ns
  | .nil =>
      ((iteratedStageNilEquivalence D).fullyFaithfulFunctor.whiskeringRight
        (IteratedStage C [])).preimage (nilNatTransChart hF hG η)
  | .cons n ns =>
      ((iteratedStageConsEquivalence D n ns).fullyFaithfulFunctor.whiskeringRight
        (IteratedStage C (n :: ns))).preimage
          (consNatTransChart hF hG n ns (mapIteratedStageNatTrans hF hG η ns))

/-- The complete zero-fold transformation retains both Nil transports and the original arrow. -/
theorem mapIteratedStageNatTrans_nil_chart
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G) :
    Functor.whiskerRight (mapIteratedStageNatTrans hF hG η [])
        (iteratedStageNilEquivalence D).functor =
      eqToHom (mapIteratedStage_nil_chart hF) ≫
        Functor.whiskerLeft (iteratedStageNilEquivalence C).functor η ≫
        eqToHom (mapIteratedStage_nil_chart hG).symm :=
  ((iteratedStageNilEquivalence D).fullyFaithfulFunctor.whiskeringRight
    (IteratedStage C [])).map_preimage (nilNatTransChart hF hG η)

/-- The whole successor transformation is the original finite-stage arrow through both charts. -/
theorem mapIteratedStageNatTrans_cons_chart
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G)
    (n : ℕ) (ns : List ℕ) :
    Functor.whiskerRight (mapIteratedStageNatTrans hF hG η (n :: ns))
        (iteratedStageConsEquivalence D n ns).functor =
      eqToHom (mapIteratedStage_cons_chart hF n ns) ≫
        Functor.whiskerLeft (iteratedStageConsEquivalence C n ns).functor
          ((mapIteratedStage_isWaldhausenExact hF ns).mapStageNatTrans
            (mapIteratedStage_isWaldhausenExact hG ns)
            (mapIteratedStageNatTrans hF hG η ns) n) ≫
        eqToHom (mapIteratedStage_cons_chart hG n ns).symm :=
  ((iteratedStageConsEquivalence D n ns).fullyFaithfulFunctor.whiskeringRight
    (IteratedStage C (n :: ns))).map_preimage
      (consNatTransChart hF hG n ns (mapIteratedStageNatTrans hF hG η ns))

/-- Identity transformations retain the complete original identity at every degree list. -/
theorem mapIteratedStageNatTrans_id (hF : F.IsWaldhausenExact) (ns : List ℕ) :
    mapIteratedStageNatTrans hF hF (𝟙 F) ns = 𝟙 (mapIteratedStage hF ns) := by
  induction ns with
  | nil =>
      apply ((iteratedStageNilEquivalence D).fullyFaithfulFunctor.whiskeringRight
        (IteratedStage C [])).map_injective
      change Functor.whiskerRight (mapIteratedStageNatTrans hF hF (𝟙 F) [])
          (iteratedStageNilEquivalence D).functor =
        Functor.whiskerRight (𝟙 (mapIteratedStage hF []))
          (iteratedStageNilEquivalence D).functor
      rw [mapIteratedStageNatTrans_nil_chart]
      simp
  | cons n ns ih =>
      apply ((iteratedStageConsEquivalence D n ns).fullyFaithfulFunctor.whiskeringRight
        (IteratedStage C (n :: ns))).map_injective
      change Functor.whiskerRight (mapIteratedStageNatTrans hF hF (𝟙 F) (n :: ns))
          (iteratedStageConsEquivalence D n ns).functor =
        Functor.whiskerRight (𝟙 (mapIteratedStage hF (n :: ns)))
          (iteratedStageConsEquivalence D n ns).functor
      rw [mapIteratedStageNatTrans_cons_chart, ih,
        Functor.IsWaldhausenExact.mapStageNatTrans_id]
      simp

/-- Composition uses the original whole transformations at every ordered degree list. -/
theorem mapIteratedStageNatTrans_comp (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (hK : K.IsWaldhausenExact) (η : F ⟶ G) (κ : G ⟶ K) (ns : List ℕ) :
    mapIteratedStageNatTrans hF hK (η ≫ κ) ns =
      mapIteratedStageNatTrans hF hG η ns ≫ mapIteratedStageNatTrans hG hK κ ns := by
  induction ns with
  | nil =>
      apply ((iteratedStageNilEquivalence D).fullyFaithfulFunctor.whiskeringRight
        (IteratedStage C [])).map_injective
      change Functor.whiskerRight (mapIteratedStageNatTrans hF hK (η ≫ κ) [])
          (iteratedStageNilEquivalence D).functor =
        Functor.whiskerRight (mapIteratedStageNatTrans hF hG η [] ≫
          mapIteratedStageNatTrans hG hK κ []) (iteratedStageNilEquivalence D).functor
      rw [Functor.whiskerRight_comp, mapIteratedStageNatTrans_nil_chart,
        mapIteratedStageNatTrans_nil_chart, mapIteratedStageNatTrans_nil_chart]
      simp
  | cons n ns ih =>
      apply ((iteratedStageConsEquivalence D n ns).fullyFaithfulFunctor.whiskeringRight
        (IteratedStage C (n :: ns))).map_injective
      change Functor.whiskerRight (mapIteratedStageNatTrans hF hK (η ≫ κ) (n :: ns))
          (iteratedStageConsEquivalence D n ns).functor =
        Functor.whiskerRight (mapIteratedStageNatTrans hF hG η (n :: ns) ≫
          mapIteratedStageNatTrans hG hK κ (n :: ns))
          (iteratedStageConsEquivalence D n ns).functor
      rw [Functor.whiskerRight_comp, mapIteratedStageNatTrans_cons_chart,
        mapIteratedStageNatTrans_cons_chart, mapIteratedStageNatTrans_cons_chart, ih,
        Functor.IsWaldhausenExact.mapStageNatTrans_comp
          (mapIteratedStage_isWaldhausenExact hF ns)
          (mapIteratedStage_isWaldhausenExact hG ns)
          (mapIteratedStage_isWaldhausenExact hK ns)
          (mapIteratedStageNatTrans hF hG η ns)
          (mapIteratedStageNatTrans hG hK κ ns) n]
      simp

private theorem iteratedNatTransAppHEq
    {A : Type (max uC vC)} [Category.{vC} A]
    {B : Type (max uD vD)} [Category.{vD} B]
    {P Q P' Q' : A ⥤ B} (hP : P = P') (hQ : Q = Q')
    (η : P ⟶ Q) (θ : P' ⟶ Q') (h : HEq η θ) (X : A) :
    HEq (η.app X) (θ.app X) := by
  cases hP
  cases hQ
  cases h
  rfl

/-- Every zero-fold component is the original component under the actual Nil charts. -/
theorem mapIteratedStageNatTrans_nil_app_heq
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G)
    (X : IteratedStage C []) :
    HEq ((iteratedStageNilEquivalence D).functor.map
      ((mapIteratedStageNatTrans hF hG η []).app X))
      (η.app ((iteratedStageNilEquivalence C).functor.obj X)) := by
  have h := (conj_eqToHom_iff_heq _ _
    (mapIteratedStage_nil_chart hF) (mapIteratedStage_nil_chart hG)).mp
      (mapIteratedStageNatTrans_nil_chart hF hG η)
  exact iteratedNatTransAppHEq (mapIteratedStage_nil_chart hF)
    (mapIteratedStage_nil_chart hG) _ _ h X

/-- The complete successor flag arrow is the previous original transformation
whiskered by the whole flag. -/
theorem mapIteratedStageNatTrans_cons_app_hom_heq
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G)
    (n : ℕ) (ns : List ℕ) (X : IteratedStage C (n :: ns)) :
    HEq (((iteratedStageConsEquivalence D n ns).functor.map
      ((mapIteratedStageNatTrans hF hG η (n :: ns)).app X)).hom)
      (Functor.whiskerLeft ((iteratedStageConsEquivalence C n ns).functor.obj X).obj
        (mapIteratedStageNatTrans hF hG η ns)) := by
  have h := (conj_eqToHom_iff_heq _ _
    (mapIteratedStage_cons_chart hF n ns) (mapIteratedStage_cons_chart hG n ns)).mp
      (mapIteratedStageNatTrans_cons_chart hF hG η n ns)
  have hX := iteratedNatTransAppHEq (mapIteratedStage_cons_chart hF n ns)
    (mapIteratedStage_cons_chart hG n ns) _ _ h X
  have hm := Functor.map_retyped_heq (forget (IteratedStage D ns) n)
    (Functor.congr_obj (mapIteratedStage_cons_chart hF n ns) X)
    (Functor.congr_obj (mapIteratedStage_cons_chart hG n ns) X) _ _ hX
  change HEq (((iteratedStageConsEquivalence D n ns).functor.map
      ((mapIteratedStageNatTrans hF hG η (n :: ns)).app X)).hom)
    ((((mapIteratedStage_isWaldhausenExact hF ns).mapStageNatTrans
      (mapIteratedStage_isWaldhausenExact hG ns)
      (mapIteratedStageNatTrans hF hG η ns) n).app
        ((iteratedStageConsEquivalence C n ns).functor.obj X)).hom) at hm
  rw [Functor.IsWaldhausenExact.mapStageNatTrans_app_hom] at hm
  exact hm

private theorem stageMap_eq_of_exact_eq
    {A : Type (max uC vC)} [Category.{vC} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
    {B : Type (max uD vD)} [Category.{vD} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
    {P Q : A ⥤ B} (hP : P.IsWaldhausenExact) (hQ : Q.IsWaldhausenExact)
    (h : P = Q) (n : ℕ) : hP.mapStage n = hQ.mapStage n := by
  subst Q
  rfl

private theorem natTransHExt
    {A : Type (max uC vC)} [Category.{vC} A]
    {B : Type (max uD vD)} [Category.{vD} B]
    {P Q P' Q' : A ⥤ B} (hP : P = P') (hQ : Q = Q')
    (η : P ⟶ Q) (θ : P' ⟶ Q') (h : ∀ X, HEq (η.app X) (θ.app X)) : HEq η θ := by
  cases hP
  cases hQ
  apply heq_of_eq
  apply NatTrans.ext
  funext X
  exact eq_of_heq (h X)

set_option backward.isDefEq.respectTransparency false in
private theorem stageNatTrans_baseChange
    {A : Type (max u₀ v₀)} [Category.{v₀} A]
    {A' : Type (max u₁ v₁)} [Category.{v₁} A']
    [HasZeroObject A] [HasZeroObject A'] [WaldhausenCategoryWithoutGluing A]
        [WaldhausenCategoryWithoutGluing A']
    {B : Type (max u₂ v₂)} [Category.{v₂} B]
    {B' : Type (max u₃ v₃)} [Category.{v₃} B']
    [HasZeroObject B] [HasZeroObject B'] [WaldhausenCategoryWithoutGluing B]
        [WaldhausenCategoryWithoutGluing B']
    {R : A ⥤ A'} {S : B ⥤ B'} {F₀ G₀ : A ⥤ B} {F₁ G₁ : A' ⥤ B'}
    (hR : R.IsWaldhausenExact) (hS : S.IsWaldhausenExact)
    (hF₀ : F₀.IsWaldhausenExact) (hG₀ : G₀.IsWaldhausenExact)
    (hF₁ : F₁.IsWaldhausenExact) (hG₁ : G₁.IsWaldhausenExact)
    (η₀ : F₀ ⟶ G₀) (η₁ : F₁ ⟶ G₁)
    (hF : R ⋙ F₁ = F₀ ⋙ S) (hG : R ⋙ G₁ = G₀ ⋙ S)
    (hη : HEq (Functor.whiskerLeft R η₁) (Functor.whiskerRight η₀ S)) (n : ℕ) :
    HEq (Functor.whiskerLeft (hR.mapStage n) (hF₁.mapStageNatTrans hG₁ η₁ n))
      (Functor.whiskerRight (hF₀.mapStageNatTrans hG₀ η₀ n) (hS.mapStage n)) := by
  have hP : hR.mapStage n ⋙ hF₁.mapStage n = hF₀.mapStage n ⋙ hS.mapStage n :=
    (hR.mapStage_comp hF₁ n).symm.trans
      ((stageMap_eq_of_exact_eq (hR.comp hF₁) (hF₀.comp hS) hF n).trans
        (hF₀.mapStage_comp hS n))
  have hQ : hR.mapStage n ⋙ hG₁.mapStage n = hG₀.mapStage n ⋙ hS.mapStage n :=
    (hR.mapStage_comp hG₁ n).symm.trans
      ((stageMap_eq_of_exact_eq (hR.comp hG₁) (hG₀.comp hS) hG n).trans
        (hG₀.mapStage_comp hS n))
  apply natTransHExt hP hQ
  intro X
  apply Functor.reflect_retyped_heq (forget B' n)
    (Functor.congr_obj hP X) (Functor.congr_obj hQ X)
  change HEq (((hF₁.mapStageNatTrans hG₁ η₁ n).app ((hR.mapStage n).obj X)).hom)
    (((hS.mapStage n).map ((hF₀.mapStageNatTrans hG₀ η₀ n).app X)).hom)
  rw [hS.mapStage_map, hF₁.mapStageNatTrans_app_hom, hF₀.mapStageNatTrans_app_hom]
  change HEq (Functor.whiskerLeft (X.obj ⋙ R) η₁)
    (Functor.whiskerRight (Functor.whiskerLeft X.obj η₀) S)
  exact Functor.map_retyped_heq
    ((Functor.whiskeringLeft (Ar n) A B').obj X.obj) hF hG _ _ hη

set_option backward.isDefEq.respectTransparency false in
private theorem transportedNatTransSquare
    {A A' : Type (max u₀ v₀)} [Category.{v₀} A] [Category.{v₀} A']
    {B B' : Type (max u₁ v₁)} [Category.{v₁} B] [Category.{v₁} B']
    {D D' : Type (max u₂ v₂)} [Category.{v₂} D] [Category.{v₂} D']
    {E E' : Type (max u₃ v₃)} [Category.{v₃} E] [Category.{v₃} E']
    (ea : A ≌ A') (eb : B ≌ B') (ed : D ≌ D') (ee : E ≌ E')
    (R : A' ⥤ B') (S : D' ⥤ E') (RO : A ⥤ B) (SO : D ⥤ E)
    (hRO : RO = ea.functor ⋙ R ⋙ eb.inverse)
    (hSO : SO = ed.functor ⋙ S ⋙ ee.inverse)
    {F₀ G₀ : A ⥤ D} {F₁ G₁ : B ⥤ E}
    {F₀' G₀' : A' ⥤ D'} {F₁' G₁' : B' ⥤ E'}
    (η₀ : F₀ ⟶ G₀) (η₁ : F₁ ⟶ G₁) (η₀' : F₀' ⟶ G₀') (η₁' : F₁' ⟶ G₁')
    (hF₀ : F₀ ⋙ ed.functor = ea.functor ⋙ F₀')
    (hG₀ : G₀ ⋙ ed.functor = ea.functor ⋙ G₀')
    (hF₁ : F₁ ⋙ ee.functor = eb.functor ⋙ F₁')
    (hG₁ : G₁ ⋙ ee.functor = eb.functor ⋙ G₁')
    (hη₀ : HEq (Functor.whiskerRight η₀ ed.functor) (Functor.whiskerLeft ea.functor η₀'))
    (hη₁ : HEq (Functor.whiskerRight η₁ ee.functor) (Functor.whiskerLeft eb.functor η₁'))
    (hF' : R ⋙ F₁' = F₀' ⋙ S) (hG' : R ⋙ G₁' = G₀' ⋙ S)
    (hη' : HEq (Functor.whiskerLeft R η₁') (Functor.whiskerRight η₀' S))
    (hF : RO ⋙ F₁ = F₀ ⋙ SO) (hG : RO ⋙ G₁ = G₀ ⋙ SO)
    (hB : eb.inverse ⋙ eb.functor = 𝟭 B') (hE : ee.inverse ⋙ ee.functor = 𝟭 E') :
    HEq (Functor.whiskerLeft RO η₁) (Functor.whiskerRight η₀ SO) := by
  have hR : RO ⋙ eb.functor = ea.functor ⋙ R :=
    (congrArg (fun K : A ⥤ B => K ⋙ eb.functor) hRO).trans (by
      change ea.functor ⋙ R ⋙ (eb.inverse ⋙ eb.functor) = _
      rw [hB]
      rfl)
  have hS : SO ⋙ ee.functor = ed.functor ⋙ S :=
    (congrArg (fun K : D ⥤ E => K ⋙ ee.functor) hSO).trans (by
      change ed.functor ⋙ S ⋙ (ee.inverse ⋙ ee.functor) = _
      rw [hE]
      rfl)
  have h₁ := Functor.map_retyped_heq
    ((Functor.whiskeringLeft A B E').obj RO) hF₁ hG₁ _ _ hη₁
  have h₂ := Functor.hcongr_hom
    (congrArg (Functor.whiskeringLeft A B' E').obj hR) η₁'
  have h₃ := Functor.map_retyped_heq
    ((Functor.whiskeringLeft A A' E').obj ea.functor) hF' hG' _ _ hη'
  have h₄ := Functor.map_retyped_heq
    ((Functor.whiskeringRight A D' E').obj S) hF₀ hG₀ _ _ hη₀
  have h₅ := Functor.hcongr_hom
    (congrArg (Functor.whiskeringRight A D E').obj hS) η₀
  apply Functor.reflect_retyped_heq
    ((Functor.whiskeringRight A E E').obj ee.functor) hF hG
  exact h₁.trans (h₂.trans (h₃.trans (h₄.symm.trans h₅.symm)))

set_option backward.isDefEq.respectTransparency false in
/-- Equal original degree lists retain the whole natural transformation
through both actual original list-transport charts. -/
theorem mapIteratedStageNatTrans_list_chart
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G)
    {ns ms : List ℕ} (h : ns = ms) :
    Functor.whiskerRight (mapIteratedStageNatTrans hF hG η ns)
        (iteratedStageListEquivalence D h).functor =
      eqToHom (mapIteratedStage_list_transport hF h) ≫
        Functor.whiskerLeft (iteratedStageListEquivalence C h).functor
          (mapIteratedStageNatTrans hF hG η ms) ≫
        eqToHom (mapIteratedStage_list_transport hG h).symm := by
  subst ms
  dsimp only [iteratedStageListEquivalence, Equivalence.refl]
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  apply NatTrans.ext
  funext X
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original tuple successor retains both list transports and the full finite-stage arrow. -/
theorem mapIteratedStageNatTrans_tuple_chart
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G)
    {r : ℕ} (d : Fin (r + 1) → ℕ) :
    let ns := List.ofFn (fun i => d i.succ)
    Functor.whiskerRight (mapIteratedStageNatTrans hF hG η (List.ofFn d))
        (iteratedStageOfFnSuccEquivalence D d).functor =
      eqToHom (mapIteratedStage_tuple_successor hF d) ≫
        Functor.whiskerLeft (iteratedStageOfFnSuccEquivalence C d).functor
          ((mapIteratedStage_isWaldhausenExact hF ns).mapStageNatTrans
            (mapIteratedStage_isWaldhausenExact hG ns)
            (mapIteratedStageNatTrans hF hG η ns) (d 0)) ≫
        eqToHom (mapIteratedStage_tuple_successor hG d).symm := by
  dsimp only
  apply (conj_eqToHom_iff_heq _ _
    (mapIteratedStage_tuple_successor hF d)
    (mapIteratedStage_tuple_successor hG d)).2
  let ns := List.ofFn (fun i => d i.succ)
  let h := List.ofFn_succ (f := d)
  let EC := (iteratedStageListEquivalence C h).functor
  let ED := (iteratedStageListEquivalence D h).functor
  let CC := (iteratedStageConsEquivalence C (d 0) ns).functor
  let CD := (iteratedStageConsEquivalence D (d 0) ns).functor
  have hl := (conj_eqToHom_iff_heq _ _
    (mapIteratedStage_list_transport hF h)
    (mapIteratedStage_list_transport hG h)).1
      (mapIteratedStageNatTrans_list_chart hF hG η h)
  have hl' := Functor.map_retyped_heq
    ((Functor.whiskeringRight (IteratedStage C (List.ofFn d))
      (IteratedStage D (d 0 :: ns)) (Stage (IteratedStage D ns) (d 0))).obj CD)
    (mapIteratedStage_list_transport hF h)
    (mapIteratedStage_list_transport hG h) _ _ hl
  have hc := (conj_eqToHom_iff_heq _ _
    (mapIteratedStage_cons_chart hF (d 0) ns)
    (mapIteratedStage_cons_chart hG (d 0) ns)).1
      (mapIteratedStageNatTrans_cons_chart hF hG η (d 0) ns)
  have hc' := Functor.map_retyped_heq
    ((Functor.whiskeringLeft (IteratedStage C (List.ofFn d))
      (IteratedStage C (d 0 :: ns)) (Stage (IteratedStage D ns) (d 0))).obj EC)
    (mapIteratedStage_cons_chart hF (d 0) ns)
    (mapIteratedStage_cons_chart hG (d 0) ns) _ _ hc
  change HEq
    (Functor.whiskerRight
      (Functor.whiskerRight (mapIteratedStageNatTrans hF hG η (List.ofFn d)) ED) CD)
    (Functor.whiskerLeft EC (Functor.whiskerLeft CC
      ((mapIteratedStage_isWaldhausenExact hF ns).mapStageNatTrans
        (mapIteratedStage_isWaldhausenExact hG ns)
        (mapIteratedStageNatTrans hF hG η ns) (d 0))))
  exact hl'.trans hc'

set_option backward.isDefEq.respectTransparency false in
private theorem iteratedNatTrans_reindex_heq
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G)
    (r : ℕ) {a b : StageSimplexTuple r} (α : a ⟶ b) :
    HEq (Functor.whiskerLeft (reindexIteratedStage C α)
        (mapIteratedStageNatTrans hF hG η (stageTupleDegrees b)))
      (Functor.whiskerRight (mapIteratedStageNatTrans hF hG η (stageTupleDegrees a))
        (reindexIteratedStage D α)) := by
  induction r with
  | zero =>
      have hab : a = b := Subsingleton.elim _ _
      subst b
      let τ := mapIteratedStageNatTrans hF hG η (stageTupleDegrees a)
      have h₁ := Functor.hcongr_hom
        (congrArg (Functor.whiskeringLeft (StageAtTuple C a) (StageAtTuple C a)
          (StageAtTuple D a)).obj (reindexIteratedStage_zero C a α)) τ
      have h₂ := Functor.hcongr_hom
        (congrArg (Functor.whiskeringRight (StageAtTuple C a) (StageAtTuple D a)
          (StageAtTuple D a)).obj (reindexIteratedStage_zero D a α)) τ
      have hm : Functor.whiskerLeft (𝟭 (StageAtTuple C a)) τ =
          Functor.whiskerRight τ (𝟭 (StageAtTuple D a)) := by rfl
      exact h₁.trans ((heq_of_eq hm).trans h₂.symm)
  | succ r ih =>
      let ta : StageSimplexTuple r := fun i => a i.succ
      let tb : StageSimplexTuple r := fun i => b i.succ
      let αt : ta ⟶ tb := fun i => α i.succ
      let CA := StageAtTuple C ta
      let DA := StageAtTuple D ta
      let DB := StageAtTuple D tb
      let hR := reindexIteratedStage_isWaldhausenExact C αt
      let hS := reindexIteratedStage_isWaldhausenExact D αt
      let hFa := mapIteratedStage_isWaldhausenExact hF (stageTupleDegrees ta)
      let hGa := mapIteratedStage_isWaldhausenExact hG (stageTupleDegrees ta)
      let hFb := mapIteratedStage_isWaldhausenExact hF (stageTupleDegrees tb)
      let hGb := mapIteratedStage_isWaldhausenExact hG (stageTupleDegrees tb)
      let ea := mapIteratedStageNatTrans hF hG η (stageTupleDegrees ta)
      let eb := mapIteratedStageNatTrans hF hG η (stageTupleDegrees tb)
      let na := (a 0).unop.len
      let nb := (b 0).unop.len
      let HC := reindexStage (C := CA) (α 0).unop
      let HD := reindexStage (C := DA) (α 0).unop
      let RC := hR.mapStage nb
      let SD := hS.mapStage nb
      have hFtail := mapIteratedStage_reindex hF r αt
      have hGtail := mapIteratedStage_reindex hG r αt
      have hP : RC ⋙ hFb.mapStage nb = hFa.mapStage nb ⋙ SD :=
        (hR.mapStage_comp hFb nb).symm.trans
          ((stageMap_eq_of_exact_eq (hR.comp hFb) (hFa.comp hS) hFtail nb).trans
            (hFa.mapStage_comp hS nb))
      have hQ : RC ⋙ hGb.mapStage nb = hGa.mapStage nb ⋙ SD :=
        (hR.mapStage_comp hGb nb).symm.trans
          ((stageMap_eq_of_exact_eq (hR.comp hGb) (hGa.comp hS) hGtail nb).trans
            (hGa.mapStage_comp hS nb))
      have ht := stageNatTrans_baseChange hR hS hFa hGa hFb hGb ea eb
        hFtail hGtail (ih αt) nb
      have ht' := Functor.map_retyped_heq
        ((Functor.whiskeringLeft (Stage CA na) (Stage CA nb) (Stage DB nb)).obj HC)
        hP hQ _ _ ht
      have hh := hFa.mapStageNatTrans_reindex hGa ea (α 0).unop
      have hh' := Functor.map_retyped_heq
        ((Functor.whiskeringRight (Stage CA na) (Stage DA nb) (Stage DB nb)).obj SD)
        (hFa.mapStage_reindex (α 0).unop) (hGa.mapStage_reindex (α 0).unop) _ _ hh
      have hPcore : (HC ⋙ RC) ⋙ hFb.mapStage nb = hFa.mapStage na ⋙ (HD ⋙ SD) := by
        change HC ⋙ (RC ⋙ hFb.mapStage nb) = _
        rw [hP]
        exact congrArg (fun K => K ⋙ SD) (hFa.mapStage_reindex (α 0).unop)
      have hQcore : (HC ⋙ RC) ⋙ hGb.mapStage nb = hGa.mapStage na ⋙ (HD ⋙ SD) := by
        change HC ⋙ (RC ⋙ hGb.mapStage nb) = _
        rw [hQ]
        exact congrArg (fun K => K ⋙ SD) (hGa.mapStage_reindex (α 0).unop)
      have hcore : HEq
          (Functor.whiskerLeft (HC ⋙ RC) (hFb.mapStageNatTrans hGb eb nb))
          (Functor.whiskerRight (hFa.mapStageNatTrans hGa ea na) (HD ⋙ SD)) :=
        ht'.trans hh'
      have ha := mapIteratedStageNatTrans_tuple_chart hF hG η
        (fun i => (a i).unop.len)
      have hb := mapIteratedStageNatTrans_tuple_chart hF hG η
        (fun i => (b i).unop.len)
      have hea := (conj_eqToHom_iff_heq _ _
        (mapIteratedStage_tuple_successor hF (fun i => (a i).unop.len))
        (mapIteratedStage_tuple_successor hG (fun i => (a i).unop.len))).1 ha
      have heb := (conj_eqToHom_iff_heq _ _
        (mapIteratedStage_tuple_successor hF (fun i => (b i).unop.len))
        (mapIteratedStage_tuple_successor hG (fun i => (b i).unop.len))).1 hb
      exact transportedNatTransSquare
        (iteratedStageOfFnSuccEquivalence C (fun i => (a i).unop.len))
        (iteratedStageOfFnSuccEquivalence C (fun i => (b i).unop.len))
        (iteratedStageOfFnSuccEquivalence D (fun i => (a i).unop.len))
        (iteratedStageOfFnSuccEquivalence D (fun i => (b i).unop.len))
        (HC ⋙ RC) (HD ⋙ SD) (reindexIteratedStage C α) (reindexIteratedStage D α)
        (reindexIteratedStage_succ C α) (reindexIteratedStage_succ D α)
        (mapIteratedStageNatTrans hF hG η (stageTupleDegrees a))
        (mapIteratedStageNatTrans hF hG η (stageTupleDegrees b))
        (hFa.mapStageNatTrans hGa ea na) (hFb.mapStageNatTrans hGb eb nb)
        (mapIteratedStage_tuple_successor hF (fun i => (a i).unop.len))
        (mapIteratedStage_tuple_successor hG (fun i => (a i).unop.len))
        (mapIteratedStage_tuple_successor hF (fun i => (b i).unop.len))
        (mapIteratedStage_tuple_successor hG (fun i => (b i).unop.len))
        hea heb hPcore hQcore hcore
        (mapIteratedStage_reindex hF (r + 1) α) (mapIteratedStage_reindex hG (r + 1) α)
        (iteratedStageOfFnSuccEquivalence_inverse_functor C (fun i => (b i).unop.len))
        (iteratedStageOfFnSuccEquivalence_inverse_functor D (fun i => (b i).unop.len))

/-- The full original natural transformation commutes with every original
tuple reindexing through both actual exact-functor equality transports. -/
theorem mapIteratedStageNatTrans_reindex
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G)
    (r : ℕ) {a b : StageSimplexTuple r} (α : a ⟶ b) :
    Functor.whiskerLeft (reindexIteratedStage C α)
        (mapIteratedStageNatTrans hF hG η (stageTupleDegrees b)) =
      eqToHom (mapIteratedStage_reindex hF r α) ≫
        Functor.whiskerRight (mapIteratedStageNatTrans hF hG η (stageTupleDegrees a))
          (reindexIteratedStage D α) ≫
        eqToHom (mapIteratedStage_reindex hG r α).symm :=
  (conj_eqToHom_iff_heq _ _ (mapIteratedStage_reindex hF r α)
    (mapIteratedStage_reindex hG r α)).2 (iteratedNatTrans_reindex_heq hF hG η r α)

private theorem iteratedMap_eq_of_functor_eq
    {A : Type (max u₀ v₀)} [Category.{v₀} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
    {B : Type (max u₁ v₁)} [Category.{v₁} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
    {P Q : A ⥤ B} (hP : P.IsWaldhausenExact) (hQ : Q.IsWaldhausenExact)
    (h : P = Q) (ns : List ℕ) : mapIteratedStage hP ns = mapIteratedStage hQ ns := by
  cases h
  rfl

private theorem iteratedMap_chart_representation
    {A A' : Type (max u₀ v₀)} [Category.{v₀} A] [Category.{v₀} A']
    {B B' : Type (max u₁ v₁)} [Category.{v₁} B] [Category.{v₁} B']
    (eA : A ≌ A') (eB : B ≌ B') {P : A ⥤ B} {Q : A' ⥤ B'}
    (h : P ⋙ eB.functor = eA.functor ⋙ Q)
    (hB : eB.functor ⋙ eB.inverse = 𝟭 B) : P = eA.functor ⋙ Q ⋙ eB.inverse := by
  calc
    P = P ⋙ (eB.functor ⋙ eB.inverse) := by rw [hB, Functor.comp_id]
    _ = (P ⋙ eB.functor) ⋙ eB.inverse := rfl
    _ = _ := congrArg (fun K => K ⋙ eB.inverse) h

set_option backward.isDefEq.respectTransparency false in
private theorem iteratedNatTrans_baseChange
    {A : Type (max u₀ v₀)} [Category.{v₀} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
    {A' : Type (max u₁ v₁)} [Category.{v₁} A'] [HasZeroObject A']
        [WaldhausenCategoryWithoutGluing A']
    {B : Type (max u₂ v₂)} [Category.{v₂} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
    {B' : Type (max u₃ v₃)} [Category.{v₃} B'] [HasZeroObject B']
        [WaldhausenCategoryWithoutGluing B']
    {R : A ⥤ A'} {S : B ⥤ B'} {F₀ G₀ : A ⥤ B} {F₁ G₁ : A' ⥤ B'}
    (hR : R.IsWaldhausenExact) (hS : S.IsWaldhausenExact)
    (hF₀ : F₀.IsWaldhausenExact) (hG₀ : G₀.IsWaldhausenExact)
    (hF₁ : F₁.IsWaldhausenExact) (hG₁ : G₁.IsWaldhausenExact)
    (η₀ : F₀ ⟶ G₀) (η₁ : F₁ ⟶ G₁)
    (hF : R ⋙ F₁ = F₀ ⋙ S) (hG : R ⋙ G₁ = G₀ ⋙ S)
    (hη : HEq (Functor.whiskerLeft R η₁) (Functor.whiskerRight η₀ S))
    (ns : List ℕ) :
    HEq (Functor.whiskerLeft (mapIteratedStage hR ns)
        (mapIteratedStageNatTrans hF₁ hG₁ η₁ ns))
      (Functor.whiskerRight (mapIteratedStageNatTrans hF₀ hG₀ η₀ ns)
        (mapIteratedStage hS ns)) := by
  have hFn (ms : List ℕ) : mapIteratedStage hR ms ⋙ mapIteratedStage hF₁ ms =
      mapIteratedStage hF₀ ms ⋙ mapIteratedStage hS ms :=
    (mapIteratedStage_comp hR hF₁ ms).symm.trans
      ((iteratedMap_eq_of_functor_eq (hR.comp hF₁) (hF₀.comp hS) hF ms).trans
        (mapIteratedStage_comp hF₀ hS ms))
  have hGn (ms : List ℕ) : mapIteratedStage hR ms ⋙ mapIteratedStage hG₁ ms =
      mapIteratedStage hG₀ ms ⋙ mapIteratedStage hS ms :=
    (mapIteratedStage_comp hR hG₁ ms).symm.trans
      ((iteratedMap_eq_of_functor_eq (hR.comp hG₁) (hG₀.comp hS) hG ms).trans
        (mapIteratedStage_comp hG₀ hS ms))
  induction ns with
  | nil =>
      have hη₀ := (conj_eqToHom_iff_heq _ _
        (mapIteratedStage_nil_chart hF₀) (mapIteratedStage_nil_chart hG₀)).mp
          (mapIteratedStageNatTrans_nil_chart hF₀ hG₀ η₀)
      have hη₁ := (conj_eqToHom_iff_heq _ _
        (mapIteratedStage_nil_chart hF₁) (mapIteratedStage_nil_chart hG₁)).mp
          (mapIteratedStageNatTrans_nil_chart hF₁ hG₁ η₁)
      exact transportedNatTransSquare
        (iteratedStageNilEquivalence A) (iteratedStageNilEquivalence A')
        (iteratedStageNilEquivalence B) (iteratedStageNilEquivalence B') R S
        (mapIteratedStage hR []) (mapIteratedStage hS [])
        (iteratedMap_chart_representation _ _ (mapIteratedStage_nil_chart hR)
          (iteratedStageNilEquivalence_functor_inverse A'))
        (iteratedMap_chart_representation _ _ (mapIteratedStage_nil_chart hS)
          (iteratedStageNilEquivalence_functor_inverse B'))
        (mapIteratedStageNatTrans hF₀ hG₀ η₀ []) (mapIteratedStageNatTrans hF₁ hG₁ η₁ [])
        η₀ η₁ (mapIteratedStage_nil_chart hF₀) (mapIteratedStage_nil_chart hG₀)
        (mapIteratedStage_nil_chart hF₁) (mapIteratedStage_nil_chart hG₁)
        hη₀ hη₁ hF hG hη (hFn []) (hGn [])
        (iteratedStageNilEquivalence_inverse_functor A')
        (iteratedStageNilEquivalence_inverse_functor B')
  | cons n ns ih =>
      let hRn := mapIteratedStage_isWaldhausenExact hR ns
      let hSn := mapIteratedStage_isWaldhausenExact hS ns
      let hF₀n := mapIteratedStage_isWaldhausenExact hF₀ ns
      let hG₀n := mapIteratedStage_isWaldhausenExact hG₀ ns
      let hF₁n := mapIteratedStage_isWaldhausenExact hF₁ ns
      let hG₁n := mapIteratedStage_isWaldhausenExact hG₁ ns
      let η₀n := mapIteratedStageNatTrans hF₀ hG₀ η₀ ns
      let η₁n := mapIteratedStageNatTrans hF₁ hG₁ η₁ ns
      have hFs : hRn.mapStage n ⋙ hF₁n.mapStage n = hF₀n.mapStage n ⋙ hSn.mapStage n :=
        (hRn.mapStage_comp hF₁n n).symm.trans
          ((stageMap_eq_of_exact_eq (hRn.comp hF₁n) (hF₀n.comp hSn) (hFn ns) n).trans
            (hF₀n.mapStage_comp hSn n))
      have hGs : hRn.mapStage n ⋙ hG₁n.mapStage n = hG₀n.mapStage n ⋙ hSn.mapStage n :=
        (hRn.mapStage_comp hG₁n n).symm.trans
          ((stageMap_eq_of_exact_eq (hRn.comp hG₁n) (hG₀n.comp hSn) (hGn ns) n).trans
            (hG₀n.mapStage_comp hSn n))
      have hηs := stageNatTrans_baseChange hRn hSn hF₀n hG₀n hF₁n hG₁n
        η₀n η₁n (hFn ns) (hGn ns) ih n
      have hη₀ := (conj_eqToHom_iff_heq _ _
        (mapIteratedStage_cons_chart hF₀ n ns) (mapIteratedStage_cons_chart hG₀ n ns)).mp
          (mapIteratedStageNatTrans_cons_chart hF₀ hG₀ η₀ n ns)
      have hη₁ := (conj_eqToHom_iff_heq _ _
        (mapIteratedStage_cons_chart hF₁ n ns) (mapIteratedStage_cons_chart hG₁ n ns)).mp
          (mapIteratedStageNatTrans_cons_chart hF₁ hG₁ η₁ n ns)
      exact transportedNatTransSquare
        (iteratedStageConsEquivalence A n ns) (iteratedStageConsEquivalence A' n ns)
        (iteratedStageConsEquivalence B n ns) (iteratedStageConsEquivalence B' n ns)
        (hRn.mapStage n) (hSn.mapStage n)
        (mapIteratedStage hR (n :: ns)) (mapIteratedStage hS (n :: ns))
        (iteratedMap_chart_representation _ _ (mapIteratedStage_cons_chart hR n ns)
          (iteratedStageConsEquivalence_functor_inverse A' n ns))
        (iteratedMap_chart_representation _ _ (mapIteratedStage_cons_chart hS n ns)
          (iteratedStageConsEquivalence_functor_inverse B' n ns))
        (mapIteratedStageNatTrans hF₀ hG₀ η₀ (n :: ns))
        (mapIteratedStageNatTrans hF₁ hG₁ η₁ (n :: ns))
        (hF₀n.mapStageNatTrans hG₀n η₀n n) (hF₁n.mapStageNatTrans hG₁n η₁n n)
        (mapIteratedStage_cons_chart hF₀ n ns) (mapIteratedStage_cons_chart hG₀ n ns)
        (mapIteratedStage_cons_chart hF₁ n ns) (mapIteratedStage_cons_chart hG₁ n ns)
        hη₀ hη₁ hFs hGs hηs (hFn (n :: ns)) (hGn (n :: ns))
        (iteratedStageConsEquivalence_inverse_functor A' n ns)
        (iteratedStageConsEquivalence_inverse_functor B' n ns)

variable {E : Type (max uE vE)} [Category.{vE} E] [HasZeroObject E]
    [WaldhausenCategoryWithoutGluing E]

/-- Precomposition by an original exact functor retains the whole iterated transformation. -/
theorem mapIteratedStageNatTrans_precomp {R : E ⥤ C} (hR : R.IsWaldhausenExact)
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G) (ns : List ℕ) :
    mapIteratedStageNatTrans (hR.comp hF) (hR.comp hG) (Functor.whiskerLeft R η) ns =
      eqToHom (mapIteratedStage_comp hR hF ns) ≫
        Functor.whiskerLeft (mapIteratedStage hR ns) (mapIteratedStageNatTrans hF hG η ns) ≫
        eqToHom (mapIteratedStage_comp hR hG ns).symm := by
  have h := iteratedNatTrans_baseChange hR (Functor.IsWaldhausenExact.id (C := D))
    (hR.comp hF) (hR.comp hG) hF hG (Functor.whiskerLeft R η) η
    (by rfl) (by rfl) (by rfl) ns
  rw [mapIteratedStage_id] at h
  apply (conj_eqToHom_iff_heq _ _
    (mapIteratedStage_comp hR hF ns) (mapIteratedStage_comp hR hG ns)).mpr
  exact h.symm

/-- Postcomposition by an original exact functor retains the whole iterated transformation. -/
theorem mapIteratedStageNatTrans_postcomp {S : D ⥤ E} (hS : S.IsWaldhausenExact)
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (η : F ⟶ G) (ns : List ℕ) :
    mapIteratedStageNatTrans (hF.comp hS) (hG.comp hS) (Functor.whiskerRight η S) ns =
      eqToHom (mapIteratedStage_comp hF hS ns) ≫
        Functor.whiskerRight (mapIteratedStageNatTrans hF hG η ns) (mapIteratedStage hS ns) ≫
        eqToHom (mapIteratedStage_comp hG hS ns).symm := by
  have h := iteratedNatTrans_baseChange (Functor.IsWaldhausenExact.id (C := C)) hS
    hF hG (hF.comp hS) (hG.comp hS) η (Functor.whiskerRight η S)
    (by rfl) (by rfl) (by rfl) ns
  rw [mapIteratedStage_id] at h
  apply (conj_eqToHom_iff_heq _ _
    (mapIteratedStage_comp hF hS ns) (mapIteratedStage_comp hG hS ns)).mpr
  exact h

end CategoryTheory.Waldhausen.SConstruction
