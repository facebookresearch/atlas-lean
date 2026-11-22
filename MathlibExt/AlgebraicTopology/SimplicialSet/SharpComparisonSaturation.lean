/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OverPullbackFilteredColimits
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel
public import MathlibExt.CategoryTheory.MorphismProperty.CoproductClosure
public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Preorder

/-!
# Saturation of anodyne pullback comparison classes

For a fixed map of simplicial sets, this file considers anodyne maps whose ordinary pullback comparisons are realization weak equivalences for every map from their target to the fixed base. This class is closed under cobase change, arrow retracts, and transfinite compositions and coproducts in the simplicial-set universe.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.SharpSaturation

/-- Rezk's original class: anodyne q and realization-weak SAME ordinary
pullback comparison for EVERY original map from its target to Y. -/
def comparisonTrivialCofibrations {X Y : SSet.{u}} (p : X ⟶ Y) :
    MorphismProperty SSet.{u} := fun A B q =>
  anodyneExtensions q ∧ ∀ t : B ⟶ Y,
    realizationWeakEquivalences
      (pullback.map p (q ≫ t) p t (𝟙 X) q (𝟙 Y) (by simp) (by simp))

private abbrev overPull (X Y : SSet.{u}) (p : X ⟶ Y) :=
  Over.pullback p ⋙ Over.forget X

private def overArrow {A B Y : SSet.{u}} (q : A ⟶ B) (t : B ⟶ Y) :
    Over.mk (q ≫ t) ⟶ Over.mk t := Over.homMk q

private def overComparisonClass {X Y : SSet.{u}} (p : X ⟶ Y) :
    MorphismProperty (Over Y) :=
  anodyneExtensions.inverseImage (Over.forget Y) ⊓
    anodyneExtensions.inverseImage (overPull X Y p)

private theorem anodyne_iff_mono_weak {A B : SSet.{u}} (q : A ⟶ B) :
    anodyneExtensions q ↔ Mono q ∧ realizationWeakEquivalences q := by
  rw [anodyneExtensions_eq_trivialCofibrations,
    HomotopicalAlgebra.mem_trivialCofibrations_iff,
    SSet.modelCategoryQuillen.cofibration_iff,
    HomotopicalAlgebra.weakEquivalence_iff]
  rfl

private theorem pullMap_square {X Y : SSet.{u}} (p : X ⟶ Y)
    {a b : Over Y} (q : a ⟶ b) :
    IsPullback ((overPull X Y p).map q) (pullback.fst a.hom p)
      (pullback.fst b.hom p) q.left := by
  have hfst : (overPull X Y p).map q ≫ pullback.fst b.hom p =
      pullback.fst a.hom p ≫ q.left := by simp [overPull, Over.pullback]
  have hsnd : (overPull X Y p).map q ≫ pullback.snd b.hom p =
      pullback.snd a.hom p := by simp [overPull, Over.pullback]
  apply IsPullback.mk' hfst
  · intro T f g hf hg
    apply pullback.hom_ext
    · exact hg
    · have h := congrArg (fun k => k ≫ pullback.snd b.hom p) hf
      simpa only [Category.assoc, hsnd] using h
  · intro T f g h
    have hcone : g ≫ a.hom = (f ≫ pullback.snd b.hom p) ≫ p := by
      calc
        g ≫ a.hom = g ≫ (q.left ≫ b.hom) := by rw [Over.w q]
        _ = (g ≫ q.left) ≫ b.hom := (Category.assoc _ _ _).symm
        _ = (f ≫ pullback.fst b.hom p) ≫ b.hom := by rw [← h]
        _ = (f ≫ pullback.snd b.hom p) ≫ p := by simp [Category.assoc, pullback.condition]
    refine ⟨pullback.lift g (f ≫ pullback.snd b.hom p) hcone, ?_, by simp⟩
    apply pullback.hom_ext
    · simpa only [Category.assoc, hfst, pullback.lift_fst_assoc] using h.symm
    · simp only [Category.assoc, hsnd, pullback.lift_snd]

private def originalArrowIso {X Y A B : SSet.{u}} (p : X ⟶ Y)
    (q : A ⟶ B) (t : B ⟶ Y) :
    Arrow.mk (pullback.map p (q ≫ t) p t (𝟙 X) q (𝟙 Y) (by simp) (by simp)) ≅
      Arrow.mk ((overPull X Y p).map (overArrow q t)) :=
  Arrow.isoMk (pullbackSymmetry p (q ≫ t)) (pullbackSymmetry p t) (by
    apply pullback.hom_ext
    · simp [overPull, overArrow, Over.pullback]
    · simp [overPull, overArrow, Over.pullback])

private def overArrowIso {Y : SSet.{u}} {a b : Over Y} (q : a ⟶ b) :
    Arrow.mk (overArrow q.left b.hom) ≅ Arrow.mk q :=
  Arrow.isoMk (Over.isoMk (Iso.refl a.left) (by
    change (𝟙 a.left) ≫ a.hom = q.left ≫ b.hom
    simpa only [Category.id_comp] using (Over.w q).symm)) (Iso.refl b) (by ext; rfl)

private theorem overClass_retract {X Y : SSet.{u}} (p : X ⟶ Y) :
    (overComparisonClass p).IsStableUnderRetracts := by
  dsimp only [overComparisonClass]
  infer_instance

private theorem class_iff_over {X Y A B : SSet.{u}} (p : X ⟶ Y) (q : A ⟶ B) :
    comparisonTrivialCofibrations p q ↔
      anodyneExtensions q ∧ ∀ t : B ⟶ Y, overComparisonClass p (overArrow q t) := by
  constructor
  · rintro ⟨hq, hw⟩
    refine ⟨hq, fun t => ⟨hq, ?_⟩⟩
    have hmono : Mono q := ((anodyne_iff_mono_weak q).1 hq).1
    have hm : Mono ((overPull _ _ p).map (overArrow q t)) :=
      (MorphismProperty.monomorphisms SSet.{u}).of_isPullback
        (pullMap_square p (overArrow q t)).flip hmono
    exact (anodyne_iff_mono_weak _).2 ⟨hm,
      (realizationWeakEquivalences.arrow_mk_iso_iff (originalArrowIso p q t)).1 (hw t)⟩
  · rintro ⟨hq, ht⟩
    refine ⟨hq, fun t => ?_⟩
    exact (realizationWeakEquivalences.arrow_mk_iso_iff (originalArrowIso p q t)).2
      ((anodyne_iff_mono_weak _).1 (ht t).2).2

private theorem overClass_mem_of_class {X Y : SSet.{u}} (p : X ⟶ Y)
    {a b : Over Y} (q : a ⟶ b) (hq : comparisonTrivialCofibrations p q.left) :
    overComparisonClass p q := by
  let _ := overClass_retract p
  exact ((overComparisonClass p).arrow_mk_iso_iff (overArrowIso q)).1
    (((class_iff_over p q.left).1 hq).2 b.hom)

private theorem overClass_cobase {X Y : SSet.{u}} (p : X ⟶ Y) :
    (overComparisonClass p).IsStableUnderCobaseChange where
  of_isPushout {a a' b b' q g q' g'} H hq := by
    let G := overPull X Y p
    have HS := H.map (Over.forget Y)
    let _ : Mono ((Over.forget Y).map q) := by
      change Mono q.left
      exact ((anodyne_iff_mono_weak q.left).1 hq.1).1
    have HK := Adhesive.van_kampen' HS
    have Htop : IsPushout (G.map g) (G.map q) (G.map q') (G.map g') :=
      (HK (G.map g) (G.map q) (G.map q') (G.map g')
        (pullback.fst a.hom p) (pullback.fst b.hom p)
        (pullback.fst a'.hom p) (pullback.fst b'.hom p)
        (pullMap_square p g) (pullMap_square p q)
        (pullMap_square p q').toCommSq (pullMap_square p g').toCommSq
        ⟨by simpa only [← G.map_comp] using congrArg G.map H.w⟩).2
        ⟨pullMap_square p q', pullMap_square p g'⟩
    exact ⟨anodyneExtensions.of_isPushout HS hq.1,
      anodyneExtensions.of_isPushout Htop hq.2⟩

private theorem class_retract {X Y : SSet.{u}} (p : X ⟶ Y) :
    (comparisonTrivialCofibrations p).IsStableUnderRetracts where
  of_retract {A B C D q r} h hr := by
    have hq := anodyneExtensions.of_retract h hr.1
    refine (class_iff_over p q).2 ⟨hq, fun t => ?_⟩
    let s := h.r.right ≫ t
    let il : Over.mk (q ≫ t) ⟶ Over.mk (r ≫ s) :=
      Over.homMk h.i.left (by
        dsimp [s]
        rw [h.i_w_assoc, h.retract_right_assoc]
        change q ≫ ((𝟙 B) ≫ t) = q ≫ t
        exact congrArg (fun k => q ≫ k) (CategoryTheory.Category.id_comp t))
    let ir : Over.mk t ⟶ Over.mk s :=
      Over.homMk h.i.right (by
        dsimp [s]; simp only [← Category.assoc, h.retract_right, Category.id_comp])
    let rl : Over.mk (r ≫ s) ⟶ Over.mk (q ≫ t) :=
      Over.homMk h.r.left (by
        dsimp [s]; simpa only [Category.assoc] using congrArg (fun k => k ≫ t) h.r_w)
    let rr : Over.mk s ⟶ Over.mk t := Over.homMk h.r.right
    have H : RetractArrow (overArrow q t) (overArrow r s) :=
      { i := Arrow.homMk il ir (by
          apply Over.OverMorphism.ext
          change h.i.left ≫ r = q ≫ h.i.right
          exact h.i_w)
        r := Arrow.homMk rl rr (by
          apply Over.OverMorphism.ext
          change h.r.left ≫ q = r ≫ h.r.right
          exact h.r_w)
        retract := by ext <;> simp [il, ir, rl, rr, h.retract_left, h.retract_right] }
    let _ := overClass_retract p
    exact (overComparisonClass p).of_retract H (((class_iff_over p r).1 hr).2 s)

private theorem class_cobase {X Y : SSet.{u}} (p : X ⟶ Y) :
    (comparisonTrivialCofibrations p).IsStableUnderCobaseChange where
  of_isPushout {A A' B B' q g q' g'} H hq := by
    have ha := anodyneExtensions.of_isPushout H hq.1
    refine (class_iff_over p q').2 ⟨ha, fun t => ?_⟩
    let a : Over Y := Over.mk (q ≫ g' ≫ t)
    let a' : Over Y := Over.mk (g' ≫ t)
    let b : Over Y := Over.mk (q' ≫ t)
    let b' : Over Y := Over.mk t
    let qo : a ⟶ a' := Over.homMk q (by simp [a, a'])
    let go : a ⟶ b := Over.homMk g (by
      dsimp [a, b]
      simpa only [Category.assoc] using congrArg (fun k => k ≫ t) H.w)
    let q'o : b ⟶ b' := Over.homMk q'
    let g'o : a' ⟶ b' := Over.homMk g'
    have Ho : IsPushout go qo q'o g'o := IsPushout.of_map_of_faithful (Over.forget Y) H
    let _ := overClass_cobase p
    exact (overComparisonClass p).of_isPushout Ho
      (overClass_mem_of_class p qo hq)

/-- The literal comparison class is closed under arbitrary original cobase
changes and WHOLE original Arrow retracts, without any assumption on p. -/
private theorem comparisonTrivialCofibrations_cobase_retract {X Y : SSet.{u}} (p : X ⟶ Y) :
    (comparisonTrivialCofibrations p).IsStableUnderCobaseChange ∧
      (comparisonTrivialCofibrations p).IsStableUnderRetracts :=
  ⟨class_cobase p, class_retract p⟩

private theorem overClass_transfinite {X Y : SSet.{u}} (p : X ⟶ Y) :
    (overComparisonClass p).IsStableUnderTransfiniteComposition.{u} := by
  constructor
  intro J _ _ _ _
  let G := overPull X Y p
  let _ : PreservesColimitsOfShape J (Over.pullback p) :=
    overPullback_preservesColimitsOfShape_of_isFiltered J p
  let _ : PreservesWellOrderContinuousOfShape J (Over.forget Y) :=
    { preservesColimitsOfShape j hj := by infer_instance }
  let _ : PreservesWellOrderContinuousOfShape J G :=
    { preservesColimitsOfShape j hj := by
        let _ : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
        let _ : PreservesColimitsOfShape (Set.Iio j) (Over.pullback p) :=
          overPullback_preservesColimitsOfShape_of_isFiltered (Set.Iio j) p
        infer_instance }
  constructor
  rintro a b q ⟨h⟩
  let h₁ : (anodyneExtensions.inverseImage (Over.forget Y)).TransfiniteCompositionOfShape J q :=
    h.ofLE (by intro A B f hf; exact hf.1)
  let h₂ : (anodyneExtensions.inverseImage G).TransfiniteCompositionOfShape J q :=
    h.ofLE (by intro A B f hf; exact hf.2)
  exact ⟨anodyneExtensions.transfiniteCompositionsOfShape_le J _ h₁.map.mem,
    anodyneExtensions.transfiniteCompositionsOfShape_le J _ h₂.map.mem⟩

private theorem class_transfinite {X Y : SSet.{u}} (p : X ⟶ Y) :
    (comparisonTrivialCofibrations p).IsStableUnderTransfiniteComposition.{u} := by
  constructor
  intro J _ _ _ _
  constructor
  rintro A B q ⟨h⟩
  have ha : anodyneExtensions q :=
    anodyneExtensions.transfiniteCompositionsOfShape_le J _
      (h.ofLE (by intro A B f hf; exact hf.1)).mem
  refine (class_iff_over p q).2 ⟨ha, fun t => ?_⟩
  let F : J ⥤ Over Y := h.F.toOver Y (fun j => h.incl.app j ≫ t) (by
    intro i j f
    have hn : h.F.map f ≫ h.incl.app j = h.incl.app i ≫ 𝟙 B := by
      simpa only [CategoryTheory.Functor.const_obj_map] using h.incl.naturality f
    have hn' := hn.trans (CategoryTheory.Category.comp_id (h.incl.app i))
    exact (CategoryTheory.Category.assoc (h.F.map f) (h.incl.app j) t).symm.trans
      (congrArg (fun k => k ≫ t) hn'))
  let hc : F.IsWellOrderContinuous :=
    { nonempty_isColimit j hj := ⟨by
        apply isColimitOfReflects (Over.forget Y)
        change IsColimit ((Set.principalSegIio j).cocone h.F)
        exact h.F.isColimitOfIsWellOrderContinuous j hj⟩ }
  let _ : F.IsWellOrderContinuous := hc
  let e₀ : F.obj ⊥ ≅ Over.mk (q ≫ t) := Over.isoMk h.isoBot (by
    change h.isoBot.hom ≫ (q ≫ t) = h.incl.app ⊥ ≫ t
    have hb : h.isoBot.hom ≫ q = h.incl.app ⊥ := by
      have hf := congrArg (fun k : A ⟶ B => h.isoBot.hom ≫ k) h.fac
      simpa only [Iso.hom_inv_id_assoc] using hf.symm
    exact (CategoryTheory.Category.assoc h.isoBot.hom q t).symm.trans
      (congrArg (fun k => k ≫ t) hb))
  let incl : F ⟶ (CategoryTheory.Functor.const J).obj (Over.mk t) :=
    { app j := Over.homMk (h.incl.app j)
      naturality i j f := by
        apply Over.OverMorphism.ext
        change h.F.map f ≫ h.incl.app j = h.incl.app i ≫ 𝟙 B
        simpa only [CategoryTheory.Functor.const_obj_map] using h.incl.naturality f }
  let ho : (overComparisonClass p).TransfiniteCompositionOfShape J (overArrow q t) :=
    { F := F
      isoBot := e₀
      incl := incl
      isColimit := by
        apply isColimitOfReflects (Over.forget Y)
        change IsColimit (Cocone.mk B h.incl)
        exact h.isColimit
      fac := by
        apply Over.OverMorphism.ext
        change h.isoBot.inv ≫ h.incl.app ⊥ = q
        exact h.fac
      map_mem j hj := overClass_mem_of_class p (F.map (homOfLE (Order.le_succ j)))
        (by
          change comparisonTrivialCofibrations p
            (h.F.map (homOfLE (Order.le_succ j)))
          exact h.map_mem j hj) }
  let _ := overClass_transfinite p
  exact (overComparisonClass p).transfiniteCompositionsOfShape_le J _ ho.mem

/-- All four original saturation closures are constructed internally for the
literal comparison class, including SAME-universe arbitrary coproducts. -/
theorem comparisonTrivialCofibrations_saturated {X Y : SSet.{u}} (p : X ⟶ Y) :
    (comparisonTrivialCofibrations p).IsStableUnderCobaseChange ∧
    (comparisonTrivialCofibrations p).IsStableUnderRetracts ∧
    (comparisonTrivialCofibrations p).IsStableUnderTransfiniteComposition.{u} ∧
    (comparisonTrivialCofibrations p).IsStableUnderCoproducts.{u} := by
  have hcr := comparisonTrivialCofibrations_cobase_retract p
  have htc := class_transfinite p
  let _ := hcr.1
  let _ := htc
  have hsum := MorphismProperty.isStableUnderCoproducts_of_cobase_transfinite
    (comparisonTrivialCofibrations p)
  exact ⟨hcr.1, hcr.2, htc, hsum⟩

end SSet.SharpSaturation
