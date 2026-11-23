/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.SourceConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
import Mathlib.AlgebraicTopology.ModelCategory.Opposite
import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Continuous inverse towers in the constructed injective model

The compatible lift on a continuous direct diagram is built at the original
bottom, every successor and every limit stage. Its opposite supplies the
injective fibrancy of a continuous inverse fibration tower. The actual
injective model is constructed from the coefficient's combinatorial model;
its entire diagram model is never an input.
-/

set_option autoImplicit false
noncomputable section
universe uC vC uJ w

open CategoryTheory CategoryTheory.Limits Opposite

namespace HomotopicalAlgebra.InverseOrdinalInjectiveLimit

section CompatibleLifts

variable {C : Type uC} [Category.{vC} C]
  {J : Type uJ} [LinearOrder J]
  {F E Z : J ⥤ C} (q : E ⟶ Z) (b : F ⟶ Z)

@[ext]
private structure PrefixLift (j : J) where
  app (k : J) (hk : k ≤ j) : F.obj k ⟶ E.obj k
  naturality (i k : J) (hi : i ≤ j) (hk : k ≤ j) (h : i ≤ k) :
    F.map (homOfLE h) ≫ app k hk = app i hi ≫ E.map (homOfLE h)
  fac (k : J) (hk : k ≤ j) : app k hk ≫ q.app k = b.app k

private def PrefixLift.restrict {i j : J} (l : PrefixLift q b j) (h : i ≤ j) :
    PrefixLift q b i where
  app k hk := l.app k (hk.trans h)
  naturality k m hk hm hkm := l.naturality k m (hk.trans h) (hm.trans h) hkm
  fac k hk := l.fac k (hk.trans h)

private def prefixLiftFunctor : Jᵒᵖ ⥤ Type (max uJ vC) where
  obj j := PrefixLift q b j.unop
  map f := ↾fun l => l.restrict q b (leOfHom f.unop)
  map_id j := by
    apply ConcreteCategory.hom_ext
    intro l
    apply PrefixLift.ext
    funext k hk
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro l
    apply PrefixLift.ext
    funext k hk
    rfl

variable [SuccOrder J]

private def successorApp (j : J) (l : PrefixLift q b j)
    (x : F.obj (Order.succ j) ⟶ E.obj (Order.succ j))
    (k : J) (hk : k ≤ Order.succ j) : F.obj k ⟶ E.obj k :=
  if h : k ≤ j then l.app k h else by
    have he : k = Order.succ j := le_antisymm hk (Order.succ_le_of_lt (lt_of_not_ge h))
    subst k
    exact x

private theorem successorApp_of_le (j : J) (l : PrefixLift q b j)
    (x : F.obj (Order.succ j) ⟶ E.obj (Order.succ j)) (k : J) (hk : k ≤ j) :
    successorApp q b j l x k (hk.trans (Order.le_succ j)) = l.app k hk := by
  simp only [successorApp, dite_eq_left hk]

private theorem successorApp_at_succ (j : J) (hj : ¬IsMax j) (l : PrefixLift q b j)
    (x : F.obj (Order.succ j) ⟶ E.obj (Order.succ j)) :
    successorApp q b j l x (Order.succ j) le_rfl = x := by
  simp only [successorApp, dite_eq_right (not_le.mpr (Order.lt_succ_of_not_isMax hj))]

private def successorPrefix (j : J) (hj : ¬IsMax j) (l : PrefixLift q b j)
    (x : F.obj (Order.succ j) ⟶ E.obj (Order.succ j))
    (hx : F.map (homOfLE (Order.le_succ j)) ≫ x =
      l.app j le_rfl ≫ E.map (homOfLE (Order.le_succ j)))
    (hq : x ≫ q.app (Order.succ j) = b.app (Order.succ j)) :
    PrefixLift q b (Order.succ j) where
  app := successorApp q b j l x
  naturality i k hi hk hik := by
    by_cases hk0 : k ≤ j
    · have hi0 := hik.trans hk0
      rw [successorApp_of_le q b j l x k hk0, successorApp_of_le q b j l x i hi0]
      exact l.naturality i k hi0 hk0 hik
    · have he : k = Order.succ j := le_antisymm hk (Order.succ_le_of_lt (lt_of_not_ge hk0))
      subst k
      rw [successorApp_at_succ q b j hj l x]
      by_cases hi0 : i ≤ j
      · rw [successorApp_of_le q b j l x i hi0]
        have hf : (homOfLE hik : i ⟶ Order.succ j) =
            homOfLE hi0 ≫ homOfLE (Order.le_succ j) := Subsingleton.elim _ _
        rw [hf, F.map_comp, Category.assoc, hx, ← Category.assoc,
          l.naturality i j hi0 le_rfl hi0, Category.assoc, ← E.map_comp]
      · have hei : i = Order.succ j := le_antisymm hi (Order.succ_le_of_lt (lt_of_not_ge hi0))
        subst i
        rw [successorApp_at_succ q b j hj l x]
        have hid : (homOfLE hik : Order.succ j ⟶ Order.succ j) = 𝟙 _ := Subsingleton.elim _ _
        rw [hid, F.map_id, E.map_id, Category.id_comp, Category.comp_id]
  fac k hk := by
    by_cases hk0 : k ≤ j
    · rw [successorApp_of_le q b j l x k hk0]
      exact l.fac k hk0
    · have he : k = Order.succ j := le_antisymm hk (Order.succ_le_of_lt (lt_of_not_ge hk0))
      subst k
      rw [successorApp_at_succ q b j hj l x]
      exact hq

private theorem successorPrefix_restrict (j : J) (hj : ¬IsMax j) (l : PrefixLift q b j)
    (x : F.obj (Order.succ j) ⟶ E.obj (Order.succ j))
    (hx : F.map (homOfLE (Order.le_succ j)) ≫ x =
      l.app j le_rfl ≫ E.map (homOfLE (Order.le_succ j)))
    (hq : x ≫ q.app (Order.succ j) = b.app (Order.succ j)) :
    (successorPrefix q b j hj l x hx hq).restrict q b (Order.le_succ j) = l := by
  apply PrefixLift.ext
  funext k hk
  exact successorApp_of_le q b j l x k hk

private abbrev preceding (j : J) : Set.Iio j ⥤ J :=
  (OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor

private def precedingApp (j : J)
    (s : ((preceding j).op ⋙ prefixLiftFunctor q b).sections)
    (k : J) (hk : k < j) : F.obj k ⟶ E.obj k :=
  (s.val (op ⟨k, hk⟩)).app k le_rfl

omit [SuccOrder J] in
private theorem precedingApp_naturality (j : J)
    (s : ((preceding j).op ⋙ prefixLiftFunctor q b).sections)
    (i k : J) (hi : i < j) (hk : k < j) (hik : i ≤ k) :
    F.map (homOfLE hik) ≫ precedingApp q b j s k hk =
      precedingApp q b j s i hi ≫ E.map (homOfLE hik) := by
  have hs := s.property (homOfLE hik : (⟨i, hi⟩ : Set.Iio j) ⟶ ⟨k, hk⟩).op
  change (s.val (op ⟨k, hk⟩)).restrict q b hik = s.val (op ⟨i, hi⟩) at hs
  have hsi := congrArg (fun t : PrefixLift q b i => t.app i le_rfl) hs
  change (s.val (op ⟨k, hk⟩)).app i hik = precedingApp q b j s i hi at hsi
  change F.map (homOfLE hik) ≫ (s.val (op ⟨k, hk⟩)).app k le_rfl = _
  rw [(s.val (op ⟨k, hk⟩)).naturality i k hik le_rfl hik, hsi]

private def precedingCocone (j : J)
    (s : ((preceding j).op ⋙ prefixLiftFunctor q b).sections) : Cocone (preceding j ⋙ F) where
  pt := E.obj j
  ι := {
    app k := precedingApp q b j s k.val k.property ≫ E.map (homOfLE k.property.le)
    naturality k m g := by
      change F.map (homOfLE (leOfHom g)) ≫
          (precedingApp q b j s m.val m.property ≫ E.map (homOfLE m.property.le)) =
        (precedingApp q b j s k.val k.property ≫ E.map (homOfLE k.property.le)) ≫ 𝟙 _
      rw [Category.comp_id]
      have h := precedingApp_naturality q b j s k.val m.val k.property m.property (leOfHom g)
      calc
        _ = (F.map (homOfLE (leOfHom g)) ≫ precedingApp q b j s m.val m.property) ≫
            E.map (homOfLE m.property.le) := (Category.assoc _ _ _).symm
        _ = (precedingApp q b j s k.val k.property ≫ E.map (homOfLE (leOfHom g))) ≫
            E.map (homOfLE m.property.le) := congrArg (fun f => f ≫ E.map _) h
        _ = _ := by rw [Category.assoc, ← E.map_comp]; rfl }

variable [F.IsWellOrderContinuous]

private def limitHom (j : J) (hj : Order.IsSuccLimit j)
    (s : ((preceding j).op ⋙ prefixLiftFunctor q b).sections) : F.obj j ⟶ E.obj j :=
  (F.isColimitOfIsWellOrderContinuous j hj).desc (precedingCocone q b j s)

omit [SuccOrder J] in
private theorem limitHom_fac (j : J) (hj : Order.IsSuccLimit j)
    (s : ((preceding j).op ⋙ prefixLiftFunctor q b).sections) (k : J) (hk : k < j) :
    F.map (homOfLE hk.le) ≫ limitHom q b j hj s =
      precedingApp q b j s k hk ≫ E.map (homOfLE hk.le) :=
  (F.isColimitOfIsWellOrderContinuous j hj).fac (precedingCocone q b j s) ⟨k, hk⟩

omit [SuccOrder J] in
private theorem limitHom_projection (j : J) (hj : Order.IsSuccLimit j)
    (s : ((preceding j).op ⋙ prefixLiftFunctor q b).sections) :
    limitHom q b j hj s ≫ q.app j = b.app j := by
  apply (F.isColimitOfIsWellOrderContinuous j hj).hom_ext
  intro k
  change F.map (homOfLE k.property.le) ≫ (limitHom q b j hj s ≫ q.app j) =
    F.map (homOfLE k.property.le) ≫ b.app j
  have hfac : precedingApp q b j s k.val k.property ≫ q.app k.val = b.app k.val :=
    (s.val (op k)).fac k.val le_rfl
  rw [← Category.assoc, limitHom_fac q b j hj s k.val k.property, Category.assoc, q.naturality,
    ← Category.assoc, hfac]
  exact (b.naturality (homOfLE k.property.le)).symm

private def limitApp (j : J) (hj : Order.IsSuccLimit j)
    (s : ((preceding j).op ⋙ prefixLiftFunctor q b).sections)
    (k : J) (hk : k ≤ j) : F.obj k ⟶ E.obj k :=
  if h : k < j then precedingApp q b j s k h else by
    have he : k = j := le_antisymm hk (le_of_not_gt h)
    subst k
    exact limitHom q b j hj s

omit [SuccOrder J] in
private theorem limitApp_of_lt (j : J) (hj : Order.IsSuccLimit j)
    (s : ((preceding j).op ⋙ prefixLiftFunctor q b).sections) (k : J) (hk : k < j) :
    limitApp q b j hj s k hk.le = precedingApp q b j s k hk := by
  simp only [limitApp, dite_eq_left hk]

omit [SuccOrder J] in
private theorem limitApp_at_limit (j : J) (hj : Order.IsSuccLimit j)
    (s : ((preceding j).op ⋙ prefixLiftFunctor q b).sections) :
    limitApp q b j hj s j le_rfl = limitHom q b j hj s := by
  simp only [limitApp, dite_eq_right (lt_irrefl j)]

private def limitPrefix (j : J) (hj : Order.IsSuccLimit j)
    (s : ((preceding j).op ⋙ prefixLiftFunctor q b).sections) : PrefixLift q b j where
  app := limitApp q b j hj s
  naturality i k hi hk hik := by
    by_cases hk0 : k < j
    · have hi0 := lt_of_le_of_lt hik hk0
      rw [limitApp_of_lt q b j hj s k hk0, limitApp_of_lt q b j hj s i hi0]
      exact precedingApp_naturality q b j s i k hi0 hk0 hik
    · have he : k = j := le_antisymm hk (le_of_not_gt hk0)
      subst k
      rw [limitApp_at_limit q b j hj s]
      by_cases hi0 : i < j
      · rw [limitApp_of_lt q b j hj s i hi0]
        exact limitHom_fac q b j hj s i hi0
      · have hei : i = j := le_antisymm hi (le_of_not_gt hi0)
        subst i
        rw [limitApp_at_limit q b j hj s]
        have hid : (homOfLE hik : j ⟶ j) = 𝟙 _ := Subsingleton.elim _ _
        rw [hid, F.map_id, E.map_id, Category.id_comp, Category.comp_id]
  fac k hk := by
    by_cases hk0 : k < j
    · rw [limitApp_of_lt q b j hj s k hk0]
      exact (s.val (op ⟨k, hk0⟩)).fac k le_rfl
    · have he : k = j := le_antisymm hk (le_of_not_gt hk0)
      subst k
      rw [limitApp_at_limit q b j hj s]
      exact limitHom_projection q b j hj s

omit [SuccOrder J] in
private theorem limitPrefix_restrict (j : J) (hj : Order.IsSuccLimit j)
    (s : ((preceding j).op ⋙ prefixLiftFunctor q b).sections) (i : J) (hi : i < j) :
    (limitPrefix q b j hj s).restrict q b hi.le = s.val (op ⟨i, hi⟩) := by
  apply PrefixLift.ext
  funext k hk
  have hkj := lt_of_le_of_lt hk hi
  change limitApp q b j hj s k (hk.trans hi.le) = (s.val (op ⟨i, hi⟩)).app k hk
  rw [limitApp_of_lt q b j hj s k hkj]
  have hs := s.property (homOfLE hk : (⟨k, hkj⟩ : Set.Iio j) ⟶ ⟨i, hi⟩).op
  change (s.val (op ⟨i, hi⟩)).restrict q b hk = s.val (op ⟨k, hkj⟩) at hs
  have hsk := congrArg (fun t : PrefixLift q b k => t.app k le_rfl) hs
  exact hsk.symm

variable [ModelCategory C] [OrderBot J] [WellFoundedLT J]

private def prefixInduction
    (hstep : ∀ j : J, ¬IsMax j → Cofibration (F.map (homOfLE (Order.le_succ j))))
    (hq : ∀ j : J, trivialFibrations C (q.app j)) :
    (prefixLiftFunctor q b).WellOrderInductionData where
  succ j hj l := by
    let _ : Cofibration (F.map (homOfLE (Order.le_succ j))) := hstep j hj
    let _ : Fibration (q.app (Order.succ j)) := (mem_trivialFibrations_iff _).mp (hq _) |>.1
    let _ : WeakEquivalence (q.app (Order.succ j)) := (mem_trivialFibrations_iff _).mp (hq _) |>.2
    let sq : CommSq (l.app j le_rfl ≫ E.map (homOfLE (Order.le_succ j)))
        (F.map (homOfLE (Order.le_succ j))) (q.app (Order.succ j)) (b.app (Order.succ j)) :=
      ⟨by
        rw [Category.assoc, q.naturality, ← Category.assoc, l.fac j le_rfl]
        exact (b.naturality _).symm⟩
    exact successorPrefix q b j hj l sq.lift sq.fac_left sq.fac_right
  map_succ j hj l := by
    dsimp
    apply successorPrefix_restrict
  lift j hj s := limitPrefix q b j hj s
  map_lift j hj s i hi := limitPrefix_restrict q b j hj s i hi

/-- The actual chosen bottom lift extends across every original successor
cofibration and every original continuous limit to a whole natural lift. -/
theorem exists_natTrans_of_fixed_bot
    (hstep : ∀ j : J, ¬IsMax j → Cofibration (F.map (homOfLE (Order.le_succ j))))
    (hq : ∀ j : J, trivialFibrations C (q.app j))
    (l₀ : F.obj ⊥ ⟶ E.obj ⊥) (hl₀ : l₀ ≫ q.app ⊥ = b.app ⊥) :
    ∃ l : F ⟶ E, l ≫ q = b ∧ l.app ⊥ = l₀ := by
  let z : PrefixLift q b ⊥ := {
    app k hk := by
      have he : k = ⊥ := le_antisymm hk bot_le
      subst k
      exact l₀
    naturality i k hi hk hik := by
      have hei : i = ⊥ := le_antisymm hi bot_le
      have hek : k = ⊥ := le_antisymm hk bot_le
      subst i
      subst k
      have hid : (homOfLE hik : (⊥ : J) ⟶ ⊥) = 𝟙 _ := Subsingleton.elim _ _
      rw [hid]
      change F.map (𝟙 (⊥ : J)) ≫ l₀ = l₀ ≫ E.map (𝟙 (⊥ : J))
      rw [F.map_id, E.map_id, Category.id_comp, Category.comp_id]
    fac k hk := by
      have he : k = ⊥ := le_antisymm hk bot_le
      subst k
      exact hl₀ }
  obtain ⟨s, hs⟩ := (prefixInduction q b hstep hq).surjective z
  let l : F ⟶ E := {
    app j := (s.val (op j)).app j le_rfl
    naturality i j g := by
      have hij := leOfHom g
      have hsij := s.property g.op
      change (s.val (op j)).restrict q b hij = s.val (op i) at hsij
      have hsi := congrArg (fun t : PrefixLift q b i => t.app i le_rfl) hsij
      change F.map (homOfLE hij) ≫ (s.val (op j)).app j le_rfl =
        (s.val (op i)).app i le_rfl ≫ E.map (homOfLE hij)
      rw [(s.val (op j)).naturality i j hij le_rfl hij]
      exact congrArg (fun f => f ≫ E.map (homOfLE hij)) hsi }
  refine ⟨l, ?_, ?_⟩
  · apply NatTrans.ext
    funext j
    exact (s.val (op j)).fac j le_rfl
  · exact congrArg (fun t : PrefixLift q b ⊥ => t.app ⊥ le_rfl) hs

end CompatibleLifts

section InverseLifts

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasTerminal C]
  {J : Type uJ} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- The actual inverse tower lifts every original pointwise trivial
cofibration as a whole natural transformation, preserving the full input map. -/
theorem exists_natTrans_of_continuous_inverseTower
    (T : Jᵒᵖ ⥤ C) [T.rightOp.IsWellOrderContinuous]
    (hbot : IsFibrant (T.obj (op (⊥ : J))))
    (hsucc : ∀ j : J, ¬IsMax j → Fibration (T.map (homOfLE (Order.le_succ j)).op))
    {A B : Jᵒᵖ ⥤ C} (i : A ⟶ B) (f : A ⟶ T)
    (hi : ∀ j : Jᵒᵖ, trivialCofibrations C (i.app j)) :
    ∃ lift : B ⟶ T, i ≫ lift = f := by
  let _ : Cofibration (i.app (op (⊥ : J))) := ((mem_trivialCofibrations_iff _).mp (hi _)).1
  let _ : WeakEquivalence (i.app (op (⊥ : J))) := ((mem_trivialCofibrations_iff _).mp (hi _)).2
  let _ : Fibration (terminal.from (T.obj (op (⊥ : J)))) := hbot
  let sq₀ : CommSq (f.app (op (⊥ : J))) (i.app (op (⊥ : J)))
      (terminal.from (T.obj (op (⊥ : J)))) (terminal.from (B.obj (op (⊥ : J)))) :=
    ⟨Subsingleton.elim _ _⟩
  have hstep : ∀ j : J, ¬IsMax j →
      Cofibration (T.rightOp.map (homOfLE (Order.le_succ j))) := by
    intro j hj
    change Cofibration ((T.map (homOfLE (Order.le_succ j)).op).op)
    exact (cofibration_op_iff _).mpr (hsucc j hj)
  have hop : ∀ j : J, trivialFibrations Cᵒᵖ (i.rightOp.app j) := by
    intro j
    change trivialFibrations Cᵒᵖ ((i.app (op j)).op)
    rw [trivialFibrations_op]
    exact hi (op j)
  have h₀ : sq₀.lift.op ≫ i.rightOp.app (⊥ : J) = f.rightOp.app (⊥ : J) :=
    congrArg Quiver.Hom.op sq₀.fac_left
  obtain ⟨l, hl, _⟩ := exists_natTrans_of_fixed_bot i.rightOp f.rightOp hstep hop sq₀.lift.op h₀
  refine ⟨l.removeRightOp, ?_⟩
  apply NatTrans.ext
  funext j
  have h := congr_app hl j.unop
  exact congrArg Quiver.Hom.unop h

end InverseLifts

section ConstructedInjectiveModel

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [IsCombinatorialModelCategory.{w} C] [HasTerminal C]
  {J : Type uJ} [Small.{w} J] [LinearOrder J] [OrderBot J]
  [SuccOrder J] [WellFoundedLT J]

local instance inverseIndexSmall : Small.{w} Jᵒᵖ :=
  small_of_injective (f := (Opposite.unop : Jᵒᵖ → J)) Opposite.unop_injective

local instance inverseIndexLocallySmall : LocallySmall.{w} Jᵒᵖ :=
  locallySmall_of_thin

local instance inverseIndexEssentiallySmall : EssentiallySmall.{w} Jᵒᵖ :=
  essentiallySmall_of_small_of_locallySmall Jᵒᵖ

/-- A continuous inverse tower with its original fibrant bottom and
successor fibrations is fibrant in the actually constructed injective model.
The full diagram lift comes from the original compatible ordinal recursion. -/
theorem isFibrant_of_continuous_inverseTower
    (T : Jᵒᵖ ⥤ C) [T.rightOp.IsWellOrderContinuous]
    (hbot : IsFibrant (T.obj (op (⊥ : J))))
    (hsucc : ∀ j : J, ¬IsMax j → Fibration (T.map (homOfLE (Order.le_succ j)).op)) :
    letI : ModelCategory (Jᵒᵖ ⥤ C) :=
      FunctorInjective.SourceConstruction.modelCategory (D := Jᵒᵖ) (C := C)
    IsFibrant T := by
  let _ : ModelCategory (Jᵒᵖ ⥤ C) :=
    FunctorInjective.SourceConstruction.modelCategory (D := Jᵒᵖ) (C := C)
  rw [isFibrant_iff, fibration_iff,
    (FunctorInjective.SourceConstruction.fiveClasses (D := Jᵒᵖ) (C := C)).2.2.2.1]
  intro A B i hi
  constructor
  intro f g sq
  obtain ⟨lift, hlift⟩ := exists_natTrans_of_continuous_inverseTower T hbot hsucc i f hi
  exact CommSq.HasLift.mk' ⟨lift, hlift, terminalIsTerminal.hom_ext _ _⟩

variable [HasLimitsOfShape Jᵒᵖ C]

omit [HasTerminal C] [OrderBot J] [SuccOrder J] [WellFoundedLT J] in
/-- The original constant/limit adjunction is Quillen on the internally
constructed injective model, using its actual objectwise left classes. -/
theorem constLim_isQuillenAdjunction :
    letI : ModelCategory (Jᵒᵖ ⥤ C) :=
      FunctorInjective.SourceConstruction.modelCategory (D := Jᵒᵖ) (C := C)
    (constLimAdj (J := Jᵒᵖ) (C := C)).IsQuillenAdjunction := by
  let _ : ModelCategory (Jᵒᵖ ⥤ C) :=
    FunctorInjective.SourceConstruction.modelCategory (D := Jᵒᵖ) (C := C)
  constructor
  · intro X Y i hi
    rw [(FunctorInjective.SourceConstruction.fiveClasses (D := Jᵒᵖ) (C := C)).2.1]
    intro j
    exact hi
  · intro X Y i hi
    rw [(FunctorInjective.SourceConstruction.fiveClasses (D := Jᵒᵖ) (C := C)).2.2.1]
    intro j
    exact hi

/-- Every original weak component between continuous inverse fibration
towers induces a weak map between the caller's actual limiting cones.
Both cone leg equations and the internally constructed injective model are retained. -/
theorem weakEquivalence_of_continuous_inverse_isLimits
    (F G : Jᵒᵖ ⥤ C) [F.rightOp.IsWellOrderContinuous] [G.rightOp.IsWellOrderContinuous]
    (α : F ⟶ G)
    (hFbot : IsFibrant (F.obj (op (⊥ : J)))) (hGbot : IsFibrant (G.obj (op (⊥ : J))))
    (hFsucc : ∀ j : J, ¬IsMax j → Fibration (F.map (homOfLE (Order.le_succ j)).op))
    (hGsucc : ∀ j : J, ¬IsMax j → Fibration (G.map (homOfLE (Order.le_succ j)).op))
    (hα : ∀ j : Jᵒᵖ, weakEquivalences C (α.app j))
    (cF : Cone F) (cG : Cone G) (hcF : IsLimit cF) (hcG : IsLimit cG)
    (d : cF.pt ⟶ cG.pt) (hd : ∀ j : Jᵒᵖ, d ≫ cG.π.app j = cF.π.app j ≫ α.app j) :
    WeakEquivalence d := by
  let _ : ModelCategory (Jᵒᵖ ⥤ C) :=
    FunctorInjective.SourceConstruction.modelCategory (D := Jᵒᵖ) (C := C)
  let _ : IsFibrant F := isFibrant_of_continuous_inverseTower F hFbot hFsucc
  let _ : IsFibrant G := isFibrant_of_continuous_inverseTower G hGbot hGsucc
  let _ : WeakEquivalence α := (weakEquivalence_iff _).mpr (by
    rw [(FunctorInjective.SourceConstruction.fiveClasses (D := Jᵒᵖ) (C := C)).1]
    exact hα)
  let _ : (constLimAdj (J := Jᵒᵖ) (C := C)).IsQuillenAdjunction := constLim_isQuillenAdjunction
  have hlim : WeakEquivalence (lim.map α) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := constLimAdj) α
  let eF := (limit.isLimit F).conePointUniqueUpToIso hcF
  let eG := (limit.isLimit G).conePointUniqueUpToIso hcG
  have comm : eF.hom ≫ d = lim.map α ≫ eG.hom := by
    apply hcG.hom_ext
    intro j
    rw [Category.assoc, hd, ← Category.assoc,
      IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit F) hcF j, Category.assoc,
      IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit G) hcG j]
    exact (limMap_π α j).symm
  exact (weakEquivalence_iff _).mpr
    (((weakEquivalences C).arrow_mk_iso_iff (Arrow.isoMk eF eG comm)).mp
      ((weakEquivalence_iff _).mp hlim))

end ConstructedInjectiveModel

end HomotopicalAlgebra.InverseOrdinalInjectiveLimit
