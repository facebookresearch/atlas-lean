/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.HCofibrationGluing
public import MathlibExt.CategoryTheory.SmallObject.Closure
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Natural comparison maps along relative cell complexes

A natural transformation between colimit-preserving functors has weak components along a
relative cell complex when it is weak on the initial object and on both endpoints of every
generating cell. The induction assumes specified coproduct, pushout and continuous
ordinal-colimit closure conditions for W and H, and requires both functors to send the
generating maps into H. Separate lemmas transport comparison components through
isomorphisms, coproducts and retracts under the corresponding closure hypotheses on W.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uC vC uD vD w t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty HomotopicalAlgebra

namespace HomotopicalAlgebra.ModuleTransfer.CellComparison

variable {C : Type uC} [Category.{vC} C]

/-- Required base closures, with original cofans, both pushouts, and both ordinal cocones. -/
structure Closure (W H : MorphismProperty C) : Prop where
  coproducts_h : H.IsStableUnderCoproducts.{w}
  cobase_h : H.IsStableUnderCobaseChange
  transfinite_h : H.IsStableUnderTransfiniteComposition.{t}
  coproducts_w : W.IsStableUnderCoproducts.{w}
  pushout
    {A X Z P A' X' Z' P' : C}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (i' : A' ⟶ X') (z' : A' ⟶ Z') (kX' : X' ⟶ P') (kZ' : Z' ⟶ P')
    (sq : IsPushout i z kX kZ) (sq' : IsPushout i' z' kX' kZ')
    (hi : H i) (hi' : H i')
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (p : P ⟶ P')
    (hI : a ≫ i' = i ≫ b) (hZ : a ≫ z' = z ≫ c)
    (hX : b ≫ kX' = kX ≫ p) (hP : c ≫ kZ' = kZ ≫ p)
    (ha : W a) (hb : W b) (hc : W c) : W p
  ordinal
    (J : Type t) [Small.{w} J] [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    (F G : J ⥤ C) [F.IsWellOrderContinuous] [G.IsWellOrderContinuous]
    (α : F ⟶ G)
    (hF : ∀ j : J, ¬IsMax j → H (F.map (homOfLE (Order.le_succ j))))
    (hG : ∀ j : J, ¬IsMax j → H (G.map (homOfLE (Order.le_succ j))))
    (hα : ∀ j : J, W (α.app j))
    (cF : Cocone F) (cG : Cocone G) (hcF : IsColimit cF) (hcG : IsColimit cG)
    (d : cF.pt ⟶ cG.pt) (hd : ∀ j : J, cF.ι.app j ≫ d = α.app j ≫ cG.ι.app j) : W d

variable {D : Type uD} [Category.{vD} D]

/-- Both mapped isomorphisms and the original naturality square form the entire comparison Arrow. -/
def comparisonArrowIso {P Q : D ⥤ C} (α : P ⟶ Q) {X Y : D} (e : X ≅ Y) :
    Arrow.mk (α.app X) ≅ Arrow.mk (α.app Y) :=
  Arrow.isoMk (P.mapIso e) (Q.mapIso e) (α.naturality e.hom)

/-- Naturality maps the original object retract into a whole comparison Arrow retract. -/
def comparisonRetract {P Q : D ⥤ C} (α : P ⟶ Q) {X Y : D} (r : Retract X Y) :
    RetractArrow (α.app X) (α.app Y) where
  i := Arrow.homMk (P.map r.i) (Q.map r.i) (α.naturality r.i)
  r := Arrow.homMk (P.map r.r) (Q.map r.r) (α.naturality r.r)
  retract := by
    apply Arrow.hom_ext
    · change P.map r.i ≫ P.map r.r = 𝟙 (P.obj X)
      rw [← P.map_comp, r.retract, P.map_id]
    · change Q.map r.i ≫ Q.map r.r = 𝟙 (Q.obj X)
      rw [← Q.map_comp, r.retract, Q.map_id]

theorem comparison_of_retract (W : MorphismProperty C) [W.IsStableUnderRetracts]
    {P Q : D ⥤ C} (α : P ⟶ Q) {X Y : D} (r : Retract X Y)
    (hY : W (α.app Y)) : W (α.app X) :=
  W.of_retract (comparisonRetract α r) hY

/-- Every actual source cofan is mapped through both preserved cocones. -/
theorem comparison_of_cofan (W : MorphismProperty C) [W.IsStableUnderCoproducts.{w}]
    {P Q : D ⥤ C} (α : P ⟶ Q)
    [PreservesColimitsOfSize.{w, w} P] [PreservesColimitsOfSize.{w, w} Q]
    {J : Type w} (X : J → D) (c : Cofan X) (hc : IsColimit c)
    (hα : ∀ j, W (α.app (X j))) : W (α.app c.pt) := by
  apply MorphismProperty.colimitsOfShape_le (W := W) (J := Discrete J)
  exact MorphismProperty.colimitsOfShape.mk' _ _ (P.mapCocone c) (Q.mapCocone c)
    (isColimitOfPreserves P hc) (isColimitOfPreserves Q hc)
    (Functor.whiskerLeft (Discrete.functor X) α) (fun j => hα j.as) (α.app c.pt)
    (fun j => α.naturality (c.ι.app j))

/-- Each mapped attaching cofan map retains all original cell labels and source maps. -/
theorem mapped_attachment_h (S : MorphismProperty D) (H : MorphismProperty C)
    [H.IsStableUnderCoproducts.{w}]
    (P : D ⥤ C) [PreservesColimitsOfSize.{w, w} P]
    (hSP : S ≤ H.inverseImage P)
    {X Y : D} {f : X ⟶ Y} (a : AttachCells.{w} S.homFamily f) : H (P.map a.m) := by
  let η : Discrete.functor (fun j : a.ι => (a.π j).1.left) ⟶
      Discrete.functor (fun j : a.ι => (a.π j).1.right) :=
    Discrete.natTrans (fun j : Discrete a.ι => (a.π j.as).1.hom)
  apply H.coproducts_le
  apply MorphismProperty.colimitsOfShape_le_coproducts H a.ι
  exact MorphismProperty.colimitsOfShape.mk' _ _ (P.mapCocone a.cofan₁) (P.mapCocone a.cofan₂)
    (isColimitOfPreserves P a.isColimit₁) (isColimitOfPreserves P a.isColimit₂)
    (Functor.whiskerRight η P)
    (fun j => by
      change H (P.map (a.π j.as).1.hom)
      exact hSP _ (a.π j.as).2) (P.map a.m)
    (fun j => by
      change P.map (a.cofan₁.inj j.as) ≫ P.map a.m =
        P.map (a.π j.as).1.hom ≫ P.map (a.cofan₂.inj j.as)
      simpa only [Functor.map_comp, MorphismProperty.homFamily] using congrArg P.map (a.hm j.as))

/-- Genuine original cells, successor cofans, bottom isomorphism, limits and endpoint determine comparison weakness. -/
theorem comparison_of_relativeCells
    (W H : MorphismProperty C) [W.RespectsIso] (cl : Closure.{uC, vC, w, t} W H)
    (S : MorphismProperty D) {P Q : D ⥤ C} (α : P ⟶ Q)
    [PreservesColimitsOfSize.{w, w} P] [PreservesColimitsOfSize.{w, w} Q]
    [PreservesColimitsOfSize.{t, t} P] [PreservesColimitsOfSize.{t, t} Q]
    (hSP : S ≤ H.inverseImage P) (hSQ : S ≤ H.inverseImage Q)
    (hEndpoints : ∀ {A X : D} (i : A ⟶ X), S i → W (α.app A) ∧ W (α.app X))
    {J : Type t} [Small.{w} J] [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {X Y : D} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} (fun (_ : J) => S.homFamily) f)
    (hX : W (α.app X)) : W (α.app Y) := by
  let : H.IsStableUnderCoproducts.{w} := cl.coproducts_h
  let : H.IsStableUnderCobaseChange := cl.cobase_h
  let : H.IsStableUnderTransfiniteComposition.{t} := cl.transfinite_h
  let : W.IsStableUnderCoproducts.{w} := cl.coproducts_w
  let : PreservesColimitsOfSize.{0, 0} P := preservesSmallestColimits_of_preservesColimits P
  let : PreservesColimitsOfSize.{0, 0} Q := preservesSmallestColimits_of_preservesColimits Q
  let : c.F.IsWellOrderContinuous := c.isWellOrderContinuous
  let : PreservesWellOrderContinuousOfShape J P :=
    { preservesColimitsOfShape := fun _ _ => by infer_instance }
  let : PreservesWellOrderContinuousOfShape J Q :=
    { preservesColimitsOfShape := fun _ _ => by infer_instance }
  have hAllP : ∀ {i k : J} (g : i ⟶ k), H (P.map (c.F.map g)) :=
    fun g => c.map_map_mem_of_le P S H hSP g
  have hAllQ : ∀ {i k : J} (g : i ⟶ k), H (Q.map (c.F.map g)) :=
    fun g => c.map_map_mem_of_le Q S H hSQ g
  have hStages : ∀ k : J, W (α.app (c.F.obj k)) := by
    intro k
    induction k using SuccOrder.limitRecOn with
    | isMin k hk =>
      obtain rfl := hk.eq_bot
      exact (W.arrow_mk_iso_iff (comparisonArrowIso α c.isoBot)).mpr hX
    | succ k hk ih =>
      let a := c.attachCells k hk
      let sources : a.ι → D := fun j => (a.π j).1.left
      let targets : a.ι → D := fun j => (a.π j).1.right
      have hSources : W (α.app a.cofan₁.pt) := comparison_of_cofan W α sources
        a.cofan₁ a.isColimit₁ (fun j => (hEndpoints (a.π j).1.hom (a.π j).2).1)
      have hTargets : W (α.app a.cofan₂.pt) := comparison_of_cofan W α targets
        a.cofan₂ a.isColimit₂ (fun j => (hEndpoints (a.π j).1.hom (a.π j).2).2)
      exact cl.pushout
        (P.map a.m) (P.map a.g₁) (P.map a.g₂) (P.map (c.F.map (homOfLE (Order.le_succ k))))
        (Q.map a.m) (Q.map a.g₁) (Q.map a.g₂) (Q.map (c.F.map (homOfLE (Order.le_succ k))))
        (a.isPushout.flip.map P) (a.isPushout.flip.map Q)
        (mapped_attachment_h S H P hSP a) (mapped_attachment_h S H Q hSQ a)
        (α.app a.cofan₁.pt) (α.app a.cofan₂.pt) (α.app (c.F.obj k)) (α.app (c.F.obj (Order.succ k)))
        (α.naturality a.m).symm (α.naturality a.g₁).symm
        (α.naturality a.g₂).symm (α.naturality (c.F.map (homOfLE (Order.le_succ k)))).symm
        hSources hTargets ih
    | isSuccLimit k hk ih =>
      let : OrderBot (Set.Iio k) := { bot := ⟨⊥, hk.bot_lt⟩, bot_le j := bot_le }
      let : SuccOrder (Set.Iio k) := SuccOrder.ofLinearWellFoundedLT (Set.Iio k)
      let F := (Set.principalSegIio k).monotone.functor ⋙ c.F
      let : F.IsWellOrderContinuous :=
        inferInstanceAs
          (((Set.principalSegIio k : Set.Iio k ≤i J)).monotone.functor ⋙ c.F).IsWellOrderContinuous
      let : PreservesWellOrderContinuousOfShape (Set.Iio k) P :=
        { preservesColimitsOfShape := fun _ _ => by infer_instance }
      let : PreservesWellOrderContinuousOfShape (Set.Iio k) Q :=
        { preservesColimitsOfShape := fun _ _ => by infer_instance }
      exact cl.ordinal (Set.Iio k) (F ⋙ P) (F ⋙ Q) (Functor.whiskerLeft F α)
        (fun j _ => hAllP ((Set.principalSegIio k).monotone.functor.map
          (homOfLE (Order.le_succ j))))
        (fun j _ => hAllQ ((Set.principalSegIio k).monotone.functor.map
          (homOfLE (Order.le_succ j))))
        (fun j => ih j.1 j.2)
        (P.mapCocone ((Set.principalSegIio k).cocone c.F))
        (Q.mapCocone ((Set.principalSegIio k).cocone c.F))
        (isColimitOfPreserves P (c.F.isColimitOfIsWellOrderContinuous k hk))
        (isColimitOfPreserves Q (c.F.isColimitOfIsWellOrderContinuous k hk))
        (α.app (c.F.obj k)) (fun j => α.naturality (((Set.principalSegIio k).cocone c.F).ι.app j))
  exact cl.ordinal J (c.F ⋙ P) (c.F ⋙ Q) (Functor.whiskerLeft c.F α)
    (fun j _ => hAllP (homOfLE (Order.le_succ j)))
    (fun j _ => hAllQ (homOfLE (Order.le_succ j))) hStages
    (P.mapCocone (Cocone.mk Y c.incl)) (Q.mapCocone (Cocone.mk Y c.incl))
    (isColimitOfPreserves P c.isColimit) (isColimitOfPreserves Q c.isColimit)
    (α.app Y) (fun j => α.naturality (c.incl.app j))

end HomotopicalAlgebra.ModuleTransfer.CellComparison
