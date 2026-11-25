/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Coproducts and cobase change of transfinite compositions

Assemble a coproduct of supplied compositions with one original ordered shape,
and transport a supplied composition through an actual endpoint pushout. Both
constructions retain the original endpoint arrow and composition shape.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe ν κ vC uC

open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty

variable {C : Type uC} [Category.{vC} C]

/-- A coproduct of actual compositions of the same shape K is a composition
of coproduct maps of that same K, at the original outer endpoint. -/
theorem coproducts_transfiniteCompositionsOfShape_le [HasCoproducts.{ν} C]
    (P : MorphismProperty C) (K : Type κ)
    [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K] :
    coproducts.{ν} (P.transfiniteCompositionsOfShape K) ≤
      (coproducts.{ν} P).transfiniteCompositionsOfShape K := by
  classical
  intro X Y q hq
  obtain ⟨I, hq⟩ := (coproducts_iff (P.transfiniteCompositionsOfShape K) q).1 hq
  obtain ⟨F₁, F₂, c₁, c₂, h₁, h₂, φ, hφ⟩ := hq
  let _ : HasColimitsOfShape (Discrete I) C := inferInstance
  let c (i : I) : P.TransfiniteCompositionOfShape K (φ.app ⟨i⟩) :=
    (hφ ⟨i⟩).some
  let V : K ⥤ (Discrete I ⥤ C) :=
    (Discrete.functor (fun i : I => (c i).F)).flip
  let τ : V ⟶ (Functor.const K).obj F₂ :=
    { app k := Discrete.natTrans (fun i : Discrete I => (c i.as).incl.app k)
      naturality k k' g := by
        ext i
        change (c i.as).F.map g ≫ (c i.as).incl.app k' =
          (c i.as).incl.app k ≫ 𝟙 _
        exact (c i.as).incl.naturality g }
  let e : V.obj ⊥ ≅ F₁ :=
    Discrete.natIso (fun i : Discrete I => (c i.as).isoBot)
  have hτ : IsColimit (Cocone.mk F₂ τ) := by
    apply evaluationJointlyReflectsColimits
    intro i
    change IsColimit (Cocone.mk (F₂.obj i) (c i.as).incl)
    exact (c i.as).isColimit
  have hV : V.IsWellOrderContinuous :=
    { nonempty_isColimit k hk := ⟨by
        apply evaluationJointlyReflectsColimits
        intro i
        change IsColimit ((Set.principalSegIio k).cocone (c i.as).F)
        let _ : (c i.as).F.IsWellOrderContinuous := (c i.as).isWellOrderContinuous
        exact (c i.as).F.isColimitOfIsWellOrderContinuous k hk⟩ }
  let L : (Discrete I ⥤ C) ⥤ C := colim
  let _ : PreservesColimitsOfShape K L := inferInstance
  let _ : PreservesWellOrderContinuousOfShape K L :=
    { preservesColimitsOfShape _ _ := inferInstance }
  let vcomp :
      ((coproducts.{ν} P).inverseImage L).TransfiniteCompositionOfShape K φ :=
    { toTransfiniteCompositionOfShape :=
        { F := V
          isoBot := e
          isWellOrderContinuous := hV
          incl := τ
          isColimit := hτ
          fac := by
            ext i
            change (c i.as).isoBot.inv ≫ (c i.as).incl.app ⊥ = φ.app i
            exact (c i.as).fac }
      map_mem k hk := by
        change coproducts.{ν} P (colimMap (V.map (homOfLE (Order.le_succ k))))
        apply P.colimitsOfShape_le_coproducts I _
        exact colimitsOfShape_colimMap (W := P)
          (X := V.obj k) (Y := V.obj (Order.succ k))
          (V.map (homOfLE (Order.le_succ k)))
          (fun i : Discrete I => (c i.as).map_mem k hk) }
  let mapped : (coproducts.{ν} P).TransfiniteCompositionOfShape K (L.map φ) :=
    vcomp.map
  let e₁ : L.obj F₁ ≅ c₁.pt :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit F₁) h₁
  let e₂ : L.obj F₂ ≅ c₂.pt :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit F₂) h₂
  let q₀ : c₁.pt ⟶ c₂.pt := h₁.desc (Cocone.mk _ (φ ≫ c₂.ι))
  have he₁ (i : Discrete I) : colimit.ι F₁ i ≫ e₁.hom = c₁.ι.app i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F₁) h₁ i
  have he₂ (i : Discrete I) : colimit.ι F₂ i ≫ e₂.hom = c₂.ι.app i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F₂) h₂ i
  have hq₀ : L.map φ ≫ e₂.hom = e₁.hom ≫ q₀ := by
    apply colimit.hom_ext
    intro i
    calc
      colimit.ι F₁ i ≫ (L.map φ ≫ e₂.hom) =
          φ.app i ≫ (colimit.ι F₂ i ≫ e₂.hom) :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun h => h ≫ e₂.hom) (ι_colimMap φ i)).trans
            (Category.assoc _ _ _))
      _ = φ.app i ≫ c₂.ι.app i := congrArg (fun h => φ.app i ≫ h) (he₂ i)
      _ = c₁.ι.app i ≫ q₀ := (h₁.fac (Cocone.mk _ (φ ≫ c₂.ι)) i).symm
      _ = (colimit.ι F₁ i ≫ e₁.hom) ≫ q₀ :=
        (congrArg (fun h => h ≫ q₀) (he₁ i)).symm
      _ = colimit.ι F₁ i ≫ (e₁.hom ≫ q₀) := Category.assoc _ _ _
  let eArrow : Arrow.mk (L.map φ) ≅ Arrow.mk q₀ :=
    Arrow.isoMk e₁ e₂ hq₀.symm
  change (coproducts.{ν} P).transfiniteCompositionsOfShape K q₀
  exact ⟨mapped.ofArrowIso eArrow⟩

end CategoryTheory.MorphismProperty

namespace CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape

variable {C : Type uC} [Category.{vC} C] {P : MorphismProperty C}
variable {K : Type κ} [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K]

/-- Push a supplied K-composition through the actual endpoint pushout, keeping
K and the literal new source X. Only pushouts along the fixed attaching map
are needed; the new successor maps are actual pushouts of the old P-maps. -/
noncomputable def cobaseChange {S Y X Z : C} {p : S ⟶ Y}
    (c : P.TransfiniteCompositionOfShape K p) (a : S ⟶ X) [HasPushoutsAlong a]
    {q : X ⟶ Z} {b : Y ⟶ Z} (sq : IsPushout a p q b) :
    P.pushouts.TransfiniteCompositionOfShape K q := by
  classical
  let _ : IsConnected K := IsFiltered.isConnected K
  let u (k : K) : S ⟶ c.F.obj k :=
    c.isoBot.inv ≫ c.F.map (homOfLE bot_le : (⊥ : K) ⟶ k)
  have hu {k k' : K} (g : k ⟶ k') : u k ≫ c.F.map g = u k' := by
    dsimp only [u]
    rw [Category.assoc, ← c.F.map_comp]
    rfl
  have huBot : u ⊥ = c.isoBot.inv := by
    change c.isoBot.inv ≫ c.F.map (𝟙 (⊥ : K)) = c.isoBot.inv
    rw [Functor.map_id, Category.comp_id]
  have huFac (k : K) : u k ≫ c.incl.app k = p := by
    have h' : c.F.map (homOfLE bot_le : (⊥ : K) ⟶ k) ≫ c.incl.app k =
        c.incl.app ⊥ ≫ 𝟙 Y :=
      c.incl.naturality (homOfLE bot_le : (⊥ : K) ⟶ k)
    have h : c.F.map (homOfLE bot_le : (⊥ : K) ⟶ k) ≫ c.incl.app k =
        c.incl.app ⊥ := h'.trans (Category.comp_id _)
    calc
      u k ≫ c.incl.app k = c.isoBot.inv ≫
          (c.F.map (homOfLE bot_le : (⊥ : K) ⟶ k) ≫ c.incl.app k) :=
        Category.assoc _ _ _
      _ = c.isoBot.inv ≫ c.incl.app ⊥ := congrArg (fun t => c.isoBot.inv ≫ t) h
      _ = p := c.fac
  let U : K ⥤ Under S :=
    { obj k := Under.mk (u k)
      map {k k'} g := Under.homMk (c.F.map g) (hu g)
      map_id k := by
        ext
        exact c.F.map_id k
      map_comp g h := by
        ext
        exact c.F.map_comp g h }
  let η : U ⟶ (Functor.const K).obj (Under.mk p) :=
    { app k := Under.homMk (c.incl.app k) (huFac k)
      naturality k k' g := by
        ext
        change c.F.map g ≫ c.incl.app k' = c.incl.app k ≫ 𝟙 _
        exact c.incl.naturality g }
  let eU : U.obj ⊥ ≅ Under.mk (𝟙 S) :=
    Under.isoMk c.isoBot (by
      change u ⊥ ≫ c.isoBot.hom = 𝟙 S
      rw [huBot]
      exact c.isoBot.inv_hom_id)
  let ε : Under.mk (𝟙 S) ⟶ Under.mk p := Under.homMk p
  have hη : IsColimit (Cocone.mk (Under.mk p) η) := by
    apply isColimitOfReflects (Under.forget S)
    change IsColimit (Cocone.mk Y c.incl)
    exact c.isColimit
  have hU : U.IsWellOrderContinuous :=
    { nonempty_isColimit k hk := ⟨by
        let _ : Nonempty (Set.Iio k) :=
          ⟨⟨⊥, not_isMin_iff_bot_lt.mp hk.1⟩⟩
        let _ : IsConnected (Set.Iio k) := IsFiltered.isConnected (Set.Iio k)
        apply isColimitOfReflects (Under.forget S)
        change IsColimit ((Set.principalSegIio k).cocone c.F)
        let _ : c.F.IsWellOrderContinuous := c.isWellOrderContinuous
        exact c.F.isColimitOfIsWellOrderContinuous k hk⟩ }
  let G : Under S ⥤ C := Under.pushout a ⋙ Under.forget X
  let _ : PreservesColimitsOfShape K G := inferInstance
  let _ : PreservesWellOrderContinuousOfShape K G :=
    { preservesColimitsOfShape k hk := by
        let _ : Nonempty (Set.Iio k) :=
          ⟨⟨⊥, not_isMin_iff_bot_lt.mp hk.1⟩⟩
        let _ : IsConnected (Set.Iio k) := IsFiltered.isConnected (Set.Iio k)
        infer_instance }
  have rectangle {k k' : K} (g : k ⟶ k') :
      IsPushout (c.F.map g) (pushout.inl (u k) a) (pushout.inl (u k') a)
        (G.map (U.map g)) := by
    let d : pushout (u k) a ⟶ pushout (u k') a := G.map (U.map g)
    have hc : u k ≫ (c.F.map g ≫ pushout.inl (u k') a) =
        a ≫ pushout.inr (u k') a := by
      rw [← Category.assoc, hu g]
      exact pushout.condition
    have hdLeft : pushout.inl (u k) a ≫ d =
        c.F.map g ≫ pushout.inl (u k') a := by
      change pushout.inl (u k) a ≫
        pushout.desc (c.F.map g ≫ pushout.inl (u k') a)
          (pushout.inr (u k') a) hc = c.F.map g ≫ pushout.inl (u k') a
      exact pushout.inl_desc _ _ _
    have hdRight : pushout.inr (u k) a ≫ d = pushout.inr (u k') a :=
      Under.w ((Under.pushout a).map (U.map g))
    have whole : IsPushout (u k ≫ c.F.map g) a (pushout.inl (u k') a)
        (pushout.inr (u k) a ≫ d) := by
      rw [hu g, hdRight]
      exact IsPushout.of_hasPushout (u k') a
    exact whole.of_left hdLeft.symm (IsPushout.of_hasPushout (u k) a)
  let underComp : (P.pushouts.inverseImage G).TransfiniteCompositionOfShape K ε :=
    { toTransfiniteCompositionOfShape :=
        { F := U
          isoBot := eU
          isWellOrderContinuous := hU
          incl := η
          isColimit := hη
          fac := by
            ext
            change c.isoBot.inv ≫ c.incl.app ⊥ = p
            exact c.fac }
      map_mem k hk := by
        change P.pushouts (G.map (U.map (homOfLE (Order.le_succ k))))
        exact P.pushouts_mk
          (rectangle (homOfLE (Order.le_succ k))).flip (c.map_mem k hk) }
  let mapped : P.pushouts.TransfiniteCompositionOfShape K (G.map ε) := underComp.map
  let _ : IsIso (pushout.inr (𝟙 S) a) :=
    (IsPushout.of_hasPushout (𝟙 S) a).isIso_inr_of_isIso
  let e₁ : G.obj (Under.mk (𝟙 S)) ≅ X := (asIso (pushout.inr (𝟙 S) a)).symm
  let e₂ : G.obj (Under.mk p) ≅ Z := sq.flip.isoPushout.symm
  have hi₁ : pushout.inr (𝟙 S) a ≫ e₁.hom = 𝟙 X :=
    (asIso (pushout.inr (𝟙 S) a)).hom_inv_id
  have hi₂ : pushout.inr p a ≫ e₂.hom = q := sq.flip.inr_isoPushout_inv
  have hG : pushout.inr (𝟙 S) a ≫ G.map ε = pushout.inr p a :=
    Under.w ((Under.pushout a).map ε)
  have hArrow : e₁.hom ≫ q = G.map ε ≫ e₂.hom := by
    apply (cancel_epi (pushout.inr (𝟙 S) a)).1
    calc
      pushout.inr (𝟙 S) a ≫ (e₁.hom ≫ q) =
          (pushout.inr (𝟙 S) a ≫ e₁.hom) ≫ q := (Category.assoc _ _ _).symm
      _ = (𝟙 X) ≫ q := congrArg (fun t => t ≫ q) hi₁
      _ = q := Category.id_comp q
      _ = pushout.inr p a ≫ e₂.hom := hi₂.symm
      _ = (pushout.inr (𝟙 S) a ≫ G.map ε) ≫ e₂.hom :=
        (congrArg (fun t => t ≫ e₂.hom) hG).symm
      _ = pushout.inr (𝟙 S) a ≫ (G.map ε ≫ e₂.hom) := Category.assoc _ _ _
  let eArrow : Arrow.mk (G.map ε) ≅ Arrow.mk q := Arrow.isoMk e₁ e₂ hArrow
  exact mapped.ofArrowIso eArrow

end CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape
