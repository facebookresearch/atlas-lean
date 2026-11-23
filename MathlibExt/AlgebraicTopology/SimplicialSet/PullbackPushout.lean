/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Pullback maps and monic pushouts of simplicial sets

Constructs maps between pullbacks induced by a factorization of one leg and
computes their two projections. Shows that base change of a pushout of
simplicial sets with a monic leg remains a pushout.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

public section

namespace SSet

/-- The map between actual pullbacks induced by one commuting base leg. -/
def pullbackLegMap {A B Y Z : SSet.{u}}
    (f : A ⟶ Y) (g : B ⟶ Y) (p : Z ⟶ Y) (s : A ⟶ B) (hs : f = s ≫ g) :
    pullback f p ⟶ pullback g p :=
  pullback.lift (pullback.fst f p ≫ s) (pullback.snd f p) (by
    calc
      (pullback.fst f p ≫ s) ≫ g = pullback.fst f p ≫ (s ≫ g) := Category.assoc _ _ _
      _ = pullback.fst f p ≫ f := congrArg (fun h => pullback.fst f p ≫ h) hs.symm
      _ = pullback.snd f p ≫ p := pullback.condition (f := f) (g := p))

/-- The source projection retains the original base leg. -/
theorem pullbackLegMap_fst {A B Y Z : SSet.{u}}
    (f : A ⟶ Y) (g : B ⟶ Y) (p : Z ⟶ Y) (s : A ⟶ B) (hs : f = s ≫ g) :
    pullbackLegMap f g p s hs ≫ pullback.fst g p = pullback.fst f p ≫ s := by
  exact pullback.lift_fst _ _ _

/-- The second projection is unchanged by the induced leg map. -/
theorem pullbackLegMap_snd {A B Y Z : SSet.{u}}
    (f : A ⟶ Y) (g : B ⟶ Y) (p : Z ⟶ Y) (s : A ⟶ B) (hs : f = s ≫ g) :
    pullbackLegMap f g p s hs ≫ pullback.snd g p = pullback.snd f p := by
  exact pullback.lift_snd _ _ _

/-- The induced leg forms the actual pullback square over the base leg. -/
theorem pullbackLegMap_isPullback {A B Y Z : SSet.{u}}
    (f : A ⟶ Y) (g : B ⟶ Y) (p : Z ⟶ Y) (s : A ⟶ B) (hs : f = s ≫ g) :
    IsPullback (pullbackLegMap f g p s hs) (pullback.fst f p) (pullback.fst g p) s := by
  have hOuter : IsPullback (pullbackLegMap f g p s hs ≫ pullback.snd g p)
      (pullback.fst f p) p (s ≫ g) := by
    rw [pullbackLegMap_snd, ← hs]
    exact (IsPullback.of_hasPullback f p).flip
  exact IsPullback.of_right hOuter (pullbackLegMap_fst f g p s hs)
    (IsPullback.of_hasPullback g p).flip

/-- Pulling a monic simplicial pushout along an arbitrary base map retains
its entire pushout square, using simplicial Van Kampen stability. -/
theorem pullbackLegPushout {A B C D Y Z : SSet.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {i : C ⟶ D}
    [Mono f] (sq : IsPushout f g h i) (c : D ⟶ Y) (p : Z ⟶ Y)
    (bY : B ⟶ Y) (cY : C ⟶ Y) (hbY : bY = h ≫ c) (hcY : cY = i ≫ c) :
    let aY := g ≫ cY
    let haY : aY = f ≫ bY :=
      (congrArg (fun t => g ≫ t) hcY).trans
        ((Category.assoc g i c).symm.trans
          ((congrArg (fun t => t ≫ c) sq.w.symm).trans
            ((Category.assoc f h c).trans (congrArg (fun t => f ≫ t) hbY.symm))))
    IsPushout
      (pullbackLegMap aY bY p f haY)
      (pullbackLegMap aY cY p g rfl)
      (pullbackLegMap bY c p h hbY)
      (pullbackLegMap cY c p i hcY) := by
  dsimp only
  let aY : A ⟶ Y := g ≫ cY
  let haY : aY = f ≫ bY :=
    (congrArg (fun t => g ≫ t) hcY).trans
      ((Category.assoc g i c).symm.trans
        ((congrArg (fun t => t ≫ c) sq.w.symm).trans
          ((Category.assoc f h c).trans (congrArg (fun t => f ≫ t) hbY.symm))))
  let F := pullbackLegMap aY bY p f haY
  let G := pullbackLegMap aY cY p g rfl
  let H := pullbackLegMap bY c p h hbY
  let I := pullbackLegMap cY c p i hcY
  have hf : IsPullback F (pullback.fst aY p) (pullback.fst bY p) f :=
    pullbackLegMap_isPullback aY bY p f haY
  have hg : IsPullback G (pullback.fst aY p) (pullback.fst cY p) g :=
    pullbackLegMap_isPullback aY cY p g rfl
  have hh : IsPullback H (pullback.fst bY p) (pullback.fst c p) h :=
    pullbackLegMap_isPullback bY c p h hbY
  have hi : IsPullback I (pullback.fst cY p) (pullback.fst c p) i :=
    pullbackLegMap_isPullback cY c p i hcY
  have hw : F ≫ H = G ≫ I := by
    apply pullback.hom_ext
    · have hl : (F ≫ H) ≫ pullback.fst c p = pullback.fst aY p ≫ (f ≫ h) :=
        (Category.assoc F H (pullback.fst c p)).trans
          ((congrArg (fun t => F ≫ t) hh.w).trans
            ((Category.assoc F (pullback.fst bY p) h).symm.trans
              ((congrArg (fun t => t ≫ h) hf.w).trans
                (Category.assoc (pullback.fst aY p) f h))))
      have hr : (G ≫ I) ≫ pullback.fst c p = pullback.fst aY p ≫ (g ≫ i) :=
        (Category.assoc G I (pullback.fst c p)).trans
          ((congrArg (fun t => G ≫ t) hi.w).trans
            ((Category.assoc G (pullback.fst cY p) i).symm.trans
              ((congrArg (fun t => t ≫ i) hg.w).trans
                (Category.assoc (pullback.fst aY p) g i))))
      exact hl.trans ((congrArg (fun t => pullback.fst aY p ≫ t) sq.w).trans hr.symm)
    · have hl : (F ≫ H) ≫ pullback.snd c p = pullback.snd aY p :=
        (Category.assoc F H (pullback.snd c p)).trans
          ((congrArg (fun t => F ≫ t) (pullbackLegMap_snd bY c p h hbY)).trans
            (pullbackLegMap_snd aY bY p f haY))
      have hr : (G ≫ I) ≫ pullback.snd c p = pullback.snd aY p :=
        (Category.assoc G I (pullback.snd c p)).trans
          ((congrArg (fun t => G ≫ t) (pullbackLegMap_snd cY c p i hcY)).trans
            (pullbackLegMap_snd aY cY p g rfl))
      exact hl.trans hr.symm
  exact ((Adhesive.van_kampen sq) F G H I
    (pullback.fst aY p) (pullback.fst bY p) (pullback.fst cY p) (pullback.fst c p)
    hf hg hh.toCommSq hi.toCommSq ⟨hw⟩).mpr ⟨hh, hi⟩

end SSet

end
