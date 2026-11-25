/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.MorphismProperty.SharpMaps
import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# Actual weak-fibration pullback comparisons and sharpness

The OTHER cospan leg is replaced by its genuine weak/fibration
factorization. All original corner maps and the complete native pullback
comparison are retained. The sharpness criterion follows from literal
pullback pasting and weak cancellation, using the original model's CM5.
This is the comparison step in Rezk's Proposition 2.7; no sharpness or
derived comparison outcome for a particular application is assumed.
-/

noncomputable section
universe v u
open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The SAME original CM5 first and second maps, read in the weak/fibration classes. -/
def weakFibrationFactorization {A B : C} (f : A ⟶ B) :
    MapFactorizationData (weakEquivalences C) (fibrations C) f :=
  let h := factorizationData (trivialCofibrations C) (fibrations C) f
  { Z := h.Z, i := h.i, p := h.p, fac := h.fac, hi := h.hi.2, hp := h.hp }

/-- The literal full original comparison into the native replaced pullback. -/
def weakFibrationPullbackComparison {P A E B : C} {f : A ⟶ B} {p : E ⟶ B}
    {a : P ⟶ A} {e : P ⟶ E} (sq : CommSq a e f p)
    (h : MapFactorizationData (weakEquivalences C) (fibrations C) f) :
    P ⟶ pullback h.p p :=
  pullback.lift (a ≫ h.i) e ((Category.assoc _ _ _).trans
    ((congrArg (fun g => a ≫ g) h.fac).trans sq.w))

/-- The SAME whole comparison retains the original first map followed by the actual replacement
unit. -/
theorem weakFibrationPullbackComparison_fst {P A E B : C} {f : A ⟶ B} {p : E ⟶ B}
    {a : P ⟶ A} {e : P ⟶ E} (sq : CommSq a e f p)
    (h : MapFactorizationData (weakEquivalences C) (fibrations C) f) :
    weakFibrationPullbackComparison sq h ≫ pullback.fst h.p p = a ≫ h.i :=
  pullback.lift_fst _ _ _

/-- The SAME whole comparison retains the original unreplaced corner map. -/
theorem weakFibrationPullbackComparison_snd {P A E B : C} {f : A ⟶ B} {p : E ⟶ B}
    {a : P ⟶ A} {e : P ⟶ E} (sq : CommSq a e f p)
    (h : MapFactorizationData (weakEquivalences C) (fibrations C) f) :
    weakFibrationPullbackComparison sq h ≫ pullback.snd h.p p = e :=
  pullback.lift_snd _ _ _

/-- For an actual original pullback, the full comparison square is literally the pullback of the
SAME first
replacement map. -/
theorem weakFibrationPullbackComparison_isPullback {P A E B : C} {f : A ⟶ B} {p : E ⟶ B}
    {a : P ⟶ A} {e : P ⟶ E} (sq : IsPullback a e f p)
    (h : MapFactorizationData (weakEquivalences C) (fibrations C) f) :
    IsPullback (weakFibrationPullbackComparison sq.toCommSq h) a (pullback.fst h.p p) h.i := by
  have outer : IsPullback
      (weakFibrationPullbackComparison sq.toCommSq h ≫ pullback.snd h.p p) a p (h.i ≫ h.p) := by
    rw [weakFibrationPullbackComparison_snd, h.fac]
    exact sq.flip
  exact outer.of_right (weakFibrationPullbackComparison_fst sq.toCommSq h)
    (IsPullback.of_hasPullback h.p p).flip

/-- A sharp original map makes every actual weak/fibration pullback comparison weak. -/
theorem sharpMaps_weakFibrationPullbackComparison {P A E B : C} {f : A ⟶ B} {p : E ⟶ B}
    {a : P ⟶ A} {e : P ⟶ E} (hp : sharpMaps (weakEquivalences C) p)
    (sq : IsPullback a e f p)
    (h : MapFactorizationData (weakEquivalences C) (fibrations C) f) :
    weakEquivalences C (weakFibrationPullbackComparison sq.toCommSq h) := by
  have hb : (weakEquivalences C).IsStableUnderBaseChangeAlong (pullback.fst h.p p) :=
    hp (pullback.snd h.p p) h.p (pullback.fst h.p p) (IsPullback.of_hasPullback h.p p)
  exact hb.of_isPullback (weakFibrationPullbackComparison_isPullback sq h).flip h.hi

/-- The actual comparison condition detects full sharpness, retaining ALL original
base maps and ALL weak/fibration replacements in the SAME model. -/
theorem sharpMaps_iff_weakFibrationPullbackComparison {E B : C} (p : E ⟶ B) :
    sharpMaps (weakEquivalences C) p ↔
      ∀ {P A : C} {f : A ⟶ B} {a : P ⟶ A} {e : P ⟶ E}
        (sq : IsPullback a e f p)
        (h : MapFactorizationData (weakEquivalences C) (fibrations C) f),
        weakEquivalences C (weakFibrationPullbackComparison sq.toCommSq h) := by
  constructor
  · intro hp P A f a e sq h
    exact sharpMaps_weakFibrationPullbackComparison hp sq h
  · intro comparisons P A e f a sq
    constructor
    intro A' P' a' k g square hg
    let h := weakFibrationFactorization f
    let h' : MapFactorizationData (weakEquivalences C) (fibrations C) (g ≫ f) :=
      { Z := h.Z, i := g ≫ h.i, p := h.p, fac := (Category.assoc _ _ _).trans
          (congrArg (fun t => g ≫ t) h.fac),
        hi := (weakEquivalences C).comp_mem _ _ hg h.hi, hp := h.hp }
    have outer := square.paste_vert sq
    have comm : k ≫ weakFibrationPullbackComparison sq.toCommSq h =
        weakFibrationPullbackComparison outer.toCommSq h' := by
      apply pullback.hom_ext
      · rw [Category.assoc, weakFibrationPullbackComparison_fst, ← Category.assoc,
          ← square.w, Category.assoc, weakFibrationPullbackComparison_fst]
      · rw [Category.assoc, weakFibrationPullbackComparison_snd,
          weakFibrationPullbackComparison_snd]
    have hc : weakEquivalences C (k ≫ weakFibrationPullbackComparison sq.toCommSq h) :=
      (congrArg (fun t : P' ⟶ pullback h.p p => weakEquivalences C t) comm).mpr
          (comparisons outer h')
    exact (weakEquivalences C).of_postcomp _ _ (comparisons sq h) hc

end HomotopicalAlgebra
