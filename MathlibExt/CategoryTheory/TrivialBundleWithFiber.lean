/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/-- Fixed-fiber product presentation of a map.

For a fixed fiber `F` and a map `p : E ⟶ B`, this packages a second
projection `r : E ⟶ F` together with the limit structure exhibiting `E`
as the binary product `B × F`. Only the fixed fiber is claimed; no chart
beyond this single presentation, no gluing, and no model structure. -/
structure TrivialBundleWithFiber (F : C) {E B : C} (p : E ⟶ B) where
  /-- Second projection to the fixed fiber. -/
  r : E ⟶ F
  /-- The two projections exhibit `E` as the product `B × F`. -/
  isLimit : IsLimit (BinaryFan.mk p r)

namespace TrivialBundleWithFiber

variable {F : C} {E B : C} {p : E ⟶ B}

@[ext]
theorem ext {h1 h2 : TrivialBundleWithFiber F p} (hr : h1.r = h2.r) :
    h1 = h2 := by
  obtain ⟨r1, l1⟩ := h1
  obtain ⟨r2, l2⟩ := h2
  simp only at hr
  subst hr
  cases Subsingleton.elim l1 l2
  rfl

/-- Pullback transport of a fixed-fiber presentation.

Given `h` on `p : E ⟶ B` and a pullback square `sq` presenting `q : P ⟶ B'`
over `p` along `f : B' ⟶ B`, this returns the presentation of `q` with the
same fiber `F` and second projection `s ≫ h.r`. Only the given square and
the parent product limit are used. -/
noncomputable def pullback {F : C} {E B B' : C} {p : E ⟶ B}
    (h : TrivialBundleWithFiber F p) {P : C} {s : P ⟶ E} {q : P ⟶ B'}
    {f : B' ⟶ B} (sq : IsPullback s q p f) :
    TrivialBundleWithFiber F q where
  r := s ≫ h.r
  isLimit := by
    refine BinaryFan.isLimitMk (fun t =>
      sq.lift (BinaryFan.IsLimit.lift h.isLimit (t.fst ≫ f) t.snd) t.fst
        (BinaryFan.IsLimit.lift_fst h.isLimit _ _)) ?fac1 ?fac2 ?uniq
    · intro t
      exact sq.lift_snd _ _ _
    · intro t
      have hLift :
          sq.lift (BinaryFan.IsLimit.lift h.isLimit (t.fst ≫ f) t.snd) t.fst
            (BinaryFan.IsLimit.lift_fst h.isLimit _ _) ≫ s =
            BinaryFan.IsLimit.lift h.isLimit (t.fst ≫ f) t.snd :=
        sq.lift_fst _ _ _
      have hCong :
          (sq.lift (BinaryFan.IsLimit.lift h.isLimit (t.fst ≫ f) t.snd) t.fst
            (BinaryFan.IsLimit.lift_fst h.isLimit _ _) ≫ s) ≫ h.r =
            (BinaryFan.IsLimit.lift h.isLimit (t.fst ≫ f) t.snd) ≫ h.r :=
        congrArg (· ≫ h.r) hLift
      have hSnd :
          (BinaryFan.IsLimit.lift h.isLimit (t.fst ≫ f) t.snd) ≫ h.r = t.snd :=
        BinaryFan.IsLimit.lift_snd _ _ _
      have hAssoc :
          sq.lift (BinaryFan.IsLimit.lift h.isLimit (t.fst ≫ f) t.snd) t.fst
            (BinaryFan.IsLimit.lift_fst h.isLimit _ _) ≫ (s ≫ h.r) =
            (sq.lift (BinaryFan.IsLimit.lift h.isLimit (t.fst ≫ f) t.snd) t.fst
              (BinaryFan.IsLimit.lift_fst h.isLimit _ _) ≫ s) ≫ h.r :=
        (Category.assoc _ _ _).symm
      exact hAssoc.trans (hCong.trans hSnd)
    · intro t m h1 h2
      apply sq.hom_ext
      · have hms : m ≫ s =
            BinaryFan.IsLimit.lift h.isLimit (t.fst ≫ f) t.snd := by
          apply BinaryFan.IsLimit.hom_ext h.isLimit
          · have e1 : (m ≫ s) ≫ p = t.fst ≫ f := by
              calc (m ≫ s) ≫ p = m ≫ (s ≫ p) := by rw [Category.assoc]
                _ = m ≫ (q ≫ f) := by rw [sq.w]
                _ = (m ≫ q) ≫ f := by rw [← Category.assoc]
                _ = t.fst ≫ f := congrArg (· ≫ f) h1
            have e2 : BinaryFan.IsLimit.lift h.isLimit (t.fst ≫ f) t.snd ≫ p =
                t.fst ≫ f :=
              BinaryFan.IsLimit.lift_fst _ _ _
            exact e1.trans e2.symm
          · have g1 : (m ≫ s) ≫ h.r = t.snd :=
              Eq.trans (Category.assoc _ _ _) h2
            have g2 : BinaryFan.IsLimit.lift h.isLimit (t.fst ≫ f) t.snd ≫ h.r =
                t.snd :=
              BinaryFan.IsLimit.lift_snd _ _ _
            exact g1.trans g2.symm
        calc m ≫ s
            = BinaryFan.IsLimit.lift h.isLimit (t.fst ≫ f) t.snd := hms
          _ = sq.lift _ _ _ ≫ s := (sq.lift_fst _ _ _).symm
      · exact Eq.trans h1 (sq.lift_snd _ _ _).symm

end TrivialBundleWithFiber

end CategoryTheory
