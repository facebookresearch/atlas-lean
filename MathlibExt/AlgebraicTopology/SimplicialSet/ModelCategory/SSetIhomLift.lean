/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetIhomPullback
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Fiber

/-!
# Bridge between lifting squares and the strict fiber of `ihomToPullback`

This file provides the smallest reusable zero-simplex bridge between a commuting
square `sq : CommSq t i p b` and the strict fiber of `ihomToPullback i p` over
`ihomToPullbackTgt₀Mk sq`. Public surface: projection formulas for
`(ihomToPullback i p).app _ a` via `ihom₀Equiv`, a fiber-membership iff at
`0`-simplices given by the two diagonal equations for `l := ihom₀Equiv B X a`,
and the equivalence `sq.HasLift ↔ fiber ≠ ⊥`.

No fibrancy, cofibrancy, Kan, or model-structure hypotheses are used.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial SSet Opposite
open scoped Simplicial

namespace SSet

variable {A B X Y : SSet.{u}}

/-- First projection of `(ihomToPullback i p).app _ a` at degree zero. -/
theorem pullback_fst_app_ihomToPullback (i : A ⟶ B) (p : X ⟶ Y)
    (a : ((ihom B).obj X) _⦋0⦌) :
    (pullback.fst ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _
        ((ihomToPullback i p).app _ a) =
      (ihom₀Equiv A X).symm (i ≫ ihom₀Equiv B X a) := by
  apply (Equiv.injective (yonedaEquiv (X := (ihom A).obj X)).symm)
  calc yonedaEquiv.symm ((pullback.fst ((ihom A).map p)
          ((MonoidalClosed.pre i).app Y)).app _
          ((ihomToPullback i p).app _ a))
      = yonedaEquiv.symm ((ihomToPullback i p).app _ a) ≫
          pullback.fst ((ihom A).map p) ((MonoidalClosed.pre i).app Y) := by
        rw [← yonedaEquiv_symm_comp]
    _ = yonedaEquiv.symm a ≫ (ihomToPullback i p ≫
          pullback.fst ((ihom A).map p) ((MonoidalClosed.pre i).app Y)) := by
        rw [← yonedaEquiv_symm_comp, Category.assoc]
    _ = yonedaEquiv.symm a ≫ (MonoidalClosed.pre i).app X := by
        rw [ihomToPullback, pullback.lift_fst]
    _ = yonedaEquiv.symm (((MonoidalClosed.pre i).app X).app _ a) := by
        rw [yonedaEquiv_symm_comp]
    _ = yonedaEquiv.symm ((ihom₀Equiv A X).symm (i ≫ ihom₀Equiv B X a)) := by
        have : ((MonoidalClosed.pre i).app X).app _ a =
          ((MonoidalClosed.pre i).app X).app _
            ((ihom₀Equiv B X).symm (ihom₀Equiv B X a)) := by
          rw [Equiv.symm_apply_apply]
        rw [this, ← ihom₀Equiv_symm_pre]

/-- Second projection of `(ihomToPullback i p).app _ a` at degree zero. -/
theorem pullback_snd_app_ihomToPullback (i : A ⟶ B) (p : X ⟶ Y)
    (a : ((ihom B).obj X) _⦋0⦌) :
    (pullback.snd ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _
        ((ihomToPullback i p).app _ a) =
      (ihom₀Equiv B Y).symm ((ihom₀Equiv B X a) ≫ p) := by
  calc (pullback.snd ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _
          ((ihomToPullback i p).app _ a)
      = (ihomToPullback i p ≫
          pullback.snd ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _ a := rfl
    _ = ((ihom B).map p).app _ a := by
        rw [ihomToPullback, pullback.lift_snd]
    _ = ((ihom B).map p).app _ ((ihom₀Equiv B X).symm (ihom₀Equiv B X a)) := by
        rw [Equiv.symm_apply_apply]
    _ = (ihom₀Equiv B Y).symm ((ihom₀Equiv B X a) ≫ p) := by
        rw [ihom₀Equiv_symm_map]

/-- Membership in the strict fiber of `ihomToPullback` over `ihomToPullbackTgt₀Mk sq`
at `0`-simplices: `a` lies in the fiber iff for `l := ihom₀Equiv B X a`,
`i ≫ l = t` and `l ≫ p = b`. -/
theorem mem_fiber_ihomToPullback_zero_iff {i : A ⟶ B} {p : X ⟶ Y}
    {t : A ⟶ X} {b : B ⟶ Y} (sq : CommSq t i p b)
    (a : ((ihom B).obj X) _⦋0⦌) :
    a ∈ (Subcomplex.fiber (ihomToPullback i p) (ihomToPullbackTgt₀Mk sq)).obj (op ⦋0⦌) ↔
      i ≫ ihom₀Equiv B X a = t ∧ ihom₀Equiv B X a ≫ p = b := by
  rw [Subcomplex.mem_fiber_obj_zero_iff]
  constructor
  · intro h_eq
    have h_fst :
        (pullback.fst ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _
            ((ihomToPullback i p).app _ a) =
          (pullback.fst ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _
            (ihomToPullbackTgt₀Mk sq) := by rw [h_eq]
    have h_snd :
        (pullback.snd ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _
            ((ihomToPullback i p).app _ a) =
          (pullback.snd ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _
            (ihomToPullbackTgt₀Mk sq) := by rw [h_eq]
    rw [pullback_fst_app_ihomToPullback,
      pullback_fst_app_ihomToPullbackTgt₀Mk] at h_fst
    rw [pullback_snd_app_ihomToPullback,
      pullback_snd_app_ihomToPullbackTgt₀Mk] at h_snd
    exact ⟨(Equiv.injective (ihom₀Equiv A X).symm) h_fst,
      (Equiv.injective (ihom₀Equiv B Y).symm) h_snd⟩
  · intro ⟨h_left, h_right⟩
    have h_fst_eq :
        (pullback.fst ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _
            ((ihomToPullback i p).app _ a) =
          (pullback.fst ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _
            (ihomToPullbackTgt₀Mk sq) := by
      rw [pullback_fst_app_ihomToPullback, pullback_fst_app_ihomToPullbackTgt₀Mk,
        h_left]
    have h_snd_eq :
        (pullback.snd ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _
            ((ihomToPullback i p).app _ a) =
          (pullback.snd ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _
            (ihomToPullbackTgt₀Mk sq) := by
      rw [pullback_snd_app_ihomToPullback, pullback_snd_app_ihomToPullbackTgt₀Mk,
        h_right]
    have h_yoneda_fst :
        yonedaEquiv.symm ((ihomToPullback i p).app _ a) ≫
            pullback.fst ((ihom A).map p) ((MonoidalClosed.pre i).app Y) =
          yonedaEquiv.symm (ihomToPullbackTgt₀Mk sq) ≫
            pullback.fst ((ihom A).map p) ((MonoidalClosed.pre i).app Y) := by
      rw [yonedaEquiv_symm_comp, yonedaEquiv_symm_comp, h_fst_eq]
    have h_yoneda_snd :
        yonedaEquiv.symm ((ihomToPullback i p).app _ a) ≫
            pullback.snd ((ihom A).map p) ((MonoidalClosed.pre i).app Y) =
          yonedaEquiv.symm (ihomToPullbackTgt₀Mk sq) ≫
            pullback.snd ((ihom A).map p) ((MonoidalClosed.pre i).app Y) := by
      rw [yonedaEquiv_symm_comp, yonedaEquiv_symm_comp, h_snd_eq]
    have h_hom :
        yonedaEquiv.symm ((ihomToPullback i p).app _ a) =
          yonedaEquiv.symm (ihomToPullbackTgt₀Mk sq) := by
      apply pullback.hom_ext
      · exact h_yoneda_fst
      · exact h_yoneda_snd
    exact (Equiv.injective (yonedaEquiv (X :=
      pullback ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).symm)) h_hom

private theorem subcomplex_ne_bot_iff_exists_zero {Z : SSet.{u}}
    (S : Z.Subcomplex) :
    S ≠ ⊥ ↔ ∃ x : Z _⦋0⦌, x ∈ S.obj (op ⦋0⦌) := by
  constructor
  · intro h_ne
    by_contra h_none
    have h_le : S ≤ ⊥ := by
      intro n x hx
      have : Z.map (SimplexCategory.const ⦋0⦌ n.unop 0).op x ∈ S.obj (op ⦋0⦌) :=
        S.map _ hx
      exact (h_none ⟨_, this⟩).elim
    exact h_ne (le_antisymm h_le bot_le)
  · rintro ⟨x, hx⟩ rfl
    simp at hx

private theorem fiber_ne_bot_iff_exists_zero {Z W : SSet.{u}} (f : Z ⟶ W)
    (w : W _⦋0⦌) :
    Subcomplex.fiber f w ≠ ⊥ ↔ ∃ x : Z _⦋0⦌, x ∈ (Subcomplex.fiber f w).obj (op ⦋0⦌) :=
  subcomplex_ne_bot_iff_exists_zero _

/-- A square has a diagonal lift iff the strict fiber of `ihomToPullback` over its
associated target vertex is not bottom. -/
theorem hasLift_iff_fiber_ihomToPullback_ne_bot {i : A ⟶ B} {p : X ⟶ Y}
    {t : A ⟶ X} {b : B ⟶ Y} (sq : CommSq t i p b) :
    sq.HasLift ↔
      Subcomplex.fiber (ihomToPullback i p) (ihomToPullbackTgt₀Mk sq) ≠ ⊥ := by
  rw [fiber_ne_bot_iff_exists_zero]
  constructor
  · intro h_lift
    obtain ⟨l_struct⟩ := h_lift.exists_lift
    let l : B ⟶ X := l_struct.l
    have h_left : i ≫ l = t := l_struct.fac_left
    have h_right : l ≫ p = b := l_struct.fac_right
    let a : ((ihom B).obj X) _⦋0⦌ := (ihom₀Equiv B X).symm l
    have ha : ihom₀Equiv B X a = l := Equiv.apply_symm_apply _ _
    exact ⟨a, by rw [mem_fiber_ihomToPullback_zero_iff, ha]; exact ⟨h_left, h_right⟩⟩
  · intro ⟨a, ha⟩
    rw [mem_fiber_ihomToPullback_zero_iff] at ha
    exact ⟨⟨⟨ihom₀Equiv B X a, ha.1, ha.2⟩⟩⟩

end SSet
