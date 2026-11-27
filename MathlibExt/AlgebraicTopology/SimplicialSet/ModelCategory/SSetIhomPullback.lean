/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetIhomZero

/-!
This module defines the internal-hom pullback comparison and the target vertex
associated to a commuting square. It requires no fibrancy or model hypotheses
and leaves fiber and lifting results to later files.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial SSet
open scoped Simplicial

namespace SSet

variable {A B X Y : SSet.{u}}

/-- Canonical map into the pullback controlling the pushout-product adjunction. -/
noncomputable abbrev ihomToPullback (i : A ⟶ B) (p : X ⟶ Y) :
    (ihom B).obj X ⟶ pullback ((ihom A).map p) ((pre i).app Y) :=
  pullback.lift ((pre i).app X) ((ihom B).map p) (pre_comm_ihom_map i p)

/-- Zero-simplex of the pullback target associated to a commuting square. -/
noncomputable def ihomToPullbackTgt₀Mk {i : A ⟶ B} {p : X ⟶ Y}
    {t : A ⟶ X} {b : B ⟶ Y} (sq : CommSq t i p b) :
    (pullback ((ihom A).map p) ((pre i).app Y) : SSet.{u}) _⦋0⦌ :=
  yonedaEquiv
    (pullback.lift
      (yonedaEquiv.symm ((ihom₀Equiv A X).symm t))
      (yonedaEquiv.symm ((ihom₀Equiv B Y).symm b))
      (by
        calc (yonedaEquiv.symm ((ihom₀Equiv A X).symm t) : Δ[0] ⟶ _) ≫ (ihom A).map p
            = yonedaEquiv.symm (((ihom A).map p).app _ ((ihom₀Equiv A X).symm t)) := by
              rw [yonedaEquiv_symm_comp]
          _ = yonedaEquiv.symm ((ihom₀Equiv A Y).symm (t ≫ p)) := by
              rw [← ihom₀Equiv_symm_map]
          _ = yonedaEquiv.symm ((ihom₀Equiv A Y).symm (i ≫ b)) := by rw [sq.w]
          _ = yonedaEquiv.symm (((pre i).app Y).app _ ((ihom₀Equiv B Y).symm b)) := by
              rw [ihom₀Equiv_symm_pre]
          _ = _ := by rw [← yonedaEquiv_symm_comp]))

@[simp]
theorem pullback_fst_app_ihomToPullbackTgt₀Mk {i : A ⟶ B} {p : X ⟶ Y}
    {t : A ⟶ X} {b : B ⟶ Y} (sq : CommSq t i p b) :
    (pullback.fst ((ihom A).map p) ((pre i).app Y)).app _ (ihomToPullbackTgt₀Mk sq) =
      (ihom₀Equiv A X).symm t := by
  simp only [ihomToPullbackTgt₀Mk, ← yonedaEquiv_comp, pullback.lift_fst,
    Equiv.apply_symm_apply]

@[simp]
theorem pullback_snd_app_ihomToPullbackTgt₀Mk {i : A ⟶ B} {p : X ⟶ Y}
    {t : A ⟶ X} {b : B ⟶ Y} (sq : CommSq t i p b) :
    (pullback.snd ((ihom A).map p) ((pre i).app Y)).app _ (ihomToPullbackTgt₀Mk sq) =
      (ihom₀Equiv B Y).symm b := by
  simp only [ihomToPullbackTgt₀Mk, ← yonedaEquiv_comp, pullback.lift_snd,
    Equiv.apply_symm_apply]

/-- Every zero-simplex of the pullback target arises from a commuting square. -/
theorem ihomToPullbackTgt₀Mk_surjective (i : A ⟶ B) (p : X ⟶ Y)
    (x : (pullback ((ihom A).map p) ((pre i).app Y) : SSet.{u}) _⦋0⦌) :
    ∃ (t : A ⟶ X) (b : B ⟶ Y) (sq : CommSq t i p b),
      ihomToPullbackTgt₀Mk sq = x := by
  let qA : ((ihom A).obj X : SSet.{u}) _⦋0⦌ :=
    (pullback.fst ((ihom A).map p) ((pre i).app Y)).app _ x
  let qB : ((ihom B).obj Y : SSet.{u}) _⦋0⦌ :=
    (pullback.snd ((ihom A).map p) ((pre i).app Y)).app _ x
  let t : A ⟶ X := ihom₀Equiv A X qA
  let b : B ⟶ Y := ihom₀Equiv B Y qB
  have ht_eq : t = ihom₀Equiv A X qA := rfl
  have hb_eq : b = ihom₀Equiv B Y qB := rfl
  have hqA_sym : (ihom₀Equiv A X).symm t = qA := by
    rw [ht_eq]; exact Equiv.symm_apply_apply _ _
  have hqB_sym : (ihom₀Equiv B Y).symm b = qB := by
    rw [hb_eq]; exact Equiv.symm_apply_apply _ _
  have hqA : qA = (ihom₀Equiv A X).symm t := hqA_sym.symm
  have hqB : qB = (ihom₀Equiv B Y).symm b := hqB_sym.symm
  have hf : yonedaEquiv.symm x ≫ pullback.fst ((ihom A).map p) ((pre i).app Y) =
      yonedaEquiv.symm qA := by
    apply yonedaEquiv.injective
    calc yonedaEquiv (yonedaEquiv.symm x ≫ pullback.fst ((ihom A).map p) ((pre i).app Y))
        = (pullback.fst ((ihom A).map p) ((pre i).app Y)).app _
            (yonedaEquiv (yonedaEquiv.symm x)) := by rw [yonedaEquiv_comp]
      _ = (pullback.fst ((ihom A).map p) ((pre i).app Y)).app _ x := by
            rw [Equiv.apply_symm_apply]
      _ = qA := rfl
      _ = yonedaEquiv (yonedaEquiv.symm qA) := (Equiv.apply_symm_apply _ _).symm
  have hg : yonedaEquiv.symm x ≫ pullback.snd ((ihom A).map p) ((pre i).app Y) =
      yonedaEquiv.symm qB := by
    apply yonedaEquiv.injective
    calc yonedaEquiv (yonedaEquiv.symm x ≫ pullback.snd ((ihom A).map p) ((pre i).app Y))
        = (pullback.snd ((ihom A).map p) ((pre i).app Y)).app _
            (yonedaEquiv (yonedaEquiv.symm x)) := by rw [yonedaEquiv_comp]
      _ = (pullback.snd ((ihom A).map p) ((pre i).app Y)).app _ x := by
            rw [Equiv.apply_symm_apply]
      _ = qB := rfl
      _ = yonedaEquiv (yonedaEquiv.symm qB) := (Equiv.apply_symm_apply _ _).symm
  have hmap : ((ihom A).map p).app _ qA = ((pre i).app Y).app _ qB := by
    have hcond : pullback.fst ((ihom A).map p) ((pre i).app Y) ≫ (ihom A).map p =
        pullback.snd ((ihom A).map p) ((pre i).app Y) ≫ (pre i).app Y :=
      pullback.condition
    have hsym : yonedaEquiv.symm (((ihom A).map p).app _ qA) =
        yonedaEquiv.symm (((pre i).app Y).app _ qB) := by
      calc yonedaEquiv.symm (((ihom A).map p).app _ qA)
          = yonedaEquiv.symm qA ≫ (ihom A).map p := by rw [← yonedaEquiv_symm_comp]
        _ = (yonedaEquiv.symm x ≫ pullback.fst ((ihom A).map p) ((pre i).app Y)) ≫
              (ihom A).map p := by rw [hf]
        _ = yonedaEquiv.symm x ≫ (pullback.fst ((ihom A).map p) ((pre i).app Y) ≫
              (ihom A).map p) := by rw [Category.assoc]
        _ = yonedaEquiv.symm x ≫ (pullback.snd ((ihom A).map p) ((pre i).app Y) ≫
              (pre i).app Y) := by rw [hcond]
        _ = (yonedaEquiv.symm x ≫ pullback.snd ((ihom A).map p) ((pre i).app Y)) ≫
              (pre i).app Y := by rw [← Category.assoc]
        _ = yonedaEquiv.symm qB ≫ (pre i).app Y := by rw [hg]
        _ = yonedaEquiv.symm (((pre i).app Y).app _ qB) := by rw [yonedaEquiv_symm_comp]
    exact (Equiv.injective (yonedaEquiv (X := (ihom A).obj Y)).symm) hsym
  rw [hqA, hqB] at hmap
  have hcomm : t ≫ p = i ≫ b := by
    have hsym : (ihom₀Equiv A Y).symm (t ≫ p) = (ihom₀Equiv A Y).symm (i ≫ b) := by
      calc (ihom₀Equiv A Y).symm (t ≫ p)
          = ((ihom A).map p).app _ ((ihom₀Equiv A X).symm t) := by rw [ihom₀Equiv_symm_map]
        _ = ((pre i).app Y).app _ ((ihom₀Equiv B Y).symm b) := hmap
        _ = (ihom₀Equiv A Y).symm (i ≫ b) := by rw [ihom₀Equiv_symm_pre]
    exact (Equiv.injective (ihom₀Equiv A Y).symm) hsym
  let sq : CommSq t i p b := ⟨hcomm⟩
  have heq : yonedaEquiv.symm (ihomToPullbackTgt₀Mk sq) = yonedaEquiv.symm x := by
    apply pullback.hom_ext
    · calc yonedaEquiv.symm (ihomToPullbackTgt₀Mk sq) ≫
            pullback.fst ((ihom A).map p) ((pre i).app Y)
          = yonedaEquiv.symm ((ihom₀Equiv A X).symm t) := by
            simp only [ihomToPullbackTgt₀Mk, Equiv.symm_apply_apply, pullback.lift_fst]
        _ = yonedaEquiv.symm qA := by rw [hqA_sym]
        _ = yonedaEquiv.symm x ≫ pullback.fst ((ihom A).map p) ((pre i).app Y) := hf.symm
    · calc yonedaEquiv.symm (ihomToPullbackTgt₀Mk sq) ≫
            pullback.snd ((ihom A).map p) ((pre i).app Y)
          = yonedaEquiv.symm ((ihom₀Equiv B Y).symm b) := by
            simp only [ihomToPullbackTgt₀Mk, Equiv.symm_apply_apply, pullback.lift_snd]
        _ = yonedaEquiv.symm qB := by rw [hqB_sym]
        _ = yonedaEquiv.symm x ≫ pullback.snd ((ihom A).map p) ((pre i).app Y) := hg.symm
  refine ⟨t, b, sq, ?_⟩
  have : yonedaEquiv (yonedaEquiv.symm (ihomToPullbackTgt₀Mk sq)) =
      yonedaEquiv (yonedaEquiv.symm x) := by rw [heq]
  simp only [Equiv.apply_symm_apply] at this
  exact this

end SSet
