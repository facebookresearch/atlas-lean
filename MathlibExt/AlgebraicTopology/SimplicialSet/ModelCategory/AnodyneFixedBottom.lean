/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

/-!
# Fixed-bottom lifting along anodyne extensions

Let `i : X ⟶ Y` be an anodyne extension of simplicial sets in universe `u`, let `p : E ⟶ B`,
and fix `b : Y ⟶ B`. Suppose that for every `σ : Δ[n + 1] ⟶ Y` and every horn index `j`, the
horn inclusion lifts against `p` with bottom map `σ ≫ b`. Then every `a : X ⟶ E` satisfying `a
≫ p = i ≫ b` extends to a map `ℓ : Y ⟶ E` with `i ≫ ℓ = a` and `ℓ ≫ p = b`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet

/-- Let `X, Y, E, B : SSet.{u}`, let `i : X ⟶ Y` be an anodyne extension, and let `p : E ⟶ B` and
`b : Y ⟶ B`. Assume that for every `n : ℕ`, `σ : Δ[n + 1] ⟶ Y`, and `j : Fin (n + 2)`, the
inclusion `(SSet.horn (n + 1) j).ι` has the lifting property against `p` with fixed bottom `σ
≫ b`. Then `HasLiftingPropertyFixedBot i p b`: each `a : X ⟶ E` with `a ≫ p = i ≫ b` admits `ℓ
: Y ⟶ E` satisfying `i ≫ ℓ = a` and `ℓ ≫ p = b`. -/
theorem anodyneExtensions.hasLiftingPropertyFixedBot_of_simplices
    {X Y E B : SSet.{u}} {i : X ⟶ Y}
    (hi : SSet.anodyneExtensions i) (p : E ⟶ B) (b : Y ⟶ B)
    (h : ∀ {n : ℕ} (σ : Δ[n + 1] ⟶ Y) (j : Fin (n + 2)),
      HasLiftingPropertyFixedBot (SSet.horn (n + 1) j).ι p (σ ≫ b)) :
    HasLiftingPropertyFixedBot i p b := by
  have hpull : SSet.modelCategoryQuillen.J.rlp (pullback.snd p b) := by
    intro _ _ _ hhorn
    simp only [SSet.modelCategoryQuillen.J,
      MorphismProperty.iSup_iff] at hhorn
    obtain ⟨n, ⟨j⟩⟩ := hhorn
    constructor
    intro top bottom sq
    have sq' : CommSq (top ≫ pullback.fst p b)
        (SSet.horn (n + 1) j).ι p (bottom ≫ b) := by
      constructor
      calc
        (top ≫ pullback.fst p b) ≫ p =
            top ≫ (pullback.fst p b ≫ p) := by rw [Category.assoc]
        _ = top ≫ (pullback.snd p b ≫ b) := by
          rw [pullback.condition]
        _ = (top ≫ pullback.snd p b) ≫ b := by
          rw [Category.assoc]
        _ = ((SSet.horn (n + 1) j).ι ≫ bottom) ≫ b := by
          rw [sq.w]
        _ = (SSet.horn (n + 1) j).ι ≫ (bottom ≫ b) := by
          rw [Category.assoc]
    let _ : sq'.HasLift := h bottom j (top ≫ pullback.fst p b) sq'
    exact ⟨⟨{
      l := pullback.lift sq'.lift bottom sq'.fac_right
      fac_left := by
        apply pullback.hom_ext
        · simpa only [Category.assoc, pullback.lift_fst] using sq'.fac_left
        · simpa only [Category.assoc, pullback.lift_snd] using sq.w.symm
      fac_right := pullback.lift_snd _ _ _ }⟩⟩
  have hi' : HasLiftingProperty i (pullback.snd p b) := by
    rw [SSet.anodyneExtensions_eq_llp_rlp] at hi
    exact hi _ hpull
  intro top sq
  let topPullback : X ⟶ pullback p b := pullback.lift top i sq.w
  have sqPullback :
      CommSq topPullback i (pullback.snd p b) (𝟙 Y) := by
    constructor
    exact pullback.lift_snd _ _ _
  let _ : HasLiftingProperty i (pullback.snd p b) := hi'
  let _ : sqPullback.HasLift := inferInstance
  exact ⟨⟨{
    l := sqPullback.lift ≫ pullback.fst p b
    fac_left := by
      rw [← Category.assoc, sqPullback.fac_left]
      change pullback.lift top i sq.w ≫ pullback.fst p b = top
      exact pullback.lift_fst _ _ _
    fac_right := by
      calc
        (sqPullback.lift ≫ pullback.fst p b) ≫ p =
            sqPullback.lift ≫ (pullback.fst p b ≫ p) := by
              rw [Category.assoc]
        _ = sqPullback.lift ≫ (pullback.snd p b ≫ b) := by
              rw [pullback.condition]
        _ = (sqPullback.lift ≫ pullback.snd p b) ≫ b := by
              rw [Category.assoc]
        _ = (𝟙 Y) ≫ b := by rw [sqPullback.fac_right]
        _ = b := Category.id_comp _ }⟩⟩

end SSet
