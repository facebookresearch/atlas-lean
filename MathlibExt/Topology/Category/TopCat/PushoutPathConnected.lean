/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Connected.PathConnected

/-!
# Path connectivity of topological pushouts

The canonical pushout of `i : A ⟶ B` and `g : A ⟶ X` is path connected when
`X` is path connected and every point of `B` can be joined to a point in the
image of `i`. This applies to a disjoint union of cells when every cell is
path connected and its boundary is nonempty.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits

universe u

namespace TopCat

/-- The canonical pushout is path connected if the original space `X` is
path connected and every point of the attached space `B` joins the image of
the attaching domain `A`. -/
theorem pathConnectedSpace_pushout_of_joined_to_boundary
    {A B X : TopCat.{u}} (i : A ⟶ B) (g : A ⟶ X)
    [PathConnectedSpace X]
    (hB : ∀ b : B, ∃ a : A, Joined b (i a)) :
    PathConnectedSpace (pushout i g : TopCat.{u}) := by
  classical
  let jB : B ⟶ (pushout i g : TopCat.{u}) := pushout.inl i g
  let jX : X ⟶ (pushout i g : TopCat.{u}) := pushout.inr i g
  have sq : IsPushout i g jB jX := IsPushout.of_hasPushout i g
  have hglue (a : A) : jB (i a) = jX (g a) := by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom sq.w a
  have hJoinX (y : (pushout i g : TopCat.{u})) : ∃ x : X, Joined y (jX x) := by
    rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) y with
      ⟨b, hb⟩ | ⟨x, hx⟩
    · change jB b = y at hb
      obtain ⟨a, ha⟩ := hB b
      have hp : Joined (jB b) (jB (i a)) := ha.map jB.hom.continuous
      rw [hb, hglue a] at hp
      exact ⟨g a, hp⟩
    · change jX x = y at hx
      refine ⟨x, ?_⟩
      rw [← hx]
  refine { nonempty := ?_, joined := ?_ }
  · obtain ⟨x⟩ := (PathConnectedSpace.nonempty : Nonempty X)
    exact ⟨jX x⟩
  · intro y z
    obtain ⟨x, hx⟩ := hJoinX y
    obtain ⟨x', hx'⟩ := hJoinX z
    have hp : Joined (jX x) (jX x') :=
      (PathConnectedSpace.joined x x').map jX.hom.continuous
    exact hx.trans (hp.trans hx'.symm)

end TopCat
