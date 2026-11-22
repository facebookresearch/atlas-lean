/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.GenuineTrivialFibrations

/-!
# Public consumers of the genuine trivial-fibration criterion
-/

@[expose] public section

universe u

open CategoryTheory MorphismProperty MonoidalClosed

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.GenuineTrivialFibrations

/-- A weak genuine categorical fibration lifts against every mono, with
both strict diagonal equations. -/
theorem exists_diagonal {A B X Y : SSet.{u}} (i : A ⟶ B) [Mono i]
    (p : X ⟶ Y) (hF : SSet.categoricalFibrations p)
    (hW : SSet.categoricalEquivalences p)
    {top : A ⟶ X} {bottom : B ⟶ Y} (sq : CommSq top i p bottom) :
    ∃ l : B ⟶ X, i ≫ l = top ∧ l ≫ p = bottom := by
  have hp : SSet.modelCategoryQuillen.I.rlp p :=
    (SSet.categoricalFibrations_and_categoricalEquivalences_iff p).mp ⟨hF, hW⟩
  have hpMono : (monomorphisms SSet.{u}).rlp p := by
    rw [SSet.rlp_monomorphisms]
    exact hp
  have : HasLiftingProperty i p := hpMono i (monomorphisms.infer_property i)
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- The converse provides genuine fibration membership and the actual hFun
equivalence for each quasicategory test object. -/
theorem categorical_fibration_and_hfun_equivalence {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : SSet.modelCategoryQuillen.I.rlp p) (C : SSet.{u})
    (hC : SSet.Quasicategory C) :
    SSet.categoricalFibrations p ∧
      (SSet.hoFunctor.map ((pre p).app C)).toFunctor.IsEquivalence := by
  have h := (SSet.categoricalFibrations_and_categoricalEquivalences_iff p).mpr hp
  exact ⟨h.1, h.2 C hC⟩

end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.GenuineTrivialFibrations
