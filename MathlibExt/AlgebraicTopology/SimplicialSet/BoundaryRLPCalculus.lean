/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.GenuineTrivialFibrations

/-!
# Boundary lifting under composition and trivial base change

Cancellation of boundary lifting is used only when the remaining map is a
genuine categorical fibration. The proof uses the existing categorical
weak equivalences and boundary weak factorization system. Base-change
reflection here is along a boundary-trivial map, and does not use right
properness of a model structure.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MorphismProperty

namespace SSet

/-- Postcomposition by a boundary-trivial map detects boundary lifting for a categorical fibration. -/
theorem rlp_I_comp_iff_of_postcomp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : categoricalFibrations f) (hg : modelCategoryQuillen.I.rlp g) :
    modelCategoryQuillen.I.rlp (f ≫ g) ↔ modelCategoryQuillen.I.rlp f := by
  constructor
  · intro hfg
    apply (categoricalFibrations_and_categoricalEquivalences_iff f).mp
    refine ⟨hf, ?_⟩
    exact categoricalEquivalences.of_postcomp f g
      (modelCategoryQuillen_I_rlp_le_categoricalEquivalences _ hg)
      (modelCategoryQuillen_I_rlp_le_categoricalEquivalences _ hfg)
  · intro h
    exact modelCategoryQuillen.I.rlp.comp_mem f g h hg

/-- Precomposition by a boundary-trivial map detects boundary lifting for a categorical fibration. -/
theorem rlp_I_comp_iff_of_precomp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : modelCategoryQuillen.I.rlp f) (hg : categoricalFibrations g) :
    modelCategoryQuillen.I.rlp (f ≫ g) ↔ modelCategoryQuillen.I.rlp g := by
  constructor
  · intro hfg
    apply (categoricalFibrations_and_categoricalEquivalences_iff g).mp
    refine ⟨hg, ?_⟩
    exact categoricalEquivalences.of_precomp f g
      (modelCategoryQuillen_I_rlp_le_categoricalEquivalences _ hf)
      (modelCategoryQuillen_I_rlp_le_categoricalEquivalences _ hfg)
  · intro h
    exact modelCategoryQuillen.I.rlp.comp_mem f g hf h

/-- A trivial base change detects boundary lifting of the original categorical fibration. -/
theorem rlp_I_iff_of_trivial_baseChange {P X A B : SSet.{u}}
    {r : P ⟶ X} {q : P ⟶ A} {p : X ⟶ B} {s : A ⟶ B}
    (h : IsPullback r q p s) (hp : categoricalFibrations p)
    (hs : modelCategoryQuillen.I.rlp s) :
    modelCategoryQuillen.I.rlp q ↔ modelCategoryQuillen.I.rlp p := by
  constructor
  · intro hq
    have hr : modelCategoryQuillen.I.rlp r :=
      IsStableUnderBaseChange.of_isPullback h.flip hs
    have hcomp : modelCategoryQuillen.I.rlp (r ≫ p) := by
      rw [h.w]
      exact modelCategoryQuillen.I.rlp.comp_mem q s hq hs
    exact (rlp_I_comp_iff_of_precomp r p hr hp).mp hcomp
  · exact fun hp' => IsStableUnderBaseChange.of_isPullback h hp'

end SSet
