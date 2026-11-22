/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.RelativePullbackPasting
import MathlibExt.AlgebraicTopology.SimplicialSet.DirectedSliceComparison

/-!
# Boundary lifting for successive original slice restrictions

These are applications of the actual pullback pasting calculus. The base
map, full diagram and both successive restrictions are fixed. The directed
anodyne hypotheses below are verified for the interval and triangle faces
by the existing endpoint-preserving lifting lemmas.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace SSet

private theorem rlp_lift_congr {D X A B : SSet.{u}} (p : X ⟶ B)
    {f f' : D ⟶ X} {g : D ⟶ A} {b b' : A ⟶ B}
    (hf : f = f') (hb : b = b')
    (w : f ≫ p = g ≫ b) (w' : f' ≫ p = g ≫ b') :
    modelCategoryQuillen.I.rlp (pullback.lift f g w) ↔
      modelCategoryQuillen.I.rlp (pullback.lift f' g w') := by
  subst f'
  subst b'
  rfl

end SSet

namespace SSet.sliceUnder

/-- A trivial first under-slice comparison detects the second comparison after pasting. -/
theorem rlp_I_composite_iff_second {K₀ K₁ K₂ X B : SSet.{u}}
    (i : K₀ ⟶ K₁) (j : K₁ ⟶ K₂) [Mono j] (t : K₂ ⟶ X) (p : X ⟶ B)
    [InnerFibration p] [Quasicategory B]
    (hi : modelCategoryQuillen.I.rlp (restrictionComparison i (j ≫ t) p)) :
    modelCategoryQuillen.I.rlp (restrictionComparison (i ≫ j) t p) ↔
      modelCategoryQuillen.I.rlp (restrictionComparison j t p) := by
  unfold restrictionComparison
  refine (SSet.rlp_lift_congr (map X ((i ≫ j) ≫ t) p)
    (restrict_comp X t i j) (restrict_comp B (t ≫ p) i j)
    (restrict_map X t (i ≫ j) p) (by
      rw [← restrict_comp X t i j, restrict_map X t (i ≫ j) p, restrict_comp B (t ≫ p) i j])).trans ?_
  exact RelativePullback.rlp_I_total_iff_second (restrict X (j ≫ t) i) (restrict X t j)
      (map X ((i ≫ j) ≫ t) p) (map X (j ≫ t) p) (map X t p)
      (restrict B (j ≫ t ≫ p) i) (restrict B (t ≫ p) j)
      (restrict_map X (j ≫ t) i p) (restrict_map X t j p) hi
      (categoricalFibration_restrictionComparison j t p)

/-- A trivial second comparison and original base restriction detect the first comparison. -/
theorem rlp_I_composite_iff_first {K₀ K₁ K₂ X B : SSet.{u}}
    (i : K₀ ⟶ K₁) [Mono i] (j : K₁ ⟶ K₂) (t : K₂ ⟶ X) (p : X ⟶ B)
    [InnerFibration p] [Quasicategory B]
    (hj : modelCategoryQuillen.I.rlp (restrictionComparison j t p))
    (hb : modelCategoryQuillen.I.rlp (restrict B (t ≫ p) j)) :
    modelCategoryQuillen.I.rlp (restrictionComparison (i ≫ j) t p) ↔
      modelCategoryQuillen.I.rlp (restrictionComparison i (j ≫ t) p) := by
  unfold restrictionComparison
  refine (SSet.rlp_lift_congr (map X ((i ≫ j) ≫ t) p)
    (restrict_comp X t i j) (restrict_comp B (t ≫ p) i j)
    (restrict_map X t (i ≫ j) p) (by
      rw [← restrict_comp X t i j, restrict_map X t (i ≫ j) p, restrict_comp B (t ≫ p) i j])).trans ?_
  exact RelativePullback.rlp_I_total_iff_first (restrict X (j ≫ t) i) (restrict X t j)
      (map X ((i ≫ j) ≫ t) p) (map X (j ≫ t) p) (map X t p)
      (restrict B (j ≫ t ≫ p) i) (restrict B (t ≫ p) j)
      (restrict_map X (j ≫ t) i p) (restrict_map X t j p)
      (categoricalFibration_restrictionComparison i (j ≫ t) p) hj hb

end SSet.sliceUnder

namespace SSet.sliceOver

/-- A trivial first over-slice comparison detects the second comparison after pasting. -/
theorem rlp_I_composite_iff_second {K₀ K₁ K₂ X B : SSet.{u}}
    (i : K₀ ⟶ K₁) (j : K₁ ⟶ K₂) [Mono j] (t : K₂ ⟶ X) (p : X ⟶ B)
    [InnerFibration p] [Quasicategory B]
    (hi : modelCategoryQuillen.I.rlp (restrictionComparison i (j ≫ t) p)) :
    modelCategoryQuillen.I.rlp (restrictionComparison (i ≫ j) t p) ↔
      modelCategoryQuillen.I.rlp (restrictionComparison j t p) := by
  unfold restrictionComparison
  refine (SSet.rlp_lift_congr (map X ((i ≫ j) ≫ t) p)
    (restrict_comp X t i j) (restrict_comp B (t ≫ p) i j)
    (restrict_map X t (i ≫ j) p) (by
      rw [← restrict_comp X t i j, restrict_map X t (i ≫ j) p, restrict_comp B (t ≫ p) i j])).trans ?_
  exact RelativePullback.rlp_I_total_iff_second (restrict X (j ≫ t) i) (restrict X t j)
      (map X ((i ≫ j) ≫ t) p) (map X (j ≫ t) p) (map X t p)
      (restrict B (j ≫ t ≫ p) i) (restrict B (t ≫ p) j)
      (restrict_map X (j ≫ t) i p) (restrict_map X t j p) hi
      (categoricalFibration_restrictionComparison j t p)

/-- A trivial second comparison and original base restriction detect the first comparison. -/
theorem rlp_I_composite_iff_first {K₀ K₁ K₂ X B : SSet.{u}}
    (i : K₀ ⟶ K₁) [Mono i] (j : K₁ ⟶ K₂) (t : K₂ ⟶ X) (p : X ⟶ B)
    [InnerFibration p] [Quasicategory B]
    (hj : modelCategoryQuillen.I.rlp (restrictionComparison j t p))
    (hb : modelCategoryQuillen.I.rlp (restrict B (t ≫ p) j)) :
    modelCategoryQuillen.I.rlp (restrictionComparison (i ≫ j) t p) ↔
      modelCategoryQuillen.I.rlp (restrictionComparison i (j ≫ t) p) := by
  unfold restrictionComparison
  refine (SSet.rlp_lift_congr (map X ((i ≫ j) ≫ t) p)
    (restrict_comp X t i j) (restrict_comp B (t ≫ p) i j)
    (restrict_map X t (i ≫ j) p) (by
      rw [← restrict_comp X t i j, restrict_map X t (i ≫ j) p, restrict_comp B (t ≫ p) i j])).trans ?_
  exact RelativePullback.rlp_I_total_iff_first (restrict X (j ≫ t) i) (restrict X t j)
      (map X ((i ≫ j) ≫ t) p) (map X (j ≫ t) p) (map X t p)
      (restrict B (j ≫ t ≫ p) i) (restrict B (t ≫ p) j)
      (restrict_map X (j ≫ t) i p) (restrict_map X t j p)
      (categoricalFibration_restrictionComparison i (j ≫ t) p) hj hb

end SSet.sliceOver
