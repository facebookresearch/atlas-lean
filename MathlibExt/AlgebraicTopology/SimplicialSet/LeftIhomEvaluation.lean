/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.LeftIhomPrism

/-!
# Original vertex evaluations of left-parameter prisms

The existing native internal-Hom evaluation at an original source vertex
reads the same left-parameter prism on the identity parameter simplex and
the degenerate source simplex. The statement holds in every degree and
requires no fibrancy or marking hypothesis.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite
open scoped Simplicial

namespace SSet

/-- The original source-vertex section retains the whole parameter coordinate. -/
def leftPrismVertexSection {X : SSet.{u}} {n : ℕ} (x : X _⦋0⦌) :
    (Δ[n] : SSet.{u}) ⟶ Δ[n] ⊗ X := lift (𝟙 _) (SSet.const x)

/-- Native internal-Hom evaluation reads the original left prism at the supplied source vertex. -/
theorem eval_leftIhomSimplexOfPrism {X Y : SSet.{u}} {n : ℕ}
    (x : X _⦋0⦌) (F : (Δ[n] : SSet.{u}) ⊗ X ⟶ Y) :
    (((pre (SSet.yonedaEquiv.symm x)).app Y ≫ (evalDeltaZeroIso Y).hom).app (op ⦋n⦌))
      (leftIhomSimplexOfPrism F) =
        F.app (op ⦋n⦌) (SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u})),
          X.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op x) := by
  have h : MonoidalClosed.curry ((β_ X (Δ[n] : SSet.{u})).hom ≫ F) ≫
      (pre (SSet.yonedaEquiv.symm x)).app Y ≫ (evalDeltaZeroIso Y).hom =
      leftPrismVertexSection x ≫ F := by
    rw [evalDeltaZeroIso_hom, MonoidalClosed.curry_pre_app_assoc,
      MonoidalClosed.curry_pre_app_assoc, curry_unitIsoSelf]
    rw [SSet.yonedaEquiv_symm_zero]
    rfl
  have h' := congrArg SSet.yonedaEquiv h
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp] at h'
  exact h'

end SSet
