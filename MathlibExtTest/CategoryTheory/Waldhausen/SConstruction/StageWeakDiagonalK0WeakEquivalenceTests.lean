/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0WeakEquivalence

/-!
# Weak-equivalence diagonal K-zero simplex tests

These tests pin the pointwise weak lift, the two mixed-degeneracy triangle
orientations, the normalized zero edge, and the resulting equality in the
simplicial fundamental groupoid.  They make no K-zero comparison,
generation, realization, additivity, or model-category claim.
-/

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalK0WeakEquivalenceTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

variable {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f)

/-- The weak-stage lift retains `f` at the unique off-diagonal interval. -/
example :
    (stageOneWeakMap C f hf).hom.hom.app
        (interval (0 : Fin 2) 1 (by decide)) = f := by
  rw [stageOneWeakMap_hom, stageOne_map_interval_zero_one]

/-- The collapsed mixed face is literally the identity edge at the zero
vertex. -/
example :
    (stageWeakDiagonal C).δ 0
        (stageWeakDiagonalWeakEquivalenceSourceTriangleSimplex C f hf) =
      (SSet.Edge.id (X := stageWeakDiagonal C)
        (stageWeakDiagonalZeroVertex C)).edge :=
  stageWeakDiagonalWeakEquivalenceSourceTriangle_d0 C f hf

/-- The zero edge itself is the identity on the degenerated zero stage. -/
example :
    (SSet.Edge.id (X := stageWeakDiagonal C)
      (stageWeakDiagonalZeroVertex C)).edge =
      ComposableArrows.mk₁
        (𝟙 ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
          (⟨stageZero C⟩ : StageWeakCategory C 0))) :=
  stageWeakDiagonalZeroEdge_edge C

/-- The source triangle has orientation `objectEdge X ; id = weakEdge f`. -/
noncomputable example :
    SSet.Edge.CompStruct (stageWeakDiagonalObjectEdge C X)
      (SSet.Edge.id (stageWeakDiagonalZeroVertex C))
      (stageWeakDiagonalWeakEquivalenceEdge C f hf) :=
  stageWeakDiagonalWeakEquivalenceSourceCompStruct C f hf

/-- The target triangle has orientation `id ; objectEdge Y = weakEdge f`. -/
noncomputable example :
    SSet.Edge.CompStruct
      (SSet.Edge.id (stageWeakDiagonalZeroVertex C))
      (stageWeakDiagonalObjectEdge C Y)
      (stageWeakDiagonalWeakEquivalenceEdge C f hf) :=
  stageWeakDiagonalWeakEquivalenceTargetCompStruct C f hf

/-- Weak equivalence identifies the two canonical object edges in the
simplicial fundamental groupoid. -/
example :
    SSet.FundamentalGroupoid.homMk (stageWeakDiagonalObjectEdge C X) =
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalObjectEdge C Y) :=
  stageWeakDiagonalObjectEdge_homMk_eq_of_weakEquivalence C f hf

end StageWeakDiagonalK0WeakEquivalenceTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
