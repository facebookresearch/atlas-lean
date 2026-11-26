/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ManifoldChernComparisonsNativeSmoothSingularSource
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

@[expose] public section

/-!
# Tests for the native smooth singular source

The native smooth singular source holds for complex one-space over itself,
and every smooth native one-simplex has a smooth zeroth face.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.SmoothManifoldSingularModels
open scoped Simplicial Manifold ContDiff

namespace MathlibExtTest.AlgebraicGeometry.ManifoldChernComparisonsNativeSmoothSingularSource

/-- The native smooth singular source holds for complex one-space over itself. -/
example : SmoothSingularSource (n := 1) (M := Coordinates 1) :=
  native_smooth_singular_source

/-- Every smooth native one-simplex has a smooth zeroth face. -/
example {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    (σ : (nativeSingularSet (M := M)).obj (op ⦋1⦌))
    (hσ : IsSmoothSimplex (n := n) (M := M) 1 σ) :
    IsSmoothSimplex (n := n) (M := M) 0
      ((nativeSingularSet (M := M)).map (SimplexCategory.δ (n := 0) 0).op σ) :=
  (native_smooth_singular_source (n := n) (M := M)).closed (op ⦋1⦌) (op ⦋0⦌)
    (SimplexCategory.δ (n := 0) 0).op σ hσ

end MathlibExtTest.AlgebraicGeometry.ManifoldChernComparisonsNativeSmoothSingularSource
