/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AnalyticCurrentsCurrentDifferentialTheory

/-!
# Differentials supplied by current differential theory

The proved provider constructs the differential of an arbitrary current and
supplies its distribution bound.

Reference: J.-P. Demailly and M. Păun, *Numerical characterization of the
Kähler cone of a compact Kähler manifold*, Ann. of Math. 159 (2004),
arXiv:math/0105176v2, Theorem 0.4 (Theorem 0.5 of the published version).
-/

namespace MathlibExtTest.AlgebraicGeometry.AnalyticCurrentsCurrentDifferentialTheory

open MathlibExt.AlgebraicGeometry
open KahlerClassGeometry ManifoldDifferentialForms CoordinateFormIntegrals AnalyticCurrents
open scoped Manifold ContDiff

example (n : ℕ) (M : Type) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    [ExteriorTheory ℝ (Coordinates n) M] (p : ℕ) (T : Current n M p)
    (h : p + 1 ≤ n * 2) :
    ∃ S : Current n M (p + 1), S.functional = differentialFunctional n M T h ∧
      IsDistribution n M (n * 2 - (p + 1)) S.functional := by
  let := WantedExt.AlgebraicGeometry.AnalyticCurrentsWanted.currentDifferentialTheory n M
  exact ⟨differential n M T h, rfl, (differential n M T h).bounded⟩

end MathlibExtTest.AlgebraicGeometry.AnalyticCurrentsCurrentDifferentialTheory
