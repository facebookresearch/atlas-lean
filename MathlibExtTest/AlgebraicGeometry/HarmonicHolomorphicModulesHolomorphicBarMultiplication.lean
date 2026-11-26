/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicBarMultiplication

@[expose] public section

namespace MathlibExtTest.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicBarMultiplication

open TopologicalSpace
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicSectionKernels
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
open scoped Manifold ContDiff

/-- Bar-holomorphic sections are stable under holomorphic scaling. -/
example {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    {r : ℕ} (B : SmoothComplexBundle n M r) (h : HermitianMetric B)
    (A : SmoothConnection B)
    (U : Opens M) (f : HolomorphicScalars (n := n) U) (s : RoughSection B U)
    (hs : IsBarHolomorphic B h A U s) : IsBarHolomorphic B h A U (f • s) := by
  refine ⟨(holomorphic_bar_multiplication B h A).smooth U f s hs.1, ?_⟩
  intro i x hx u
  rw [(holomorphic_bar_multiplication B h A).bar U f s hs.1 i x hx u,
    hs.2 i x hx u, smul_zero]

end MathlibExtTest.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicBarMultiplication
