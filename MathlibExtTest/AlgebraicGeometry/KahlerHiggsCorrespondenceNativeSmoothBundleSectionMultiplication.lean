/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.KahlerHiggsCorrespondenceNativeSmoothBundleSectionMultiplication

/-!
# Tests for native smooth bundle section multiplication

The multiplication theorem gives closure under successive smooth coefficients and their product.

Background: Carlos Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, section 2 and Theorem 2.3, pp. 7--11. That theorem motivates the
Kähler Higgs correspondence this lemma serves; it is not the source of this lemma.
-/

namespace MathlibExtTest.AlgebraicGeometry
namespace KahlerHiggsCorrespondenceNativeSmoothBundleSectionMultiplication

open CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
open MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
open MathlibExt.AlgebraicGeometry.HolomorphicSmoothScalarModels
open scoped Manifold ContDiff

example {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    {r : ℕ} (B : SmoothComplexBundle n M r) (U : Opens M)
    (f g : SmoothScalars (n := n) U) (s : RoughSection B U) (hs : IsSmoothSection B U s) :
    IsSmoothSection B U (f • (g • s)) := by
  let _ := native_smooth_bundle_section_multiplication B
  exact SmoothSectionMultiplication.smooth U f (g • s)
    (SmoothSectionMultiplication.smooth U g s hs)

example {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    {r : ℕ} (B : SmoothComplexBundle n M r) (U : Opens M)
    (f g : SmoothScalars (n := n) U) (s : RoughSection B U) (hs : IsSmoothSection B U s) :
    IsSmoothSection B U ((f * g) • s) := by
  let _ := native_smooth_bundle_section_multiplication B
  exact SmoothSectionMultiplication.smooth U (f * g) s hs

end KahlerHiggsCorrespondenceNativeSmoothBundleSectionMultiplication
end MathlibExtTest.AlgebraicGeometry
