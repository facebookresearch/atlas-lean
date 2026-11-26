/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.KahlerHiggsCorrespondenceNativeSmoothBundleSectionGluing
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Tests for native smooth bundle section gluing

The native gluing theorem gives a unique smooth section for each compatible
family of smooth sections on an open cover.

Source: Carlos Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, section 2 and Theorem 2.3, pp. 7--11.
-/

open CategoryTheory Opposite TopologicalSpace
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
open MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
open MathlibExt.AlgebraicGeometry.HolomorphicSmoothScalarModels
open scoped Manifold ContDiff

namespace MathlibExtTest.AlgebraicGeometry.KahlerHiggsCorrespondenceNativeSmoothBundleSectionGluing

example {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]
    [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
    [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
    {r : ℕ} (B : SmoothComplexBundle n M r)
    [SectionCalculus B 0] [SmoothSectionMultiplication B]
    {ι : Type} (U : ι → Opens M) (s : ∀ i, smoothSectionModule B (U i))
    (hs : TopCat.Presheaf.IsCompatible (X := TopCat.of M) (smoothSectionPresheaf B).presheaf U s) :
    ∃! t : smoothSectionModule B (iSup U),
      TopCat.Presheaf.IsGluing (X := TopCat.of M) (smoothSectionPresheaf B).presheaf U s t := by
  have h := (native_smooth_bundle_section_gluing B).isSheaf
  exact TopCat.Presheaf.IsSheaf.isSheafUniqueGluing (X := TopCat.of M) h U s hs

end MathlibExtTest.AlgebraicGeometry.KahlerHiggsCorrespondenceNativeSmoothBundleSectionGluing
