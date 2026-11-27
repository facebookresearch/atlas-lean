/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesPluriharmonicHiggsIntegrable

/-!
# Tests for pluriharmonic Higgs integrability

Corollaries of `pluriharmonic_higgs_integrable`: vanishing of the
exterior-square map and of its action on local holomorphic sections.
-/

namespace MathlibExtTest.AlgebraicGeometry.HarmonicHolomorphicModulesPluriharmonicHiggsIntegrable

open CategoryTheory Opposite TopologicalSpace
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicSectionKernels
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
open MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicFrameModels
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M] {r : ℕ}
  [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  (B : SmoothComplexBundle n M r) (h : HermitianMetric B) (A : SmoothConnection B)
  [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A]
  [MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves.SheafCondition
    (Coordinates n) M]
  [KernelSheafCondition B h A]
  [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- Integrability unfolds to vanishing of the exterior-square map. -/
example (hh : IsPluriharmonic B h A) (H : HarmonicHiggsModel B h A)
    (S : HiggsExteriorSquare B h A H) : S.map = 0 :=
  pluriharmonic_higgs_integrable B h A hh H S

/-- Hence every local holomorphic section is sent to zero. -/
example (hh : IsPluriharmonic B h A) (H : HarmonicHiggsModel B h A)
    (S : HiggsExteriorSquare B h A H) (U : Opens M)
    (s : (holomorphicModule B h A).val.obj (op U)) :
    (S.map.val.app (op U)).hom s = 0 := by
  have h0 : S.map = 0 := pluriharmonic_higgs_integrable B h A hh H S
  exact congrArg (fun f => (f.val.app (op U)).hom s) h0

end MathlibExtTest.AlgebraicGeometry.HarmonicHolomorphicModulesPluriharmonicHiggsIntegrable
