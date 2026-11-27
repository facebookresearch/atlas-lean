/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicFrameModels
public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicCoefficientSheafCondition
public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicBarMultiplication
public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicCotangentSheafCondition
public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHarmonicHolomorphicKernelSheafCondition
public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicCotangentSectionCalculus
public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesPluriharmonicHiggsIntegrable

/-!
# Wanted native holomorphic-kernel, cotangent and Higgs constructions

All ordinary support requests concern the fixed public section formulas.
The holomorphic coefficient sheaf condition
`holomorphic_coefficient_sheaf_condition` is proved in
`MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicCoefficientSheafCondition`,
`holomorphic_bar_multiplication` is proved in
`MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicBarMultiplication`,
`holomorphic_cotangent_sheaf_condition` is proved in
`MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicCotangentSheafCondition`,
`holomorphic_cotangent_section_calculus` is proved in
`MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicCotangentSectionCalculus`,
`harmonic_holomorphic_kernel_sheaf_condition` is proved in
`MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHarmonicHolomorphicKernelSheafCondition`,
and `pluriharmonic_higgs_integrable` is proved in
`MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesPluriharmonicHiggsIntegrable`.
Integrability produces new holomorphic frames and the actual O-linear
Higgs map; it does not declare the original smooth frames holomorphic.
Polystability, Chern vanishing and the full correspondence are separate
theorems. Simpson, alg-geom/9604005v1, section 2, printed pages 9--11.
-/

open CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicSectionKernels
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
open MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicFrameModels
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  {r : ℕ}

/-- The actual integrable bar connection admits new local holomorphic frames. -/
def_wanted pluriharmonic_local_holomorphic_frame [T2Space M] [SecondCountableTopology M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    (B : SmoothComplexBundle n M r) (h : HermitianMetric B) (A : SmoothConnection B)
    (hh : IsPluriharmonic B h A) (x : M) : LocalHolomorphicFrame B h A x

/-- These same genuine frames identify the actual holomorphic kernel with finite free O-modules. -/
def_wanted harmonic_holomorphic_frame_kernel
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    (B : SmoothComplexBundle n M r)
    (h : HermitianMetric B) (A : SmoothConnection B)
    [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A]
    (x : M) (F : LocalHolomorphicFrame B h A x) : KernelFrameModel B h A F

variable [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  (B : SmoothComplexBundle n M r) (h : HermitianMetric B) (A : SmoothConnection B)
  [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A]
  [MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]
  [KernelSheafCondition B h A]
  [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- Native tensor/sheafification realizes these same finite free holomorphic frame coordinates. -/
def_wanted harmonic_holomorphic_tensor_frame (x : M) (F : LocalHolomorphicFrame B h A x)
    (C : KernelFrameModel B h A F) (p : ℕ) : TensorFrameModel B h A C p

/-- Integrability supplies the actual holomorphic O-linear Higgs map with its extracted matrix formula. -/
def_wanted pluriharmonic_holomorphic_higgs_model [T2Space M] [SecondCountableTopology M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    (hh : IsPluriharmonic B h A) : HarmonicHiggsModel B h A

/-- Construct the actual exterior-square map of this same normalized Higgs field. -/
def_wanted harmonic_higgs_exterior_square (H : HarmonicHiggsModel B h A) : HiggsExteriorSquare B h A H
