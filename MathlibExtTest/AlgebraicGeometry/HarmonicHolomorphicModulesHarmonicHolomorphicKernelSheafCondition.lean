/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHarmonicHolomorphicKernelSheafCondition

/-!
# Tests for gluing of the harmonic holomorphic kernel

The kernel sheaf condition applies to fixed bundle data, yields that the
underlying abelian presheaf is a sheaf, and, with the coefficient sheaf
condition, produces the holomorphic bundle sheaf of modules.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicSectionKernels
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
open scoped Manifold ContDiff

namespace MathlibExtTest.AlgebraicGeometry.HarmonicHolomorphicModulesHarmonicHolomorphicKernelSheafCondition

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  {r : ℕ} (B : SmoothComplexBundle n M r)
  (h : HermitianMetric B) (A : SmoothConnection B)
  [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A]

/-- The kernel presheaf satisfies the sheaf condition. -/
example : KernelSheafCondition B h A :=
  harmonic_holomorphic_kernel_sheaf_condition B h A

/-- The underlying abelian presheaf is a sheaf. -/
example : Presheaf.IsSheaf (Opens.grothendieckTopology M)
    (holomorphicModulePresheaf B h A).presheaf :=
  (harmonic_holomorphic_kernel_sheaf_condition B h A).isSheaf

variable [MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves.SheafCondition
  (Coordinates n) M]

/-- The holomorphic bundle sheaf exists with no integrability hypothesis. -/
example : SheafOfModules.{0} (holomorphicStructureRing (n := n) (M := M)) :=
  haveI := harmonic_holomorphic_kernel_sheaf_condition B h A
  holomorphicModule B h A

end MathlibExtTest.AlgebraicGeometry.HarmonicHolomorphicModulesHarmonicHolomorphicKernelSheafCondition
