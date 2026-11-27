/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ManifoldComponentModuleMaps
public import MathlibExt.AlgebraicGeometry.ManifoldComponentModuleMapsNativeComponentModuleAssemblyIsIso

/-!
# Wanted finite component and native module assembly comparisons

The maps are the actual native component restrictions, pushforwards
and adjunction-unit finite product. These supply component assembly
for general compact manifolds while the pointed Higgs correspondence
is stated on a connected nonempty manifold. The native module assembly
comparison `native_component_module_assembly_isIso` is proved in
`MathlibExt.AlgebraicGeometry.ManifoldComponentModuleMapsNativeComponentModuleAssemblyIsIso`.
-/

open CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry
open KahlerClassGeometry HarmonicHolomorphicModuleModels HolomorphicCotangentModuleModels
open HolomorphicSheafHiggsModels ManifoldComponentModuleMaps
open scoped Manifold ContDiff

/-- A compact manifold has its actual finite connected clopen component partition. -/
def_wanted native_manifold_finite_component_partition (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] : FiniteComponentPartition (M := M)

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]
  [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
