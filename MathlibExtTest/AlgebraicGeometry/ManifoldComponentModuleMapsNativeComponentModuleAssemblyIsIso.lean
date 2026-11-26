/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.ManifoldComponentModuleMapsNativeComponentModuleAssemblyIsIso

/-!
# Tests for native component module assembly

The assembly unit admits an inverse satisfying both inverse identities.
-/

open CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry
open KahlerClassGeometry HarmonicHolomorphicModuleModels HolomorphicCotangentModuleModels
open HolomorphicSheafHiggsModels ManifoldComponentModuleMaps
open scoped Manifold ContDiff

namespace MathlibExtTest.AlgebraicGeometry
namespace ManifoldComponentModuleMapsNativeComponentModuleAssemblyIsIso

example {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]
    (P : FiniteComponentPartition (M := M))
    (E : HolomorphicModules (n := n) (M := M)) :
    ∃ a : assembleComponents (n := n) P
        (fun i => (componentRestriction (n := n) (P.component i)).obj E) ⟶ E,
      componentAssemblyUnit (n := n) P E ≫ a = 𝟙 E ∧
        a ≫ componentAssemblyUnit (n := n) P E = 𝟙 _ := by
  let := native_component_module_assembly_isIso P E
  exact ⟨inv (componentAssemblyUnit (n := n) P E),
    IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

end ManifoldComponentModuleMapsNativeComponentModuleAssemblyIsIso
end MathlibExtTest.AlgebraicGeometry
