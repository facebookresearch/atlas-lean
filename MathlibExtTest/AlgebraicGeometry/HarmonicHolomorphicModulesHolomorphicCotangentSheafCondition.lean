/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicCotangentSheafCondition
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Unique gluing of holomorphic cotangent sections

A compatible family of actual holomorphic one-forms has a unique gluing.

Reference: Carlos Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, section 2, printed pages 9--11.
-/

open CategoryTheory TopologicalSpace Opposite
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
open scoped Manifold ContDiff

namespace MathlibExtTest.AlgebraicGeometry
namespace HarmonicHolomorphicModulesHolomorphicCotangentSheafCondition

example {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    [CotangentSectionCalculus (n := n) (M := M)] {ι : Type} (U : ι → Opens M)
    (s : ∀ i, holomorphicFormModule (n := n) (M := M) (U i) 1)
    (hs : TopCat.Presheaf.IsCompatible (X := TopCat.of M)
      (formModulePresheaf (n := n) (M := M) 1).presheaf U s) :
    ∃! t : holomorphicFormModule (n := n) (M := M) (iSup U) 1,
      ∀ i, formRestriction (n := n) (M := M) (le_iSup U i) 1 t = s i := by
  have h := holomorphic_cotangent_sheaf_condition (n := n) (M := M)
  exact TopCat.Presheaf.IsSheaf.isSheafUniqueGluing (X := TopCat.of M) (h.isSheaf 1) U s hs

end HarmonicHolomorphicModulesHolomorphicCotangentSheafCondition
end MathlibExtTest.AlgebraicGeometry
