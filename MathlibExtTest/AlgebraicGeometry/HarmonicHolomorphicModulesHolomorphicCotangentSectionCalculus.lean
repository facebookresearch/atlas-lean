/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicCotangentSectionCalculus

/-!
# Tests for holomorphic cotangent section calculus

Multiplication followed by restriction preserves smoothness, and the calculus
instance supports the holomorphic form restriction map.

Carlos Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, section 2, printed pages 9–11.
-/

open TopologicalSpace
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
open MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
open scoped Manifold ContDiff

namespace MathlibExtTest.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicCotangentSectionCalculus

example {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] (U V : Opens M) (h : V ≤ U) (p : ℕ)
    (f : HolomorphicScalars (n := n) U) (α : RoughForm ℂ (Coordinates n) M U p)
    (hα : IsSmooth ℂ (Coordinates n) M α) :
    IsSmooth ℂ (Coordinates n) M
      (fun x : V => f.val ⟨x.val, h x.property⟩ • α ⟨x.val, h x.property⟩) := by
  have hc := holomorphic_cotangent_section_calculus (n := n) (M := M)
  exact hc.restriction U V h p (f • α) (hc.mul U p f α hα)

example (U V : Opens (Coordinates 1)) (h : V ≤ U)
    (α : smoothForms ℂ (Coordinates 1) (Coordinates 1) U 1) :
    IsSmooth ℂ (Coordinates 1) (Coordinates 1)
      (fun x : V => α.val ⟨x.val, h x.property⟩) := by
  let := holomorphic_cotangent_section_calculus (n := 1) (M := Coordinates 1)
  exact (formRestriction (n := 1) (M := Coordinates 1) h 1 ⟨α.val, α.property⟩).property

end MathlibExtTest.AlgebraicGeometry.HarmonicHolomorphicModulesHolomorphicCotangentSectionCalculus
