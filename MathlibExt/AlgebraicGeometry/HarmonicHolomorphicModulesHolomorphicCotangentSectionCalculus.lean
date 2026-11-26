/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Holomorphic cotangent section calculus

Smooth complex tangent forms are closed under multiplication by holomorphic
functions and restriction to smaller open sets.

Carlos Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, section 2, printed pages 9–11.
-/

public section

open TopologicalSpace
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms
open MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
open MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
open scoped Manifold ContDiff

/-- Actual holomorphic tangent covectors satisfy ordinary local multiplication and restriction
calculus. -/
theorem holomorphic_cotangent_section_calculus {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] :
    CotangentSectionCalculus (n := n) (M := M) where
  mul U p f α hα := by
    intro a
    apply ((f.property a).smul (hα a)).congr
    intro z hz
    classical
    change chartForm ℂ (Coordinates n) M (f • α) a z =
      chartFunction (Coordinates n) M f.val a z • chartForm ℂ (Coordinates n) M α a z
    simp only [chartForm, chartFunction, dite_eq_left hz]
    ext v
    rfl
  restriction U V h p α hα := by
    intro a
    have hd : chartDomain ℂ (Coordinates n) M V a ⊆
        chartDomain ℂ (Coordinates n) M U a := fun _ hz => ⟨hz.1, h hz.2⟩
    apply ((hα a).mono hd).congr
    intro z hz
    simp only [chartForm, dite_eq_left hz, dite_eq_left (hd hz)]
