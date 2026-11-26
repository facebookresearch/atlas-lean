/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HolomorphicSmoothScalarModels

/-!
# Native smooth bundle section multiplication

Multiplication by native smooth complex functions preserves smooth sections of the same bundle.

Background: Carlos Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, section 2 and Theorem 2.3, pp. 7--11. That theorem motivates the
Kähler Higgs correspondence this lemma serves; it is not the source of this lemma.
-/

open CategoryTheory TopologicalSpace Set
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
open MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
open MathlibExt.AlgebraicGeometry.HolomorphicSmoothScalarModels
open scoped Manifold ContDiff

/-- Actual native smooth coefficient multiplication preserves the same bundle sections. -/
public theorem native_smooth_bundle_section_multiplication {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (Coordinates n) M] {r : ℕ}
    (B : SmoothComplexBundle n M r) : SmoothSectionMultiplication B := by
  classical
  refine ⟨fun U f s hs i => ?_⟩
  let f' : C^∞⟮𝓘(ℝ, Coordinates n), U; 𝓘(ℝ, ℂ), ℂ⟯ := f
  let g : M → ℂ := fun x => if hx : x ∈ U then f' ⟨x, hx⟩ else 0
  have hg : ContMDiffOn 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ) ∞ g (U : Set M) := by
    intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    apply (contMDiffAt_subtype_iff (x := ⟨x, hx⟩)).mp
    simpa [g, f'] using f'.contMDiff.contMDiffAt (x := ⟨x, hx⟩)
  have hcoord : coordinateSection B i U (f • s) = g • coordinateSection B i U s := by
    funext x
    change coordinateSection B i U (f • s) x = g x • coordinateSection B i U s x
    by_cases hx : x ∈ U
    · simp only [coordinateSection, dite_eq_left hx, g,
        VectorBundleCore.localTriv_apply]
      change B.core.coordChange (B.core.indexAt x) i x (f' ⟨x, hx⟩ • s ⟨x, hx⟩) =
        f' ⟨x, hx⟩ • B.core.coordChange (B.core.indexAt x) i x (s ⟨x, hx⟩)
      exact map_smul _ _ _
    · simp [coordinateSection, g, hx]
  rw [hcoord]
  apply contMDiffOn_pi_module_iff.mpr
  intro j
  exact (hg.mono inter_subset_left).mul (contMDiffOn_pi_module_iff.mp (hs i) j)
