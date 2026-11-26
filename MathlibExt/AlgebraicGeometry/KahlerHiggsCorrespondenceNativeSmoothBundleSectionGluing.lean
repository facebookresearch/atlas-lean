/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HolomorphicSmoothScalarModels
import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# Native smooth bundle section gluing

Smoothness of native bundle sections is a local predicate. The presheaf of
these sections satisfies the ordinary sheaf condition.

Background: Carlos Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, section 2 and Theorem 2.3, pp. 7--11. That theorem motivates the
Kähler Higgs correspondence this lemma serves; it is not the source of this lemma.
-/

open CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
open MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
open MathlibExt.AlgebraicGeometry.HolomorphicSmoothScalarModels
open scoped Manifold ContDiff

private def smoothSectionLocalPredicate {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] {r : ℕ} (B : SmoothComplexBundle n M r)
    [SectionCalculus B 0] : TopCat.LocalPredicate (X := TopCat.of M) (fun x ↦ B.core.Fiber x) where
  pred {U} s := IsSmoothSection B U s
  res {U V} a s hs := SectionCalculus.smooth_restrict (B := B) (A := 0) V U a.le s hs
  locality {U} s hs := by
    classical
    intro i x hx
    obtain ⟨V, hxV, a, hV⟩ := hs ⟨x, hx.1⟩
    apply ContMDiffAt.contMDiffWithinAt
    apply ((hV i x ⟨hxV, hx.2⟩).contMDiffAt
      ((V.isOpen.inter (B.core.isOpen_baseSet i)).mem_nhds ⟨hxV, hx.2⟩)).congr_of_eventuallyEq
    filter_upwards [V.isOpen.mem_nhds hxV] with y hy
    change y ∈ (V : Opens M) at hy
    dsimp only [coordinateSection]
    rw [dite_eq_left hy, dite_eq_left (a.le hy)]
    rfl

/-- Assuming `SectionCalculus B 0` and `SmoothSectionMultiplication B`, smooth sections of `B` that
agree on pairwise overlaps glue uniquely over the union. -/
public theorem native_smooth_bundle_section_gluing {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] {r : ℕ} (B : SmoothComplexBundle n M r)
    [SectionCalculus B 0] [SmoothSectionMultiplication B] : SmoothBundleSheafCondition B := by
  constructor
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)]
  exact TopCat.subpresheafToTypes.isSheaf (smoothSectionLocalPredicate B)
