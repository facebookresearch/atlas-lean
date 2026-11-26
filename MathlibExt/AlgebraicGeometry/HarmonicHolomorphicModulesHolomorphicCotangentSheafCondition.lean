/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Forget

/-!
# The sheaf condition for holomorphic cotangent forms

`CotangentSectionCalculus` supplies multiplication and restriction for the
holomorphic cotangent-form presheaves `formModulePresheaf p`. Assuming this
calculus, `holomorphic_cotangent_sheaf_condition` proves that these same
presheaves satisfy the sheaf condition for every degree `p`, because
regularity of their chart pullbacks is local.

Reference: Carlos Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, section 2, printed pages 9--11.
-/

open CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms
open MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
open scoped Manifold ContDiff Topology

private theorem isSmooth_local {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    {U : Opens M} {p : ℕ} (α : RoughForm ℂ (Coordinates n) M U p)
    (h : ∀ x : U, ∃ (V : Opens M) (_ : x.val ∈ V) (i : V ⟶ U),
      IsSmooth ℂ (Coordinates n) M (fun y : V => α ⟨y.val, i.le y.property⟩)) :
    IsSmooth ℂ (Coordinates n) M α := by
  classical
  intro a z hz
  obtain ⟨V, hxV, i, hV⟩ := h ⟨(extChartAt 𝓘(ℂ, Coordinates n) a).symm z, hz.2⟩
  have hd : chartDomain ℂ (Coordinates n) M V a ∈ 𝓝 z :=
    Filter.inter_mem ((isOpen_extChartAt_target a).mem_nhds hz.1)
      ((continuousAt_extChartAt_symm'' hz.1).preimage_mem_nhds (V.isOpen.mem_nhds hxV))
  apply ContDiffAt.contDiffWithinAt
  apply ((hV a).contDiffAt hd).congr_of_eventuallyEq
  filter_upwards [hd] with w hw
  have hwU : w ∈ chartDomain ℂ (Coordinates n) M U a := ⟨hw.1, i.le hw.2⟩
  simp only [chartForm, dite_eq_left hw, dite_eq_left hwU]

private def formLocalPredicate {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    [CotangentSectionCalculus (n := n) (M := M)] (p : ℕ) :
    TopCat.LocalPredicate (X := TopCat.of M)
      (fun x => TangentSpace 𝓘(ℂ, Coordinates n) x [⋀^Fin p]→L[ℂ] ℂ) where
  pred := IsSmooth ℂ (Coordinates n) M
  res i α hα := CotangentSectionCalculus.restriction _ _ i.le p α hα
  locality := isSmooth_local

/-- The same actual cotangent-form presheaves satisfy the ordinary gluing condition. -/
public theorem holomorphic_cotangent_sheaf_condition {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    [CotangentSectionCalculus (n := n) (M := M)] :
    CotangentSheafCondition (n := n) (M := M) := by
  constructor
  intro p
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (X := TopCat.of M) (forget AddCommGrpCat)
    (formModulePresheaf (n := n) (M := M) p).presheaf).mpr
  exact TopCat.subpresheafToTypes.isSheaf (formLocalPredicate (n := n) (M := M) p)
