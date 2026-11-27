/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves
public import MathlibExt.AlgebraicGeometry.KahlerClassGeometry
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# The sheaf condition for holomorphic coefficients

The chart-wise holomorphic predicate is local, so the presheaf of actual
holomorphic scalar rings satisfies the sheaf condition.

Carlos Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, section 2, printed pages 9--11.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms
open MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open scoped Manifold ContDiff Topology

private def holomorphicLocalPredicate (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M] :
    TopCat.LocalPredicate (fun _ : TopCat.of M ↦ ℂ) where
  pred := IsHolomorphic E M
  res i f hf := (restriction E M i.le ⟨f, hf⟩).property
  locality {U} f hf := by
    intro a z hz
    obtain ⟨V, hV, i, hi⟩ := hf ⟨(extChartAt 𝓘(ℂ, E) a).symm z, hz.2⟩
    have hd : chartDomain ℂ E M V a ⊆ chartDomain ℂ E M U a :=
      fun _ hw ↦ ⟨hw.1, i.le hw.2⟩
    have ho : IsOpen (chartDomain ℂ E M V a) :=
      (continuousOn_extChartAt_symm (I := 𝓘(ℂ, E)) a).isOpen_inter_preimage
        (isOpen_extChartAt_target a) V.isOpen
    have hzV : z ∈ chartDomain ℂ E M V a := ⟨hz.1, hV⟩
    have he : chartFunction E M f a =ᶠ[𝓝 z]
        chartFunction E M (fun x : V ↦ f ⟨x.val, i.le x.property⟩) a := by
      filter_upwards [ho.mem_nhds hzV] with w hw
      simp [chartFunction, hw, hd hw]
    exact ((hi a).contDiffAt (ho.mem_nhds hzV)).congr_of_eventuallyEq he
      |>.contDiffWithinAt

/-- The actual holomorphic scalar ring has the ordinary local sheaf condition. -/
theorem holomorphic_coefficient_sheaf_condition {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] :
    MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves.SheafCondition
      (Coordinates n) M := by
  constructor
  rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget RingCat)]
  exact TopCat.subpresheafToTypes.isSheaf (holomorphicLocalPredicate (Coordinates n) M)
