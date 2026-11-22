/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubePoint
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeMaximum
import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexFibrationTransitions

/-!
# Actual degreewise weak comparison of the original right-cube quotient

The genuine descended quotient cylinder makes its full-path projection
weak. The actual standard resolving simplex also projects weakly to the
unit. Two-out-of-three proves that the whole original quotient maximum
map is a realization weak equivalence. No relative frame or mapping-space
weak conclusion follows here without the remaining Hom/latching proof.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeWeakComparison

/-- The actual original right-cube quotient projects weakly to the unit by its constructed full-path contraction. -/
theorem quotient_projection_weak (n : ℕ) : SSet.realizationWeakEquivalences (RightCubePoint.projection.{u} n) := by
  have h₀ := RightCubePoint.projection_section_weak.{u} n
  have h₁ : SSet.realizationWeakEquivalences (RightCubePoint.sectionMap.{u} n ≫ RightCubePoint.projection n) :=
    (RightCubePoint.section_projection n).symm ▸ SSet.realizationWeakEquivalences.of_isIso _
  exact SSet.realizationWeakEquivalences.left_of_comp_comp h₀ h₁

/-- The actual standard resolving simplex projects weakly to the simplicial tensor unit. -/
theorem simplex_projection_weak (n : ℕ) : SSet.realizationWeakEquivalences
    (SimplicialEnrichment.toUnit (Δ[n] : SSet.{u})) := by
  let e : (Δ[0] : SSet.{u}) ≅ 𝟙_ SSet.{u} :=
    SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
  have h := SSet.stdSimplex_to_point_mem_realizationWeakEquivalences.{u} (SimplexCategory.mk n)
  have hE := SSet.realizationWeakEquivalences.of_isIso e.hom
  have hC := SSet.realizationWeakEquivalences.comp_mem _ _ h hE
  have hEq : SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u}) ≫ e.hom = SimplicialEnrichment.toUnit _ := by
    ext q a
    exact @Subsingleton.elim PUnit.{u + 1} inferInstance _ _
  exact hEq ▸ hC

/-- The actual whole quotient maximum map is a degreewise realization weak equivalence with its original
  flag section and no Kan/frame hypothesis. -/
theorem maximum_weak (n : ℕ) : SSet.realizationWeakEquivalences (RightCubeMaximum.map.{u} n) := by
  have hQ := quotient_projection_weak.{u} n
  have hS := simplex_projection_weak.{u} n
  have hEq : RightCubeMaximum.map.{u} n ≫ SimplicialEnrichment.toUnit (Δ[n] : SSet.{u}) =
    RightCubePoint.projection n := by
    ext q a
    exact @Subsingleton.elim PUnit.{u + 1} inferInstance _ _
  exact SSet.realizationWeakEquivalences.of_postcomp _ _ hS (hEq.symm ▸ hQ)

end CategoryTheory.CoherentRealization.RightCubeWeakComparison
