/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MinimalSourcePresentability
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FiniteSourcePresentability
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FibrationCells
import MathlibExt.CategoryTheory.Presentable.SmallFunctorCategory
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable

/-!
# An actual original-universe presentability bound for the native cells

The fixed native Kan detector has a presentability cardinal as an original
simplicial presheaf. At that same regular cardinal, every finite native
horn and simplex is presentable. Minimal marking and finite selected-edge
marking preserve this proven presentability. Hence every actual Cartesian
and cocartesian cell source is presentable at one original-universe bound.
This is a source bound, not merely smallness of the indexing family.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CellSmallness

/-- The fixed native Kan detector has an actual presentability bound as the original presheaf. -/
theorem exists_detector_presentability_cardinal :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular),
      IsCardinalPresentable KanEdgeDetector.object.{u} κ := by
  let _ : IsLocallyPresentable.{u} SSet.{u} :=
    isLocallyPresentable_presheaf_of_essentiallySmall.{u} (D := SimplexCategory) (A := Type u)
  let _ : IsPresentable.{u} KanEdgeDetector.object.{u} := inferInstance
  exact Functor.IsAccessible.exists_cardinal (coyoneda.obj (op KanEdgeDetector.object.{u}))

/-- The actual regular source cardinal chosen from the detector's native presheaf presentability. -/
def cardinal : Cardinal.{u} := exists_detector_presentability_cardinal.choose

/-- The chosen bound is genuinely regular. -/
theorem cardinal_regular : Fact cardinal.{u}.IsRegular :=
  exists_detector_presentability_cardinal.choose_spec.choose

local instance : Fact cardinal.{u}.IsRegular := cardinal_regular

/-- The actual native Kan detector is presentable at the chosen original-universe bound. -/
theorem detector_presentable : IsCardinalPresentable KanEdgeDetector.object.{u} cardinal.{u} :=
  exists_detector_presentability_cardinal.choose_spec.choose_spec

/-- The regular bound contains the finite-source presentability rank. -/
theorem aleph0_le_cardinal : Cardinal.aleph0.{u} ≤ cardinal.{u} :=
  Cardinal.IsRegular.aleph0_le Fact.out

/-- Every actual finite original simplicial source is presentable at that same bound. -/
theorem finite_source_presentable (X : SSet.{u}) [X.Finite] : IsCardinalPresentable X cardinal.{u} := by
  let _ : Fact Cardinal.aleph0.{u}.IsRegular := Cardinal.fact_isRegular_aleph0
  exact isCardinalPresentable_of_le X aleph0_le_cardinal

/-- All native Cartesian cell sources are genuinely presentable at the single actual original-universe rank. -/
theorem cartesian_source_presentable (s : FibrationCellIndex) :
    IsCardinalPresentable (cartesianCell.{u} s).left cardinal.{u} := by
  rcases s with ⟨n, i⟩ | n | i
  · change IsCardinalPresentable (min (Λ[n + 2, i.val] : SSet.{u})) cardinal.{u}
    let _ : IsCardinalPresentable (Λ[n + 2, i.val] : SSet.{u}) cardinal.{u} :=
      finite_source_presentable _
    exact min_isCardinalPresentable _ _
  · change IsCardinalPresentable (withEdges (Λ[n + 2, Fin.last (n + 2)] : SSet.{u})
      {rightHornEdgeSimplex.{u} n}) cardinal.{u}
    let _ : IsCardinalPresentable (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) cardinal.{u} :=
      finite_source_presentable _
    exact withEdges_isCardinalPresentable _ _ (Set.finite_singleton _) _
  · fin_cases i
    · change IsCardinalPresentable (min (Δ[0] : SSet.{u})) cardinal.{u}
      let _ : IsCardinalPresentable (Δ[0] : SSet.{u}) cardinal.{u} := finite_source_presentable _
      exact min_isCardinalPresentable _ _
    · change IsCardinalPresentable (withEdges (Δ[2] : SSet.{u}) compositionShortEdges.{u}) cardinal.{u}
      let _ : IsCardinalPresentable (Δ[2] : SSet.{u}) cardinal.{u} := finite_source_presentable _
      exact withEdges_isCardinalPresentable _ _ ((Set.finite_singleton (yonedaEquiv (stdSimplex.δ.{u} (0 :
        Fin 3)))).insert
        (yonedaEquiv (stdSimplex.δ.{u} (2 : Fin 3)))) _
    · change IsCardinalPresentable (min KanEdgeDetector.object.{u}) cardinal.{u}
      let _ : IsCardinalPresentable KanEdgeDetector.object.{u} cardinal.{u} := detector_presentable
      exact min_isCardinalPresentable _ _

/-- The dual original cell sources obey the same genuine source-presentability bound. -/
theorem cocartesian_source_presentable (s : FibrationCellIndex) :
    IsCardinalPresentable (cocartesianCell.{u} s).left cardinal.{u} := by
  rcases s with ⟨n, i⟩ | n | i
  · change IsCardinalPresentable (min (Λ[n + 2, i.val] : SSet.{u})) cardinal.{u}
    let _ : IsCardinalPresentable (Λ[n + 2, i.val] : SSet.{u}) cardinal.{u} :=
      finite_source_presentable _
    exact min_isCardinalPresentable _ _
  · change IsCardinalPresentable (withEdges (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u})
      {leftHornEdgeSimplex.{u} n}) cardinal.{u}
    let _ : IsCardinalPresentable (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) cardinal.{u} :=
      finite_source_presentable _
    exact withEdges_isCardinalPresentable _ _ (Set.finite_singleton _) _
  · fin_cases i
    · change IsCardinalPresentable (min (Δ[0] : SSet.{u})) cardinal.{u}
      let _ : IsCardinalPresentable (Δ[0] : SSet.{u}) cardinal.{u} := finite_source_presentable _
      exact min_isCardinalPresentable _ _
    · change IsCardinalPresentable (withEdges (Δ[2] : SSet.{u}) compositionShortEdges.{u}) cardinal.{u}
      let _ : IsCardinalPresentable (Δ[2] : SSet.{u}) cardinal.{u} := finite_source_presentable _
      exact withEdges_isCardinalPresentable _ _ ((Set.finite_singleton (yonedaEquiv (stdSimplex.δ.{u} (0 :
        Fin 3)))).insert
        (yonedaEquiv (stdSimplex.δ.{u} (2 : Fin 3)))) _
    · change IsCardinalPresentable (min KanEdgeDetector.object.{u}) cardinal.{u}
      let _ : IsCardinalPresentable KanEdgeDetector.object.{u} cardinal.{u} := detector_presentable
      exact min_isCardinalPresentable _ _

end SSet.Marked.CellSmallness
