/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationOpenCellCover

/-!
# Open-cell cover dimension-zero regression

Direct universe-zero client of
`SSet.exists_nonDegenerate_interior_presentation` at `Y = Δ[0]`: for an
arbitrary realization point, expose the theorem's witnesses and return both
pointwise strict positivity of the standard-simplex coordinate and the exact
realization equation. Unfolds only the public open-cell predicate; claims no
uniqueness, coordinate equality, or positive-dimensional fact.
-/

@[expose] public section

open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory.SSetRealizationOpenCellCoverTests

/-- Dimension-zero cover: every point of `|Δ[0]|` has a nondegenerate interior
presentation with a strictly positive coordinate. -/
theorem exists_zero_interior_pos (x : SSet.toTop.obj (Δ[0] : SSet.{0})) :
    ∃ (n : ℕ) (s : (Δ[0] : SSet.{0}) _⦋n⦌) (_ : s ∈ (Δ[0] : SSet.{0}).nonDegenerate n)
      (q : Convexity.StdSimplex ℝ (Fin (n + 1))),
      (∀ i, 0 < q.weights i) ∧
        SSet.toTop.map (SSet.yonedaEquiv.symm s)
          ((SSet.stdSimplex.toTopIso ⦋n⦌).inv q) = x := by
  obtain ⟨n, s, hs, q, hq, hx⟩ :=
    SSet.exists_nonDegenerate_interior_presentation (Δ[0] : SSet.{0}) x
  refine ⟨n, s, hs, q, ?_, hx⟩
  simpa [SSet.realizationCellInterior.openCell, Set.mem_ofPred_eq] using hq

#print axioms exists_zero_interior_pos

end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory.SSetRealizationOpenCellCoverTests
