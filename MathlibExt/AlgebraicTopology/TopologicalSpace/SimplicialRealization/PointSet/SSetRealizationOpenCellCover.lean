/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationCellInterior
public import MathlibExt.Analysis.Convex.StdSimplex

/-!
# Open-cell cover of the geometric realization

Every point of `SSet.toTop.obj Y` is presented by a nondegenerate simplex
together with a strictly positive coordinate, i.e. a point of
`SSet.realizationCellInterior.openCell`. The presentation is
universe-polymorphic (`SSet.{u}`) and transports points through
`SimplexCategory.toTopHomeo`; for `SSet.{0}` this agrees with the former
`SSet.stdSimplex.toTopIso` form by `rfl`, so universe-zero callers keep the
same effective call shape.

Scope: `SSet.{u}` for any universe `u`. No dimension-zero special casing is
needed beyond the interior provider.

Reuse map (accepted for this consolidation):
- `SSet.OpenCell.exists_openCell`
  (`SSetRealizationCellInterior.lean`): `reuse` for the initial interior
  (strictly positive) presentation.
- `SSet.exists_nonDegenerate` (pinned Eilenberg--Zilber): `reuse` for the
  degeneracy epi onto a nondegenerate simplex.
- `Convexity.StdSimplex.map_surjective_pos`
  (`MathlibExt/Analysis/Convex/StdSimplex.lean`): `reuse` (degeneracy
  pushforward preserves strict positivity).
- `SSet.yonedaEquiv_symm_naturality_left`
  (pinned `Mathlib/AlgebraicTopology/SimplicialSet/StdSimplex.lean`): `reuse`.
- `SimplexCategory.toTopHomeo_symm_naturality_apply`
  (pinned `Mathlib/AlgebraicTopology/SimplicialSet/TopAdj.lean`): `reuse`
  for the realized degeneracy transport.
- No new reusable construction beyond the existence statement below.

Nonclaims: no uniqueness of the cell, no injectivity, no compact-support or
local-finiteness, no product/pullback preservation, no KQ4 result.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped Simplicial

namespace SSet

/-- Realized degeneracy transport: factoring the presenting simplex through a
simplicial degeneracy epi transports the realized presentation to the
nondegenerate simplex at the mapped interior point. -/
private theorem degeneracy_transport {T : SSet.{u}} {d m : ℕ}
    (f : ⦋d⦌ ⟶ ⦋m⦌) (v : T _⦋m⦌)
    (y : SSet.toTop.obj (SSet.stdSimplex.obj ⦋d⦌)) :
    SSet.toTop.map (SSet.yonedaEquiv.symm (T.map f.op v)) y =
      SSet.toTop.map (SSet.yonedaEquiv.symm v)
        ((SimplexCategory.toTopHomeo ⦋m⦌).symm
          (Convexity.StdSimplex.map (⇑f.toOrderHom)
            ((SimplexCategory.toTopHomeo ⦋d⦌) y))) := by
  have hyon : SSet.stdSimplex.map f ≫ SSet.yonedaEquiv.symm v =
      SSet.yonedaEquiv.symm (T.map f.op v) :=
    SSet.yonedaEquiv_symm_naturality_left f _
  have hface : SSet.toTop.map (SSet.stdSimplex.map f) y =
      (SimplexCategory.toTopHomeo ⦋m⦌).symm
        (Convexity.StdSimplex.map (⇑f.toOrderHom)
          ((SimplexCategory.toTopHomeo ⦋d⦌) y)) := by
    have hnat := SimplexCategory.toTopHomeo_symm_naturality_apply f
      ((SimplexCategory.toTopHomeo ⦋d⦌) y)
    conv_lhs => rw [← Homeomorph.symm_apply_apply (SimplexCategory.toTopHomeo ⦋d⦌) y]
    exact hnat.symm
  rw [← hyon, SSet.toTop.map_comp, TopCat.comp_app, hface]

/-- Every realization point has a nondegenerate interior presentation: a
nondegenerate simplex whose standard-simplex coordinate lies in the
positive-coordinate open cell. Universe-polymorphic (`SSet.{u}`) via
`SimplexCategory.toTopHomeo`. -/
theorem exists_nonDegenerate_interior_presentation (Y : SSet.{u})
    (x : SSet.toTop.obj Y) :
    ∃ (n : ℕ) (s : Y _⦋n⦌) (_ : s ∈ Y.nonDegenerate n)
      (q : Convexity.StdSimplex ℝ (Fin (n + 1))),
      q ∈ SSet.realizationCellInterior.openCell n ∧
      SSet.toTop.map (SSet.yonedaEquiv.symm s)
        ((SimplexCategory.toTopHomeo ⦋n⦌).symm q) = x := by
  obtain ⟨d, s, y, hy, hq⟩ := SSet.OpenCell.exists_openCell Y x
  obtain ⟨m, f, hf, ⟨v, hv⟩, ht⟩ := Y.exists_nonDegenerate s
  have := hf
  set q : Convexity.StdSimplex ℝ (Fin (m + 1)) :=
    Convexity.StdSimplex.map (⇑f.toOrderHom)
      ((SimplexCategory.toTopHomeo ⦋d⦌) y) with hqdef
  have hqpos : ∀ j, 0 < q.weights j := by
    intro j
    rw [hqdef]
    exact Convexity.StdSimplex.map_surjective_pos
      (SimplexCategory.epi_iff_surjective.mp inferInstance) hq j
  have hqmem : q ∈ SSet.realizationCellInterior.openCell m := hqpos
  refine ⟨m, v, hv, q, hqmem, ?_⟩
  subst ht
  rw [← degeneracy_transport f v y]
  exact hy

end SSet
