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
# Nondegenerate interior presentations of realization points

Every point of a simplicial-set realization is represented by a nondegenerate
simplex and a standard-simplex point with all barycentric coordinates strictly
positive. A simplex presentation can be reduced to a nondegenerate carrier,
and the degeneracy pushforward preserves the positive-coordinate presentation.
The statement is valid in every simplicial-set universe.
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

/--
Every point of `|Y|` has a presentation by a nondegenerate simplex of `Y`
and a strictly positive barycentric point of its standard simplex, transported
through the realization homeomorphism.
-/
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
