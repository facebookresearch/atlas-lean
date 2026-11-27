/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroToZerothHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

/-!
# Every realization path component contains a vertex

For any simplicial set `X`, every path component of its geometric realization
contains a realized vertex. A point is represented in a topological standard
simplex, where it can be joined to a vertex, and that path maps to `|X|`.
Consequently the canonical map from simplicial connected components to realized
path components is surjective.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

/-- Every point of `|Δ[n]|` is joined to some realized vertex. -/
private theorem exists_joined_stdSimplex_realizedVertex (n : ℕ)
    (y : SSet.toTop.obj (SSet.stdSimplex.obj ⦋n⦌)) :
    ∃ v : (SSet.stdSimplex.obj ⦋n⦌) _⦋0⦌, Joined y (SSet.realizedVertex v) := by
  have hNe : Nonempty (Fin (⦋n⦌.len + 1)) := ⟨⟨0, Nat.zero_lt_succ _⟩⟩
  have hStd : PathConnectedSpace (Convexity.StdSimplex ℝ (Fin (⦋n⦌.len + 1))) :=
    @Convexity.StdSimplex.pathConnectedSpace _ hNe
  have hTop : PathConnectedSpace ↥(SSet.toTop.obj (SSet.stdSimplex.obj ⦋n⦌)) :=
    @Homeomorph.pathConnectedSpace _ _ _ _ hStd (SimplexCategory.toTopHomeo ⦋n⦌).symm
  refine ⟨SSet.stdSimplex.obj₀Equiv.symm ⟨0, Nat.zero_lt_succ n⟩, ?_⟩
  exact @PathConnectedSpace.joined _ _ hTop _ _

/--
For every simplicial set, the canonical map from its simplicial connected
components to the path components of its geometric realization is surjective.
-/
theorem piZeroToZerothHomotopy_surjective (X : SSet.{u}) :
    Function.Surjective (piZeroToZerothHomotopy X) := by
  intro q
  obtain ⟨p, rfl⟩ := ZerothHomotopy.mk_surjective q
  obtain ⟨n, s, _, y, hy⟩ := SSet.exists_nonDegenerate_toTop_presentation X p
  obtain ⟨v, hv⟩ := exists_joined_stdSimplex_realizedVertex n y
  refine ⟨SSet.π₀.mk ((SSet.yonedaEquiv.symm s).app _ v), ?_⟩
  have hMap := hv.map (SSet.toTop.map (SSet.yonedaEquiv.symm s)).hom.continuous
  rw [hy] at hMap
  rw [← SSet.realizedVertex_naturality (SSet.yonedaEquiv.symm s) v] at hMap
  rw [SSet.piZeroToZerothHomotopy_mk]
  exact (ZerothHomotopy.sound hMap.somePath).symm

end SSet

end
