/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroToZerothHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

/-!
# Surjectivity of simplicial π₀ to realized path components

For any simplicial set `X`, the canonical map
`SSet.piZeroToZerothHomotopy X` to the path components of its realization is
surjective. The presentation `SSet.exists_nonDegenerate_toTop_presentation`
places each realization point in a realized standard simplex, whose path
connectedness joins it to a vertex. Naturality of realized vertices and
`ZerothHomotopy.sound` identify the resulting path component with the image
of that vertex.
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

/-- Canonical map from simplicial `π₀` to realized path components is surjective. -/
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
