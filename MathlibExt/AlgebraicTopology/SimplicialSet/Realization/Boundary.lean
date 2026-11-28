/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Analysis.Convex.StdSimplex

/-!
# A zero barycentric coordinate gives realized-boundary membership

Identify the realization of Δ[n] with the real standard simplex of nonnegative weights summing
to one. If a barycentric point p has p.weights(j)=0, it belongs to the face omitting vertex j,
and its corresponding realized point lies in the image of |∂Δ[n]| → |Δ[n]|.

For n>0, the face map inserts the zero coordinate and factors through the simplicial boundary.
In dimension zero the unique weight is one, so a vanishing-coordinate hypothesis is
impossible. The statement retains every n : ℕ and every simplicial-set universe.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

/-- Realized simplex-boundary membership from a vanishing coordinate.

For p in the real standard n-simplex and j ∈ Fin(n+1), if p.weights(j)=0, then the realized
point corresponding to p under the canonical simplex homeomorphism belongs to the range of
|∂Δ[n]| → |Δ[n]|. This holds in all natural dimensions, with the dimension-zero hypothesis
vacuous. -/
theorem mem_realizedBoundary_of_zeroCoord (n : ℕ)
    (p : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : p.weights j = 0) :
    (⦋n⦌.toTopHomeo).symm p ∈
      Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} n).ι) := by
  cases n with
  | zero =>
    exfalso
    have hsum := Convexity.StdSimplex.total_of_fintype p
    have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    have huniv : (Finset.univ : Finset (Fin (0 + 1))) = {j} := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim x j
    rw [huniv, Finset.sum_singleton] at hsum
    rw [hj] at hsum
    exact zero_ne_one hsum
  | succ m =>
    have hmem :
        p ∈ Set.range (Convexity.StdSimplex.map (Fin.succAbove j)) := by
      rw [Convexity.StdSimplex.mem_range_map_iff]
      intro y hy
      rw [Fin.range_succAbove] at hy
      have hyj : y = j := by simpa using hy
      rw [hyj]
      exact hj
    obtain ⟨q, hq⟩ := hmem
    have hδ_eq : (SSet.stdSimplex.δ (n := m) j : (Δ[m] : SSet.{u}) ⟶
        (Δ[m + 1] : SSet.{u})) =
        SSet.stdSimplex.map (SimplexCategory.δ (n := m) j) := rfl
    have hcoe : (⇑(SimplexCategory.δ (n := m) j) :
        Fin (m + 1) → Fin (m + 2)) = Fin.succAbove j := rfl
    have hsym : (⦋m + 1⦌.toTopHomeo).symm p =
        SSet.toTop.map (SSet.stdSimplex.δ (n := m) j)
          ((⦋m⦌.toTopHomeo).symm q) := by
      have hnat := SimplexCategory.toTopHomeo_symm_naturality_apply
        (f := SimplexCategory.δ (n := m) j) (x := q)
      rw [← hq]
      rw [hδ_eq]
      simpa [hcoe] using hnat
    refine ⟨SSet.toTop.map (SSet.boundary.ι (n := m) j)
      ((⦋m⦌.toTopHomeo).symm q), ?_⟩
    rw [hsym]
    have hEq := congrArg SSet.toTop.map (SSet.boundary.ι_ι (n := m) j)
    rw [Functor.map_comp] at hEq
    exact ConcreteCategory.congr_hom hEq ((⦋m⦌.toTopHomeo).symm q)

end SSet
