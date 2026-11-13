/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Edge-disjoint monochromatic triangles (Erdős Problem 76)

Erdős Problem 76 (Erdős, Faudree and Ordman): is it true that in any `2`-colouring of the edges of
`K_n` there must exist at least `(1 + o(1)) n² / 12` many edge-disjoint monochromatic triangles?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.MonochromaticTrianglePackingErdosProblem76Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #76, https://www.erdosproblems.com/76 (status PROVED).
UnsolvedMath record UM-30006713 (`EP-76`), dataset ulamai/UnsolvedMath v1.8.0.

A `2`-colouring of `K_n` is a red graph `R` on `Fin n` with blue graph `Rᶜ`. Edge-disjoint triangles
are `3`-sets any two of which share at most one vertex. `(1 + o(1)) n² / 12` as a lower bound is:
for every `ε > 0` and large `n`, at least `(1 - ε) n² / 12`.
-/

/-- Erdős Problem 76 (Erdős, Faudree and Ordman): every `2`-colouring of the edges of `K_n` (red
graph `R`, blue graph its complement) has at least `(1 + o(1)) n² / 12` edge-disjoint
monochromatic triangles: for every `ε > 0` and large `n` there is a family of at least
`(1 - ε) n² / 12` monochromatic triangles, any two sharing at most one vertex. -/
def edgeDisjointMonochromaticTriangles : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, ∀ R : SimpleGraph (Fin n),
    ∃ T : Finset (Finset (Fin n)),
      (∀ t ∈ T, t.card = 3 ∧ ((∀ x ∈ t, ∀ y ∈ t, x ≠ y → R.Adj x y) ∨
        (∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ R.Adj x y))) ∧
      (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → (t ∩ t').card ≤ 1) ∧
      (1 - ε) * (n : ℝ) ^ 2 / 12 ≤ T.card

/--
Resolved true: Gruslys and Letzter proved that every `2`-edge-colouring of `K_n` contains `n²/12 +
o(n²)` edge-disjoint monochromatic triangles (best possible by two equal parts with red edges
between them); erdosproblems.com/76 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #76, https://www.erdosproblems.com/76 (status PROVED); resolution: V. Gruslys and
S. Letzter, Monochromatic triangle packings in red-blue graphs, arXiv:2008.05311 (2020), abstract:
every 2-edge-colouring of K_n has a collection of n²/12 + o(n²) edge-disjoint monochromatic
triangles, confirming a conjecture of Erdős; erdosproblems.com/76: proved by Gruslys and Letzter,
https://arxiv.org/abs/2008.05311.
-/
public theorem_wanted edgeDisjointMonochromaticTriangles_holds : edgeDisjointMonochromaticTriangles

end MathlibExt.GraphTheory.MonochromaticTrianglePackingErdosProblem76Wanted
