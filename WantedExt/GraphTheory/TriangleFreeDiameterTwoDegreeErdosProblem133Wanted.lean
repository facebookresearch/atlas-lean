/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Maximum degree of triangle-free graphs of diameter two (Erdős Problem 133)

Erdős Problem 133: let `f(n)` be minimal such that every triangle-free graph with `n` vertices and
diameter `2` has a vertex of degree `≥ f(n)`. What is the order of growth of `f(n)`? Does `f(n)/√n →
∞`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.TriangleFreeDiameterTwoDegreeErdosProblem133Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #133, https://www.erdosproblems.com/133 (status
DISPROVED). UnsolvedMath record UM-30006734 (`EP-133`), dataset ulamai/UnsolvedMath v1.8.0.

Both questions are targets. The order of growth is `f(n) = Θ(√n)`, stated as two-sided bounds for
all large `n`; `f(n)/√n → ∞` is the second target. Both are stated without naming `f`, the least
maximum degree of such a graph. Diameter `2` is written as: distinct vertices are adjacent or have a
common neighbour; for triangle-free graphs on `n ≥ 3` vertices this is diameter exactly `2`.
Compared with the formal-conjectures statement `ErdosProblems/133.lean` (the first target is
`erdos_133.variants.isTheta`, the second `erdos_133`; no code imported).
-/

open Filter

/-- Erdős Problem 133, first question (order of growth): `f(n) = Θ(√n)`, where `f(n)` is the least
maximum degree of a triangle-free graph on `n` vertices with diameter `2`; that is, there are
`c, C > 0` such that for all large `n` every triangle-free graph on `n` vertices in which any two
distinct vertices are adjacent or have a common neighbour has a vertex of degree at least `c √n`,
and some such graph has all degrees at most `C √n`. -/
def triangleFreeDiameterTwoDegreeOrderSqrt : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    (∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
      (∀ x y, x ≠ y → G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y) →
        ∃ v, c * Real.sqrt n ≤ (G.neighborSet v).ncard) ∧
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧
      (∀ x y, x ≠ y → G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y) ∧
        ∀ v, ((G.neighborSet v).ncard : ℝ) ≤ C * Real.sqrt n

/-- Erdős Problem 133, second question: `f(n)/√n → ∞`, where `f(n)` is the least maximum degree of
a triangle-free graph on `n` vertices with diameter `2`; that is, for every `K` and all large
`n`, every triangle-free graph on `n` vertices in which any two distinct vertices are adjacent or
have a common neighbour has a vertex of degree at least `K √n`. -/
def triangleFreeDiameterTwoDegreeSuperSqrt : Prop :=
  ∀ K : ℝ, ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
    (∀ x y, x ≠ y → G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y) →
      ∃ v, K * Real.sqrt n ≤ (G.neighborSet v).ncard

/--
Resolved: `f(n) = Θ(√n)`. A graph of maximum degree `d` and diameter `2` has at most `d² + 1`
vertices, so `f(n) ≥ (1 - o(1)) √n`; Hanson and Seyffarth constructed triangle-free Cayley graphs of
diameter `2` on `ℤ/nℤ` with maximum degree `(√2 + o(1)) √n` (Füredi and Seress: `(2/√3 + o(1)) √n`).
plby/lean-proofs proves `√n - 1 ≤ f(n) ≤ 4 √n` for `n ≥ 64`; erdosproblems.com/133 records these
bounds. Source: T. F. Bloom, Erdős Problems, Problem #133, https://www.erdosproblems.com/133 (status
DISPROVED); resolution: D. Hanson and K. Seyffarth, k-saturated graphs of prescribed maximum degree,
Congr. Numer. (1984), 169-182; Z. Füredi and Á. Seress, Maximal triangle-free graphs with
restrictions on the degrees, J. Graph Theory 18 (1994), 11-24, erdosproblems.com/133: f(n) ≥ (1 -
o(1)) √n since a graph of maximum degree d and diameter 2 has at most d² + 1 vertices; f(n) ≤ (√2 +
o(1)) √n (Hanson-Seyffarth) and f(n) ≤ (2/√3 + o(1)) √n (Füredi-Seress); formal proof of √n - 1 ≤
f(n) ≤ 4 √n for n ≥ 64 in plby/lean-proofs src/latest/ErdosProblems/Erdos133.lean.
-/
public theorem_wanted triangleFreeDiameterTwoDegreeOrderSqrt_holds :
    triangleFreeDiameterTwoDegreeOrderSqrt

/--
Resolved false: Hanson and Seyffarth constructed triangle-free Cayley graphs of diameter `2` on
`ℤ/nℤ` with maximum degree `(√2 + o(1)) √n`, and Füredi and Seress improved this to `(2/√3 + o(1))
√n`, so `f(n) = O(√n)`; erdosproblems.com/133 lists the problem as disproved. Source: T. F. Bloom,
Erdős Problems, Problem #133, https://www.erdosproblems.com/133 (status DISPROVED); resolution: D.
Hanson and K. Seyffarth, k-saturated graphs of prescribed maximum degree, Congr. Numer. (1984),
169-182; Z. Füredi and Á. Seress, Maximal triangle-free graphs with restrictions on the degrees, J.
Graph Theory 18 (1994), 11-24, erdosproblems.com/133: f(n) ≥ (1 - o(1)) √n since a graph of maximum
degree d and diameter 2 has at most d² + 1 vertices; f(n) ≤ (√2 + o(1)) √n (Hanson-Seyffarth) and
f(n) ≤ (2/√3 + o(1)) √n (Füredi-Seress); formal proof of √n - 1 ≤ f(n) ≤ 4 √n for n ≥ 64 in
plby/lean-proofs src/latest/ErdosProblems/Erdos133.lean.
-/
public theorem_wanted triangleFreeDiameterTwoDegreeSuperSqrt_refuted :
    ¬ triangleFreeDiameterTwoDegreeSuperSqrt

end MathlibExt.GraphTheory.TriangleFreeDiameterTwoDegreeErdosProblem133Wanted
