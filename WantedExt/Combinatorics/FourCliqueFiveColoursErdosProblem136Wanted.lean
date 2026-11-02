/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Edge colourings in which every K₄ sees five colours (Erdős Problem 136)

Erdős Problem 136: let `f(n)` be the smallest number of colours needed to colour the edges of `K_n`
so that every `K_4` contains at least `5` colours. Determine the size of `f(n)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.FourCliqueFiveColoursErdosProblem136Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #136, https://www.erdosproblems.com/136 (status
SOLVED). UnsolvedMath record UM-30006737 (`EP-136`), dataset ulamai/UnsolvedMath v1.8.0.

The determination is the asymptotic `f(n) = (5/6 + o(1)) n`. A colouring is a symmetric map on pairs
of vertices (the diagonal is unused). Compared with the formal-conjectures statement
`ErdosProblems/136.lean` (equivalent; no code imported).
-/

open Filter

/-- **$(4, 5)$-colourings of $K_n$.** For natural numbers $n$ and $k$, the complete graph $K_n$ on
the vertices $0, 1, \dots, n - 1$ has a $(4, 5)$-colouring with $k$ colours if there is a map $c$
assigning to every ordered pair $(x, y)$ of vertices one of $k$ colours, with $c(x, y) = c(y, x)$
for all $x, y$, such that for any four distinct vertices the six edges between them receive at
least five distinct colours. -/
def HasFourFiveColouring (n k : ℕ) : Prop :=
  ∃ c : Fin n → Fin n → Fin k, (∀ x y, c x y = c y x) ∧ ∀ v : Fin 4 ↪ Fin n,
    5 ≤ ((Finset.univ : Finset (Fin 4)).offDiag.image fun q => c (v q.1) (v q.2)).card

/-- **The $(4, 5)$-colouring number $f(n)$.** For a natural number $n$, $f(n)$ is the least
natural number $k$ such that $K_n$ has a $(4, 5)$-colouring with $k$ colours; such a $k$
always exists. -/
noncomputable def fourFiveColourNumber (n : ℕ) : ℕ :=
  sInf {k : ℕ | HasFourFiveColouring n k}

/-- **The asymptotic of the $(4, 5)$-colouring number (Erdős Problem 136).** Let $f(n)$ be the
least number of colours in a $(4, 5)$-colouring of $K_n$. This is the proposition that $f(n)/n$
tends to $5/6$ as $n \to \infty$; equivalently, $f(n) = (5/6 + o(1))\, n$. -/
def fourFiveColourNumberAsymptotic : Prop :=
  Tendsto (fun n : ℕ => (fourFiveColourNumber n : ℝ) / n) atTop (nhds (5 / 6))

/--
**Erdős Problem 136: the $(4, 5)$-colouring number of $K_n$ is asymptotically $5n/6$.** Let
$f(n)$ be the least number of colours in a $(4, 5)$-colouring of $K_n$, that is, a symmetric
colouring of the pairs of vertices of $K_n$ in which the six edges of every $K_4$ receive at
least five distinct colours. Then $f(n)/n \to 5/6$ as $n \to \infty$.

Erdős and Gyárfás proved $f(n) > 5(n - 1)/6$, and Bennett, Cushman, Dudek and Prałat constructed
$(4, 5)$-colourings of $K_n$ with $5n/6 + o(n)$ colours (Joos and Mubayi gave a shorter proof).

Source: T. F. Bloom, Erdős Problems,
Problem #136, https://www.erdosproblems.com/136 (status SOLVED); resolution: P. Bennett, R. Cushman,
A. Dudek and P. Prałat, The Erdős-Gyárfás function f(n, 4, 5) = 5n/6 + o(n) - so Gyárfás was right,
arXiv:2207.02920 (2022); F. Joos and D. Mubayi, Ramsey theory constructions from hypergraph
matchings, arXiv:2208.12563 (2022), abstract: (4, 5)-colourings of K_n with 5n/6 + o(n) colours;
with the Erdős-Gyárfás lower bound f(n) > 5(n - 1)/6 this gives f(n) ~ 5n/6 (erdosproblems.com/136),
https://arxiv.org/abs/2207.02920.
-/
public theorem_wanted fourFiveColourNumberAsymptotic_holds : fourFiveColourNumberAsymptotic

end MathlibExt.Combinatorics.FourCliqueFiveColoursErdosProblem136Wanted
