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

/-- `K_n` has a `(4, 5)`-colouring with `k` colours: a symmetric colouring `c` of the pairs of
vertices such that the six edges of every `K_4` receive at least five distinct colours. -/
def HasFourFiveColouring (n k : ℕ) : Prop :=
  ∃ c : Fin n → Fin n → Fin k, (∀ x y, c x y = c y x) ∧ ∀ v : Fin 4 ↪ Fin n,
    5 ≤ ((Finset.univ : Finset (Fin 4)).offDiag.image fun q => c (v q.1) (v q.2)).card

/-- `f(n)`: the least number of colours in a `(4, 5)`-colouring of `K_n`. -/
noncomputable def fourFiveColourNumber (n : ℕ) : ℕ :=
  sInf {k : ℕ | HasFourFiveColouring n k}

/-- Erdős Problem 136: `f(n) = (5/6 + o(1)) n`. -/
def fourFiveColourNumberAsymptotic : Prop :=
  Tendsto (fun n : ℕ => (fourFiveColourNumber n : ℝ) / n) atTop (nhds (5 / 6))

/--
Resolved true: Erdős and Gyárfás proved `f(n) > 5(n - 1)/6`, and Bennett, Cushman, Dudek and Prałat
constructed `(4, 5)`-colourings of `K_n` with `5n/6 + o(n)` colours (Joos and Mubayi gave a shorter
proof), so `f(n) ~ 5n/6`; erdosproblems.com/136 records this. Source: T. F. Bloom, Erdős Problems,
Problem #136, https://www.erdosproblems.com/136 (status SOLVED); resolution: P. Bennett, R. Cushman,
A. Dudek and P. Prałat, The Erdős-Gyárfás function f(n, 4, 5) = 5n/6 + o(n) - so Gyárfás was right,
arXiv:2207.02920 (2022); F. Joos and D. Mubayi, Ramsey theory constructions from hypergraph
matchings, arXiv:2208.12563 (2022), abstract: (4, 5)-colourings of K_n with 5n/6 + o(n) colours;
with the Erdős-Gyárfás lower bound f(n) > 5(n - 1)/6 this gives f(n) ~ 5n/6 (erdosproblems.com/136),
https://arxiv.org/abs/2207.02920.
-/
public theorem_wanted fourFiveColourNumberAsymptotic_holds : fourFiveColourNumberAsymptotic

end MathlibExt.Combinatorics.FourCliqueFiveColoursErdosProblem136Wanted
