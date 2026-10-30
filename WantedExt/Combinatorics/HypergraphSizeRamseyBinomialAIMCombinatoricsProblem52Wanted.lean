/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dudek–Rödl: is `r̂₃(n, n) = C(r₃(n, n), 3)`? (AIM Graph Ramsey theory, Problem 1.08)

AimPL: Graph Ramsey Theory, Section 1, item 4 "Hypergraph size Ramsey numbers", Problem 1.08
[Andrzej Dudek] (Dudek–Rödl): the size Ramsey number `r̂(n, n)` is the minimum number `m` for which
there exists a graph with `m` edges such that every 2-edge-coloring of it produces a monochromatic
`K_n`; `r̂₃(n, n)` is the corresponding 3-uniform size Ramsey number. For graphs
`r̂(n, n) = C(r(n, n), 2)`. Is `r̂₃(n, n) = C(r₃(n, n), 3)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.Combinatorics.HypergraphSizeRamseyBinomialAIMCombinatoricsProblem52Wanted

/-!
Source: AimPL: Graph Ramsey Theory, Problem 1.08 [Andrzej Dudek] (Dudek–Rödl),
http://aimpl.org/graphramsey/1/; the same question is Question 2.2 of A. Dudek, S. La Fleur,
D. Mubayi and V. Rödl, On the size-Ramsey number of hypergraphs, J. Graph Theory 86 (2017),
arXiv:1503.06304. UnsolvedMath record UM-20000927 (`AIM-COMBINATORICS-0052`), dataset
ulamai/UnsolvedMath v1.8.0.

A 3-graph is a finite family of 3-subsets of `Fin N` (any `N`); a copy of `K_n^{(3)}` in it is an
`n`-set all of whose triples are edges, monochromatic when all those triples get one colour. Both
numbers are defined by `sInf` (the sets are nonempty by Ramsey's theorem). `ramsey3` is the
definition of the OpenConjectures entry `AIMCombinatoricsProblem53` (the "In particular" part of
the same AimPL item), copied here under the same name because WantedExt cannot import
OpenConjectures. For `n ≤ 3` both sides agree (`0, 0, 0, 1`); the question is posed for every `n`,
so the refutation is of the universal statement.
-/

/-- The 3-graph `H` on `Fin N` arrows `K_n^{(3)}`: under every 2-colouring of its triples there is
an `n`-set all of whose triples are edges of `H` of one colour. -/
def Arrows3 {N : ℕ} (H : Finset (Finset (Fin N))) (n : ℕ) : Prop :=
  ∀ c : Finset (Fin N) → Bool, ∃ S : Finset (Fin N), S.card = n ∧
    ∃ col : Bool, ∀ f ⊆ S, f.card = 3 → f ∈ H ∧ c f = col

/-- The 3-uniform diagonal Ramsey number `r₃(n, n)`: the least `N` such that every 2-colouring of
the triples of `Fin N` has an `n`-set all of whose triples have one colour (copied from the
OpenConjectures entry `AIMCombinatoricsProblem53`). -/
noncomputable def ramsey3 (n : ℕ) : ℕ :=
  sInf {N | ∀ c : Finset (Fin N) → Bool, ∃ S : Finset (Fin N), S.card = n ∧
    ∃ col : Bool, ∀ f ⊆ S, f.card = 3 → c f = col}

/-- The 3-uniform size Ramsey number `r̂₃(n, n)`: the least number of edges of a 3-graph that
arrows `K_n^{(3)}`. -/
noncomputable def sizeRamsey3 (n : ℕ) : ℕ :=
  sInf {m | ∃ (N : ℕ) (H : Finset (Finset (Fin N))), (∀ e ∈ H, e.card = 3) ∧ H.card = m ∧
    Arrows3 H n}

/-- Problem 1.08 (Dudek–Rödl): `r̂₃(n, n) = C(r₃(n, n), 3)` for every `n`. -/
def sizeRamseyEqualsBinomial : Prop :=
  ∀ n : ℕ, sizeRamsey3 n = (ramsey3 n).choose 3

/--
Resolved false: McKay shows that `K_13^{(3)}` with one triple removed cannot be 2-coloured
without a monochromatic `K_4^{(3)}`; since `r₃(4, 4) = 13` (McKay and Radziszowski, 1991, recalled
in the same paper) this gives `r̂₃(4, 4) ≤ 285 < 286 = C(13, 3)`, "which answers Dudek et al.'s
question in the negative". Source: AimPL: Graph Ramsey Theory, Problem 1.08 [Andrzej Dudek]
(Dudek–Rödl), http://aimpl.org/graphramsey/1/ (Question 2.2 of Dudek, La Fleur, Mubayi and Rödl,
J. Graph Theory 86 (2017)); resolution: B. D. McKay, A class of Ramsey-extremal hypergraphs,
Trans. Comb. 6 (2017), no. 3, 37-43, arXiv:1608.07762, abstract and Section 3 (last paragraph),
https://toc.ui.ac.ir/article_21468.html.
-/
public theorem_wanted sizeRamseyEqualsBinomial_refuted : ¬ sizeRamseyEqualsBinomial

end MathlibExt.Combinatorics.HypergraphSizeRamseyBinomialAIMCombinatoricsProblem52Wanted
