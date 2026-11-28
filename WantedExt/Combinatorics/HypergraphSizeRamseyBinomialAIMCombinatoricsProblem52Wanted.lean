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

/-- **Hypergraph arrowing the complete 3-uniform hypergraph.** Let $H$ be a family of subsets of
$\{0, \dots, N-1\}$ and let $n$ be a natural number. Then $H$ arrows $K_n^{(3)}$ when for every
colouring of the subsets of $\{0, \dots, N-1\}$ with two colours there exist an $n$-element set
$S \subseteq \{0, \dots, N-1\}$ and a colour such that every 3-element subset of $S$ belongs to
$H$ and has that colour. -/
def Arrows3 {N : ℕ} (H : Finset (Finset (Fin N))) (n : ℕ) : Prop :=
  ∀ c : Finset (Fin N) → Bool, ∃ S : Finset (Fin N), S.card = n ∧
    ∃ col : Bool, ∀ f ⊆ S, f.card = 3 → f ∈ H ∧ c f = col

/-- **Diagonal 3-uniform Ramsey number.** For a natural number $n$, the Ramsey number
$r_3(n, n)$ is the least natural number $N$ such that for every colouring of the subsets of
$\{0, \dots, N-1\}$ with two colours there is an $n$-element set $S \subseteq \{0, \dots, N-1\}$
all of whose 3-element subsets have the same colour.

Source: definition copied from the OpenConjectures entry `AIMCombinatoricsProblem53`. -/
noncomputable def ramsey3 (n : ℕ) : ℕ :=
  sInf {N | ∀ c : Finset (Fin N) → Bool, ∃ S : Finset (Fin N), S.card = n ∧
    ∃ col : Bool, ∀ f ⊆ S, f.card = 3 → c f = col}

/-- **3-uniform size Ramsey number.** For a natural number $n$, the size Ramsey number
$\hat r_3(n, n)$ is the least natural number $m$ such that for some $N$ there is a 3-uniform
hypergraph $H$ on $\{0, \dots, N-1\}$ with exactly $m$ edges that arrows $K_n^{(3)}$. -/
noncomputable def sizeRamsey3 (n : ℕ) : ℕ :=
  sInf {m | ∃ (N : ℕ) (H : Finset (Finset (Fin N))), (∀ e ∈ H, e.card = 3) ∧ H.card = m ∧
    Arrows3 H n}

/-- **Dudek–Rödl size Ramsey question.** The statement that for every natural number $n$ the
3-uniform size Ramsey number $\hat r_3(n, n)$ equals the binomial coefficient
$\binom{r_3(n, n)}{3}$, where $r_3(n, n)$ is the diagonal 3-uniform Ramsey number (AimPL Graph
Ramsey Theory, Problem 1.08). -/
def sizeRamseyEqualsBinomial : Prop :=
  ∀ n : ℕ, sizeRamsey3 n = (ramsey3 n).choose 3

/--
**The Dudek–Rödl size Ramsey question has a negative answer.** It is not true that for every
natural number $n$ the 3-uniform size Ramsey number $\hat r_3(n, n)$ equals the binomial
coefficient $\binom{r_3(n, n)}{3}$, where $r_3(n, n)$ is the diagonal 3-uniform Ramsey number.

McKay shows that the complete 3-uniform hypergraph $K_{13}^{(3)}$ on 13 vertices with one triple
removed cannot be 2-coloured without a monochromatic copy of the complete 3-uniform hypergraph
$K_4^{(3)}$ on 4 vertices; since $r_3(4, 4) = 13$ (McKay and Radziszowski, 1991, recalled in the
same paper) this gives $\hat r_3(4, 4) \le 285 < 286 = \binom{13}{3}$, "which answers Dudek et
al.'s question in the negative".

Source: AimPL: Graph Ramsey Theory, Problem 1.08 [Andrzej Dudek]
(Dudek–Rödl), http://aimpl.org/graphramsey/1/ (Question 2.2 of Dudek, La Fleur, Mubayi and Rödl,
J. Graph Theory 86 (2017)); resolution: B. D. McKay, A class of Ramsey-extremal hypergraphs,
Trans. Comb. 6 (2017), no. 3, 37-43, arXiv:1608.07762, abstract and Section 3 (last paragraph),
https://toc.ui.ac.ir/article_21468.html.
-/
public theorem_wanted sizeRamseyEqualsBinomial_refuted : ¬ sizeRamseyEqualsBinomial

end MathlibExt.Combinatorics.HypergraphSizeRamseyBinomialAIMCombinatoricsProblem52Wanted
