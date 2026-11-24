/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Edges of hypergraphs with given chromatic number (Erdős Problem 832)

Erdős Problem 832: let `r ≥ 3` and `k` be sufficiently large in terms of `r`. Does every `r`-uniform
hypergraph with chromatic number `k` have at least `C((r - 1)(k - 1) + 1, r)` edges, with equality
only for the complete hypergraph on `(r - 1)(k - 1) + 1` vertices?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Filter.AtTopBot.Defs
public import WantedExt.Combinatorics.HypergraphColoringShared

@[expose] public section

namespace MathlibExt.Combinatorics.HypergraphChromaticEdgeCountErdosProblem832Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #832, https://www.erdosproblems.com/832 (status
DISPROVED). UnsolvedMath record UM-30007052 (`EP-832`), dataset ulamai/UnsolvedMath v1.8.0.

Hypergraphs are finite sets of `r`-element edges on `Fin n`; chromatic number `k` means
`k`-colorable and not `(k - 1)`-colorable, a coloring being proper when no edge is monochromatic.
The complete hypergraph on `S` is `S.powersetCard r`. Compared with the formal-conjectures statement
`ErdosProblems/832.lean` (equivalent; no code imported).
-/

open MathlibExt.Combinatorics.HypergraphColoringShared

/-- **Erdős Problem 832.** The statement that for every integer $r \ge 3$ there is a $K$ such that
for every $k \ge K$, every $n$ and every $r$-uniform hypergraph $H$ on the vertex set
$\{0, \dots, n-1\}$ with chromatic number $k$ (it is $k$-colorable but not $(k-1)$-colorable),
$H$ has at least $\binom{(r-1)(k-1)+1}{r}$ edges, and if it has exactly that many edges then it is
the complete $r$-uniform hypergraph on some set of $(r-1)(k-1)+1$ of its vertices. -/
def chromaticEdgeLowerBound : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ᶠ k : ℕ in Filter.atTop, ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
    (∀ e ∈ H, e.card = r) → HypergraphColorable H k → ¬ HypergraphColorable H (k - 1) →
      ((r - 1) * (k - 1) + 1).choose r ≤ H.card ∧
        (H.card = ((r - 1) * (k - 1) + 1).choose r →
          ∃ S : Finset (Fin n), S.card = (r - 1) * (k - 1) + 1 ∧ H = S.powersetCard r)

/-- **Alon's refutation of Erdős Problem 832.** There is an integer $r \ge 3$ such that for
infinitely many $k$ there are an $n$ and an $r$-uniform hypergraph $H$ on the vertex set
$\{0, \dots, n-1\}$ with chromatic number $k$ (it is $k$-colorable but not $(k-1)$-colorable)
that either has fewer than $\binom{(r-1)(k-1)+1}{r}$ edges, or has exactly that many edges but is
not the complete $r$-uniform hypergraph on any set of $(r-1)(k-1)+1$ of its vertices.

Alon deduced this from an upper bound through Turán numbers: for an absolute constant $C$, every
$r \ge C$ and every $k \ge Cr$, some $r$-uniform hypergraph with chromatic number at least $k$ has
at most $(7/8)^r \binom{(r-1)(k-1)+1}{r}$ edges, and an edge-minimal one among these has
chromatic number exactly $k$. Known Turán bounds disprove the conjecture for every $r \ge 4$; the
case $r = 3$ is open.

Source: T. F. Bloom, Erdős Problems, Problem #832,
https://www.erdosproblems.com/832 (status DISPROVED); resolution: N. Alon, Hypergraphs with high
chromatic number, Graphs Combin. 1 (1985), 387-389, with f(k, s) the least number of edges of a
k-uniform hypergraph of chromatic number at least s: 'Erdős and Hajnal conjectured that for every
fixed k, if s > s_0(k) then equality holds in (2)' (f(k, s) = C((s - 1)(k - 1) + 1, k)), and 'This
conjecture is false, as easily follows from' Proposition 1 (an upper bound for f(k, s) through Turán
numbers); erdosproblems.com/832: for an absolute C, r ≥ C and k ≥ C r there is an r-uniform
hypergraph with chromatic number at least k and at most (7/8)^r C((r - 1)(k - 1) + 1, r) edges,
known Turán bounds disprove the conjecture for every r ≥ 4, and r = 3 remains open,
https://web.math.princeton.edu/~nalon/PDFS/Publications/Hypergraphs%20with%20high%20chromatic%20number.pdf.
-/
public theorem_wanted chromaticEdgeLowerBound_refuted : ¬ chromaticEdgeLowerBound

end MathlibExt.Combinatorics.HypergraphChromaticEdgeCountErdosProblem832Wanted
