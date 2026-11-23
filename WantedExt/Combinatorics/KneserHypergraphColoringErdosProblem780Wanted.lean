/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Colorings of the complete `r`-uniform hypergraph (Erdős Problem 780)

Erdős Problem 780: suppose `n ≥ k r + (t - 1)(k - 1)` and the edges of the complete `r`-uniform
hypergraph on `n` vertices are colored with `t` colors. Prove that some color class contains `k`
pairwise disjoint edges.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.KneserHypergraphColoringErdosProblem780Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #780, https://www.erdosproblems.com/780 (status
PROVED). UnsolvedMath record UM-30007030 (`EP-780`), dataset ulamai/UnsolvedMath v1.8.0.

A coloring is any `c : Finset (Fin n) → Fin t` (only its values on `r`-subsets matter). The
statement assumes `r ≥ 1` and `t ≥ 1`: for `r = 0` the empty set is the only edge and is disjoint
from itself, and `t = 0` admits no coloring of a nonempty hypergraph. `MathlibExt` proves the Kneser
graph case `k = 2` (Lovász, `MathlibExt.Combinatorics.SimpleGraph.KneserLovasz`), not the general
statement. Compared with the formal-conjectures statement `ErdosProblems/780.lean` (equivalent; no
code imported).
-/

/-- **Erdős's Kneser hypergraph problem.** The statement that for all natural numbers
$n, k, r, t$ with $r \ge 1$, $t \ge 1$ and $n \ge kr + (t - 1)(k - 1)$, every coloring of the
$r$-element subsets of $\{0, \dots, n - 1\}$ with $t$ colors has a color class containing $k$
pairwise disjoint $r$-element subsets. -/
def kneserHypergraphColoring : Prop :=
  ∀ n k r t : ℕ, 1 ≤ r → 1 ≤ t → k * r + (t - 1) * (k - 1) ≤ n →
    ∀ c : Finset (Fin n) → Fin t, ∃ (i : Fin t) (E : Finset (Finset (Fin n))),
      E ⊆ (Finset.univ : Finset (Fin n)).powersetCard r ∧ E.card = k ∧ (∀ e ∈ E, c e = i) ∧
        (E : Set (Finset (Fin n))).PairwiseDisjoint id

/--
**Alon–Frankl–Lovász theorem on Kneser hypergraphs.** For all natural numbers $n, k, r, t$ with
$r \ge 1$, $t \ge 1$ and $n \ge kr + (t - 1)(k - 1)$, every coloring of the $r$-element subsets
of $\{0, \dots, n - 1\}$ with $t$ colors has a color class containing $k$ pairwise disjoint
$r$-element subsets.

Alon, Frankl and Lovász proved this for all positive $n, k, r, t$ (Theorem 1.1; the case $k = 2$
is Lovász's proof of Kneser's conjecture), and the bound on $n$ is sharp; erdosproblems.com/780
lists the problem as proved.

Source: T. F. Bloom, Erdős Problems, Problem
#780, https://www.erdosproblems.com/780 (status PROVED); resolution: N. Alon, P. Frankl and L.
Lovász, The chromatic number of Kneser hypergraphs, Trans. Amer. Math. Soc. 298 (1986), 359-370,
Theorem 1.1: for positive integers n, k, r, t with n ≥ kr + (t - 1)(k - 1), if the r-subsets of an
n-element set are partitioned into t families then one family contains k pairwise disjoint r-sets
(conjectured by Erdős in 1973; k = 2 is Kneser's conjecture, proved by Lovász),
https://web.math.princeton.edu/~nalon/PDFS/Publications/The%20chromatic%20number%20of%20Kneser%20hypergraphs.pdf.
-/
public theorem_wanted kneserHypergraphColoring_holds : kneserHypergraphColoring

end MathlibExt.Combinatorics.KneserHypergraphColoringErdosProblem780Wanted
