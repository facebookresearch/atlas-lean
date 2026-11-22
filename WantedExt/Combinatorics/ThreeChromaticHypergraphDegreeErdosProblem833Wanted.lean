/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# High-degree vertices of `3`-chromatic hypergraphs (Erdős Problem 833)

Erdős Problem 833: does there exist an absolute constant `c > 0` such that, for all `r ≥ 2`, in any
`r`-uniform hypergraph with chromatic number `3` there is a vertex contained in at least `(1 + c)^r`
edges?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import WantedExt.Combinatorics.HypergraphColoringShared

@[expose] public section

namespace MathlibExt.Combinatorics.ThreeChromaticHypergraphDegreeErdosProblem833Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #833, https://www.erdosproblems.com/833 (status
PROVED). UnsolvedMath record UM-30007053 (`EP-833`), dataset ulamai/UnsolvedMath v1.8.0.

Hypergraphs are finite (on `Fin n`; by compactness this loses nothing); chromatic number `3` is
`3`-colorable and not `2`-colorable. The open-ended 'determine `f(r)`' on the page is not
formalized. Compared with the formal-conjectures statement `ErdosProblems/833.lean` (equivalent; no
code imported).
-/

open MathlibExt.Combinatorics.HypergraphColoringShared

/-- Erdős Problem 833: there is an absolute `c > 0` such that for every `r ≥ 2`, every finite
`r`-uniform hypergraph with chromatic number `3` has a vertex in at least `(1 + c)^r` edges. -/
def threeChromaticHighDegreeVertex : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r → ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
    (∀ e ∈ H, e.card = r) → HypergraphColorable H 3 → ¬ HypergraphColorable H 2 →
      ∃ v : Fin n, (1 + c) ^ r ≤ ((H.filter fun e => v ∈ e).card : ℝ)

/--
Resolved true: Erdős and Lovász proved that every `r`-uniform hypergraph with chromatic number `3`
has a vertex in at least `2^{r-1} / (4r)` edges (Theorem 2 with `k = 2`), which exceeds `(1 + c)^r`
for a small absolute `c` once `r` is large, while for every `r` some vertex lies in two edges
(pairwise disjoint edges can be `2`-colored); erdosproblems.com/833 lists the problem as proved.
Source: T. F. Bloom, Erdős Problems, Problem #833, https://www.erdosproblems.com/833 (status
PROVED); resolution: P. Erdős and L. Lovász, Problems and results on 3-chromatic hypergraphs and
some related questions, Infinite and finite sets (Colloq. Keszthely, 1973), Colloq. Math. Soc. János
Bolyai 10 (1975), 609-627, Theorem 2: a (k + 1)-chromatic r-uniform hypergraph has an edge meeting
at least k^{r-1}/4 other edges, so some vertex has degree at least k^{r-1}/(4r); for k = 2 this is
2^{r-1}/(4r), https://users.renyi.hu/~p_erdos/1975-34.pdf.
-/
public theorem_wanted threeChromaticHighDegreeVertex_holds : threeChromaticHighDegreeVertex

end MathlibExt.Combinatorics.ThreeChromaticHypergraphDegreeErdosProblem833Wanted
