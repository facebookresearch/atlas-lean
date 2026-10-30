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

/-- Erdős Problem 832: for every `r ≥ 3` and all large `k`, every `r`-uniform hypergraph with
chromatic number `k` has at least `C((r - 1)(k - 1) + 1, r)` edges, with equality only for the
complete `r`-uniform hypergraph on `(r - 1)(k - 1) + 1` vertices. -/
def chromaticEdgeLowerBound : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ᶠ k : ℕ in Filter.atTop, ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
    (∀ e ∈ H, e.card = r) → HypergraphColorable H k → ¬ HypergraphColorable H (k - 1) →
      ((r - 1) * (k - 1) + 1).choose r ≤ H.card ∧
        (H.card = ((r - 1) * (k - 1) + 1).choose r →
          ∃ S : Finset (Fin n), S.card = (r - 1) * (k - 1) + 1 ∧ H = S.powersetCard r)

/--
Resolved false: Alon disproved it using Turán numbers (Proposition 1): for an absolute `C`, `r ≥ C`
and `k ≥ C r` some `r`-uniform hypergraph with chromatic number at least `k` has at most `(7/8)^r
C((r - 1)(k - 1) + 1, r)` edges, and an edge-minimal one among these has chromatic number exactly
`k`. erdosproblems.com/832 lists the problem as disproved, for every `r ≥ 4` by known Turán bounds
(the case `r = 3` is open). Source: T. F. Bloom, Erdős Problems, Problem #832,
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
