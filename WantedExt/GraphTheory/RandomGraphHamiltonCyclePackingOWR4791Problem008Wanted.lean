/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Packing Hamilton cycles in random graphs (Oberwolfach Reports 1/2011)

Oberwolfach workshop Combinatorics (2011), problem session, M. Krivelevich (conjecture of A. Frieze
and M. Krivelevich): for every `p = p(n)`, with high probability `G ~ G(n, p)` contains `⌊δ(G)/2⌋`
edge-disjoint Hamilton cycles.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.RandomGraphHamiltonCyclePackingOWR4791Problem008Wanted

/-!
Source: M. Krivelevich, problem session, in Combinatorics, Oberwolfach Reports 8 (2011), no. 1, p.
75, DOI 10.4171/OWR/2011/01. UnsolvedMath record UM-30001652 (`OWR-4791-008`), dataset
ulamai/UnsolvedMath v1.8.0.

`G(n, p)` is Mathlib's binomial random graph `SimpleGraph.binomialRandom (Fin n) p`, for every `p :
ℕ → [0, 1]`. Hamilton cycles are `SimpleGraph.Walk.IsHamiltonianCycle` and edge-disjointness
compares edge lists.
-/

open Filter Topology unitInterval

/-- `G` contains `r` pairwise edge-disjoint Hamilton cycles. -/
def HasEdgeDisjointHamiltonCycles {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  ∃ (v : Fin r → Fin n) (C : ∀ i, G.Walk (v i) (v i)), (∀ i, (C i).IsHamiltonianCycle) ∧
    ∀ i j, i ≠ j → ∀ e ∈ (C i).edges, e ∉ (C j).edges

open Classical in
/-- The conjecture of Frieze and Krivelevich (Oberwolfach Report 1/2011, p. 75): for every edge
probability `p = p(n)`, with probability tending to `1` the binomial random graph
`G ~ G(n, p)` (Mathlib's `SimpleGraph.binomialRandom`) contains `⌊δ(G) / 2⌋` edge-disjoint
Hamilton cycles. -/
def hamiltonCyclePacking : Prop :=
  ∀ p : ℕ → I,
    Tendsto (fun n => (SimpleGraph.binomialRandom (Fin n) (p n)).real
      {G | HasEdgeDisjointHamiltonCycles G (G.minDegree / 2)}) atTop (𝓝 1)

/--
Resolved true: Kühn and Osthus (Theorem 1.10), combining their very dense case with the results of
Knox, Kühn and Osthus and of Krivelevich and Samotij, proved that for any `p = p(n)` asymptotically
almost surely `G(n, p)` contains `⌊δ/2⌋` edge-disjoint Hamilton cycles. Source: M. Krivelevich,
problem session, in Combinatorics, Oberwolfach Reports 8 (2011), no. 1, p. 75, DOI
10.4171/OWR/2011/01; resolution: D. Kühn and D. Osthus, Hamilton decompositions of regular
expanders: applications, J. Combin. Theory Ser. B 104 (2014), 1-27, arXiv:1203.0659, Theorem 1.10:
for any p = p(n), a.a.s. G_{n,p} contains ⌊δ(G_{n,p})/2⌋ edge-disjoint Hamilton cycles; the authors
credit the main contribution to Knox, Kühn and Osthus (Random Structures Algorithms 46 (2015)) and
Krivelevich and Samotij (SIAM J. Discrete Math. 26 (2012)), https://arxiv.org/abs/1203.0659.
-/
public theorem_wanted hamiltonCyclePacking_holds : hamiltonCyclePacking

end MathlibExt.GraphTheory.RandomGraphHamiltonCyclePackingOWR4791Problem008Wanted
