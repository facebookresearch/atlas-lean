/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Perfect matchings in dense uniform hypergraphs (Oberwolfach Reports 48/2006)

Oberwolfach workshop Combinatorics, Probability and Computing (2006), Problem 5 (A. Ruciński): for
`k ≥ 2` and `1/k ≤ c < 1/2`, determine the complexity of deciding whether a `k`-uniform hypergraph
`H` with `k ∣ |V(H)|` and `δ_{k-1}(H) ≥ c n` has a perfect matching.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.BinaryNatEncoding

@[expose] public section

namespace MathlibExt.Complexity.DenseHypergraphPerfectMatchingOWR1386Problem015Wanted

/-!
Source: A. Ruciński, in Combinatorics, Probability and Computing, Oberwolfach Reports 3 (2006), no.
48, p. 2929, Problem 5, DOI 10.4171/OWR/2006/48. UnsolvedMath record UM-30000608 (`OWR-1386-015`),
dataset ulamai/UnsolvedMath v1.8.0.

The answer (polynomial time) is stated with the repository's bitstring complexity class `P`
(`MetaMathlibExt.ComplexityTheory`). The input is `(n, E)`, a vertex count and an edge list; the
language checks well-formedness, `k ∣ n` and the codegree condition and asks for a perfect matching.
`c` is rational, so the codegree condition is decidable; for `k = 2` the range of `c` is empty.
-/

open MetaMathlibExt.ComplexityTheory MetaMathlibExt.BitstringEncoding

open Classical in
/-- The decision problem `PM(k, c)` over bitstrings. An input decodes to `(n, E)`, a list `E` of
edges of a `k`-uniform hypergraph `H` on `{0, …, n - 1}`; it is accepted iff every listed edge is
a list of `k` distinct vertices below `n`, `k ∣ n`, every `(k - 1)`-set of vertices lies in at
least `c n` edges (`δ_{k-1}(H) ≥ c n`), and `H` has a perfect matching (`n / k` pairwise disjoint
edges). Inputs that do not decode are rejected. -/
noncomputable def perfectMatchingProblem (k : ℕ) (c : ℚ) : DecisionProblem := fun x =>
  match bitDecode (α := ℕ × List (List ℕ)) x with
  | some (n, E) =>
      let edges : Finset (Finset ℕ) := (E.map List.toFinset).toFinset
      decide ((∀ e ∈ E, e.length = k ∧ e.Nodup ∧ ∀ v ∈ e, v < n) ∧ k ∣ n ∧
        (∀ S ⊆ Finset.range n, S.card = k - 1 →
          c * n ≤ ((edges.filter fun e => S ⊆ e).card : ℚ)) ∧
        ∃ M ⊆ edges, M.card = n / k ∧ (M : Set (Finset ℕ)).PairwiseDisjoint id)
  | none => false

/-- Ruciński's question (Oberwolfach Combinatorics, Probability and Computing, 2006, Problem 5),
answered: for `k ≥ 2` and rational `1 / k ≤ c < 1 / 2`, deciding whether a `k`-uniform hypergraph
with `k ∣ n` and minimum codegree at least `c n` has a perfect matching is in `P`. -/
def denseHypergraphPerfectMatchingInP : Prop :=
  ∀ (k : ℕ) (c : ℚ), 2 ≤ k → 1 / (k : ℚ) ≤ c → c < 1 / 2 → perfectMatchingProblem k c ∈ P

/--
Resolved true: Keevash, Knox and Mycroft give a polynomial-time algorithm when the minimum codegree
is at least `n/k + γn` for a fixed `γ > 0`, and Han extends it to minimum codegree at least `n/k`,
so the problem is in `P` for every `1/k ≤ c < 1/2`. Inputs whose edge count is below what the
codegree condition forces are rejected first, so `n` is polynomial in the input size whenever the
remaining checks run. Source: A. Ruciński, in Combinatorics, Probability and Computing, Oberwolfach
Reports 3 (2006), no. 48, p. 2929, Problem 5, DOI 10.4171/OWR/2006/48; resolution: P. Keevash, F.
Knox and R. Mycroft, Polynomial-time perfect matchings in dense hypergraphs, Adv. Math. 269 (2015),
265-334, arXiv:1307.2608 (c > 1/k); J. Han, Decision problem for perfect matchings in dense
k-uniform hypergraphs, Trans. Amer. Math. Soc. 369 (2017), 5197-5218, arXiv:1409.5931 (c = 1/k), KKM
main theorem (codegree ≥ n/k + γn) and Han main theorem (codegree ≥ n/k): polynomial-time decision,
https://arxiv.org/abs/1409.5931.
-/
public theorem_wanted denseHypergraphPerfectMatchingInP_holds : denseHypergraphPerfectMatchingInP

end MathlibExt.Complexity.DenseHypergraphPerfectMatchingOWR1386Problem015Wanted
