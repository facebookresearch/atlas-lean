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
/-- **Perfect matching in uniform hypergraphs with a codegree condition.** For a natural number
$k$ and a rational $c$, $\mathrm{PM}(k, c)$ is the decision problem on bitstrings that decodes an
input as a pair $(n, E)$ of a natural number $n$ and a list $E$ of lists of natural numbers, and
accepts it iff every list in $E$ consists of $k$ distinct vertices below $n$, $k \mid n$, every
$(k-1)$-element subset of $\{0, \dots, n-1\}$ is contained in at least $cn$ edges of the
hypergraph $H$ whose edges are the vertex sets of the lists in $E$, and $H$ has a perfect
matching, that is, $n/k$ pairwise disjoint edges. Inputs that do not decode are rejected. -/
noncomputable def perfectMatchingProblem (k : ℕ) (c : ℚ) : DecisionProblem := fun x =>
  match bitDecode (α := ℕ × List (List ℕ)) x with
  | some (n, E) =>
      let edges : Finset (Finset ℕ) := (E.map List.toFinset).toFinset
      decide ((∀ e ∈ E, e.length = k ∧ e.Nodup ∧ ∀ v ∈ e, v < n) ∧ k ∣ n ∧
        (∀ S ⊆ Finset.range n, S.card = k - 1 →
          c * n ≤ ((edges.filter fun e => S ⊆ e).card : ℚ)) ∧
        ∃ M ⊆ edges, M.card = n / k ∧ (M : Set (Finset ℕ)).PairwiseDisjoint id)
  | none => false

/-- **Ruciński's question on perfect matchings in dense hypergraphs.** The statement that for every
natural number $k \ge 2$ and every rational $c$ with $1/k \le c < 1/2$, the decision problem
$\mathrm{PM}(k, c)$ is in the complexity class P. Here $\mathrm{PM}(k, c)$ accepts a list of edges
of a $k$-uniform hypergraph $H$ on the vertices $0, \dots, n-1$ iff every edge consists of $k$
distinct vertices below $n$, $k \mid n$, every $(k-1)$-element set of vertices lies in at least
$cn$ edges of $H$, and $H$ has a perfect matching; inputs that do not decode are rejected. This is
the positive answer to Ruciński's question (Oberwolfach Combinatorics, Probability and Computing,
2006, Problem 5). -/
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
