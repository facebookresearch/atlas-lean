/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Continuum many ends of the infinite clusters for p_c < p < p_u (Benjamini–Schramm, Conjecture 5)

Benjamini–Schramm, Conjecture 5: let `G` be a connected almost transitive graph and fix `p ∈ (0,
1)`. Suppose that almost surely there is more than one infinite component in the percolation
subgraph. Then, with probability 1, each infinite component in the percolation subgraph has
precisely `2^ℵ₀` ends.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
public import Mathlib.SetTheory.Cardinal.Continuum
public import MathlibExt.Probability.ProductBondPercolation

@[expose] public section

namespace MathlibExt.Probability.NonuniquenessClusterEndsAMR99Problem0085Wanted

/-!
Source: I. Benjamini and O. Schramm, Percolation beyond ℤ^d, many questions and a few answers,
Electron. Comm. Probab. 1 (1996), 71-82, Conjecture 5. UnsolvedMath record UM-10000085
(`AMR-099-0085`), dataset ulamai/UnsolvedMath v1.8.0.

Bernoulli bond percolation with MathlibExt's product law `gbernoulliLaw`, open clusters `gcluster`
and critical probability `criticalProb`; quasi-transitive (Benjamini–Schramm: almost transitive)
means that the automorphism group has finitely many vertex orbits. `p_u` is the uniqueness threshold
`inf {p : P_p(exactly one infinite cluster) = 1}` (Benjamini–Schramm §2, Häggström–Peres–Schonmann
Theorem 1.2). Ends are Mathlib's `SimpleGraph.end` of the cluster (Benjamini–Schramm's Definition 1:
a consistent choice of a component of the complement of every finite vertex set);
Häggström–Peres–Schonmann define the ends of a cluster as classes of self-avoiding paths modulo
finite edge sets, the same end space for these locally finite clusters. The statement is their
Theorem 1.6 at a fixed density `p` (the theorem holds simultaneously for all `p` in the standard
coupling, whose level-`p` marginal is Bernoulli(`p`) percolation).
-/

open MeasureTheory MathlibExt.Probability.ProductBondPercolation

/-- `G` is quasi-transitive (Benjamini–Schramm's "almost transitive"): its automorphism group acts
on the vertices with finitely many orbits, i.e. some finite set of vertices meets every orbit. -/
def IsQuasiTransitive {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ F : Finset V, ∀ v : V, ∃ φ : G ≃g G, ∃ u ∈ F, φ u = v

/-- In the bond configuration `ω` there is exactly one infinite open cluster. -/
def UniqueInfiniteCluster {V : Type} (G : SimpleGraph V) (ω : Sym2 V → Bool) : Prop :=
  ∃ x : V, (gcluster G ω x).Infinite ∧
    ∀ y : V, (gcluster G ω y).Infinite → gcluster G ω y = gcluster G ω x

/-- The uniqueness threshold `p_u(G)` of Bernoulli bond percolation: the infimum of the densities
`p ∈ [0, 1]` at which there is almost surely exactly one infinite open cluster (with `1` inserted,
as in `criticalProb`, so that the value lies in `[0, 1]`). -/
noncomputable def bondUniquenessThreshold {V : Type} (G : SimpleGraph V) : ℝ :=
  sInf (insert 1 {p : ℝ | ∃ hp0 : 0 ≤ p, ∃ hp1 : p ≤ 1,
    gbernoulliLaw (V := V) p hp0 hp1 {ω | UniqueInfiniteCluster G ω} = 1})

/-- The ends of the open cluster of `x` in the configuration `ω`: Mathlib's ends (consistent choices
of a component of the complement of every finite vertex set, Benjamini–Schramm's Definition 1) of
the cluster, viewed as the subgraph of the open subgraph induced on the cluster. -/
def clusterEnds {V : Type} (G : SimpleGraph V) (ω : Sym2 V → Bool) (x : V) :=
  ((openSubgraph G ω).induce (gcluster G ω x)).end

/-- Häggström–Peres–Schonmann, Theorem 1.6 (at a fixed density): for Bernoulli(`p`) bond percolation
on an infinite, connected, locally finite, quasi-transitive graph with `p_c < p < p_u`, almost
surely every infinite open cluster has exactly `2^ℵ₀` ends. -/
def nonuniquenessClusterEnds : Prop :=
  ∀ (V : Type) [Countable V] (G : SimpleGraph V), Infinite V → G.Connected →
    (∀ v : V, (G.neighborSet v).Finite) → IsQuasiTransitive G →
      ∀ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1), criticalProb G < p → p < bondUniquenessThreshold G →
        ∀ᵐ ω ∂(gbernoulliLaw (V := V) p hp0 hp1), ∀ x : V, (gcluster G ω x).Infinite →
          Cardinal.mk (clusterEnds G ω x) = Cardinal.continuum

/--
Resolved true for p_c < p < p_u: Häggström, Peres and Schonmann prove that for Bernoulli bond
percolation on an infinite, locally finite, connected, quasi-transitive graph, almost surely, for
all p ∈ (p_c, p_u), every infinite cluster has precisely 2^ℵ₀ ends (Theorem 1.6), and present this
as confirming Benjamini–Schramm's Conjecture 5 except for the case p = p_c. Source: I. Benjamini and
O. Schramm, Percolation beyond ℤ^d, many questions and a few answers, Electron. Comm. Probab. 1
(1996), 71-82, Conjecture 5; resolution: O. Häggström, Y. Peres and R. H. Schonmann, Percolation on
transitive graphs as a coalescent process: relentless merging followed by simultaneous uniqueness,
in Perplexing Problems in Probability (Festschrift for H. Kesten), Progr. Probab. 44, Birkhäuser
(1999), 69-90, Theorem 1.6: 'Let G be an infinite, locally finite, connected, quasi-transitive
graph. Then, Ψ_G-a.s., for all p ∈ (p_c, p_u) every infinite p-cluster has precisely 2^ℵ₀ many
ends'; the paper adds that the proof extends to p = p_u when there are several infinite clusters
there, so that 'this theorem confirms Conjecture 5 of Benjamini and Schramm (except for the case p =
p_c, if infinitely many infinite clusters can exist there)'; see also R. Lyons and Y. Peres,
Probability on Trees and Networks (Cambridge, 2016), Theorem 8.32 and the notes to Chapter 8,
https://www.math.ucla.edu/~rhs/papers/hps.pdf.
-/
public theorem_wanted nonuniquenessClusterEnds_holds : nonuniquenessClusterEnds

end MathlibExt.Probability.NonuniquenessClusterEndsAMR99Problem0085Wanted
