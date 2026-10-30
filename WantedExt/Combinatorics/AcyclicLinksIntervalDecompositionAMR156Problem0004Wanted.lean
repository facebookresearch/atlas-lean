/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Interval decompositions of complexes with acyclic low-dimensional links (Stanley, Problem 5)

R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics, Problem 5: suppose
that the link of every face `F` of the finite simplicial complex `Δ` of dimension at most `j`
(including `link(∅) = Δ`) is acyclic over `ℚ`. Can `Δ` be partitioned into intervals `[F, F']` such
that (a) `dim F' - dim F = j + 2` and (b) the bottom elements `F` form a subcomplex of `Δ`?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Combinatorics.RationalSimplicialHomologyShared

@[expose] public section

namespace MathlibExt.Combinatorics.AcyclicLinksIntervalDecompositionAMR156Problem0004Wanted

/-!
Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics (1999),
Problem 5 (interval decompositions of complexes with acyclic links). UnsolvedMath record UM-00801178
(`AMR-156-0004`), dataset ulamai/UnsolvedMath v1.8.0.

Written with `k = j + 2 ≥ 1` (Doolittle–Goeckner's "`k`-fold acyclic": the link of every face with
fewer than `k` vertices is acyclic); `j = -1` is Stanley's theorem on acyclic complexes. Complexes,
links and acyclicity over `ℚ` (all reduced rational Betti numbers zero) are those of
`WantedExt/Combinatorics/RationalSimplicialHomologyShared.lean`. A decomposition is a family `B` of
bottoms closed under subsets with tops `top F ∈ K`, `|top F| = |F| + k`, every face in exactly one
interval. Doolittle–Goeckner work over an arbitrary field; acyclicity over any field implies
acyclicity over `ℚ` (universal coefficients), so their counterexample applies.
-/

open MathlibExt.Combinatorics.RationalSimplicialHomologyShared

/-- `K` has a rank-`k` interval decomposition with a subcomplex of bottoms: a family `B` of faces,
closed under subsets, and tops `top F ∈ K` with `F ⊆ top F` and `|top F| = |F| + k`, such that every
face of `K` lies in exactly one interval `[F, top F]` with `F ∈ B`. -/
def HasRankIntervalDecomposition (K : Finset (Finset ℕ)) (k : ℕ) : Prop :=
  ∃ (B : Finset (Finset ℕ)) (top : Finset ℕ → Finset ℕ), (∀ F ∈ B, ∀ G ⊆ F, G ∈ B) ∧
    (∀ F ∈ B, F ⊆ top F ∧ (top F).card = F.card + k ∧ top F ∈ K) ∧
    ∀ σ ∈ K, ∃! F, F ∈ B ∧ F ⊆ σ ∧ σ ⊆ top F

/-- Stanley's Problem 5 (Positivity Problems; Conjecture 2.4 of Stanley, Discrete Math. 120
(1993)), with `k = j + 2`: if the link of every face with fewer than `k` vertices (faces of
dimension at most `j`, including `link(∅) = K`) is acyclic over `ℚ`, then `K` is partitioned into
intervals `[F, F']` with `dim F' - dim F = k` whose bottom elements form a subcomplex. -/
def acyclicLinksIntervalDecomposition : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ K : Finset (Finset ℕ), IsSimplicialComplex K →
    (∀ F ∈ K, F.card < k → IsRationallyAcyclic (link K F)) → HasRankIntervalDecomposition K k

/--
Resolved false: Doolittle and Goeckner constructed a `2`-fold acyclic simplicial complex (`j = 0`)
that cannot be written as a disjoint union of rank `2` boolean intervals at all, a counterexample to
Stanley's conjecture (Problem 5); the case `j = -1` is Stanley's theorem. Source: R. P. Stanley,
Positivity Problems and Conjectures in Algebraic Combinatorics (1999), Problem 5 (interval
decompositions of complexes with acyclic links); resolution: J. Doolittle and B. Goeckner, Resolving
Stanley's conjecture on k-fold acyclic complexes, FPSAC 2019 (Sém. Lothar. Combin. 82B, Article 46),
arXiv:1811.08518, §3: Theorem 3.2 (gluing N copies of Δ along Γ preserves k-fold acyclicity and
non-decomposability for N > ℓ/2^k) with Theorem 3.4 (Φ = (Δ, Γ) is not rank 2 boolean decomposable);
"Ω₁₇ is a counterexample to Conjecture 1.3" (Stanley's Conjecture 2.4 = Problem 5 of the 1999 list,
k = 2), https://arxiv.org/abs/1811.08518.
-/
public theorem_wanted acyclicLinksIntervalDecomposition_refuted :
    ¬ acyclicLinksIntervalDecomposition

end MathlibExt.Combinatorics.AcyclicLinksIntervalDecompositionAMR156Problem0004Wanted
