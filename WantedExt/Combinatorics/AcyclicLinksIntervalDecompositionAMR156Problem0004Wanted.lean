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

/-- **Rank-$k$ interval decomposition with a subcomplex of bottoms.** For a natural number $k$, a
finite family $K$ of finite subsets of $\mathbb{N}$ has a rank-$k$ interval decomposition with a
subcomplex of bottoms if there are a finite family $B$ of finite subsets of $\mathbb{N}$, closed
under taking subsets, and an assignment of a finite set $\mathrm{top}(F) \subseteq \mathbb{N}$ to
each finite set $F \subseteq \mathbb{N}$, such that every $F \in B$ satisfies
$F \subseteq \mathrm{top}(F)$, $|\mathrm{top}(F)| = |F| + k$ and $\mathrm{top}(F) \in K$, and every
$\sigma \in K$ lies in the interval $[F, \mathrm{top}(F)] = \{G : F \subseteq G \subseteq
\mathrm{top}(F)\}$ for exactly one $F \in B$. -/
def HasRankIntervalDecomposition (K : Finset (Finset ℕ)) (k : ℕ) : Prop :=
  ∃ (B : Finset (Finset ℕ)) (top : Finset ℕ → Finset ℕ), (∀ F ∈ B, ∀ G ⊆ F, G ∈ B) ∧
    (∀ F ∈ B, F ⊆ top F ∧ (top F).card = F.card + k ∧ top F ∈ K) ∧
    ∀ σ ∈ K, ∃! F, F ∈ B ∧ F ⊆ σ ∧ σ ⊆ top F

/-- **Stanley's interval-decomposition conjecture for complexes with acyclic links.** The statement
that for every integer $k \ge 1$ and every finite simplicial complex $K$ on the vertex set
$\mathbb{N}$ (a finite family of finite subsets of $\mathbb{N}$ closed under taking subsets): if the
link $\mathrm{lk}_K(F) = \{G \in K : G \cap F = \emptyset,\ G \cup F \in K\}$ of every face
$F \in K$ with fewer than $k$ vertices (including $\mathrm{lk}_K(\emptyset) = K$) is acyclic over
$\mathbb{Q}$ (all of its reduced rational homology vanishes), then $K$ has a rank-$k$ interval
decomposition with a subcomplex of bottoms: there are a family $B$ of finite subsets of
$\mathbb{N}$, closed under taking subsets, and faces $\mathrm{top}(F) \in K$ for $F \in B$ with
$F \subseteq \mathrm{top}(F)$ and $|\mathrm{top}(F)| = |F| + k$, such that every face of $K$ lies
in the interval $[F, \mathrm{top}(F)]$ for exactly one $F \in B$.

This is Stanley's Problem 5 (Positivity Problems; Conjecture 2.4 of Stanley, Discrete Math. 120
(1993)) with $k = j + 2$: the faces with fewer than $k$ vertices are the faces of dimension at most
$j$, and for an interval $[F, F']$ with $F' = \mathrm{top}(F)$, the condition $|F'| = |F| + k$
means $\dim F' - \dim F = k$. -/
def acyclicLinksIntervalDecomposition : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ K : Finset (Finset ℕ), IsSimplicialComplex K →
    (∀ F ∈ K, F.card < k → IsRationallyAcyclic (link K F)) → HasRankIntervalDecomposition K k

/--
**Stanley's interval-decomposition conjecture for complexes with acyclic links is false.** It is
not true that for every integer $k \ge 1$ and every finite simplicial complex $K$ on the vertex set
$\mathbb{N}$ (a finite family of finite subsets of $\mathbb{N}$ closed under taking subsets) such
that the link $\mathrm{lk}_K(F) = \{G \in K : G \cap F = \emptyset,\ G \cup F \in K\}$ of every
face $F \in K$ with fewer than $k$ vertices is acyclic over $\mathbb{Q}$ (all of its reduced
rational homology vanishes), there are a family $B$ of finite subsets of $\mathbb{N}$, closed under
taking subsets, and faces $\mathrm{top}(F) \in K$ for $F \in B$ with $F \subseteq \mathrm{top}(F)$
and $|\mathrm{top}(F)| = |F| + k$, such that every face of $K$ lies in the interval
$[F, \mathrm{top}(F)]$ for exactly one $F \in B$.

Doolittle and Goeckner constructed a complex with $k = 2$ (a $2$-fold acyclic complex) that cannot
be partitioned into intervals $[F, F']$ with $|F'| = |F| + 2$ at all; the case $k = 1$ is
Stanley's theorem.

Source: R. P. Stanley,
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
