/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A non-partitionable Cohen–Macaulay complex (Stanley, Problem 6)

R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics, Problem 6: let `Δ` be
a pure `(d - 1)`-dimensional simplicial complex that is Cohen–Macaulay over `ℚ` (`H̃_i(link(F); ℚ) =
0` for all faces `F` and `i ≠ dim link(F)`). Is every Cohen–Macaulay complex partitionable into
intervals `[F, F']` with each `F'` a facet?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Combinatorics.RationalSimplicialHomologyShared

@[expose] public section

namespace MathlibExt.Combinatorics.CohenMacaulayPartitionabilityAMR156Problem0005Wanted

/-!
Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics (1999),
Problem 6 (Stanley–Garsia partitionability conjecture). UnsolvedMath record UM-00801179
(`AMR-156-0005`), dataset ulamai/UnsolvedMath v1.8.0.

Finite abstract simplicial complexes on the vertex set `ℕ`, links and reduced rational Betti numbers
are those of `WantedExt/Combinatorics/RationalSimplicialHomologyShared.lean`. Cohen–Macaulay over
`ℚ` is Reisner's criterion: `H̃_i(link F; ℚ) = 0` for `i < dim link F` (degrees above the dimension
vanish automatically). Partitionable: the faces are partitioned into intervals `[r F, F]` indexed by
the facets. Duval–Goeckner–Klivans–Martin take Reisner's criterion over an arbitrary field;
Cohen–Macaulayness over any field implies it over `ℚ` (universal coefficients: vanishing mod `p`
forces the integral homology to be finite), and their complexes are built from shellable balls.
-/

open MathlibExt.Combinatorics.RationalSimplicialHomologyShared

/-- **Cohen–Macaulay complexes over $\mathbb{Q}$.** A finite family $K$ of finite subsets of
$\mathbb{N}$ is Cohen–Macaulay over $\mathbb{Q}$ when for every member $F$ of $K$ (the empty face
included, if it belongs to $K$) the link
$L = \operatorname{lk}_K F = \{G \in K : G \cap F = \emptyset,\ G \cup F \in K\}$ satisfies
$\tilde\beta_i(L) = 0$ for every integer $i$ with $-1 \le i < \dim L$. Here $\dim L$ is one less
than the largest number of elements of a member of $L$, taken to be $-1$ when $L$ has no nonempty
member, and $\tilde\beta_i(L)$ is the number of members of $L$ with $i + 1$ elements minus the
ranks of the augmented rational simplicial boundary maps (vertices ordered as in $\mathbb{N}$) out
of and into the span of these members; when $L$ is a simplicial complex,
$\tilde\beta_i(L) = \dim \tilde H_i(L; \mathbb{Q})$.

For a simplicial complex this is Reisner's criterion. -/
def IsCohenMacaulayOverRat (K : Finset (Finset ℕ)) : Prop :=
  ∀ F ∈ K, ∀ k, k < topCard (link K F) → reducedBetti (link K F) k = 0

/-- **Pure complexes.** A finite family $K$ of finite subsets of $\mathbb{N}$ is pure when all
its facets (maximal members) have the same number of elements. -/
def IsPure (K : Finset (Finset ℕ)) : Prop :=
  ∃ d : ℕ, ∀ F, IsFacet K F → F.card = d

/-- **Partitionable complexes.** A finite family $K$ of finite subsets of $\mathbb{N}$ is
partitionable when there is a map $r$ assigning to each facet $F$ of $K$ a set $r(F) \subseteq F$
such that for every member $\sigma$ of $K$ there is exactly one facet $F$ of $K$ with
$r(F) \subseteq \sigma \subseteq F$.

For a simplicial complex this says that its faces are partitioned into the intervals
$[r(F), F] = \{\sigma : r(F) \subseteq \sigma \subseteq F\}$, one for each facet $F$. -/
def IsPartitionable (K : Finset (Finset ℕ)) : Prop :=
  ∃ r : Finset ℕ → Finset ℕ, (∀ F, IsFacet K F → r F ⊆ F) ∧
    ∀ σ ∈ K, ∃! F, IsFacet K F ∧ r F ⊆ σ ∧ σ ⊆ F

/-- **Stanley–Garsia partitionability conjecture.** Every finite simplicial complex on the vertex
set $\mathbb{N}$ that is pure and Cohen–Macaulay over $\mathbb{Q}$ is partitionable.

Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics, Problem 6
(partitionability conjecture of Stanley and Garsia). -/
def cohenMacaulayPartitionable : Prop :=
  ∀ K : Finset (Finset ℕ), IsSimplicialComplex K → IsPure K → IsCohenMacaulayOverRat K →
    IsPartitionable K

/--
**The Stanley–Garsia partitionability conjecture is false.** There is a finite simplicial complex
on the vertex set $\mathbb{N}$ that is pure and Cohen–Macaulay over $\mathbb{Q}$ but not
partitionable.

Duval, Goeckner, Klivans and Martin constructed explicit pure $3$-dimensional Cohen–Macaulay
simplicial complexes that are not partitionable.

Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic
Combinatorics (1999), Problem 6 (Stanley–Garsia partitionability conjecture); resolution: A. M.
Duval, B. Goeckner, C. J. Klivans and J. L. Martin, A non-partitionable Cohen-Macaulay simplicial
complex, Adv. Math. 299 (2016), 381-395, arXiv:1504.04279, Theorem 3.5 (arXiv numbering): the
complex C₃ obtained by gluing three copies of X along A is Cohen-Macaulay and non-partitionable
(Theorem 3.4: likewise C₂₅, by the gluing Theorem 3.1); abstract: "We disprove the conjecture by
constructing an explicit counterexample", https://arxiv.org/abs/1504.04279.
-/
public theorem_wanted cohenMacaulayPartitionable_refuted : ¬ cohenMacaulayPartitionable

end MathlibExt.Combinatorics.CohenMacaulayPartitionabilityAMR156Problem0005Wanted
