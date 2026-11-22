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

/-- `K` is Cohen–Macaulay over `ℚ` (Reisner's criterion): for every face `F`, including `∅`,
`H̃_i(link_K(F); ℚ) = 0` for all `i < dim link_K(F)`; in the vertex-count indexing of
`reducedBetti`, degree `i = k - 1` and `dim link_K(F) = topCard (link K F) - 1`. -/
def IsCohenMacaulayOverRat (K : Finset (Finset ℕ)) : Prop :=
  ∀ F ∈ K, ∀ k, k < topCard (link K F) → reducedBetti (link K F) k = 0

/-- `K` is pure: all facets have the same number of vertices. -/
def IsPure (K : Finset (Finset ℕ)) : Prop :=
  ∃ d : ℕ, ∀ F, IsFacet K F → F.card = d

/-- `K` is partitionable: its faces are partitioned into intervals `[r F, F]` (all faces between
`r F` and `F`) with `F` running over the facets. -/
def IsPartitionable (K : Finset (Finset ℕ)) : Prop :=
  ∃ r : Finset ℕ → Finset ℕ, (∀ F, IsFacet K F → r F ⊆ F) ∧
    ∀ σ ∈ K, ∃! F, IsFacet K F ∧ r F ⊆ σ ∧ σ ⊆ F

/-- The partitionability conjecture of Stanley and Garsia (Stanley, Positivity Problems, Problem
6): every pure Cohen–Macaulay (over `ℚ`) simplicial complex is partitionable. -/
def cohenMacaulayPartitionable : Prop :=
  ∀ K : Finset (Finset ℕ), IsSimplicialComplex K → IsPure K → IsCohenMacaulayOverRat K →
    IsPartitionable K

/--
Resolved false: Duval, Goeckner, Klivans and Martin constructed explicit pure `3`-dimensional
Cohen–Macaulay simplicial complexes that are not partitionable, disproving the Stanley–Garsia
partitionability conjecture. Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic
Combinatorics (1999), Problem 6 (Stanley–Garsia partitionability conjecture); resolution: A. M.
Duval, B. Goeckner, C. J. Klivans and J. L. Martin, A non-partitionable Cohen-Macaulay simplicial
complex, Adv. Math. 299 (2016), 381-395, arXiv:1504.04279, Theorem 3.5 (arXiv numbering): the
complex C₃ obtained by gluing three copies of X along A is Cohen-Macaulay and non-partitionable
(Theorem 3.4: likewise C₂₅, by the gluing Theorem 3.1); abstract: "We disprove the conjecture by
constructing an explicit counterexample", https://arxiv.org/abs/1504.04279.
-/
public theorem_wanted cohenMacaulayPartitionable_refuted : ¬ cohenMacaulayPartitionable

end MathlibExt.Combinatorics.CohenMacaulayPartitionabilityAMR156Problem0005Wanted
