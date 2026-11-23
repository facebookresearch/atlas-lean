/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Non-trivial percolation threshold on Cayley graphs (Abért, Some questions, Question 26)

M. Abért, Some questions (2010), Question 26 (Lyons): let `G` be an infinite Cayley graph of a group
that is not virtually cyclic. Show that there exists `p < 1` such that the `p`-edge percolation of
`G` has some infinite clusters.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.GroupTheory.SpecificGroups.VirtuallyCyclic
public import MathlibExt.Probability.ProductBondPercolation

@[expose] public section

namespace MathlibExt.Probability.PercolationPhaseTransitionCayleyAMR11Problem0026Wanted

/-!
Source: M. Abért, Some questions (2010), Question 26 (Lyons),
https://www.renyi.hu/~abert/questions.pdf. UnsolvedMath record UM-01200026 (`AMR-011-0026`), dataset
ulamai/UnsolvedMath v1.8.0.

Cayley graphs are Mathlib's `SimpleGraph.mulCayley S` for finite generating sets `S`, and virtually
cyclic is Mathlib's `Group.IsVirtuallyCyclic`. `criticalProb` (MathlibExt) is the infimum of the `p
∈ [0, 1]` for which Bernoulli(`p`) bond percolation has an infinite cluster with positive
probability (with `1` adjoined), so `criticalProb < 1` says some `p < 1` has infinite clusters. The
source states, right after Question 26, that not virtually cyclic is the same as not having linear
word growth, i.e. `limsup |B_r| / r = ∞`, which is the super-linear growth hypothesis of the
resolving theorem.
-/

/-- Lyons's question (Abért's Question 26), answered: for every infinite Cayley graph
`SimpleGraph.mulCayley S` of a finitely generated group that is not virtually cyclic
(`Group.IsVirtuallyCyclic`), Bernoulli bond percolation has an infinite cluster with positive
probability for some `p < 1`, i.e. `p_c < 1`. -/
def percolationPhaseTransitionCayley : Prop :=
  ∀ (Γ : Type) [Group Γ] [Countable Γ] (S : Finset Γ), Subgroup.closure (S : Set Γ) = ⊤ →
    Infinite Γ → ¬ Group.IsVirtuallyCyclic Γ →
      MathlibExt.Probability.ProductBondPercolation.criticalProb
        (SimpleGraph.mulCayley (S : Set Γ)) < 1

/--
Resolved true: Duminil-Copin, Goswami, Raoufi, Severo and Yadin proved `p_c(G) < 1` for every
quasi-transitive graph of super-linear growth, in particular for every Cayley graph of a finitely
generated group that is not virtually cyclic (by the source's remark after Question 26, not
virtually cyclic means not of linear growth). Source: M. Abért, Some questions (2010), Question 26
(Lyons), https://www.renyi.hu/~abert/questions.pdf; resolution: H. Duminil-Copin, S. Goswami, A.
Raoufi, F. Severo and A. Yadin, Existence of phase transition for percolation using the Gaussian
free field, Duke Math. J. 169 (2020), 3539-3563, arXiv:1806.07733, Theorem 1.3: "Let G be a
quasi-transitive graph with super-linear growth, then p_c(G) < 1" (super-linear growth: limsup
|B_r(x)| / r = ∞); the abstract states it for infinite quasi-transitive graphs, "in particular,
Cayley graphs", answering a conjecture of Benjamini and Schramm, https://arxiv.org/abs/1806.07733.
-/
public theorem_wanted percolationPhaseTransitionCayley_holds : percolationPhaseTransitionCayley

end MathlibExt.Probability.PercolationPhaseTransitionCayleyAMR11Problem0026Wanted
