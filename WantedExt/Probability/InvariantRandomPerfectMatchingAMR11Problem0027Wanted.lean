/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Invariant random perfect matchings of Cayley graphs (Abért, Some questions, Question 27)

M. Abért, Some questions (2010), Question 27: let `G` be an infinite connected Cayley graph. Then
`G` has a perfect matching. Does `G` have an invariant random subgraph that is a perfect matching
almost surely?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace MathlibExt.Probability.InvariantRandomPerfectMatchingAMR11Problem0027Wanted

/-!
Source: M. Abért, Some questions (2010), Question 27, https://www.renyi.hu/~abert/questions.pdf.
UnsolvedMath record UM-01200027 (`AMR-011-0027`), dataset ulamai/UnsolvedMath v1.8.0.

The Cayley graph of a group `Γ` for a finite generating set `S` is Mathlib's `SimpleGraph.mulCayley
S`; it is connected because `S` generates. A random subgraph is a probability measure on edge
configurations `Sym2 Γ → Bool` (product σ-algebra); invariance is under the left action `(γ • ω) e =
ω (γ⁻¹ • e)`, which acts by graph automorphisms. A configuration is a perfect matching when its edge
set is the edge set of a subgraph satisfying Mathlib's `Subgraph.IsPerfectMatching`.
-/

/-- Left translation of an edge configuration: `(γ • ω) e = ω (γ⁻¹ • e)`. -/
def shiftConfig {Γ : Type*} [Group Γ] (γ : Γ) (ω : Sym2 Γ → Bool) : Sym2 Γ → Bool :=
  fun e => ω (Sym2.map (fun g => γ⁻¹ * g) e)

/-- Abért's Question 27, answered: every infinite connected Cayley graph
`SimpleGraph.mulCayley S` of a finitely generated group `Γ` admits a `Γ`-invariant random perfect
matching: a probability measure on edge configurations, invariant under left translation, whose
random edge set is almost surely the edge set of a perfect matching (Mathlib's
`Subgraph.IsPerfectMatching`). -/
def invariantRandomPerfectMatching : Prop :=
  ∀ (Γ : Type) [Group Γ] (S : Finset Γ), Subgroup.closure (S : Set Γ) = ⊤ → Infinite Γ →
    ∃ μ : MeasureTheory.Measure (Sym2 Γ → Bool), MeasureTheory.IsProbabilityMeasure μ ∧
      (∀ γ : Γ, μ.map (shiftConfig γ) = μ) ∧
      ∀ᵐ ω ∂μ, ∃ M : (SimpleGraph.mulCayley (S : Set Γ)).Subgraph,
        M.IsPerfectMatching ∧ M.edgeSet = {e | ω e = true}

/--
Resolved true: Csóka and Lippner proved that every Cayley graph of an infinite finitely generated
group admits an invariant random perfect matching (a factor of IID one in the non-amenable case).
Source: M. Abért, Some questions (2010), Question 27, https://www.renyi.hu/~abert/questions.pdf;
resolution: E. Csóka and G. Lippner, Invariant random perfect matchings in Cayley graphs, Groups
Geom. Dyn. 11 (2017), 211-243, arXiv:1211.2374, Corollary 1.3: "Every Cayley graph admits an
invariant random perfect matching" (Theorem 1.1: factor of IID perfect matchings for non-amenable
Cayley graphs; Theorem 1.2 with Conley–Kechris–Tucker-Drob for the amenable case), invariant random
subgraphs being Γ-invariant probability distributions on subgraphs of a locally finite Cayley graph
(Introduction), https://arxiv.org/abs/1211.2374.
-/
public theorem_wanted invariantRandomPerfectMatching_holds : invariantRandomPerfectMatching

end MathlibExt.Probability.InvariantRandomPerfectMatchingAMR11Problem0027Wanted
