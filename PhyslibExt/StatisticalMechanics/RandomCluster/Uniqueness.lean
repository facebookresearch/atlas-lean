/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.EdgeMarginal
/-!
# Agreement of FK measures off a countable set of parameters

Measure-theoretic reduction for the uniqueness of random-cluster measures: equal edge
marginals plus a monotone coupling give equality on increasing events, and a monotone edge
density has countably many discontinuities.

## i. Overview

Let `μ ≼ ν` be probability vectors on the configurations of a finite edge set, coupled
monotonically. If every edge has the same marginal under `μ` and `ν`, the coupling is supported
on the diagonal, so `μ` and `ν` agree on every increasing event (`fk_unique_of_edgeMarg_eq`). For
families `μ p`, `ν p` indexed by `p ∈ ℝ`, if the edge marginals agree at every continuity point
of a monotone function `p ↦ ν_p(ω(e) = 1)`, then agreement on increasing events fails only on
the countable set of its discontinuities.

These lemmas carry the agreement of edge marginals at continuity points as a hypothesis
(`heq_at_cont`). That hypothesis is the substantive input of the uniqueness theorem for
random-cluster measures (`φ⁰_(p,q) = φ¹_(p,q)` for all but countably many `p`); it is not proved
here.

## ii. Key results

- `fk_unique_of_edgeMarg_eq` : equal edge marginals and a monotone coupling give equality on
  increasing events.
- `countable_edgeMarg_ne` : two functions agreeing at the continuity points of a monotone one
  differ on a countable set.
- `phi0_eq_phi1_off_countable`, `countable_phi_ne` : the parametric agreement statements.

## iii. Table of contents

- A. Agreement from equal edge marginals
- B. Countable exceptional sets

## iv. References

- G. R. Grimmett, *The Random-Cluster Model*, Springer, 2006.
-/

@[expose] public section

open Set Filter Topology
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

variable {E : Type*} [Fintype E] [DecidableEq E]

/-!
## A. Agreement from equal edge marginals
-/

/-- Two monotonically coupled probability vectors with equal edge marginals agree on increasing
events. Restatement of `eventMass_eq_of_edgeMarg_eq` (`EdgeMarginal`), kept because other modules
use this name. -/
lemma fk_unique_of_edgeMarg_eq {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν)
    (hmarg : ∀ e : E, edgeMargProb μ e = edgeMargProb ν e)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    eventMassProb μ A = eventMassProb ν A :=
  eventMass_eq_of_edgeMarg_eq hP hmarg hA

/-!
## B. Countable exceptional sets
-/

section Densities

variable {a b : ℝ → ℝ}

/-- If `a` agrees with a monotone `b` at every continuity point of `b`, then `{p | a p ≠ b p}` is
countable. -/
lemma countable_edgeMarg_ne (hb : Monotone b)
    (heq_at_cont : ∀ p : ℝ, ContinuousAt b p → a p = b p) :
    {p : ℝ | a p ≠ b p}.Countable := by
  refine hb.countable_not_continuousAt.mono ?_
  intro p hp
  simp only [mem_ofPred_eq] at hp ⊢
  exact fun hcont => hp (heq_at_cont p hcont)

end Densities

/-- Parametric agreement: if for each `p` there is a monotone coupling of `μ p` and `ν p`, and edge
marginals agree at every continuity point of the monotone map `p ↦ ν_p(ω(e) = 1)`, then `μ p` and `ν
p` agree on increasing events for all `p` outside a countable set. -/
lemma phi0_eq_phi1_off_countable
    (μ ν : ℝ → ConfigSpace E → ℝ) (e : E)
    (P : ℝ → ConfigSpace E × ConfigSpace E → ℝ)
    (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
    (hb : Monotone (fun p => edgeMargProb (ν p) e))
    (heq_at_cont : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p →
      ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e') :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ p ∉ S, ∀ {A : Set (ConfigSpace E)}, IsIncreasing A →
        eventMassProb (μ p) A = eventMassProb (ν p) A := by
  refine ⟨{p : ℝ | ¬ ContinuousAt (fun p => edgeMargProb (ν p) e) p},
    hb.countable_not_continuousAt, ?_⟩
  intro p hp A hA
  simp only [mem_ofPred_eq, not_not] at hp
  exact fk_unique_of_edgeMarg_eq (hcoup p) (heq_at_cont p hp) hA

/-- Under the hypotheses of `phi0_eq_phi1_off_countable`, the set of `p` for which some increasing
event separates `μ p` and `ν p` is countable. -/
lemma countable_phi_ne
    (μ ν : ℝ → ConfigSpace E → ℝ) (e : E)
    (P : ℝ → ConfigSpace E × ConfigSpace E → ℝ)
    (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
    (hb : Monotone (fun p => edgeMargProb (ν p) e))
    (heq_at_cont : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p →
      ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e') :
    {p : ℝ | ∃ A : Set (ConfigSpace E), IsIncreasing A ∧
        eventMassProb (μ p) A ≠ eventMassProb (ν p) A}.Countable := by
  refine hb.countable_not_continuousAt.mono ?_
  intro p hp
  simp only [mem_ofPred_eq] at hp ⊢
  obtain ⟨A, hA, hne⟩ := hp
  intro hcont
  exact hne (fk_unique_of_edgeMarg_eq (hcoup p) (heq_at_cont p hcont) hA)

end FK

end StatMech
