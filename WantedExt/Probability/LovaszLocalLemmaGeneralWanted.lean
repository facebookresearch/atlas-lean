/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic

/-!
# The general (asymmetric) Lovász local lemma

The asymmetric form of the local lemma, in the finite setting of
`MathlibExt.Probability.Combinatorics.LovaszLocalLemma` (a probability mass function on a finite
set, a finite family of events and a dependency graph): if there are `xᵢ ∈ [0, 1)` with
`P(Aᵢ) ≤ xᵢ ∏_{j ~ i} (1 - xⱼ)` for every `i`, and each `Aᵢ` is mutually independent of the
events that are neither `Aᵢ` nor adjacent to it, then `P(no Aᵢ occurs) ≥ ∏ᵢ (1 - xᵢ)`. Taking
`xᵢ = 1/(d + 1)` recovers the symmetric criterion `e p (d + 1) ≤ 1` already proved in
`lovasz_local_lemma_symmetric_finite`.

Reference: Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes,
Spring 2019, Theorem 6.10 and the deduction of Theorem 6.9 after it
(https://yufeizhao.com/pm/sp19/pmnotes.pdf).
-/

@[expose] public section

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemmaGeneralWanted

/-- **Lovász local lemma, general form.** Let `pmf` be a probability mass function on a finite
set `Ω`, let `(Aᵢ)_{i ∈ I}` be finitely many events and `G` a graph on `I` such that, for every
`i` and every set `S` of indices that are neither `i` nor neighbours of `i`,
`P(Aᵢ ∩ ⋂_{j ∈ S} Aⱼ) = P(Aᵢ) P(⋂_{j ∈ S} Aⱼ)`. If `x : I → [0, 1)` satisfies
`P(Aᵢ) ≤ xᵢ ∏_{j ~ i} (1 - xⱼ)` for all `i`, then the probability that no `Aᵢ` occurs is at least
`∏ᵢ (1 - xᵢ)` (Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019,
Theorem 6.10, with mutual independence as in Definition 6.2; the hypothesis on intersections
of the `Aⱼ` with all `S` is the form used in `lovasz_local_lemma_symmetric_finite`). -/
theorem_wanted lovasz_local_lemma_general_finite {Ω I : Type*} [Fintype Ω] [Fintype I]
    [DecidableEq I] (pmf : Ω → ℝ) (hpmf_nonneg : ∀ ω, 0 ≤ pmf ω)
    (hpmf_sum : ∑ ω : Ω, pmf ω = 1) (A : I → Set Ω) (G : SimpleGraph I) [DecidableRel G.Adj]
    (hDep : ∀ (i : I) (S : Finset I), (∀ j ∈ S, j ∉ insert i (G.neighborSet i)) →
      ∑ ω : Ω, (if ω ∈ A i ∧ ∀ j ∈ S, ω ∈ A j then pmf ω else 0) =
        (∑ ω : Ω, (if ω ∈ A i then pmf ω else 0)) *
          (∑ ω : Ω, (if ∀ j ∈ S, ω ∈ A j then pmf ω else 0)))
    (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hA : ∀ i, ∑ ω : Ω, (if ω ∈ A i then pmf ω else 0) ≤
      x i * ∏ j ∈ G.neighborFinset i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ ∑ ω : Ω, (if ∀ i : I, ω ∉ A i then pmf ω else 0)

end MathlibExt.Probability.Combinatorics.LovaszLocalLemmaGeneralWanted
