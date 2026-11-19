/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.AdmixtureGraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Target-only `f3` positivity

Patterson et al. (2012, Appendix C, Theorem 1, no-ascertainment case) show
`F3(C; A, B) = E[(c - a) * (c - b)] ≥ 0` for populations on a simple
phylogeny, so a negative `f3` is evidence of complex phylogeny in the target
`C`. In the second-moment drift model of
`MathlibExt.Biology.PopulationGenetics.FStatistics`, only the target's
lineage weights need to be binary for this conclusion: the sources `A` and
`B` may themselves be admixed, with weights anywhere in `[0, 1]`. This
strengthens `DriftModel.f3_nonneg_of_hasBinaryLoadings`, which requires
binary loadings for every population.

## Main results

* `sum_nonneg_of_target_binary`: the finite-sum core estimate.
* `DriftModel.f3_nonneg_of_binary_target`: target-only positivity in any
  drift model.
* `AdmixtureGraph.f3_nonneg_of_binary_weights`: the admixture-graph form,
  where graph weights automatically lie in `[0, 1]`.
* `AdmixtureGraph.exists_weight_ne_zero_ne_one_of_f3_neg`: if `f3 C A B < 0`
  in a graph drift model, then some lineage weight of `C` is neither `0`
  nor `1`.

## References

* N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan,
  T. Genschoreck, T. Webster, D. Reich, *Ancient admixture in human
  history*, Genetics 192 (2012), 1065–1093.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Biology.PopulationGenetics.Admixture

/-- Core termwise estimate behind target-only `f3` positivity: a finite sum of
`(wC e - wA e) * (wC e - wB e) * len e` is nonnegative when every `len e` is
nonnegative, every target weight `wC e` is `0` or `1`, and the source weights
`wA e`, `wB e` lie in `[0, 1]` (they need not be binary). -/
theorem sum_nonneg_of_target_binary {ι : Type*} [Fintype ι]
    (len wC wA wB : ι → ℝ)
    (hlen : ∀ e, 0 ≤ len e)
    (hC : ∀ e, wC e = 0 ∨ wC e = 1)
    (hA0 : ∀ e, 0 ≤ wA e) (hA1 : ∀ e, wA e ≤ 1)
    (hB0 : ∀ e, 0 ≤ wB e) (hB1 : ∀ e, wB e ≤ 1) :
    0 ≤ ∑ e, (wC e - wA e) * (wC e - wB e) * len e := by
  apply Finset.sum_nonneg
  intro e _
  rcases hC e with h | h
  · rw [h, zero_sub, zero_sub, neg_mul_neg]
    exact mul_nonneg (mul_nonneg (hA0 e) (hB0 e)) (hlen e)
  · rw [h]
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr (hA1 e)) (sub_nonneg.mpr (hB1 e)))
      (hlen e)

end MathlibExt.Biology.PopulationGenetics.Admixture

namespace MathlibExt.Biology.PopulationGenetics.FStatistics

open MathlibExt.Biology.PopulationGenetics.Admixture

/-- Target-only `f3` positivity in the drift model: if the target `C` has
binary lineage weights and the source weights of `A` and `B` lie in `[0, 1]`
(they need not be binary, so `A` and `B` may be admixed), then
`f3 C A B ≥ 0`. -/
theorem DriftModel.f3_nonneg_of_binary_target
    {Ω P E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E]
    (M : DriftModel μ E P) (C A B : P)
    (hC : ∀ e, M.weight C e = 0 ∨ M.weight C e = 1)
    (hA : ∀ e, 0 ≤ M.weight A e ∧ M.weight A e ≤ 1)
    (hB : ∀ e, 0 ≤ M.weight B e ∧ M.weight B e ≤ 1) :
    0 ≤ f3 μ M.freq C A B := by
  rw [M.f3_freq]
  exact sum_nonneg_of_target_binary M.len (M.weight C) (M.weight A)
    (M.weight B) M.len_nonneg hC (fun e => (hA e).1) (fun e => (hA e).2)
    (fun e => (hB e).1) (fun e => (hB e).2)

end MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExt.Biology.PopulationGenetics

open MathlibExt.Biology.PopulationGenetics.FStatistics

/-- On an admixture graph, a target `C` whose lineage weights are all `0` or
`1` has `f3 C A B ≥ 0` for arbitrary, possibly admixed, sources `A` and `B`,
in any drift model carrying the graph's weights. Graph weights always lie
in `[0, 1]` (`AdmixtureGraph.weight_nonneg`,
`AdmixtureGraph.weight_le_one`). Binarity of `C`'s weights is assumed
directly; characterizing it by a unique root-ward path is not proved here. -/
theorem AdmixtureGraph.f3_nonneg_of_binary_weights
    {V Ω : Type*} [DecidableEq V] [Fintype V] {m : MeasurableSpace Ω}
    {μ : Measure Ω} (G : AdmixtureGraph V) {M : DriftModel μ G.Edge V}
    (hM : M.weight = G.weight) (C A B : V)
    (hC : ∀ e, G.weight C e = 0 ∨ G.weight C e = 1) :
    0 ≤ f3 μ M.freq C A B := by
  apply M.f3_nonneg_of_binary_target C A B
  · intro e
    rw [hM]
    exact hC e
  · intro e
    rw [hM]
    exact ⟨G.weight_nonneg A e, G.weight_le_one A e⟩
  · intro e
    rw [hM]
    exact ⟨G.weight_nonneg B e, G.weight_le_one B e⟩

/-- Contrapositive: in a graph drift model with `f3 C A B < 0`, the target
`C` has a lineage weight that is neither `0` nor `1`, so `C` does not have
the binary weights of an unadmixed population. -/
theorem AdmixtureGraph.exists_weight_ne_zero_ne_one_of_f3_neg
    {V Ω : Type*} [DecidableEq V] [Fintype V] {m : MeasurableSpace Ω}
    {μ : Measure Ω} (G : AdmixtureGraph V) {M : DriftModel μ G.Edge V}
    (hM : M.weight = G.weight) {C A B : V} (h : f3 μ M.freq C A B < 0) :
    ∃ e, G.weight C e ≠ 0 ∧ G.weight C e ≠ 1 := by
  by_contra hcon
  refine (G.f3_nonneg_of_binary_weights hM C A B (fun e => ?_)).not_gt h
  by_cases h0 : G.weight C e = 0
  · exact Or.inl h0
  · exact Or.inr (by
      by_contra h1
      exact hcon ⟨e, h0, h1⟩)

end MathlibExt.Biology.PopulationGenetics
