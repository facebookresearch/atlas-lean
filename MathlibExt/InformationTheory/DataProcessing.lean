/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import MathlibExt.Probability.MarkovChainContraction

/-!
# Total variation: data processing and the classical Helstrom identity

Total variation is the shared half-`L1` distance
`MathlibExt.Probability.MarkovChainContraction.tvDist` of two PMFs on a finite type. The
data-processing inequality (pushing two distributions through the same kernel `α → PMF β`
cannot increase their total variation) is
`MathlibExt.Probability.MarkovChainContraction.tvDist_bind_le`. This file adds the classical
Helstrom identity for two equally likely hypotheses.

## Main results

* `helstrom_max_sum`: `∑ a, max (p a) (q a) = 1 + tvDist p q`, so the optimal probability of
  guessing which of `p` and `q` produced a sample is `(1 + tvDist p q) / 2`.
-/

@[expose] public section

namespace MathlibExt.InformationTheory.DataProcessing

open MathlibExt.Probability.MarkovChainContraction (tvDist)

private theorem pmf_toReal_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  have h : (∑ a, p a).toReal = (1 : ENNReal).toReal := by
    congr 1
    rw [← PMF.tsum_coe p, tsum_eq_sum (fun a ha => False.elim (ha (Finset.mem_univ a)))]
  rw [ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a), ENNReal.toReal_one] at h
  exact h

/-- Helstrom discrimination for two equally likely classical
states: the sum over outcomes of the larger likelihood is
`1 + tvDist p q`, so the optimal guessing probability (that sum
halved) is `(1 + tvDist p q) / 2`. -/
theorem helstrom_max_sum {α : Type*} [Fintype α]
    (p q : PMF α) :
    (∑ a, max (p a).toReal (q a).toReal) = 1 + tvDist p q := by
  have hpt : ∀ a, max (p a).toReal (q a).toReal
      = ((p a).toReal + (q a).toReal + |(p a).toReal - (q a).toReal|) / 2 := by
    intro a
    rcases le_total (p a).toReal (q a).toReal with h | h
    · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  unfold tvDist MathlibExt.Probability.MarkovMixing.tvDist
  calc (∑ a, max (p a).toReal (q a).toReal)
      = ∑ a, (((p a).toReal + (q a).toReal) / 2
          + |(p a).toReal - (q a).toReal| / 2) :=
        Finset.sum_congr rfl (fun a _ => by rw [hpt a]; ring)
    _ = (∑ a, ((p a).toReal + (q a).toReal)) / 2
          + (∑ a, |(p a).toReal - (q a).toReal|) / 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
    _ = 1 + 1 / 2 * ∑ a, |(p a).toReal - (q a).toReal| := by
        rw [Finset.sum_add_distrib, pmf_toReal_sum p, pmf_toReal_sum q]
        ring

end MathlibExt.InformationTheory.DataProcessing
