/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Ideal mixer and nonselective splitter

For finite species and streams, the ideal units conserve each species. Composition
is normalized only for streams with positive total flow.
-/

open scoped BigOperators

namespace Domains.Chemistry.ProcessBalances.MixerSplitter

/-- The ideal mixer adds species flows. Its positive-total outlet has component
fractions given by the convex combination of positive-flow inlets, with weights
proportional to their totals. A nonselective splitter conserves the inlet species
flows and preserves composition at every positive-flow outlet.

Source for the splitter balances: *Introduction to Chemical Engineering Processes*,
Wikibooks, [How to Analyze a Recycle System](https://en.wikibooks.org/wiki/Introduction_to_Chemical_Engineering_Processes/How_to_Analyze_a_Recycle_System). -/
public theorem mixer_splitter_balances {S I K : Type*} [Fintype S] [Fintype I] [Fintype K]
    (inlet : I → S → ℝ) (feed : S → ℝ) (fraction : K → ℝ)
    (hinlet : ∀ i s, 0 ≤ inlet i s) (_hfeed : ∀ s, 0 ≤ feed s)
    (hfraction : ∀ k, 0 ≤ fraction k) (hshares : ∑ k, fraction k = 1) :
    let total (q : S → ℝ) := ∑ s, q s
    let mixed (s : S) := ∑ i, inlet i s
    let split (k : K) (s : S) := fraction k * feed s
    let positive := Finset.univ.filter (fun i => 0 < total (inlet i))
    (total mixed = ∑ i, total (inlet i)) ∧
    (0 < total mixed →
      (∀ i ∈ positive, 0 ≤ total (inlet i) / total mixed) ∧
      (∑ i ∈ positive, total (inlet i) / total mixed) = 1 ∧
      ∀ s, mixed s / total mixed = ∑ i ∈ positive,
        (total (inlet i) / total mixed) * (inlet i s / total (inlet i))) ∧
    (∀ s, ∑ k, split k s = feed s) ∧
    (∀ k, 0 < total (split k) → 0 < total feed ∧
      ∀ s, split k s / total (split k) = feed s / total feed) := by
  let total (q : S → ℝ) := ∑ s, q s
  let mixed (s : S) := ∑ i, inlet i s
  let split (k : K) (s : S) := fraction k * feed s
  have hm : total mixed = ∑ i, total (inlet i) := Finset.sum_comm
  have hn (i : I) : 0 ≤ total (inlet i) := Finset.sum_nonneg fun s _ => hinlet i s
  have hz (i : I) (h : ¬ 0 < total (inlet i)) (s : S) : inlet i s = 0 := by
    have hs : inlet i s ≤ total (inlet i) :=
      Finset.single_le_sum (fun a _ => hinlet i a) (Finset.mem_univ s)
    exact le_antisymm (hs.trans (le_of_not_gt h)) (hinlet i s)
  refine ⟨hm, ?_, ?_, ?_⟩
  · intro hout
    change 0 < total mixed at hout
    refine ⟨fun i _ => div_nonneg (hn i) hout.le, ?_, ?_⟩
    · change (∑ i ∈ Finset.univ.filter (fun i => 0 < total (inlet i)),
          total (inlet i) / total mixed) = 1
      rw [Finset.sum_filter]
      calc
        _ = ∑ i, total (inlet i) / total mixed := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : 0 < total (inlet i)
          · simp [hi]
          · have hi0 : total (inlet i) = 0 := le_antisymm (le_of_not_gt hi) (hn i)
            simp [hi0]
        _ = (∑ i, total (inlet i)) / total mixed := (Finset.sum_div _ _ _).symm
        _ = 1 := by rw [← hm, div_self (ne_of_gt hout)]
    · intro s
      change (∑ i, inlet i s) / total mixed =
        ∑ i ∈ Finset.univ.filter (fun i => 0 < total (inlet i)),
          (total (inlet i) / total mixed) * (inlet i s / total (inlet i))
      rw [Finset.sum_div, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : 0 < total (inlet i)
      · rw [ite_eq_left hi, mul_comm, div_mul_div_cancel₀ (ne_of_gt hi)]
      · simp [hi, hz i hi s]
  · intro s
    change (∑ k, fraction k * feed s) = feed s
    rw [← Finset.sum_mul, hshares, one_mul]
  · intro k hk
    change 0 < total (split k) at hk
    have htotal : total (split k) = fraction k * total feed := (Finset.mul_sum _ _ _).symm
    rw [htotal] at hk
    rcases mul_pos_iff.mp hk with ⟨hfrac, htot⟩ | ⟨hfrac, _⟩
    · refine ⟨htot, fun s => ?_⟩
      change fraction k * feed s / total (split k) = feed s / total feed
      rw [htotal]
      exact mul_div_mul_left _ _ (ne_of_gt hfrac)
    · exact False.elim (not_lt_of_ge (hfraction k) hfrac)

end Domains.Chemistry.ProcessBalances.MixerSplitter
