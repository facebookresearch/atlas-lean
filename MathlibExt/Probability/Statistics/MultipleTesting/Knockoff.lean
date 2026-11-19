/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import Mathlib.Order.WithBot

/-!
# The knockoff filter: thresholds and selected sets

The knockoff filter (R. F. Barber and E. J. Candès, *Controlling the false discovery rate via
knockoffs*, Ann. Statist. 43 (2015), arXiv:1404.5609; E. Candès, Y. Fan, L. Janson and J. Lv,
*Panning for gold: model-X knockoffs for high dimensional controlled variable selection*,
J. R. Statist. Soc. B 80 (2018), arXiv:1610.02351) selects variables from a vector of statistics
`W = (W_1, …, W_p)`, one per variable, where a large positive `W_j` is evidence that variable `j`
is relevant. For a target FDR level `q` it uses the data-dependent threshold

`T = min {t ∈ 𝒲 : (c + #{j : W_j ≤ -t}) / (#{j : W_j ≥ t} ∨ 1) ≤ q}`,

with `𝒲 = {|W_j|} \ {0}` and `T = +∞` if the set is empty, and selects `Ŝ = {j : W_j ≥ T}`. The
offset `c = 0` is the knockoff filter and `c = 1` the knockoff+ filter. This module defines the
threshold and the selected set as functions of the vector `W` and proves their deterministic
properties. The FDR guarantees, which depend only on the null statistics having i.i.d. fair signs
independent of `|W|` (see `flipSigns`), are recorded as wanted statements in
`WantedExt.Probability.KnockoffFDRWanted`.

## Main definitions

* `knockoffThreshold c q W`: the threshold `T ∈ ℝ ∪ {+∞}` with offset `c`.
* `knockoffSelection c q W`: the selected set `{j : W_j ≥ T}`.
* `flipSigns S w`: `w` with the signs of the coordinates in `S` flipped.

## Main results

* `pos_of_mem_knockoffSelection`: only variables with `W_j > 0` are selected.
* `knockoffThreshold_ratio_le`: at a finite threshold `T`, the estimated false discovery
  proportion `(c + #{j : W_j ≤ -T}) / (#Ŝ ∨ 1)` is at most `q`.
* `knockoffSelection_one_subset_zero`: knockoff+ selects a subset of what knockoff selects.
* `falseDiscoveryProportion_knockoffSelection_one_le`: at a finite knockoff+ threshold `T`,
  `FDP ≤ q · #{null, W_j ≥ T} / (1 + #{null, W_j ≤ -T})` (Barber and Candès 2015, (2.5)).
-/

@[expose] public section

open Finset

namespace MathlibExt.Probability.Statistics.MultipleTesting.Knockoff

variable {p : ℕ}

/-- **Knockoff threshold.** For an offset `c` (`0` for knockoff, `1` for knockoff+), a target level
`q` and statistics `W : Fin p → ℝ`, the least `t = |W_j| > 0` with
`(c + #{i : W_i ≤ -t}) / (#{i : W_i ≥ t} ∨ 1) ≤ q`, and `⊤` if there is none.

Source: R. F. Barber and E. J. Candès, *Controlling the false discovery rate via knockoffs*,
Ann. Statist. 43 (2015) 2055-2085, arXiv:1404.5609, equation (1.8) (`c = 0`) and Definition 2,
equation (1.9) (`c = 1`). -/
noncomputable def knockoffThreshold (c : ℕ) (q : ℝ) (W : Fin p → ℝ) : WithTop ℝ :=
  (univ.filter fun j => W j ≠ 0 ∧
      ((c : ℝ) + (univ.filter fun i => W i ≤ -|W j|).card) /
        max ((univ.filter fun i => |W j| ≤ W i).card : ℝ) 1 ≤ q).inf
    fun j => ((|W j| : ℝ) : WithTop ℝ)

/-- **Knockoff selected set.** The variables `j` with `W_j ≥ T`, for the threshold
`T = knockoffThreshold c q W`; it is empty when `T = ⊤`.

Source: R. F. Barber and E. J. Candès, *Controlling the false discovery rate via knockoffs*,
Ann. Statist. 43 (2015), arXiv:1404.5609, Definitions 1 and 2. -/
noncomputable def knockoffSelection (c : ℕ) (q : ℝ) (W : Fin p → ℝ) : Finset (Fin p) :=
  univ.filter fun j => knockoffThreshold c q W ≤ ((W j : ℝ) : WithTop ℝ)

/-- **Sign flip on a set of coordinates.** `flipSigns S w` is `w` with `w_j` replaced by `-w_j`
for `j ∈ S`. The knockoff FDR theorems need only that flipping the signs of any set of null
statistics leaves the law of `W` unchanged, the form in which Lemma 1 of Barber and Candès (2015,
arXiv:1404.5609) and Lemma 3.3 of Candès, Fan, Janson and Lv (2018, arXiv:1610.02351) are
proved. -/
def flipSigns (S : Finset (Fin p)) (w : Fin p → ℝ) : Fin p → ℝ :=
  fun j => if j ∈ S then -w j else w j

/-- **The knockoff threshold is attained.** A finite threshold equals `|W_j|` for some `j` with
`W_j ≠ 0` that satisfies the defining inequality. -/
theorem exists_eq_of_knockoffThreshold_eq_coe {c : ℕ} {q : ℝ} {W : Fin p → ℝ} {t : ℝ}
    (ht : knockoffThreshold c q W = (t : WithTop ℝ)) :
    ∃ j, W j ≠ 0 ∧ ((c : ℝ) + (univ.filter fun i => W i ≤ -|W j|).card) /
        max ((univ.filter fun i => |W j| ≤ W i).card : ℝ) 1 ≤ q ∧ |W j| = t := by
  classical
  set s := univ.filter fun j => W j ≠ 0 ∧
      ((c : ℝ) + (univ.filter fun i => W i ≤ -|W j|).card) /
        max ((univ.filter fun i => |W j| ≤ W i).card : ℝ) 1 ≤ q with hs
  rcases s.eq_empty_or_nonempty with he | hne
  · have : knockoffThreshold c q W = ⊤ := by
      rw [knockoffThreshold, ← hs, he, Finset.inf_empty]
    rw [this] at ht
    exact absurd ht WithTop.top_ne_coe
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf s hne fun j => ((|W j| : ℝ) : WithTop ℝ)
    have hj' := (Finset.mem_filter.1 hj).2
    refine ⟨j, hj'.1, hj'.2, ?_⟩
    have : knockoffThreshold c q W = ((|W j| : ℝ) : WithTop ℝ) := by
      rw [knockoffThreshold, ← hs, hjeq]
    rw [this] at ht
    exact WithTop.coe_injective ht

/-- **A finite knockoff threshold is positive.** -/
theorem pos_of_knockoffThreshold_eq_coe {c : ℕ} {q : ℝ} {W : Fin p → ℝ} {t : ℝ}
    (ht : knockoffThreshold c q W = (t : WithTop ℝ)) : 0 < t := by
  obtain ⟨j, hj, -, rfl⟩ := exists_eq_of_knockoffThreshold_eq_coe ht
  exact abs_pos.2 hj

/-- **Only positive statistics are selected.** Every variable selected by the knockoff filter
(with any offset and level) has `W_j > 0`. -/
theorem pos_of_mem_knockoffSelection {c : ℕ} {q : ℝ} {W : Fin p → ℝ} {j : Fin p}
    (hj : j ∈ knockoffSelection c q W) : 0 < W j := by
  have hle := (Finset.mem_filter.1 hj).2
  induction h : knockoffThreshold c q W with
  | top => rw [h] at hle; exact absurd hle (by simp)
  | coe t =>
    rw [h, WithTop.coe_le_coe] at hle
    exact (pos_of_knockoffThreshold_eq_coe h).trans_le hle

/-- **The estimated false discovery proportion is at most `q` at the threshold.** If the knockoff
threshold is a finite `T`, then `(c + #{j : W_j ≤ -T}) / (#Ŝ ∨ 1) ≤ q`, where `Ŝ` is the selected
set. This is the defining property of `T` (Barber and Candès 2015, arXiv:1404.5609, equations
(1.8)-(1.9)). -/
theorem knockoffThreshold_ratio_le {c : ℕ} {q : ℝ} {W : Fin p → ℝ} {t : ℝ}
    (ht : knockoffThreshold c q W = (t : WithTop ℝ)) :
    ((c : ℝ) + (univ.filter fun i => W i ≤ -t).card) /
        max ((knockoffSelection c q W).card : ℝ) 1 ≤ q := by
  obtain ⟨j, -, hratio, hjt⟩ := exists_eq_of_knockoffThreshold_eq_coe ht
  have hsel : knockoffSelection c q W = univ.filter fun i => |W j| ≤ W i := by
    ext i
    simp only [knockoffSelection, Finset.mem_filter, Finset.mem_univ, true_and, ht,
      WithTop.coe_le_coe, hjt]
  rw [hsel, ← hjt]
  exact hratio

/-- **Knockoff+ is more conservative than knockoff.** The knockoff+ threshold (offset `1`) is at
least the knockoff threshold (offset `0`), so knockoff+ selects a subset of the knockoff
selection (Barber and Candès 2015, arXiv:1404.5609, remark after Definition 2). -/
theorem knockoffSelection_one_subset_zero (q : ℝ) (W : Fin p → ℝ) :
    knockoffSelection 1 q W ⊆ knockoffSelection 0 q W := by
  have hT : knockoffThreshold 0 q W ≤ knockoffThreshold 1 q W := by
    refine Finset.inf_mono fun j hj => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    refine ⟨hj.1, le_trans ?_ hj.2⟩
    exact div_le_div_of_nonneg_right (by simp) (le_max_of_le_right zero_le_one)
  intro j hj
  simp only [knockoffSelection, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hT.trans hj

/-- **The false discovery proportion of knockoff+ is bounded by a null-count ratio.** If the
knockoff+ threshold is a finite `T`, then for any set `H0` of null variables the false discovery
proportion of the knockoff+ selection `Ŝ` satisfies
`FDP ≤ q · #{j ∈ H0 : W_j ≥ T} / (1 + #{j ∈ H0 : W_j ≤ -T})`. This is the deterministic first step
of the proof of FDR control, after which it remains to bound the expectation of the ratio by `1`.

Source: R. F. Barber and E. J. Candès, *Controlling the false discovery rate via knockoffs*,
Ann. Statist. 43 (2015), arXiv:1404.5609, Section 2.4, equation (2.5). -/
theorem falseDiscoveryProportion_knockoffSelection_one_le {q : ℝ} {W : Fin p → ℝ} {t : ℝ}
    (ht : knockoffThreshold 1 q W = (t : WithTop ℝ)) (H0 : Finset (Fin p)) :
    falseDiscoveryProportion H0 (knockoffSelection 1 q W) ≤
      q * ((knockoffSelection 1 q W ∩ H0).card : ℝ) /
        (1 + ((H0.filter fun j => W j ≤ -t).card : ℝ)) := by
  have hratio := knockoffThreshold_ratio_le ht
  set a : ℝ := ((knockoffSelection 1 q W ∩ H0).card : ℝ)
  set D : ℝ := max ((knockoffSelection 1 q W).card : ℝ) 1
  set N : ℝ := ((univ.filter fun i => W i ≤ -t).card : ℝ)
  set N0 : ℝ := ((H0.filter fun j => W j ≤ -t).card : ℝ)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hN0N : N0 ≤ N := by
    simp only [N0, N]
    exact_mod_cast Finset.card_le_card fun j hj => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; exact hj.2
  have hN0 : 0 ≤ N0 := Nat.cast_nonneg _
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hqD : 1 + N ≤ q * D := by
    have := (div_le_iff₀ hD).1 (by simpa [N, D] using hratio)
    linarith
  rw [falseDiscoveryProportion]
  change a / D ≤ q * a / (1 + N0)
  rw [div_le_div_iff₀ hD (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hN0N ha, mul_le_mul_of_nonneg_left hqD ha]

end MathlibExt.Probability.Statistics.MultipleTesting.Knockoff
