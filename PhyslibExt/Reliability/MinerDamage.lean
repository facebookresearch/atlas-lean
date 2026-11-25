/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Palmgren–Miner damage sum

The empirical cycle-ratio sum `D = ∑ i, n i / N i` over finitely many declared
cycle classes, with class-count aggregation and monotonicity.

## i. Overview

A declared cycle spectrum has finitely many cycle classes `i : ι`. Class `i`
carries a declared count `n i` (cycles applied in that class) and a calibrated
life `N i` (cycles to failure under constant-amplitude loading at that class).
Its Palmgren–Miner damage sum is `D = ∑ i, n i / N i` (`minerDamage`), an
empirical bookkeeping index, not a failure model. `minerDamage` is a
dimensionless cycle-ratio sum: it is not `Reliability.damageLifetime` (a
hitting time) or `Reliability.linearDamage` (a damage path in time), and no
lifetime or failure event is derived from it.

Counts are declared reals `n i ≥ 0`, so a half cycle counts `1 / 2`; how a load
history is reduced to counted cycles is not modeled. Declared records `k : κ`
carry counts `r k ≥ 0` and a class `g k`; `cycleClassCounts g r` adds the
counts of the records of each class. For a pavement layer the records can be
axle-load groups by season and the lives the allowable repetitions of a
calibrated fatigue transfer function.

`N i` is the value at class `i` of a supplied calibrated constant-amplitude
S–N (Wöhler), strain-life or transfer curve; its empirical constants and any
temperature or rate calibration stay inside the supplied values. Only
`0 < N i` is assumed: no analytic law, slope, endurance limit or infinite life
is fixed. A class of infinite life (at or below an endurance limit or cutoff)
is not representable here, and its cycles are not declared. `minerDamage`
takes a proof that every life is positive, so a zero life is rejected; with
Lean's `x / 0 = 0` the bare sum would ignore the count at a zero-life class.

Counts and lives use one cycle unit (cycles, reversals or thousands of
repetitions), so each `n i / N i` is dimensionless. For nonnegative counts
`0 ≤ D`, with `D = 0` exactly when no cycle is declared. `D` is nondecreasing
in each count, nonincreasing in each life, and linear in the counts with no
cap; `D = 1` has no special status. `D` sees declared records only through
their class counts: merging or splitting classes of equal life, or reordering
records, leaves `D` unchanged. This is a property of the sum and need not
preserve physical damage.

Excluded: no Miner failure theorem (nothing is asserted at `D = 1` or any
other threshold), no sequence-effect, mean-stress, healing or nonlinear
damage model, no new fatigue law or S–N curve, no cycle-counting algorithm,
no fitted constants or data, and no safety certification.

## ii. Key results

- `Reliability.minerDamage`: the damage sum, defined only for positive lives.
- `Reliability.cycleClassCounts`: class counts aggregated from records.
- `Reliability.minerDamage_cycleClassCounts`: aggregation conserves counts
  and gives the record-wise damage.
- `Reliability.minerDamage_unit_change`: one cycle unit for counts and lives.
- `Reliability.minerDamage_nonneg_and_eq_zero_iff`: nonnegative damage, zero
  exactly at zero counts.
- `Reliability.minerDamage_mono`: more cycles and shorter lives do not
  decrease damage.
- `Reliability.bareSum_at_zero_life_misreports`: the unguarded sum is blind
  to a zero-life class.

## iii. Table of contents

- A. The damage sum and class counts
- B. Units, damage domain and monotonicity
- C. Boundary examples

## iv. References

- A. Palmgren, *Die Lebensdauer von Kugellagern*, VDI-Zeitschrift 68 (1924)
  339–341.
- M. A. Miner, *Cumulative damage in fatigue*, J. Appl. Mech. 12 (1945)
  A159–A164.

Both state the linear damage-accumulation hypothesis, failure when the cycle
ratios `n / N` sum to one; only the summation is adopted here.
-/

@[expose] public section

namespace Reliability

/-! ## A. The damage sum and class counts -/

variable {ι κ : Type*}

/-- Palmgren–Miner damage sum `D = ∑ i, n i / N i`: `n i` declared cycles and calibrated life
`N i` cycles in class `i`. Defined only for positive lives, so a zero life is rejected. An
empirical index: no failure is asserted at `D = 1`. -/
noncomputable def minerDamage [Fintype ι] (n N : ι → ℝ) (_hN : ∀ i, 0 < N i) : ℝ :=
  ∑ i, n i / N i

/-- Class counts of declared records: record `k` carries `r k` cycles of class `g k`, and the
count of class `i` is the sum of `r k` over the records with `g k = i`. -/
def cycleClassCounts [Fintype κ] [DecidableEq ι] (g : κ → ι) (r : κ → ℝ) (i : ι) : ℝ :=
  ∑ k with g k = i, r k

/-- Declared-count adapter, the bridge from declared records to the class spectrum. Records with
nonnegative counts `r k` are assigned classes `g k` with positive calibrated lives `N i`.
Aggregating by class gives nonnegative class counts, conserves the total count, and gives the
record-wise damage `∑ k, r k / N (g k)`, each record read as its own class with the life of its
class. So regrouping records within classes, or merging and splitting classes of equal life,
leaves the damage unchanged. -/
lemma minerDamage_cycleClassCounts [Fintype κ] [Fintype ι] [DecidableEq ι] (g : κ → ι)
    {r : κ → ℝ} (hr : ∀ k, 0 ≤ r k) {N : ι → ℝ} (hN : ∀ i, 0 < N i) :
    (∀ i, 0 ≤ cycleClassCounts g r i) ∧ ∑ i, cycleClassCounts g r i = ∑ k, r k ∧
      minerDamage (cycleClassCounts g r) N hN =
        minerDamage r (fun k => N (g k)) (fun k => hN (g k)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    unfold cycleClassCounts
    exact Finset.sum_nonneg (fun k _ => hr k)
  · simp only [cycleClassCounts]
    exact Finset.sum_fiberwise Finset.univ g r
  · unfold minerDamage
    simp only [cycleClassCounts]
    have h : ∀ i, (∑ k with g k = i, r k) / N i
        = ∑ k with g k = i, r k / N (g k) := by
      intro i
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk2 : g k = i := (Finset.mem_filter.mp hk).2
      rw [hk2]
    simp_rw [h]
    exact Finset.sum_fiberwise Finset.univ g (fun k => r k / N (g k))

/-! ## B. Units, damage domain and monotonicity -/

/-- Unit convention. Counts and lives must use one cycle unit. Changing it by a factor `c > 0`
for both (cycles to reversals: `c = 2`) leaves `D` unchanged; converting only the counts
multiplies `D` by `c`, so counts in reversals read against lives in cycles double `D`. The second
identity shows that `D` scales linearly with a common factor on the counts,
with no cap at `D = 1`. -/
lemma minerDamage_unit_change [Fintype ι] {c : ℝ} (hc : 0 < c) (n : ι → ℝ) {N : ι → ℝ}
    (hN : ∀ i, 0 < N i) :
    minerDamage (fun i => c * n i) (fun i => c * N i) (fun i => mul_pos hc (hN i)) =
        minerDamage n N hN ∧
      minerDamage (fun i => c * n i) N hN = c * minerDamage n N hN := by
  constructor
  · unfold minerDamage
    apply Finset.sum_congr rfl
    intro i _
    exact mul_div_mul_left _ _ (ne_of_gt hc)
  · unfold minerDamage
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_div_assoc c (n i) (N i)

/-- Damage domain and zero cycles. For nonnegative counts and positive lives, `0 ≤ D`, and
`D = 0` exactly when every declared count is zero: no cycles give no damage, and every declared
cycle registers. -/
lemma minerDamage_nonneg_and_eq_zero_iff [Fintype ι] {n N : ι → ℝ} (hn : ∀ i, 0 ≤ n i)
    (hN : ∀ i, 0 < N i) :
    0 ≤ minerDamage n N hN ∧ (minerDamage n N hN = 0 ↔ ∀ i, n i = 0) := by
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ n i / N i :=
    fun i _ => div_nonneg (hn i) (le_of_lt (hN i))
  constructor
  · unfold minerDamage
    exact Finset.sum_nonneg hterm
  · unfold minerDamage
    rw [Finset.sum_eq_zero_iff_of_nonneg hterm]
    constructor
    · intro h i
      have hi := h i (Finset.mem_univ i)
      rw [div_eq_zero_iff] at hi
      rcases hi with h0 | h0
      · exact h0
      · exact absurd h0 (ne_of_gt (hN i))
    · intro h i _
      rw [h i]
      exact zero_div (N i)

/-- Monotonicity. More declared cycles and shorter calibrated lives never decrease the damage:
for nonnegative counts `n ≤ n'` and positive lives `N' ≤ N`, `D(n, N) ≤ D(n', N')`. Damage only
accumulates as cycles are added, and a shorter-life (conservative) calibration gives a larger
`D`. -/
lemma minerDamage_mono [Fintype ι] {n n' N N' : ι → ℝ} (hn : ∀ i, 0 ≤ n i)
    (hnn' : ∀ i, n i ≤ n' i) (hN' : ∀ i, 0 < N' i) (hNN' : ∀ i, N' i ≤ N i) :
    minerDamage n N (fun i => (hN' i).trans_le (hNN' i)) ≤ minerDamage n' N' hN' := by
  unfold minerDamage
  apply Finset.sum_le_sum
  intro i _
  have hNi : 0 < N i := lt_of_lt_of_le (hN' i) (hNN' i)
  have hn'i : 0 ≤ n' i := le_trans (hn i) (hnn' i)
  have step1 : n i / N i ≤ n' i / N i := by
    rw [div_eq_mul_one_div (n i) (N i), div_eq_mul_one_div (n' i) (N i)]
    exact mul_le_mul_of_nonneg_right (hnn' i) (le_of_lt (one_div_pos.mpr hNi))
  have step2 : n' i / N i ≤ n' i / N' i := by
    rw [div_eq_mul_one_div (n' i) (N i), div_eq_mul_one_div (n' i) (N' i)]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (hN' i) (hNN' i)) hn'i
  exact le_trans step1 step2

/-! ## C. Boundary examples -/

/-- Zero life rejected, control. Without the positivity precondition, Lean's `x / 0 = 0` makes
the bare sum `∑ i, n i / N i` blind to the count at a class `j` with `N j = 0`: any count there
registers no damage, although a vanishing life would mean immediate failure. This is why
`minerDamage` demands `∀ i, 0 < N i`. -/
lemma bareSum_at_zero_life_misreports [Fintype ι] [DecidableEq ι] (n N : ι → ℝ) {j : ι}
    (hj : N j = 0) (x : ℝ) :
    ∑ i, Function.update n j x i / N i = ∑ i, n i / N i := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i = j
  · subst h
    rw [Function.update_self, hj, div_zero, div_zero]
  · rw [Function.update_of_ne h]

end Reliability
