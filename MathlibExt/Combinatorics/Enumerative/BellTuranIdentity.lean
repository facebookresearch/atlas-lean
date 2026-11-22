/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

namespace MetaMathlibExt

private lemma aux_two_pow (n : ℕ) (hn : 1 ≤ n) : (2 : ℝ) ^ n ≤ 2 * (n.factorial : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have h2 : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      have h : 2 ≤ n + 1 := by omega
      exact_mod_cast h
    calc (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
      _ ≤ 2 * (2 * (n.factorial : ℝ)) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ 2 * ((((n + 1 : ℕ)) : ℝ) * (n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h2 (by positivity)) (by norm_num)
      _ = 2 * (((n + 1).factorial : ℝ)) := by
        rw [Nat.factorial_succ]; push_cast; ring

private lemma two_pow_le_two_mul_factorial (k : ℕ) : (2 : ℝ) ^ k ≤ 2 * (k.factorial : ℝ) := by
  rcases eq_zero_or_pos k with rfl | hpos
  · norm_num [Nat.factorial_zero]
  · have h1 : 1 ≤ k := hpos
    exact aux_two_pow k h1

private lemma summable_pow_div_factorial_real (m : ℕ) :
    Summable (fun k : ℕ => (k : ℝ) ^ m / (k.factorial : ℝ)) := by
  have hgeo : Summable (fun k : ℕ => (k : ℝ) ^ m * ((1 / 2 : ℝ) ^ k)) :=
    summable_pow_mul_geometric_of_norm_lt_one m (by norm_num)
  have h2 := hgeo.mul_left 2
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h2
  have hfact := two_pow_le_two_mul_factorial k
  have hpos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hnn : (0 : ℝ) ≤ (k : ℝ) ^ m := by positivity
  have h1 : (1 : ℝ) ≤ 2 * ((1 / 2 : ℝ) ^ k) * (k.factorial : ℝ) := by
    have e : (2 : ℝ) * ((1 / 2 : ℝ) ^ k) * (k.factorial : ℝ)
        = (2 * (k.factorial : ℝ)) / (2 : ℝ) ^ k := by
      rw [div_pow, one_pow]; ring
    rw [e, le_div_iff₀ h2k, one_mul]
    exact hfact
  rw [div_le_iff₀ hpos]
  calc (k : ℝ) ^ m = 1 * (k : ℝ) ^ m := (one_mul _).symm
    _ ≤ (2 * ((1 / 2 : ℝ) ^ k) * (k.factorial : ℝ)) * (k : ℝ) ^ m :=
      mul_le_mul_of_nonneg_right h1 hnn
    _ = 2 * ((k : ℝ) ^ m * ((1 / 2 : ℝ) ^ k)) * (k.factorial : ℝ) := by ring

/-- Dobiński sum: `∑' k, k ^ m / k !`. -/
private noncomputable def dobinskiSum (m : ℕ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) ^ m / (k.factorial : ℝ)

private lemma dobinski_zero : dobinskiSum 0 = Real.exp 1 * (Nat.bell 0 : ℝ) := by
  have hexp := NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)
  rw [Real.exp_eq_exp_ℝ]
  simp only [Nat.bell_zero, Nat.cast_one, mul_one]
  rw [← hexp.tsum_eq]
  unfold dobinskiSum
  apply tsum_congr
  intro k
  simp


private lemma dobinski_shift (m : ℕ) :
    dobinskiSum (m + 1) = ∑' k : ℕ, (((k : ℝ) + 1) ^ m / (k.factorial : ℝ)) := by
  have hS := summable_pow_div_factorial_real (m + 1)
  have h0 : ((0 : ℕ) : ℝ) ^ (m + 1) / ((((0).factorial : ℕ)) : ℝ) = 0 := by simp
  have hshift := hS.tsum_eq_zero_add
  unfold dobinskiSum
  rw [hshift, h0, zero_add]
  apply tsum_congr
  intro k
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk1c : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hfact : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  change ((k + 1 : ℕ) : ℝ) ^ (m + 1) / ((((k + 1).factorial : ℕ)) : ℝ)
    = ((k : ℝ) + 1) ^ m / (k.factorial : ℝ)
  rw [hk1c, Nat.factorial_succ]
  push_cast
  rw [pow_succ]
  field_simp

private lemma dobinski_recurrence (m : ℕ) :
    dobinskiSum (m + 1)
      = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * dobinskiSum (m - i) := by
  rw [dobinski_shift m]
  have hexpand : ∀ k : ℕ, (((k : ℝ) + 1) ^ m / (k.factorial : ℝ))
      = ∑ i ∈ Finset.range (m + 1),
        ((k : ℝ) ^ (m - i) * (m.choose i : ℝ) / (k.factorial : ℝ)) := by
    intro k
    have h := add_pow (1 : ℝ) (k : ℝ) m
    rw [add_comm (1 : ℝ) (k : ℝ)] at h
    rw [h]
    simp only [div_eq_mul_inv, ← Finset.sum_mul, one_pow, one_mul]
  rw [tsum_congr hexpand]
  have hswap : (∑' k : ℕ, ∑ i ∈ Finset.range (m + 1),
        ((k : ℝ) ^ (m - i) * (m.choose i : ℝ) / (k.factorial : ℝ)))
      = ∑ i ∈ Finset.range (m + 1), ∑' k : ℕ,
        ((k : ℝ) ^ (m - i) * (m.choose i : ℝ) / (k.factorial : ℝ)) := by
    refine Summable.tsum_finsetSum (fun i hi => ?_)
    have hiS := summable_pow_div_factorial_real (m - i)
    have e : (fun k : ℕ => (k : ℝ) ^ (m - i) * (m.choose i : ℝ) / (k.factorial : ℝ))
        = (fun k : ℕ => ((k : ℝ) ^ (m - i) / (k.factorial : ℝ)) * (m.choose i : ℝ)) := by
      funext k; ring
    rw [e]
    exact hiS.mul_right _
  rw [hswap]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiS := summable_pow_div_factorial_real (m - i)
  have e : (fun k : ℕ => (k : ℝ) ^ (m - i) * (m.choose i : ℝ) / (k.factorial : ℝ))
      = (fun k : ℕ => (m.choose i : ℝ) * ((k : ℝ) ^ (m - i) / (k.factorial : ℝ))) := by
    funext k; ring
  rw [e, tsum_mul_left]
  rfl

private lemma dobinski_aux : ∀ m : ℕ, ∀ j ≤ m,
    dobinskiSum j = Real.exp 1 * (Nat.bell j : ℝ) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    interval_cases j
    exact dobinski_zero
  | succ m ihm =>
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact dobinski_zero
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hkm : k ≤ m := by omega
      rw [dobinski_recurrence k]
      have hbell : ((Nat.bell (k + 1) : ℕ) : ℝ)
          = ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ((Nat.bell (k - i) : ℕ) : ℝ) := by
        rw [Nat.bell_succ k, ← Nat.range_succ_eq_Iic]
        push_cast
        rfl
      rw [hbell, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hki : k - i ≤ m := by
        have := Finset.mem_range_succ_iff.mp hi
        omega
      rw [ihm (k - i) hki]
      ring

/-- Dobinski formula. -/
private lemma dobinski (m : ℕ) : dobinskiSum m = Real.exp 1 * (Nat.bell m : ℝ) :=
  dobinski_aux m m le_rfl

/-- summand of the regrouped double sum, in the exact shape of the goal. -/
private noncomputable def fiberTerm (m s k : ℕ) : ℝ :=
  (((k : ℝ) ^ (m + 1) * ((s - k : ℕ) : ℝ) ^ (m + 1))
    / ((Nat.factorial k : ℝ) * (Nat.factorial (s - k) : ℝ)))
    * (((s : ℝ) - 2 * (k : ℝ)) ^ 2)

private lemma fiber_swap (m s : ℕ) :
    (∑ k ∈ Finset.range (s + 1),
      ((k : ℝ) ^ (m + 3) * ((s - k : ℕ) : ℝ) ^ (m + 1)
        / ((k.factorial : ℝ) * ((s - k).factorial : ℝ))))
    = (∑ k ∈ Finset.range (s + 1),
      ((k : ℝ) ^ (m + 1) * ((s - k : ℕ) : ℝ) ^ (m + 3)
        / ((k.factorial : ℝ) * ((s - k).factorial : ℝ)))) := by
  rw [← Finset.sum_range_reflect
    (fun j => ((j : ℝ) ^ (m + 3) * ((s - j : ℕ) : ℝ) ^ (m + 1)
      / ((j.factorial : ℝ) * ((s - j).factorial : ℝ)))) (s + 1)]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hss : s - (s - k) = k := by
    have hks : k ≤ s := by
      have := Finset.mem_range_succ_iff.mp hk
      omega
    omega
  rw [hss]
  ring

private lemma fiber_identity (m s k : ℕ) (hks : k ≤ s) :
    ((k : ℝ) ^ (m + 1) * ((s - k : ℕ) : ℝ) ^ (m + 3)
      / ((k.factorial : ℝ) * ((s - k).factorial : ℝ)))
    + ((k : ℝ) ^ (m + 3) * ((s - k : ℕ) : ℝ) ^ (m + 1)
      / ((k.factorial : ℝ) * ((s - k).factorial : ℝ)))
    - 2 * ((k : ℝ) ^ (m + 2) * ((s - k : ℕ) : ℝ) ^ (m + 2)
      / ((k.factorial : ℝ) * ((s - k).factorial : ℝ)))
    = fiberTerm m s k := by
  have hcast : ((s - k : ℕ) : ℝ) = (s : ℝ) - (k : ℝ) := Nat.cast_sub hks
  have e1 : (k : ℝ) ^ (m + 3) = (k : ℝ) ^ (m + 1) * (k : ℝ) ^ 2 :=
    pow_add _ (m + 1) 2
  have e2 : ((s - k : ℕ) : ℝ) ^ (m + 3)
      = ((s - k : ℕ) : ℝ) ^ (m + 1) * ((s - k : ℕ) : ℝ) ^ 2 :=
    pow_add _ (m + 1) 2
  have e3 : (k : ℝ) ^ (m + 2) = (k : ℝ) ^ (m + 1) * (k : ℝ) :=
    pow_succ _ (m + 1)
  have e4 : ((s - k : ℕ) : ℝ) ^ (m + 2)
      = ((s - k : ℕ) : ℝ) ^ (m + 1) * ((s - k : ℕ) : ℝ) :=
    pow_succ _ (m + 1)
  have hD : ((k.factorial : ℝ) * ((s - k).factorial : ℝ)) ≠ 0 := by positivity
  unfold fiberTerm
  rw [e1, e2, e3, e4, hcast]
  field_simp
  ring

private lemma fiber_sum_eq (m s : ℕ) :
    (∑ k ∈ Finset.range (s + 1),
      ((k : ℝ) ^ (m + 1) * ((s - k : ℕ) : ℝ) ^ (m + 3)
        / ((k.factorial : ℝ) * ((s - k).factorial : ℝ))))
    - (∑ k ∈ Finset.range (s + 1),
      ((k : ℝ) ^ (m + 2) * ((s - k : ℕ) : ℝ) ^ (m + 2)
        / ((k.factorial : ℝ) * ((s - k).factorial : ℝ))))
    = (1 / 2) * (∑ k ∈ Finset.range (s + 1), fiberTerm m s k) := by
  have hswap := fiber_swap m s
  have hid : ∀ k ∈ Finset.range (s + 1),
      (((k : ℝ) ^ (m + 1) * ((s - k : ℕ) : ℝ) ^ (m + 3)
        / ((k.factorial : ℝ) * ((s - k).factorial : ℝ)))
      + ((k : ℝ) ^ (m + 3) * ((s - k : ℕ) : ℝ) ^ (m + 1)
        / ((k.factorial : ℝ) * ((s - k).factorial : ℝ)))
      - 2 * ((k : ℝ) ^ (m + 2) * ((s - k : ℕ) : ℝ) ^ (m + 2)
        / ((k.factorial : ℝ) * ((s - k).factorial : ℝ))))
      = fiberTerm m s k := by
    intro k hk
    have hks : k ≤ s := by
      have := Finset.mem_range_succ_iff.mp hk
      omega
    exact fiber_identity m s k hks
  have hsum := Finset.sum_congr rfl hid
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hswap] at hsum
  linear_combination hsum / 2

private lemma fiberTerm_eq_zero (m s k : ℕ) (h : k = 0 ∨ k = s) :
    fiberTerm m s k = 0 := by
  have hpow : (k : ℝ) ^ (m + 1) * ((s - k : ℕ) : ℝ) ^ (m + 1) = 0 := by
    rcases h with rfl | rfl
    · rw [Nat.cast_zero, zero_pow (by omega : m + 1 ≠ 0)]
      exact zero_mul _
    · rw [Nat.sub_self, Nat.cast_zero, zero_pow (by omega : m + 1 ≠ 0)]
      exact mul_zero _
  unfold fiberTerm
  rw [hpow, zero_div, zero_mul]

private lemma fiberTerm_Icc_eq_zero (m s : ℕ) (hs : s < 2) :
    (∑ j ∈ Finset.Icc 1 (s - 1), fiberTerm m s j) = 0 := by
  have hempty : Finset.Icc 1 (s - 1) = ∅ := by
    interval_cases s <;> decide
  rw [hempty, Finset.sum_empty]

private lemma fiber_eq_Icc (m s : ℕ) (hs : 2 ≤ s) :
    (∑ k ∈ Finset.range (s + 1), fiberTerm m s k)
    = ∑ j ∈ Finset.Icc 1 (s - 1), fiberTerm m s j := by
  symm
  refine Finset.sum_subset (fun k hk => ?_) (fun k hk hkn => ?_)
  · simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    omega
  · simp only [Finset.mem_Icc, not_and, not_le] at hkn
    have hks : k ≤ s := by
      have := Finset.mem_range_succ_iff.mp hk
      omega
    apply fiberTerm_eq_zero m s k
    by_cases h1 : k < 1
    · left; omega
    · right
      have := hkn (by omega : 1 ≤ k)
      omega

private lemma fiber_main (m s : ℕ) :
    (∑ k ∈ Finset.range (s + 1),
      (((k : ℝ) ^ (m + 1) / (k.factorial : ℝ))
        * (((s - k : ℕ) : ℝ) ^ (m + 3) / ((s - k).factorial : ℝ))))
    - (∑ k ∈ Finset.range (s + 1),
      (((k : ℝ) ^ (m + 2) / (k.factorial : ℝ))
        * (((s - k : ℕ) : ℝ) ^ (m + 2) / ((s - k).factorial : ℝ))))
    = (1 / 2) * (∑ k ∈ Finset.range (s + 1), fiberTerm m s k) := by
  simp only [div_mul_div_comm]
  exact fiber_sum_eq m s

/--
**Turán-type identity for the Bell numbers.** For every natural number $n \ge 2$, the Bell
numbers $B_m$ satisfy

$$B_{n-1} B_{n+1} - B_n^2 = \frac{1}{2e^2} \sum_{k=2}^{\infty} \sum_{j=1}^{k-1}
\frac{j^{n-1} (k-j)^{n-1}}{j! \, (k-j)!} \, (k-2j)^2,$$

where $e = \exp(1)$.

Every summand is nonnegative and the summand with $k = 3$, $j = 1$ is positive, so the identity
refines Engel's inequality $B_n^2 \le B_{n-1} B_{n+1}$ to a strict inequality.

Proves `Wanted` entry `bell_turan_identity`.

Source: Horst Alzer, "On Engel's Inequality for Bell Numbers,"
Journal of Integer Sequences 22 (2019), Article 19.7.1,
Theorem with Equation (E3), lines 114–120,
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Alzer/alzer6.tex>.
-/
theorem bell_turan_identity
    (n : ℕ) (hn : 2 ≤ n) :
    (Nat.bell (n - 1) : ℝ) * (Nat.bell (n + 1) : ℝ) -
        (Nat.bell n : ℝ) ^ 2 =
      (1 / (2 * Real.exp 1 ^ 2)) *
        ∑' k : {k : ℕ // 2 ≤ k},
          ∑ j ∈ Finset.Icc 1 (k.1 - 1),
            (((j : ℝ) ^ (n - 1) * ((k.1 - j : ℕ) : ℝ) ^ (n - 1)) /
                ((Nat.factorial j : ℝ) * (Nat.factorial (k.1 - j) : ℝ))) *
              ((k.1 : ℝ) - 2 * (j : ℝ)) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 + 1 = m + 3 by omega]
  have he0 : (Real.exp 1 : ℝ) ≠ 0 := Real.exp_ne_zero 1
  have hS1 := summable_pow_div_factorial_real (m + 1)
  have hS2 := summable_pow_div_factorial_real (m + 2)
  have hS3 := summable_pow_div_factorial_real (m + 3)
  have hnn : ∀ a : ℕ, 0 ≤ (fun k : ℕ => (k : ℝ) ^ a / (k.factorial : ℝ)) :=
    fun a k => by positivity
  have hprod13 := hS1.mul_of_nonneg hS3 (hnn _) (hnn _)
  have hprod22 := hS2.mul_of_nonneg hS2 (hnn _) (hnn _)
  have d1 := dobinski (m + 1)
  have d2 := dobinski (m + 2)
  have d3 := dobinski (m + 3)
  have b1 : (Nat.bell (m + 1) : ℝ) = dobinskiSum (m + 1) / Real.exp 1 := by
    rw [d1, mul_div_cancel_left₀ _ he0]
  have b2 : (Nat.bell (m + 2) : ℝ) = dobinskiSum (m + 2) / Real.exp 1 := by
    rw [d2, mul_div_cancel_left₀ _ he0]
  have b3 : (Nat.bell (m + 3) : ℝ) = dobinskiSum (m + 3) / Real.exp 1 := by
    rw [d3, mul_div_cancel_left₀ _ he0]
  have hval : dobinskiSum (m + 1) * dobinskiSum (m + 3) - dobinskiSum (m + 2) ^ 2
      = (1 / 2) * ∑' s : ℕ, (∑ k ∈ Finset.range (s + 1), fiberTerm m s k) := by
    have e1 := hS1.tsum_mul_tsum_eq_tsum_sum_range hS3 hprod13
    have e2 := hS2.tsum_mul_tsum_eq_tsum_sum_range hS2 hprod22
    have hAsum : Summable (fun s : ℕ => ∑ k ∈ Finset.range (s + 1),
        (((k : ℝ) ^ (m + 1) / (k.factorial : ℝ))
          * (((s - k : ℕ) : ℝ) ^ (m + 3) / ((s - k).factorial : ℝ)))) :=
      summable_sum_mul_range_of_summable_mul
        (f := fun k : ℕ => (k : ℝ) ^ (m + 1) / (k.factorial : ℝ))
        (g := fun k : ℕ => (k : ℝ) ^ (m + 3) / (k.factorial : ℝ))
        hprod13
    have hBsum : Summable (fun s : ℕ => ∑ k ∈ Finset.range (s + 1),
        (((k : ℝ) ^ (m + 2) / (k.factorial : ℝ))
          * (((s - k : ℕ) : ℝ) ^ (m + 2) / ((s - k).factorial : ℝ)))) :=
      summable_sum_mul_range_of_summable_mul
        (f := fun k : ℕ => (k : ℝ) ^ (m + 2) / (k.factorial : ℝ))
        (g := fun k : ℕ => (k : ℝ) ^ (m + 2) / (k.factorial : ℝ))
        hprod22
    have e1' : dobinskiSum (m + 1) * dobinskiSum (m + 3)
        = ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1),
          (((k : ℝ) ^ (m + 1) / (k.factorial : ℝ))
            * (((n - k : ℕ) : ℝ) ^ (m + 3) / ((n - k).factorial : ℝ))) := e1
    have e2' : dobinskiSum (m + 2) * dobinskiSum (m + 2)
        = ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1),
          (((k : ℝ) ^ (m + 2) / (k.factorial : ℝ))
            * (((n - k : ℕ) : ℝ) ^ (m + 2) / ((n - k).factorial : ℝ))) := e2
    rw [e1', pow_two, e2', (hAsum.tsum_sub hBsum).symm, ← tsum_mul_left]
    exact tsum_congr (fun s => fiber_main m s)
  have hbridge : (∑' s : ℕ, ∑ k ∈ Finset.range (s + 1), fiberTerm m s k)
      = ∑' st : {s : ℕ // 2 ≤ s},
        ∑ j ∈ Finset.Icc 1 (st.1 - 1), fiberTerm m st.1 j := by
    have hper : ∀ s : ℕ, (∑ k ∈ Finset.range (s + 1), fiberTerm m s k)
        = ∑ j ∈ Finset.Icc 1 (s - 1), fiberTerm m s j := by
      intro s
      rcases lt_or_ge s 2 with hs | hs
      · have hr : (∑ k ∈ Finset.range (s + 1), fiberTerm m s k) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hks : k ≤ s := by
            have := Finset.mem_range_succ_iff.mp hk
            omega
          apply fiberTerm_eq_zero m s k
          omega
        rw [hr, fiberTerm_Icc_eq_zero m s hs]
      · exact fiber_eq_Icc m s hs
    rw [tsum_congr hper]
    have hsupp : Function.support
        (fun s : ℕ => ∑ j ∈ Finset.Icc 1 (s - 1), fiberTerm m s j)
        ⊆ {s : ℕ | 2 ≤ s} := by
      rw [Function.support_subset_iff]
      intro s hs
      change 2 ≤ s
      by_contra hcon
      exact hs (fiberTerm_Icc_eq_zero m s (lt_of_not_ge hcon))
    have hsub := tsum_subtype_eq_of_support_subset
      (f := fun s : ℕ => ∑ j ∈ Finset.Icc 1 (s - 1), fiberTerm m s j)
      (s := {s : ℕ | 2 ≤ s}) hsupp
    exact hsub.symm
  have hLHS : (dobinskiSum (m + 1) / Real.exp 1) * (dobinskiSum (m + 3) / Real.exp 1)
      - (dobinskiSum (m + 2) / Real.exp 1) ^ 2
      = (dobinskiSum (m + 1) * dobinskiSum (m + 3) - dobinskiSum (m + 2) ^ 2)
        / Real.exp 1 ^ 2 := by
    rw [div_mul_div_comm, div_pow, ← pow_two, ← sub_div]
  rw [b1, b3, b2, hLHS, hval, hbridge]
  simp only [fiberTerm]
  ring

end MetaMathlibExt
