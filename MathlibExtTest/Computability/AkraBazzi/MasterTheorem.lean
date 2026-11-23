/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Computability.AkraBazzi.MasterTheorem

/-!
# Master theorem consumers and boundary checks

Every positive example below constructs a cost by well-founded recursion and
proves the hypotheses of the public floor/ceiling adapter. None assumes an
Akra–Bazzi witness or an asymptotic bound on the cost. This module imports only
the public production interface, not the private power-sum proof helpers.
-/

open Filter Asymptotics Finset Real AkraBazziRecurrence
open scoped Topology

namespace MasterTheoremTest

private noncomputable def recurrenceCost (a : ℝ) (g : ℝ → ℝ) (r : ℕ → ℕ)
    (N : ℕ) (shrink : ∀ n, N ≤ n → r n < n) (n : ℕ) : ℝ :=
  if _hn : n < N then 1 else a * recurrenceCost a g r N shrink (r n) + g n
termination_by n
decreasing_by
  apply shrink
  omega

private lemma recurrenceCost_base (a : ℝ) (g : ℝ → ℝ) (r : ℕ → ℕ)
    (N : ℕ) (shrink : ∀ n, N ≤ n → r n < n) (n : ℕ) (hn : n < N) :
    recurrenceCost a g r N shrink n = 1 := by
  rw [recurrenceCost, dite_eq_left hn]

private lemma recurrenceCost_step (a : ℝ) (g : ℝ → ℝ) (r : ℕ → ℕ)
    (N : ℕ) (shrink : ∀ n, N ≤ n → r n < n) (n : ℕ) (hn : N ≤ n) :
    recurrenceCost a g r N shrink n = a * recurrenceCost a g r N shrink (r n) + g n := by
  rw [recurrenceCost, dite_eq_right (not_lt_of_ge hn)]

private lemma floor_shrink {b : ℝ} (hb : 1 < b) (n : ℕ) (hn : 1 ≤ n) :
    ⌊(n : ℝ) / b⌋₊ < n := by
  apply (Nat.floor_lt (div_nonneg (Nat.cast_nonneg n) (by linarith))).2
  exact div_lt_self (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)) hb

private lemma ceil_shrink {b : ℝ} {N : ℕ} (hb : 1 < b) (hN : 0 < N)
    (hcut : b / (b - 1) ≤ (N : ℝ)) (n : ℕ) (hn : N ≤ n) :
    ⌈(n : ℝ) / b⌉₊ < n := by
  have hnpos := hN.trans_le hn
  have hbn : b ≤ (n : ℝ) * (b - 1) :=
    (div_le_iff₀ (by linarith : 0 < b - 1)).1 (hcut.trans (by exact_mod_cast hn))
  have hchild : ⌈(n : ℝ) / b⌉₊ ≤ n - 1 := by
    rw [Nat.ceil_le, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hnpos.ne'), Nat.cast_one]
    apply (div_le_iff₀ (by linarith : 0 < b)).2
    nlinarith
  exact hchild.trans_lt (Nat.sub_lt hnpos (by decide))

private noncomputable def floorCost (a b : ℝ) (g : ℝ → ℝ) (hb : 1 < b) : ℕ → ℝ :=
  recurrenceCost a g (fun n => ⌊(n : ℝ) / b⌋₊) 1 (floor_shrink hb)

private noncomputable def ceilCost (a b : ℝ) (g : ℝ → ℝ) (N : ℕ)
    (hb : 1 < b) (hN : 0 < N) (hcut : b / (b - 1) ≤ (N : ℝ)) : ℕ → ℝ :=
  recurrenceCost a g (fun n => ⌈(n : ℝ) / b⌉₊) N (ceil_shrink hb hN hcut)

private noncomputable def floorRecurrence {a b c : ℝ} {g : ℝ → ℝ}
    (ha : 0 < a) (hb : 1 < b) (hg0 : ∀ x ≥ 0, 0 ≤ g x)
    (hg : g =Θ[atTop] (fun x : ℝ => x ^ c)) :
    AkraBazziRecurrence (floorCost a b g hb) g
      (fun _ : Unit => a) (fun _ => b⁻¹) (fun _ n => ⌊(n : ℝ) / b⌋₊) := by
  apply ofFloor 1 ha hb (by decide) hg0 hg
  · intro n hn
    change 0 < recurrenceCost a g _ 1 _ n
    rw [recurrenceCost_base a g _ 1 _ n hn]
    norm_num
  · intro n hn
    exact recurrenceCost_step a g _ 1 _ n hn

private noncomputable def ceilRecurrence {a b c : ℝ} {g : ℝ → ℝ} (N : ℕ)
    (ha : 0 < a) (hb : 1 < b) (hN : 0 < N) (hcut : b / (b - 1) ≤ (N : ℝ))
    (hg0 : ∀ x ≥ 0, 0 ≤ g x) (hg : g =Θ[atTop] (fun x : ℝ => x ^ c)) :
    AkraBazziRecurrence (ceilCost a b g N hb hN hcut) g
      (fun _ : Unit => a) (fun _ => b⁻¹) (fun _ n => ⌈(n : ℝ) / b⌉₊) := by
  apply ofCeil N ha hb hN hcut hg0 hg
  · intro n hn
    change 0 < recurrenceCost a g _ N _ n
    rw [recurrenceCost_base a g _ N _ n hn]
    norm_num
  · intro n hn
    exact recurrenceCost_step a g _ N _ n hn

private lemma two_gt_one : (1 : ℝ) < 2 := by norm_num

private lemma theta_one : (fun _ : ℝ => (1 : ℝ)) =Θ[atTop] (fun x : ℝ => x ^ (0 : ℝ)) := by
  simp only [rpow_zero]
  exact isTheta_rfl

private lemma theta_id : (fun x : ℝ => x) =Θ[atTop] (fun x : ℝ => x ^ (1 : ℝ)) := by
  simp only [rpow_one]
  exact isTheta_rfl

private lemma theta_square : (fun x : ℝ => x ^ 2) =Θ[atTop] (fun x : ℝ => x ^ (2 : ℝ)) := by
  simp only [rpow_two]
  exact isTheta_rfl

private lemma logb_two_two : logb 2 2 = 1 := logb_self_eq_one two_gt_one

private lemma logb_two_four : logb 2 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, logb_pow, logb_two_two]
  norm_num

/-! The three cases, with both rounding choices. -/

private theorem floor_recursive :
    floorCost 2 2 (fun _ => 1) two_gt_one =Θ[atTop] (fun n : ℕ => (n : ℝ)) := by
  have R := floorRecurrence (a := 2) (by norm_num) two_gt_one (fun _ _ => by norm_num) theta_one
  simpa only [logb_two_two, rpow_one] using
    R.master_lt two_gt_one (by norm_num) theta_one (by rw [logb_two_two]; norm_num)

private theorem ceil_recursive :
    ceilCost 2 2 (fun _ => 1) 2 two_gt_one (by decide) (by norm_num) =Θ[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  have R := ceilRecurrence (a := 2) 2 (by norm_num) two_gt_one (by decide) (by norm_num)
    (fun _ _ => by norm_num) theta_one
  simpa only [logb_two_two, rpow_one] using
    R.master_lt two_gt_one (by norm_num) theta_one (by rw [logb_two_two]; norm_num)

private theorem floor_critical :
    floorCost 2 2 (fun x => x) two_gt_one =Θ[atTop] (fun n : ℕ => (n : ℝ) * log n) := by
  have R := floorRecurrence (a := 2) (by norm_num) two_gt_one (fun _ hx => hx) theta_id
  simpa only [rpow_one] using
    R.master_eq two_gt_one (by norm_num) theta_id logb_two_two.symm

private theorem ceil_critical :
    ceilCost 2 2 (fun x => x) 2 two_gt_one (by decide) (by norm_num) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) * log n) := by
  have R := ceilRecurrence (a := 2) 2 (by norm_num) two_gt_one (by decide) (by norm_num)
    (fun _ hx => hx) theta_id
  simpa only [rpow_one] using R.master_eq two_gt_one (by norm_num) theta_id logb_two_two.symm

private theorem floor_toll_dominant :
    floorCost 2 2 (fun x => x ^ 2) two_gt_one =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 2) := by
  have R := floorRecurrence (a := 2) (by norm_num) two_gt_one (fun x _ => sq_nonneg x) theta_square
  simpa only [rpow_two] using
    R.master_gt two_gt_one (by norm_num) theta_square (by rw [logb_two_two]; norm_num)

private theorem ceil_toll_dominant :
    ceilCost 2 2 (fun x => x ^ 2) 2 two_gt_one (by decide) (by norm_num) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2) := by
  have R := ceilRecurrence (a := 2) 2 (by norm_num) two_gt_one (by decide) (by norm_num)
    (fun x _ => sq_nonneg x) theta_square
  simpa only [rpow_two] using
    R.master_gt two_gt_one (by norm_num) theta_square (by rw [logb_two_two]; norm_num)

private theorem critical_zero_exponent :
    floorCost 1 2 (fun _ => 1) two_gt_one =Θ[atTop] (fun n : ℕ => log n) := by
  have R := floorRecurrence (a := 1) (by norm_num) two_gt_one (fun _ _ => by norm_num) theta_one
  simpa only [rpow_zero, one_mul] using R.master_eq two_gt_one (by norm_num) theta_one (by simp)

private theorem critical_square :
    ceilCost 4 2 (fun x => x ^ 2) 2 two_gt_one (by decide) (by norm_num) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2 * log n) := by
  have R := ceilRecurrence (a := 4) 2 (by norm_num) two_gt_one (by decide) (by norm_num)
    (fun x _ => sq_nonneg x) theta_square
  simpa only [rpow_two] using R.master_eq two_gt_one (by norm_num) theta_square logb_two_four.symm

private theorem noninteger_exponent :
    ceilCost 3 2 (fun x => x) 2 two_gt_one (by decide) (by norm_num) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ logb 2 3) := by
  have R := ceilRecurrence (a := 3) 2 (by norm_num) two_gt_one (by decide) (by norm_num)
    (fun _ hx => hx) theta_id
  apply R.master_lt two_gt_one (by norm_num) theta_id
  rw [lt_logb_iff_rpow_lt two_gt_one (by norm_num : (0 : ℝ) < 3), rpow_one]
  norm_num

private theorem weighted_coefficient :
    floorCost (1 / 2) 2 (fun _ => 1) two_gt_one =Θ[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  have R := floorRecurrence (a := 1 / 2) (by norm_num) two_gt_one (fun _ _ => by norm_num) theta_one
  simpa only [rpow_zero] using R.master_gt two_gt_one (by norm_num) theta_one
    (logb_neg two_gt_one (by norm_num) (by norm_num))

private theorem sharp_ceiling_cutoff :
    ceilCost 2 (11 / 10) (fun _ => 1) 11 (by norm_num) (by decide) (by norm_num) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ logb (11 / 10) 2) := by
  have R := ceilRecurrence (a := 2) (b := 11 / 10) 11 (by norm_num) (by norm_num)
    (by decide) (by norm_num) (fun _ _ => by norm_num) theta_one
  exact R.master_lt (by norm_num) (by norm_num) theta_one (logb_pos (by norm_num) (by norm_num))

private lemma ceil_ten_div_eleven_tenths : ⌈(10 : ℝ) / (11 / 10)⌉₊ = 10 := by
  apply le_antisymm
  · apply Nat.ceil_le.2
    norm_num
  · have h : 9 < ⌈(10 : ℝ) / (11 / 10)⌉₊ := Nat.lt_ceil.2 (by norm_num)
    exact Nat.succ_le_of_lt h
private lemma ceil_predecessor_not_shrinking : ¬⌈(10 : ℝ) / (11 / 10)⌉₊ < 10 := by
  rw [ceil_ten_div_eleven_tenths]
  omega
private lemma ceil_at_sharp_cutoff : ⌈(11 : ℝ) / (11 / 10)⌉₊ = 10 := by norm_num

/-! Finite-prefix freedom and lack of toll monotonicity. -/

private noncomputable def prefixToll (x : ℝ) : ℝ := if x < 7 then 0 else x

private lemma prefixToll_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ prefixToll x := by
  unfold prefixToll
  split_ifs <;> positivity

private lemma prefixToll_theta : prefixToll =Θ[atTop] (fun x : ℝ => x ^ (1 : ℝ)) := by
  apply EventuallyEq.trans_isTheta _ theta_id
  filter_upwards [eventually_ge_atTop 7] with x hx
  simp only [prefixToll, not_lt_of_ge hx, ite_false]

private theorem finite_prefix_toll :
    floorCost 2 2 prefixToll two_gt_one =Θ[atTop] (fun n : ℕ => (n : ℝ) * log n) := by
  have R := floorRecurrence (a := 2) (by norm_num) two_gt_one prefixToll_nonneg prefixToll_theta
  simpa only [rpow_one] using R.master_eq two_gt_one (by norm_num) prefixToll_theta logb_two_two.symm

private noncomputable def oscillatingToll (x : ℝ) : ℝ :=
  if x < 1 then 0 else if Even ⌊logb 2 x⌋₊ then x ^ 2 else 16 * x ^ 2

private lemma oscillatingToll_nonneg (x : ℝ) (_hx : 0 ≤ x) : 0 ≤ oscillatingToll x := by
  unfold oscillatingToll
  split_ifs <;> positivity

private lemma oscillatingToll_bounds {x : ℝ} (hx : 1 ≤ x) :
    x ^ 2 ≤ oscillatingToll x ∧ oscillatingToll x ≤ 16 * x ^ 2 := by
  unfold oscillatingToll
  rw [ite_eq_right (not_lt_of_ge hx)]
  split_ifs <;> constructor <;> nlinarith [sq_nonneg x]

private lemma oscillatingToll_theta :
    oscillatingToll =Θ[atTop] (fun x : ℝ => x ^ (2 : ℝ)) := by
  constructor
  · refine IsBigO.of_bound 16 ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    simpa only [rpow_two, Real.norm_of_nonneg (sq_nonneg x),
      Real.norm_of_nonneg (oscillatingToll_nonneg x (by linarith))] using (oscillatingToll_bounds hx).2
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    simpa only [rpow_two, one_mul, Real.norm_of_nonneg (sq_nonneg x),
      Real.norm_of_nonneg (oscillatingToll_nonneg x (by linarith))] using (oscillatingToll_bounds hx).1

private theorem nonmonotone_toll :
    ceilCost 2 2 oscillatingToll 2 two_gt_one (by decide) (by norm_num) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2) := by
  have R := ceilRecurrence (a := 2) 2 (by norm_num) two_gt_one (by decide) (by norm_num)
    oscillatingToll_nonneg oscillatingToll_theta
  simpa only [rpow_two] using R.master_gt two_gt_one (by norm_num) oscillatingToll_theta
    (by rw [logb_two_two]; norm_num)

private lemma oscillatingToll_eight : oscillatingToll 8 = 1024 := by
  have h : logb 2 8 = 3 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, logb_pow, logb_two_two]
    norm_num
  have ho : ¬Even (3 : ℕ) := by decide
  norm_num [oscillatingToll, h, ho]

private lemma oscillatingToll_sixteen : oscillatingToll 16 = 256 := by
  have h : logb 2 16 = 4 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, logb_pow, logb_two_two]
    norm_num
  have he : Even (4 : ℕ) := by decide
  norm_num [oscillatingToll, h, he]

private lemma oscillatingToll_not_monotone : ¬Monotone oscillatingToll := by
  intro h
  have := h (by norm_num : (8 : ℝ) ≤ 16)
  rw [oscillatingToll_eight, oscillatingToll_sixteen] at this
  norm_num at this

private lemma oscillatingToll_regularity_counterexample :
    2 * oscillatingToll (16 / 2) = 8 * oscillatingToll 16 := by
  norm_num only [show (16 / 2 : ℝ) = 8 by norm_num, oscillatingToll_eight, oscillatingToll_sixteen]

/-! Positive recurrences exercising normalized exponents -1/2 and 2.
The other cases above exercise -2, -1, and 0. -/

private theorem fractional_power_sum_regime :
    floorCost 2 2 (fun x => x ^ (3 / 2 : ℝ)) two_gt_one =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  have hg : (fun x : ℝ => x ^ (3 / 2 : ℝ)) =Θ[atTop] (fun x : ℝ => x ^ (3 / 2 : ℝ)) := isTheta_rfl
  have R := floorRecurrence (a := 2) (by norm_num) two_gt_one
    (fun x hx => rpow_nonneg hx _) hg
  exact R.master_gt two_gt_one (by norm_num) hg (by rw [logb_two_two]; norm_num)

private theorem positive_power_sum_regime :
    floorCost 2 2 (fun x => x ^ (4 : ℝ)) two_gt_one =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (4 : ℝ)) := by
  have hg : (fun x : ℝ => x ^ (4 : ℝ)) =Θ[atTop] (fun x : ℝ => x ^ (4 : ℝ)) := isTheta_rfl
  have R := floorRecurrence (a := 2) (by norm_num) two_gt_one
    (fun x hx => rpow_nonneg hx _) hg
  exact R.master_gt two_gt_one (by norm_num) hg (by rw [logb_two_two]; norm_num)

private lemma power_sum_zero (q : ℝ) : 1 + ∑ i ∈ range 0, (i : ℝ) ^ q = 1 := by simp
private lemma power_sum_one_neg_two : 1 + ∑ i ∈ range 1, (i : ℝ) ^ (-2 : ℝ) = 1 := by norm_num
private lemma power_sum_one_neg_one : 1 + ∑ i ∈ range 1, (i : ℝ) ^ (-1 : ℝ) = 1 := by norm_num
private lemma power_sum_one_neg_half : 1 + ∑ i ∈ range 1, (i : ℝ) ^ (-1 / 2 : ℝ) = 1 := by norm_num
private lemma power_sum_one_zero : 1 + ∑ i ∈ range 1, (i : ℝ) ^ (0 : ℝ) = 2 := by norm_num
private lemma power_sum_one_two : 1 + ∑ i ∈ range 1, (i : ℝ) ^ (2 : ℝ) = 1 := by norm_num
private lemma power_sum_two_neg_two : 1 + ∑ i ∈ range 2, (i : ℝ) ^ (-2 : ℝ) = 2 := by
  norm_num [sum_range_succ]
private lemma power_sum_two_neg_one : 1 + ∑ i ∈ range 2, (i : ℝ) ^ (-1 : ℝ) = 2 := by
  norm_num [sum_range_succ]
private lemma power_sum_two_neg_half : 1 + ∑ i ∈ range 2, (i : ℝ) ^ (-1 / 2 : ℝ) = 2 := by
  norm_num [sum_range_succ]
private lemma power_sum_two_zero : 1 + ∑ i ∈ range 2, (i : ℝ) ^ (0 : ℝ) = 3 := by
  norm_num [sum_range_succ]
private lemma power_sum_two_two : 1 + ∑ i ∈ range 2, (i : ℝ) ^ (2 : ℝ) = 2 := by
  norm_num [sum_range_succ]

-- At p=-1 the zero-index denominator is 0^0=1, not zero.
private lemma normalized_toll_zero_negative_exponent : (1 : ℝ) / (0 : ℝ) ^ ((-1 : ℝ) + 1) = 1 := by norm_num
private lemma normalized_toll_zero_positive_exponent : (1 : ℝ) / (0 : ℝ) ^ ((1 : ℝ) + 1) = 0 := by norm_num
private lemma critical_comparison_at_one : log (1 : ℝ) = 0 := by simp

/-! Rejection checks and actual countermodels to omitted hypotheses. -/

private lemma not_constant_theta_of_tendsto (z : ℝ) {f : ℕ → ℝ}
    (hf : Tendsto f atTop atTop) : ¬(fun _ : ℕ => z) =Θ[atTop] f := by
  intro h
  obtain ⟨C, hC, hbound⟩ := h.2.exists_pos
  obtain ⟨n, hn, hn0, hnorm⟩ :=
    ((hf.eventually_gt_atTop (C * ‖z‖)).and
      ((hf.eventually_ge_atTop 0).and hbound.bound)).exists
  rw [Real.norm_of_nonneg hn0] at hnorm
  exact (not_lt_of_ge hnorm) hn

private lemma critical_zero_not_constant :
    ¬floorCost 1 2 (fun _ => 1) two_gt_one =Θ[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  intro h
  exact not_constant_theta_of_tendsto 1
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) (h.symm.trans critical_zero_exponent)

private lemma negative_toll_recurrence (n : ℕ) : (fun _ : ℕ => (1 : ℝ)) n =
    2 * (fun _ : ℕ => (1 : ℝ)) ⌊(n : ℝ) / 2⌋₊ + (fun _ : ℝ => (-1 : ℝ)) n := by norm_num
private lemma negative_toll_theta :
    (fun _ : ℝ => (-1 : ℝ)) =Θ[atTop] (fun x : ℝ => x ^ (0 : ℝ)) := by
  simpa only [rpow_zero] using
    (isTheta_const_const (l := (atTop : Filter ℝ)) (by norm_num : (-1 : ℝ) ≠ 0) one_ne_zero)
private lemma negative_toll_not_nonneg : ¬(∀ x ≥ (0 : ℝ), 0 ≤ (-1 : ℝ)) := by
  intro h
  have h0 := h 0 le_rfl
  norm_num at h0
private lemma negative_toll_counterexample :
    ¬(fun _ : ℕ => (1 : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ)) :=
  not_constant_theta_of_tendsto 1 tendsto_natCast_atTop_atTop

private lemma negative_base_recurrence (n : ℕ) : (fun _ : ℕ => (-1 : ℝ)) n =
    2 * (fun _ : ℕ => (-1 : ℝ)) ⌊(n : ℝ) / 2⌋₊ + (fun _ : ℝ => (1 : ℝ)) n := by norm_num
private lemma negative_base_not_positive : ¬(∀ n : ℕ, n < 1 → 0 < (-1 : ℝ)) := by norm_num
private lemma negative_base_counterexample :
    ¬(fun _ : ℕ => (-1 : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ)) :=
  not_constant_theta_of_tendsto (-1) tendsto_natCast_atTop_atTop

private lemma zero_toll_recurrence (n : ℕ) : (fun _ : ℕ => (1 : ℝ)) n =
    1 * (fun _ : ℕ => (1 : ℝ)) ⌊(n : ℝ) / 2⌋₊ + (fun _ : ℝ => (0 : ℝ)) n := by norm_num
private lemma zero_toll_isBigO :
    (fun _ : ℝ => (0 : ℝ)) =O[atTop] (fun x : ℝ => x ^ (0 : ℝ)) := isBigO_zero _ _
private lemma zero_toll_counterexample : ¬(fun _ : ℕ => (1 : ℝ)) =Θ[atTop] (fun n : ℕ => log n) :=
  not_constant_theta_of_tendsto 1 (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma zero_coefficient_excluded : ¬(0 < (0 : ℝ)) := by norm_num
private lemma unit_divisor_excluded : ¬(1 < (1 : ℝ)) := by norm_num
private lemma zero_cutoff_cannot_shrink (r : ℕ → ℕ) : ¬(∀ n, 0 ≤ n → r n < n) := by
  intro h
  exact Nat.not_lt_zero _ (h 0 (by decide))
private lemma zero_cutoff_not_positive : ¬(0 < (0 : ℕ)) := by decide
private lemma unit_ceiling_cutoff_inconsistent (T : ℕ → ℝ) :
    ¬(T 1 = T ⌈(1 : ℝ) / 2⌉₊ + 1) := by
  have hc : ⌈(1 : ℝ) / 2⌉₊ = 1 := by
    apply le_antisymm (Nat.ceil_le.2 (by norm_num))
    exact Nat.succ_le_of_lt (Nat.lt_ceil.2 (by norm_num) : 0 < ⌈(1 : ℝ) / 2⌉₊)
  rw [hc]
  intro h
  linarith

end MasterTheoremTest
