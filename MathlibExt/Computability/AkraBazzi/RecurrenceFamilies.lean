/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.AkraBazzi.MasterTheorem

/-!
# Akra-Bazzi recurrence families and the constant shift

A constant shift of the solution of an Akra-Bazzi recurrence is again an
Akra-Bazzi recurrence, with the toll shifted by the same constant times
`1 - ∑ i, a i`. This lets a recurrence with a nonzero finite base be
normalized before the master theorem is applied.

## Cost model

The charged primitive is one recursive call, charged `a i` times per
branch, plus the declared per-call toll `g`. Rounding is free. No
machine-time claim is made.

## References

* Tom Leighton, Notes on better master theorems for divide-and-conquer
  recurrences, 1996.
-/

public section

open Filter Asymptotics Finset Real
open scoped Topology

namespace AkraBazziRecurrence

variable {α : Type*} [Fintype α] [Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}

/-- **Constant shift of a recurrence.** Adding `c` to `T` and `c * (1 - ∑ i, a i)`
to `g` preserves the recurrence relation. -/
noncomputable def shift (R : AkraBazziRecurrence T g a b r) (c : ℝ)
    (hT : ∀ n < R.n₀, 0 < T n + c) (hg : ∀ x ≥ 0, 0 ≤ g x + c * (1 - ∑ i, a i))
    (hgpoly : AkraBazziRecurrence.GrowsPolynomially
      (fun x => g x + c * (1 - ∑ i, a i))) :
    AkraBazziRecurrence (fun n => T n + c) (fun x => g x + c * (1 - ∑ i, a i))
      a b r where
  n₀ := R.n₀
  n₀_gt_zero := R.n₀_gt_zero
  a_pos := R.a_pos
  b_pos := R.b_pos
  b_lt_one := R.b_lt_one
  g_nonneg x hx := hg x hx
  g_grows_poly := hgpoly
  h_rec n hn := by
    rw [R.h_rec n hn]
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  T_gt_zero' n hn := hT n hn
  r_lt_n := R.r_lt_n
  dist_r_b := R.dist_r_b

private lemma isLittleO_of_bounded {e : ℕ → ℝ} (he : ∀ n, |e n| ≤ 1) :
    e =o[atTop] (fun n : ℕ => (n : ℝ) / (log n) ^ 2) := by
  have hlog : (fun n : ℕ => (log n) ^ 2 * (1 : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
    have h : (fun n : ℕ => (log n) ^ 2) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
      (Real.isLittleO_pow_log_id_atTop (n := 2)).natCast_atTop
    simpa only [mul_one] using h
  have hne : ∀ᶠ n : ℕ in atTop, (log n) ^ 2 ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact pow_ne_zero _ (ne_of_gt (log_pos (by exact_mod_cast hn)))
  have hsmall := (isLittleO_mul_iff_isLittleO_div hne).1 hlog
  apply (IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)).trans_isLittleO hsmall
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using he n

/-- **Floor-plus-ceiling family.** Pairs each `d`-branch floor child with its
ceiling sibling over `κ ⊕ κ`, weighted by `a`. The cutoff `n₀` satisfies
`d i / (d i - 1) ≤ n₀` for every branch so ceiling children strictly shrink. -/
noncomputable def ofFloorCeilFamily {κ : Type*} [Fintype κ] [Nonempty κ]
    {T : ℕ → ℝ} {g : ℝ → ℝ} {a d : κ → ℝ} (n₀ : ℕ)
    (ha : ∀ i, 0 < a i) (hd : ∀ i, 1 < d i) (hn₀ : 0 < n₀)
    (hcut : ∀ i, d i / (d i - 1) ≤ (n₀ : ℝ))
    (hgrow : AkraBazziRecurrence.GrowsPolynomially g)
    (hg0 : ∀ x ≥ 0, 0 ≤ g x)
    (hbase : ∀ n < n₀, 0 < T n)
    (hrec : ∀ n, n₀ ≤ n →
      T n = (∑ i, a i * T ⌊(n : ℝ) / d i⌋₊)
        + (∑ i, a i * T ⌈(n : ℝ) / d i⌉₊) + g n) :
    AkraBazziRecurrence T g (Sum.elim a a) (Sum.elim (fun i => (d i)⁻¹) (fun i => (d i)⁻¹))
      (Sum.elim (fun i n => ⌊(n : ℝ) / d i⌋₊) (fun i n => ⌈(n : ℝ) / d i⌉₊)) where
  n₀ := n₀
  n₀_gt_zero := hn₀
  a_pos j := by
    cases j with
    | inl i => simpa only [Sum.elim_inl] using ha i
    | inr i => simpa only [Sum.elim_inr] using ha i
  b_pos j := by
    cases j with
    | inl i => simpa only [Sum.elim_inl] using inv_pos.2 (by linarith [hd i])
    | inr i => simpa only [Sum.elim_inr] using inv_pos.2 (by linarith [hd i])
  b_lt_one j := by
    cases j with
    | inl i => simpa only [Sum.elim_inl] using (inv_lt_one₀ (by linarith [hd i])).2 (hd i)
    | inr i => simpa only [Sum.elim_inr] using (inv_lt_one₀ (by linarith [hd i])).2 (hd i)
  g_nonneg := hg0
  g_grows_poly := hgrow
  h_rec n hn := by
    rw [hrec n hn]
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  T_gt_zero' := hbase
  r_lt_n j n hn := by
    cases j with
    | inl i =>
        have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn₀.trans_le hn
        apply (Nat.floor_lt (div_nonneg (Nat.cast_nonneg n) (by linarith [hd i]))).2
        exact div_lt_self hnpos (hd i)
    | inr i =>
        have hnpos : 0 < n := hn₀.trans_le hn
        have hbn : d i ≤ (n : ℝ) * (d i - 1) :=
          (div_le_iff₀ (by linarith [hd i] : 0 < d i - 1)).1 ((hcut i).trans (by exact_mod_cast hn))
        have hchild : ⌈(n : ℝ) / d i⌉₊ ≤ n - 1 := by
          rw [Nat.ceil_le, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hnpos.ne'), Nat.cast_one]
          apply (div_le_iff₀ (by linarith [hd i] : 0 < d i)).2
          nlinarith [hd i]
        exact hchild.trans_lt (Nat.sub_lt hnpos (by decide))
  dist_r_b j := by
    cases j with
    | inl i =>
        apply isLittleO_of_bounded
        intro n
        simpa only [Sum.elim_inl, div_eq_mul_inv, mul_comm] using
          Nat.abs_floor_sub_le (div_nonneg (Nat.cast_nonneg n) (by linarith [hd i] : 0 ≤ d i))
    | inr i =>
        apply isLittleO_of_bounded
        intro n
        simpa only [Sum.elim_inr, div_eq_mul_inv, mul_comm] using
          Nat.abs_ceil_sub_le (div_nonneg (Nat.cast_nonneg n) (by linarith [hd i] : 0 ≤ d i))

end AkraBazziRecurrence
