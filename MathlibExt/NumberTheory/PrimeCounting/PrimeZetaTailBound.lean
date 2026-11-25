/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# A uniform tail bound for the prime zeta series

This file proves `MetaMathlibExt.tsum_rpow_neg_primes_gt_exp_inv_le`: for every real `α` with
`0 < α ≤ 1`, the sum of `p ^ (-(1 + α))` over the primes `p > exp (1 / α)` is at most `0.9235`.
This is Lemma 10 of Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess
Bound via Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66 (Lemma 4.10 of the preprint
arXiv:2007.08119v1).

The preprint's proof sums by parts against an explicit Rosser–Schoenfeld bound for the
prime-counting function and obtains `(1 + α) · 1.2551 / e`. Here the summation by parts uses
Chebyshev's bound `θ(n) ≤ n log 4` (`Chebyshev.theta_le_log4_mul_x`) instead. With
`x = exp (1 / α)`, `N = ⌊x⌋₊` and `f t = t ^ (-(1 + α)) / log t`, it bounds the sum over the
primes in `(N, M]` by `log 4 * ((N + 1) f (N + 1) + ∑_{N + 1 < n ≤ M} f n)`. The last sum
telescopes against `H t = t ^ (-α) / (α log t + 1 / 2)`, using only `log (1 - 1 / t) ≤ -1 / t`
and `1 + u ≤ exp u`, so no integrals are needed. This bounds the tail sum by
`(5 / 3) log 4 / e < 0.85`.
-/

open Real Finset

namespace MetaMathlibExt

namespace tsum_rpow_neg_primes_gt_exp_inv_le

/-- One telescoping step: for `s ≥ 1` with `α log (s + 1) ≥ 1 / 2`, the term
`(s + 1) ^ (-(1 + α)) / log (s + 1)` is at most `H s - H (s + 1)`, where
`H t = t ^ (-α) / (α log t + 1 / 2)`. -/
private theorem step_le {α s : ℝ} (hα₀ : 0 < α) (hs : 1 ≤ s) (hv : 1 / 2 ≤ α * log (s + 1)) :
    (s + 1) ^ (-(1 + α)) / log (s + 1) ≤
      s ^ (-α) / (α * log s + 1 / 2) - (s + 1) ^ (-α) / (α * log (s + 1) + 1 / 2) := by
  have hs0 : 0 < s := by linarith
  have ht : 0 < s + 1 := by linarith
  set L := log (s + 1)
  set L' := log s
  have hL : 0 < L := log_pos (by linarith)
  have hL' : 0 ≤ L' := log_nonneg hs
  -- `log (s + 1) - log s ≥ 1 / (s + 1)`
  have hδ : 1 ≤ (s + 1) * (L - L') := by
    have h := log_le_sub_one_of_pos (show 0 < s / (s + 1) by positivity)
    rw [log_div hs0.ne' ht.ne'] at h
    have h' : s / (s + 1) - 1 = -1 / (s + 1) := by field_simp; ring
    rw [h', le_div_iff₀ ht] at h
    nlinarith
  set a := (s + 1) ^ (-α) with ha
  have ha0 : 0 < a := rpow_pos_of_pos ht _
  have hb : a * (1 + α * (L - L')) ≤ s ^ (-α) := by
    rw [ha, rpow_def_of_pos ht, rpow_def_of_pos hs0]
    have hexp : exp (L' * -α) = exp (L * -α) * exp (α * (L - L')) := by
      rw [← exp_add]; ring_nf
    rw [hexp]
    gcongr
    linarith [add_one_le_exp (α * (L - L'))]
  have hnum : (s + 1) ^ (-(1 + α)) = a / (s + 1) := by
    rw [neg_add, rpow_add ht, rpow_neg_one, ha, div_eq_inv_mul]
  rw [hnum]
  have hw' : 0 < α * L' + 1 / 2 := by positivity
  have hw : 0 < α * L + 1 / 2 := by positivity
  have hcore : 1 / ((s + 1) * L) + 1 / (α * L + 1 / 2) ≤
      (1 + α * (L - L')) / (α * L' + 1 / 2) := by
    rw [div_add_div _ _ (by positivity) hw.ne', div_le_div_iff₀ (by positivity) hw']
    have h1 : 0 ≤ α * L * ((s + 1) * (L - L') - 1) := by
      apply mul_nonneg (by positivity); linarith
    have h2 : 0 ≤ α * L * (α * L + 1 / 2) * ((s + 1) * (L - L') - 1) := by
      apply mul_nonneg (by positivity); linarith
    have h3 : 0 ≤ α * (L - L') * (α * L + 1 / 2) := by
      apply mul_nonneg (mul_nonneg hα₀.le ?_) hw.le
      nlinarith
    nlinarith
  calc a / (s + 1) / L
      = a * (1 / ((s + 1) * L)) := by field_simp
    _ ≤ a * ((1 + α * (L - L')) / (α * L' + 1 / 2) - 1 / (α * L + 1 / 2)) := by
        gcongr; linarith
    _ = a * (1 + α * (L - L')) / (α * L' + 1 / 2) - a / (α * L + 1 / 2) := by ring
    _ ≤ s ^ (-α) / (α * L' + 1 / 2) - a / (α * L + 1 / 2) := by gcongr

end tsum_rpow_neg_primes_gt_exp_inv_le

open tsum_rpow_neg_primes_gt_exp_inv_le in
/-- **Uniform tail bound for the prime zeta series.** For every real $\alpha$ with
$0 < \alpha \le 1$, $\sum_{p > e^{1/\alpha}} p^{-(1 + \alpha)} \le 0.9235$, where the sum runs
over the primes $p > e^{1/\alpha}$.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 10 (`integers-2024-A66-lem-10`). -/
public theorem tsum_rpow_neg_primes_gt_exp_inv_le {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    ∑' p : {p : ℕ // p.Prime ∧ exp (1 / α) < p}, ((p : ℕ) : ℝ) ^ (-(1 + α)) ≤ 0.9235 := by
  set x := exp (1 / α) with hx
  set N := ⌊x⌋₊
  have hx0 : 0 < x := exp_pos _
  have hlogx : log x = 1 / α := log_exp _
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  set f : ℝ → ℝ := fun t => t ^ (-(1 + α)) / log t with hf
  set H : ℝ → ℝ := fun t => t ^ (-α) / (α * log t + 1 / 2) with hH
  -- every `n ≥ N + 1` lies beyond `x = exp (1 / α)`
  have hgt (n : ℕ) (hn : N + 1 ≤ n) : x < n := by
    have : ((N + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this
    linarith
  have hlog_gt (n : ℕ) (hn : N + 1 ≤ n) : 1 < α * log n := by
    have h := log_lt_log hx0 (hgt n hn)
    rw [hlogx, div_lt_iff₀ hα₀] at h
    linarith
  have hn1 (n : ℕ) (hn : N + 1 ≤ n) : (1 : ℝ) < n :=
    (show 1 < x from Real.one_lt_exp_iff.mpr (by positivity)).trans (hgt n hn)
  have hlog_pos (n : ℕ) (hn : N + 1 ≤ n) : 0 < log (n : ℝ) := log_pos (hn1 n hn)
  -- `f` is antitone beyond `x`
  have hf_anti (n : ℕ) (hn : N + 1 ≤ n) : f ((n : ℝ) + 1) ≤ f n := by
    simp only [hf]
    have h1 := hn1 n hn
    have hl := hlog_pos n hn
    apply div_le_div₀ (rpow_nonneg (by positivity) _) _ hl
    · exact log_le_log (by linarith) (by linarith)
    · exact rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have hf_nonneg (t : ℝ) (ht : 1 ≤ t) : 0 ≤ f t := by
    simp only [hf]
    exact div_nonneg (rpow_nonneg (by linarith) _) (log_nonneg ht)
  -- Chebyshev's bound `θ(M) ≤ M log 4`
  have hθ (M : ℕ) : (∑ n ∈ Ioc N M, if n.Prime then log (n : ℝ) else 0) ≤ M * log 4 := by
    have h1 : (∑ n ∈ Ioc N M, if n.Prime then log (n : ℝ) else 0) ≤
        ∑ n ∈ Ioc 0 M, if n.Prime then log (n : ℝ) else 0 := by
      apply sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le N))
      intro n _ _
      split_ifs
      exacts [log_natCast_nonneg n, le_rfl]
    have h2 := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
    rw [Chebyshev.theta, Nat.floor_natCast, sum_filter] at h2
    linarith
  -- summation by parts
  have key : ∀ M : ℕ, N + 1 ≤ M →
      (∑ n ∈ Ioc N M, if n.Prime then (n : ℝ) ^ (-(1 + α)) else 0) +
        ((M : ℝ) * log 4 - ∑ n ∈ Ioc N M, if n.Prime then log (n : ℝ) else 0) * f M ≤
      log 4 * (((N : ℝ) + 1) * f ((N : ℝ) + 1) + ∑ n ∈ Ioc (N + 1) M, f n) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      rw [Nat.Ioc_succ_singleton, sum_singleton, sum_singleton, Ioc_self, sum_empty]
      push_cast
      split_ifs with hp
      · have hl := hlog_pos (N + 1) le_rfl
        push_cast at hl
        have : ((N : ℝ) + 1) ^ (-(1 + α)) = log ((N : ℝ) + 1) * f ((N : ℝ) + 1) := by
          simp only [hf]
          field_simp
        rw [this]
        exact le_of_eq (by ring)
      · exact le_of_eq (by ring)
    | succ M hM ih =>
      rw [sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega),
        sum_Ioc_succ_top (by omega)]
      have hanti := hf_anti M hM
      have hD : 0 ≤ (M : ℝ) * log 4 - ∑ n ∈ Ioc N M, if n.Prime then log (n : ℝ) else 0 := by
        linarith [hθ M]
      have hfM1 := hf_nonneg ((M : ℝ) + 1) (by linarith [hn1 M hM])
      have hl := hlog_pos (M + 1) (by omega)
      push_cast at hl ⊢
      have hprime : (if (M + 1).Prime then ((M : ℝ) + 1) ^ (-(1 + α)) else 0) =
          (if (M + 1).Prime then log ((M : ℝ) + 1) else 0) * f ((M : ℝ) + 1) := by
        split_ifs
        · simp only [hf]
          field_simp
        · simp
      rw [hprime]
      nlinarith
  -- telescoping comparison of `∑ f` with `H`
  have tele : ∀ M : ℕ, N + 1 ≤ M → ∑ n ∈ Ioc (N + 1) M, f n ≤ H ((N : ℝ) + 1) - H M := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      rw [sum_Ioc_succ_top hM]
      have h1 := hn1 M hM
      have hstep := step_le hα₀ (s := (M : ℝ)) h1.le (by
        have := hlog_gt (M + 1) (by omega)
        push_cast at this
        linarith)
      push_cast
      simp only [hf, hH] at ih ⊢
      linarith
  have hH_nonneg (M : ℕ) (hM : N + 1 ≤ M) : 0 ≤ H M := by
    simp only [hH]
    have := hlog_gt M hM
    exact div_nonneg (rpow_nonneg (Nat.cast_nonneg M) _) (by linarith)
  -- the values at `N + 1`
  have hN1 := hgt (N + 1) le_rfl
  have hlN1 := hlog_gt (N + 1) le_rfl
  push_cast at hN1 hlN1
  have hpow : ((N : ℝ) + 1) ^ (-α) ≤ exp (-1) := by
    calc ((N : ℝ) + 1) ^ (-α) ≤ x ^ (-α) := rpow_le_rpow_of_nonpos hx0 hN1.le (by linarith)
      _ = exp (-1) := by
        rw [hx, ← exp_mul]
        congr 1
        field_simp
  have hlogN1 : 1 ≤ log ((N : ℝ) + 1) := by nlinarith
  have hfirst : ((N : ℝ) + 1) * f ((N : ℝ) + 1) ≤ exp (-1) := by
    simp only [hf]
    have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [neg_add, rpow_add hN1pos, rpow_neg_one]
    have : ((N : ℝ) + 1) * (((N : ℝ) + 1)⁻¹ * ((N : ℝ) + 1) ^ (-α) / log ((N : ℝ) + 1)) =
        ((N : ℝ) + 1) ^ (-α) / log ((N : ℝ) + 1) := by
      field_simp
    rw [this]
    calc ((N : ℝ) + 1) ^ (-α) / log ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) ^ (-α) :=
          div_le_self (rpow_nonneg (by positivity) _) hlogN1
      _ ≤ exp (-1) := hpow
  have hsecond : H ((N : ℝ) + 1) ≤ 2 / 3 * exp (-1) := by
    simp only [hH]
    rw [div_le_iff₀ (by linarith)]
    nlinarith [exp_pos (-1), rpow_nonneg (show (0 : ℝ) ≤ (N : ℝ) + 1 by positivity) (-α)]
  have hnum : 5 / 3 * log 4 * exp (-1) ≤ (0.9235 : ℝ) := by
    have h4 : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
      norm_num
    rw [h4, exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos 1)]
    nlinarith [log_two_lt_d9, exp_one_gt_d9]
  have hbound (M : ℕ) (hM : N + 1 ≤ M) :
      (∑ n ∈ Ioc N M, if n.Prime then (n : ℝ) ^ (-(1 + α)) else 0) ≤ 0.9235 := by
    have h1 := key M hM
    have h2 := tele M hM
    have h3 := hH_nonneg M hM
    have h4 : 0 ≤ ((M : ℝ) * log 4 - ∑ n ∈ Ioc N M, if n.Prime then log (n : ℝ) else 0) *
        f M := mul_nonneg (by linarith [hθ M]) (hf_nonneg M (hn1 M hM).le)
    have hlog4 : 0 < log (4 : ℝ) := log_pos (by norm_num)
    have h5 : log 4 * (((N : ℝ) + 1) * f ((N : ℝ) + 1) + ∑ n ∈ Ioc (N + 1) M, f n) ≤
        log 4 * (exp (-1) + 2 / 3 * exp (-1)) := by
      gcongr
      linarith
    linarith
  -- pass to the infinite sum
  refine Real.tsum_le_of_sum_le (fun p => rpow_nonneg (Nat.cast_nonneg _) _) fun u => ?_
  set M := max (N + 1) (u.sup Subtype.val) with hM
  calc ∑ p ∈ u, ((p : ℕ) : ℝ) ^ (-(1 + α))
      = ∑ n ∈ u.map (Function.Embedding.subtype _), (n : ℝ) ^ (-(1 + α)) := by
        rw [sum_map]
        rfl
    _ ≤ ∑ n ∈ Ioc N M with n.Prime, (n : ℝ) ^ (-(1 + α)) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [mem_map] at hn
          obtain ⟨p, hp, rfl⟩ := hn
          rw [mem_filter, mem_Ioc]
          refine ⟨⟨?_, ?_⟩, p.2.1⟩
          · exact (Nat.floor_lt hx0.le).2 p.2.2
          · exact (le_sup (f := Subtype.val) hp).trans ((le_max_right _ _).trans_eq hM.symm)
        · intro n _ _
          exact rpow_nonneg (Nat.cast_nonneg _) _
    _ = ∑ n ∈ Ioc N M, if n.Prime then (n : ℝ) ^ (-(1 + α)) else 0 := sum_filter _ _
    _ ≤ 0.9235 := hbound M ((le_max_left _ _).trans_eq hM.symm)

end MetaMathlibExt
