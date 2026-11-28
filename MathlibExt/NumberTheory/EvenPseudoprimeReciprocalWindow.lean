/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Reciprocal sums over a residue class in an exponential window

Write `ℓ₂(p)` for the multiplicative order of `2` modulo a prime `p`, that is
`orderOf (2 : ZMod p)`. For an odd prime `p` and a natural number `k`, the sum of `1 / N` over
the integers `N` with `e ^ k < N ≤ e ^ (k + 1)`, `N ≡ p [MOD p * ℓ₂(p)]` and `p < N` is at most
`2 / (p * ℓ₂(p))` (`MetaMathlibExt.sum_inv_modEq_orderOf_le`).

## Proof outline

Put `m = p * ℓ₂(p)`, which is positive since `ℓ₂(p)` divides `p - 1`. If the window holds a
term, let `x` be the smallest one. Every term has the form `x + i * m` with
`x + i * m ≤ e ^ (k + 1)`, and `x ≥ p + m ≥ m` because `x ≡ p [MOD m]` and `x > p`.

* The first term gives `1 / x ≤ 1 / m`.
* From `log y ≥ 1 - 1 / y`, `1 / (x + i * m) ≤ (log (x + i * m) - log (x + (i - 1) * m)) / m`
  for `i ≥ 1`, and these differences telescope to `log (x + n * m) - log x < (k + 1) - k = 1`.
-/

public section

namespace MetaMathlibExt

namespace SumInvModEqOrderOfLe

/-- For `x, m > 0`, the reciprocals of an arithmetic progression with first term `x` and
difference `m` satisfy `∑ i ≤ n, 1 / (x + i m) ≤ 1 / x + (log (x + n m) - log x) / m`. -/
private theorem sum_range_inv_le (x m : ℝ) (hx : 0 < x) (hm : 0 < m) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), 1 / (x + i * m) ≤
      1 / x + (Real.log (x + n * m) - Real.log x) / m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hB : 0 < x + n * m := by positivity
    have hA : 0 < x + ((n + 1 : ℕ) : ℝ) * m := by positivity
    have hlog : 1 - ((x + ((n + 1 : ℕ) : ℝ) * m) / (x + n * m))⁻¹ ≤
        Real.log (x + ((n + 1 : ℕ) : ℝ) * m) - Real.log (x + n * m) := by
      rw [← Real.log_div hA.ne' hB.ne']
      exact Real.one_sub_inv_le_log_of_pos (div_pos hA hB)
    have hstep : 1 / (x + ((n + 1 : ℕ) : ℝ) * m) ≤
        (Real.log (x + ((n + 1 : ℕ) : ℝ) * m) - Real.log (x + n * m)) / m := by
      rw [le_div_iff₀ hm]
      refine le_trans (le_of_eq ?_) hlog
      rw [inv_div]
      field_simp
      push_cast
      ring
    calc _ ≤ 1 / x + (Real.log (x + n * m) - Real.log x) / m +
          (Real.log (x + ((n + 1 : ℕ) : ℝ) * m) - Real.log (x + n * m)) / m :=
          add_le_add ih hstep
      _ = _ := by ring

/-- The bound of `MetaMathlibExt.sum_inv_modEq_orderOf_le` for an arbitrary positive modulus
`m` in place of `p * ℓ₂(p)`. -/
private theorem sum_inv_modEq_le (p m : ℕ) (hm : 0 < m) (k : ℕ) :
    ∑ N ∈ (Finset.Icc 1 ⌊Real.exp (k + 1)⌋₊).filter (fun N : ℕ =>
        Real.exp k < N ∧ N ≡ p [MOD m] ∧ p < N), (1 : ℝ) / N ≤ 2 / m := by
  classical
  set S := (Finset.Icc 1 ⌊Real.exp (k + 1)⌋₊).filter (fun N : ℕ =>
    Real.exp k < N ∧ N ≡ p [MOD m] ∧ p < N) with hS
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rcases S.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.sum_empty]
    positivity
  set x := S.min' hne with hxdef
  have hxS : x ∈ S := S.min'_mem hne
  simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hxS
  obtain ⟨⟨hx1, hxF⟩, hxk, hxp, hpx⟩ := hxS
  set F := ⌊Real.exp (k + 1)⌋₊ with hF
  set n := (F - x) / m with hn
  -- Every term is `x + i * m` with `i ≤ n`.
  have hsub : S ⊆ (Finset.range (n + 1)).image (fun i => x + i * m) := by
    intro N hN
    have hxN : x ≤ N := S.min'_le N hN
    simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hN
    obtain ⟨⟨_, hNF⟩, _, hNp, _⟩ := hN
    have hdvd : m ∣ N - x := (Nat.modEq_iff_dvd' hxN).mp (hxp.trans hNp.symm)
    obtain ⟨i, hi⟩ := hdvd
    refine Finset.mem_image.mpr ⟨i, ?_, by rw [mul_comm]; omega⟩
    rw [Finset.mem_range, Nat.lt_succ_iff, hn]
    calc i = (N - x) / m := by rw [hi, Nat.mul_div_cancel_left _ hm]
      _ ≤ (F - x) / m := Nat.div_le_div_right (by omega)
  have hinj : Set.InjOn (fun i => x + i * m) (Finset.range (n + 1) : Set ℕ) := by
    intro i _ j _ hij
    simp only at hij
    exact Nat.eq_of_mul_eq_mul_right hm (by omega)
  have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  calc ∑ N ∈ S, (1 : ℝ) / N
      ≤ ∑ N ∈ (Finset.range (n + 1)).image (fun i => x + i * m), (1 : ℝ) / N :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), 1 / ((x : ℝ) + i * m) := by
        rw [Finset.sum_image hinj]
        push_cast
        rfl
    _ ≤ 1 / x + (Real.log (x + n * m) - Real.log x) / m := sum_range_inv_le _ _ hxR hmR n
    _ ≤ 1 / m + 1 / m := by
        gcongr ?_ + ?_
        · -- `m ≤ x`, since `m ∣ x - p` and `p < x`.
          have hdvd : m ∣ x - p := (Nat.modEq_iff_dvd' hpx.le).mp hxp.symm
          have hle : m ≤ x := (Nat.le_of_dvd (by omega) hdvd).trans (Nat.sub_le _ _)
          exact one_div_le_one_div_of_le hmR (by exact_mod_cast hle)
        · rw [div_le_div_iff_of_pos_right hmR]
          have htop : (x : ℝ) + n * m ≤ Real.exp (k + 1) := by
            have h1 : x + n * m ≤ F := by
              have := Nat.div_mul_le_self (F - x) m
              rw [← hn] at this
              omega
            calc (x : ℝ) + n * m = ((x + n * m : ℕ) : ℝ) := by push_cast; ring
              _ ≤ (F : ℝ) := by exact_mod_cast h1
              _ ≤ Real.exp (k + 1) := Nat.floor_le (Real.exp_pos _).le
          have hhi : Real.log (x + n * m) ≤ k + 1 := by
            rw [← Real.log_exp ((k : ℝ) + 1)]
            exact Real.log_le_log (by positivity) htop
          have hlo : (k : ℝ) < Real.log x := (Real.lt_log_iff_exp_lt hxR).mpr hxk
          linarith
    _ = 2 / m := by ring

end SumInvModEqOrderOfLe

open scoped Classical in
/-- **Reciprocal sum over a residue class in an exponential window.** Write $\ell_2(p)$ for the
multiplicative order of $2$ modulo a prime $p$. Let $p$ be an odd prime and $k$ a natural
number, and let $F_p(k)$ be the sum of $1/N$ over the integers $N$ with $e^k < N \le e^{k+1}$,
$N \equiv p \pmod{p\,\ell_2(p)}$ and $N > p$. Then $F_p(k) \le 2 / (p\,\ell_2(p))$.

The bound holds for every $k$, since the terms are $1/N$ with $N = p + j\,p\,\ell_2(p)$ and
$j \ge 1$.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Proposition 11 (`jis-2026-26.1.3-prop-11`). -/
theorem sum_inv_modEq_orderOf_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    ∑ N ∈ (Finset.Icc 1 ⌊Real.exp (k + 1)⌋₊).filter (fun N : ℕ =>
        Real.exp k < N ∧ N ≡ p [MOD p * orderOf (2 : ZMod p)] ∧ p < N), (1 : ℝ) / N ≤
      2 / (p * orderOf (2 : ZMod p)) := by
  have := Fact.mk hp
  -- `ℓ₂(p)` divides `p - 1 ≠ 0`, so it is positive.
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hord : 0 < orderOf (2 : ZMod p) :=
    Nat.pos_of_dvd_of_pos (ZMod.orderOf_dvd_card_sub_one h2) (by have := hp.two_le; omega)
  have hm : 0 < p * orderOf (2 : ZMod p) := Nat.mul_pos hp.pos hord
  have := SumInvModEqOrderOfLe.sum_inv_modEq_le p _ hm k
  convert this using 2
  push_cast
  rfl

end MetaMathlibExt
