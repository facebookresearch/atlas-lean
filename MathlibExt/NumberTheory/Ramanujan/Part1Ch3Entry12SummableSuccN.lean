/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Computability.Reduce

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 12

Summability of (n+k)^(r+1+k)/(aᵏk!) for |a|>e.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry12SummableSuccN

/-- **Absolute convergence of the shifted series in Entry 12 for every $n$.** Let $r$ be an
integer and let $n$ and $a$ be complex numbers with $|a| > e$, or with $a = e$ and $r \le -2$.
Then
$$\sum_{k=0}^{\infty} \left| \frac{(n+k)^{r+1+k}}{a^k\, k!} \right| < \infty,$$
where integer powers of complex numbers follow the convention $0^m = 0$ for $m < 0$.

Unlike the version that assumes $n + k \ne 0$ whenever $k \ge 0$ and $r + k < 0$, nothing is
assumed about $n$. At an index where $n + k = 0$ and the exponent $r + 1 + k$ is negative, the
term is $0^{r+1+k} = 0$, whereas the source's term is undefined there. Summability depends only
on the tail, where every exponent is nonnegative. -/
theorem ramanujan_part1_ch3_entry12_summable_succ_n_general (r : ℤ) (n a : ℂ)
    (ha : norm a > Real.exp 1 ∨ (a = ↑(Real.exp 1) ∧ r ≤ -2)) :
    Summable (fun k : ℕ => norm ((n + (k : ℂ)) ^ (r + 1 + (k : ℤ)) / ((a ^ k) * (k.factorial : ℂ)))) := by
  set N : ℝ := norm n with hNdef
  set q : ℝ := norm a with hqdef
  have hN : (0:ℝ) ≤ N := norm_nonneg _
  set K0 : ℕ := (-(r + 1)).toNat + Nat.ceil (2 * N + 2) + 2 with hK0def
  have hK0_ge_s : (-(r + 1)).toNat ≤ K0 := by rw [hK0def]; omega
  have hK0_ge2 : 2 ≤ K0 := by rw [hK0def]; omega
  have hK0R : 2 * N + 2 ≤ (K0 : ℝ) := by
    have h1 := Nat.le_ceil (2 * N + 2)
    have hs0 : (0:ℝ) ≤ (((-(r + 1)).toNat : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hK0def]
    push_cast
    linarith
  have hs_int : (-(r + 1) : ℤ) ≤ (((-(r + 1)).toNat : ℕ) : ℤ) := by omega
  have htail : ∀ k : ℕ, K0 ≤ k → (0:ℤ) ≤ r + 1 + (k : ℤ) := by
    intro k hk
    omega
  have hts : ∀ k : ℕ, K0 ≤ k → (r + 1 + (k : ℤ)).toNat + (-(r + 1)).toNat = k + (r + 1).toNat := by
    intro k hk
    have h0 := htail k hk
    omega
  have hk1 : ∀ k : ℕ, K0 ≤ k → 1 ≤ k := by
    intro k hk
    omega
  have hNk0 : ∀ k : ℕ, (0:ℝ) ≤ N + (k:ℝ) := fun k => add_nonneg hN (Nat.cast_nonneg k)
  have hNk1 : ∀ k : ℕ, K0 ≤ k → (1:ℝ) ≤ N + (k:ℝ) := by
    intro k hk
    have hk2 : (2:ℕ) ≤ k := le_trans hK0_ge2 hk
    have hkR : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
    linarith [hN]
  have hNk_half : ∀ k : ℕ, K0 ≤ k → ((k:ℝ)+1)/2 ≤ N + (k:ℝ) := by
    intro k hk
    have hkR : (K0:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith [hK0R, hN]
  have hKpos : ∀ k : ℕ, K0 ≤ k → (0:ℝ) < (k.factorial:ℝ) := by
    intro k _
    exact_mod_cast Nat.factorial_pos k
  have hNk_le : ∀ k : ℕ, N + (k:ℝ) ≤ (N+1) * ((k:ℝ)+1) := by
    intro k
    have h1 : (0:ℝ) ≤ N * (k:ℝ) := mul_nonneg hN (Nat.cast_nonneg k)
    have he : (N+1) * ((k:ℝ)+1) = N * (k:ℝ) + (N + (k:ℝ)) + 1 := by ring
    linarith
  have hbase_norm : ∀ k : ℕ, norm (n + (k:ℂ)) ≤ N + (k:ℝ) := by
    intro k
    calc norm (n + (k:ℂ)) ≤ norm n + norm ((k:ℂ)) := norm_add_le _ _
      _ = N + (k:ℝ) := by rw [Complex.norm_natCast, ← hNdef]
  have hA : ∀ k : ℕ, norm (n + (k:ℂ))^((r+1+(k:ℤ)).toNat)
      ≤ (N+(k:ℝ))^((r+1+(k:ℤ)).toNat) := by
    intro k
    exact pow_le_pow_left₀ (norm_nonneg _) (hbase_norm k) _
  have hterm : ∀ k : ℕ, norm ((n + (k:ℂ))^(r+1+(k:ℤ)) / ((a^k) * (k.factorial:ℂ)))
      = norm (n + (k:ℂ))^(r+1+(k:ℤ)) / (q^k * (k.factorial:ℝ)) := by
    intro k
    rw [norm_div, norm_zpow, norm_mul, norm_pow, Complex.norm_natCast, ← hqdef]
  have hzpow : ∀ k : ℕ, K0 ≤ k → (norm (n + (k:ℂ)))^(r+1+(k:ℤ))
      = (norm (n + (k:ℂ)))^((r+1+(k:ℤ)).toNat) := by
    intro k hk
    conv_lhs => rw [← Int.toNat_of_nonneg (htail k hk)]
    exact zpow_natCast _ _
  have hsplit : ∀ k : ℕ, K0 ≤ k → (N + (k:ℝ)) ^ (r + 1 + (k:ℤ)).toNat * (N + (k:ℝ)) ^ (-(r+1)).toNat
      = (N + (k:ℝ)) ^ k * (N + (k:ℝ)) ^ (r+1).toNat := by
    intro k hk
    rw [← pow_add, ← pow_add, hts k hk]
  have e_exp : ∀ k : ℕ, Real.exp (k:ℝ) = Real.exp 1 ^ k := by
    intro k
    rw [← mul_one (k:ℝ), Real.exp_nat_mul]
  have hfact_elem : ∀ k : ℕ, (k:ℝ)^k / (k.factorial:ℝ) ≤ Real.exp 1^k := by
    intro k
    have h := Real.pow_div_factorial_le_exp (k:ℝ) (Nat.cast_nonneg k) k
    rwa [e_exp k] at h
  have hexp_base : ∀ k : ℕ, 1 ≤ k → (1 + N / (k:ℝ))^k ≤ Real.exp N := by
    intro k hk
    have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkpos
    have h1 : (1:ℝ) + N / (k:ℝ) ≤ Real.exp (N / (k:ℝ)) := by
      have h := Real.add_one_le_exp (N / (k:ℝ))
      linarith
    have h2 : ((1:ℝ) + N/(k:ℝ))^k ≤ (Real.exp (N/(k:ℝ)))^k :=
      pow_le_pow_left₀ (add_nonneg zero_le_one (div_nonneg hN (Nat.cast_nonneg k))) h1 k
    have h3 : (Real.exp (N/(k:ℝ)))^k = Real.exp N := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [mul_comm, div_mul_cancel₀ _ hkne]
    exact le_trans h2 (le_of_eq h3)
  have hfact_stir : ∀ k : ℕ, 1 ≤ k →
      (k:ℝ)^k / (k.factorial:ℝ) ≤ Real.exp 1^k / Real.sqrt (2 * Real.pi * (k:ℝ)) := by
    intro k hk
    have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hS := Stirling.le_factorial_stirling k
    have harg : (0:ℝ) < 2 * Real.pi * (k:ℝ) :=
      mul_pos (by linarith [Real.pi_pos]) hkpos
    have hsqrt_pos : (0:ℝ) < Real.sqrt (2 * Real.pi * (k:ℝ)) := Real.sqrt_pos.mpr harg
    have hfact_pos : (0:ℝ) < (k.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hexp_pos : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    have hexpand : (k:ℝ)^k = ((k:ℝ) / Real.exp 1)^k * Real.exp 1^k := by
      rw [← mul_pow, div_mul_cancel₀ _ (ne_of_gt hexp_pos)]
    have hstep : Real.sqrt (2 * Real.pi * (k:ℝ)) * ((k:ℝ) / Real.exp 1)^k * Real.exp 1^k
        ≤ (k.factorial:ℝ) * Real.exp 1^k :=
      mul_le_mul_of_nonneg_right hS (pow_nonneg hexp_pos.le k)
    rw [div_le_iff₀ hfact_pos, div_mul_eq_mul_div, le_div_iff₀ hsqrt_pos, hexpand]
    calc ((k:ℝ) / Real.exp 1)^k * Real.exp 1^k * Real.sqrt (2 * Real.pi * (k:ℝ))
        = Real.sqrt (2 * Real.pi * (k:ℝ)) * ((k:ℝ) / Real.exp 1)^k * Real.exp 1^k := by ring
      _ ≤ (k.factorial:ℝ) * Real.exp 1^k := hstep
      _ = Real.exp 1^k * (k.factorial:ℝ) := by ring
  have hNk_eq : ∀ k : ℕ, 1 ≤ k → N + (k:ℝ) = (1 + N/(k:ℝ)) * (k:ℝ) := by
    intro k hk
    have hkne : (k:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Nat.pos_of_ne_zero (by omega))
    have e : (1 + N/(k:ℝ)) * (k:ℝ) = N + (k:ℝ) := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ hkne, add_comm]
    exact e.symm
  have hpoly : ∀ k : ℕ, (N + (k:ℝ))^((r+1).toNat)
      ≤ (N+1)^((r+1).toNat) * ((k:ℝ)+1)^((r+1).toNat) := by
    intro k
    have h := pow_le_pow_left₀ (hNk0 k) (hNk_le k) ((r+1).toNat)
    rwa [mul_pow] at h
  have hrpow : ∀ X : ℝ, 0 < X → X * Real.sqrt X = X^((3/2):ℝ) := by
    intro X hX
    have e : ((3/2):ℝ) = 1 + 1/2 := by ring
    rw [e, Real.rpow_add hX, Real.rpow_one, Real.sqrt_eq_rpow]
  rcases ha with ha1 | ⟨ha2, hr⟩
  · -- Case |a| > e: comparison with polynomial times geometric series.
    have hqpos : (0:ℝ) < q := lt_trans (Real.exp_pos 1) ha1
    have hnorm1 : norm (Real.exp 1 / q : ℝ) < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le hqpos.le), div_lt_one hqpos]
      exact ha1
    have hbase1 : Summable (fun m : ℕ => ((m:ℝ))^((r+1).toNat) * ((Real.exp 1/q))^m) :=
      summable_pow_mul_geometric_of_norm_lt_one _ hnorm1
    have hH1 : Summable (fun j : ℕ => ((((j+K0:ℕ)):ℝ))^((r+1).toNat) * ((Real.exp 1/q))^(j+K0)) :=
      (summable_nat_add_iff K0).mpr hbase1
    have hcore1 : ∀ k : ℕ, K0 ≤ k → norm ((n + (k:ℂ))^(r+1+(k:ℤ)) / ((a^k) * (k.factorial:ℂ)))
        ≤ ((N+1)^((r+1).toNat) * Real.exp N * 2^((r+1).toNat))
          * ((((k:ℝ))^((r+1).toNat)) * ((Real.exp 1/q)^k)) := by
      intro k hk
      rw [hterm k, hzpow k hk]
      have hkk : (k:ℝ)^k ≤ Real.exp 1^k * (k.factorial:ℝ) := by
        have h := hfact_elem k
        rwa [div_le_iff₀ (hKpos k hk)] at h
      have hP : (N+(k:ℝ))^k ≤ Real.exp N * (k:ℝ)^k := by
        have e1 : (N+(k:ℝ))^k = (1 + N/(k:ℝ))^k * (k:ℝ)^k := by
          rw [hNk_eq k (hk1 k hk), mul_pow]
        rw [e1]
        exact mul_le_mul (hexp_base k (hk1 k hk)) le_rfl
          (pow_nonneg (Nat.cast_nonneg k) k) (Real.exp_pos _).le
      have hQ' : ((k:ℝ)+1)^((r+1).toNat) ≤ 2^((r+1).toNat) * (k:ℝ)^((r+1).toNat) := by
        have hk1R : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1 k hk
        have h12 : (k:ℝ)+1 ≤ 2*(k:ℝ) := by linarith
        have h0 : (0:ℝ) ≤ (k:ℝ)+1 := by
          have hc : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
          linarith
        have h := pow_le_pow_left₀ h0 h12 ((r+1).toNat)
        rwa [mul_pow] at h
      have hs1 : (1:ℝ) ≤ (N+(k:ℝ))^((-(r+1)).toNat) := one_le_pow₀ (hNk1 k hk)
      have hAt : (N+(k:ℝ))^((r+1+(k:ℤ)).toNat)
          ≤ (N+(k:ℝ))^k * (N+(k:ℝ))^((r+1).toNat) := by
        have h2 := hsplit k hk
        calc (N+(k:ℝ))^((r+1+(k:ℤ)).toNat) = (N+(k:ℝ))^((r+1+(k:ℤ)).toNat) * 1 := by rw [mul_one]
          _ ≤ (N+(k:ℝ))^((r+1+(k:ℤ)).toNat) * (N+(k:ℝ))^((-(r+1)).toNat) :=
              mul_le_mul_of_nonneg_left hs1 (pow_nonneg (hNk0 k) _)
          _ = (N+(k:ℝ))^k * (N+(k:ℝ))^((r+1).toNat) := h2
      have step1 : (N+(k:ℝ))^k * (N+(k:ℝ))^((r+1).toNat)
          ≤ (Real.exp N * (k:ℝ)^k) * ((N+1)^((r+1).toNat) * ((k:ℝ)+1)^((r+1).toNat)) :=
        mul_le_mul hP (hpoly k) (pow_nonneg (hNk0 k) _)
          (mul_nonneg (Real.exp_pos _).le (pow_nonneg (Nat.cast_nonneg k) _))
      have hkk2 : Real.exp N * (k:ℝ)^k ≤ Real.exp N * (Real.exp 1^k * (k.factorial:ℝ)) :=
        mul_le_mul_of_nonneg_left hkk (Real.exp_pos _).le
      have hQ2 : (N+1)^((r+1).toNat) * ((k:ℝ)+1)^((r+1).toNat)
          ≤ (N+1)^((r+1).toNat) * (2^((r+1).toNat) * (k:ℝ)^((r+1).toNat)) :=
        mul_le_mul_of_nonneg_left hQ' (pow_nonneg (by linarith [hN]) _)
      have step2 : (Real.exp N * (k:ℝ)^k) * ((N+1)^((r+1).toNat) * ((k:ℝ)+1)^((r+1).toNat))
          ≤ (Real.exp N * (Real.exp 1^k * (k.factorial:ℝ)))
            * ((N+1)^((r+1).toNat) * (2^((r+1).toNat) * (k:ℝ)^((r+1).toNat))) :=
        mul_le_mul hkk2 hQ2
          (mul_nonneg (pow_nonneg (by linarith [hN]) _)
            (pow_nonneg (by have hc : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith) _))
          (mul_nonneg (Real.exp_pos _).le
            (mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (by exact_mod_cast (Nat.factorial_pos k).le)))
      have hA2 : norm (n + (k:ℂ))^((r+1+(k:ℤ)).toNat)
          ≤ (Real.exp N * (Real.exp 1^k * (k.factorial:ℝ)))
            * ((N+1)^((r+1).toNat) * (2^((r+1).toNat) * (k:ℝ)^((r+1).toNat))) :=
        le_trans (le_trans (hA k) hAt) (le_trans step1 step2)
      have hDpos : (0:ℝ) < q^k * (k.factorial:ℝ) :=
        mul_pos (pow_pos hqpos k) (hKpos k hk)
      have heqk : (Real.exp 1/q)^k * (q^k * (k.factorial:ℝ)) = Real.exp 1^k * (k.factorial:ℝ) := by
        rw [div_pow, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero k (ne_of_gt hqpos))]
      rw [div_le_iff₀ hDpos]
      simp only [mul_assoc]
      rw [heqk]
      exact le_trans hA2 (le_of_eq (by ring))
    rw [← summable_nat_add_iff K0]
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => hcore1 (j+K0) (Nat.le_add_left K0 j))
      ((hH1).mul_left ((N+1)^((r+1).toNat) * Real.exp N * 2^((r+1).toNat)))
  · -- Case a = e, r ≤ -2: comparison with a 3/2-power series via Stirling.
    have hq_eq : q = Real.exp 1 := by
      rw [hqdef, ha2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos 1)]
    have hlib : Summable (fun m : ℕ => 1 / ((m:ℝ))^((3/2):ℝ)) :=
      (Real.summable_one_div_nat_rpow (p := (3/2:ℝ))).mpr (by norm_num)
    have hH2 : Summable (fun j : ℕ => 1 / ((((j+(K0+1):ℕ)):ℝ))^((3/2):ℝ)) := by
      have h := (summable_nat_add_iff (K0+1)).mpr hlib
      exact h
    have hkbd : ∀ k : ℕ, K0 ≤ k → norm ((n + (k:ℂ))^(r+1+(k:ℤ)) / ((a^k) * (k.factorial:ℂ)))
        ≤ (Real.exp N * 2^((-(r+1)).toNat)) / ((((k:ℝ)+1) * Real.sqrt ((k:ℝ)+1))) := by
      intro k hk
      rw [hterm k, hzpow k hk, hq_eq]
      have hDpos : (0:ℝ) < Real.exp 1^k * (k.factorial:ℝ) :=
        mul_pos (pow_pos (Real.exp_pos 1) k) (hKpos k hk)
      have hSpos : (0:ℝ) < ((k:ℝ)+1) * Real.sqrt ((k:ℝ)+1) := by
        have hk1' : (0:ℝ) < (k:ℝ)+1 := by
          have h0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
          linarith
        exact mul_pos hk1' (Real.sqrt_pos.mpr hk1')
      rw [div_le_iff₀ hDpos, div_mul_eq_mul_div, le_div_iff₀ hSpos]
      have hp0 : (r+1).toNat = 0 := by omega
      have hdenpos : (0:ℝ) < (N+(k:ℝ))^((-(r+1)).toNat) :=
        pow_pos (by linarith [hNk1 k hk]) _
      have hteq : (N+(k:ℝ))^((r+1+(k:ℤ)).toNat)
          = (N+(k:ℝ))^k / (N+(k:ℝ))^((-(r+1)).toNat) := by
        rw [eq_div_iff hdenpos.ne']
        have h2 := hsplit k hk
        rw [hp0, pow_zero, mul_one] at h2
        exact h2
      have hAt : norm (n + (k:ℂ))^((r+1+(k:ℤ)).toNat)
          ≤ (N+(k:ℝ))^k / (N+(k:ℝ))^((-(r+1)).toNat) := by
        rw [← hteq]
        exact hA k
      have hkk2 : (N+(k:ℝ))^k / (k.factorial:ℝ)
          ≤ Real.exp N * (Real.exp 1^k / Real.sqrt (2 * Real.pi * (k:ℝ))) := by
        have e1 : (N+(k:ℝ))^k / (k.factorial:ℝ)
            = (1 + N/(k:ℝ))^k * ((k:ℝ)^k / (k.factorial:ℝ)) := by
          rw [hNk_eq k (hk1 k hk), mul_pow, mul_div_assoc]
        rw [e1]
        exact mul_le_mul (hexp_base k (hk1 k hk)) (hfact_stir k (hk1 k hk))
          (div_nonneg (pow_nonneg (Nat.cast_nonneg k) _) (Nat.cast_nonneg _))
          (Real.exp_pos _).le
      have hPD : (N+(k:ℝ))^k
          ≤ (Real.exp N * (Real.exp 1^k / Real.sqrt (2 * Real.pi * (k:ℝ)))) * (k.factorial:ℝ) := by
        have h := hkk2
        rwa [div_le_iff₀ (hKpos k hk)] at h
      have hs1nat : (1:ℕ) ≤ (-(r+1)).toNat := by omega
      have h1 : ((k:ℝ)+1) ≤ ((k:ℝ)+1)^((-(r+1)).toNat) :=
        le_self_pow₀ (by have h0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith)
          (ne_of_gt (lt_of_lt_of_le zero_lt_one hs1nat))
      have h2 : (((k:ℝ)+1)/2)^((-(r+1)).toNat) ≤ (N+(k:ℝ))^((-(r+1)).toNat) :=
        pow_le_pow_left₀ (by have h0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith)
          (hNk_half k hk) _
      rw [div_pow] at h2
      have h2s : (0:ℝ) < (2:ℝ)^((-(r+1)).toNat) := pow_pos zero_lt_two _
      rw [div_le_iff₀ h2s] at h2
      have hkp : ((k:ℝ)+1) ≤ 2^((-(r+1)).toNat) * (N+(k:ℝ))^((-(r+1)).toNat) := by
        calc ((k:ℝ)+1) ≤ ((k:ℝ)+1)^((-(r+1)).toNat) := h1
          _ ≤ (N+(k:ℝ))^((-(r+1)).toNat) * 2^((-(r+1)).toNat) := h2
          _ = 2^((-(r+1)).toNat) * (N+(k:ℝ))^((-(r+1)).toNat) := by ring
      have hsqrtge : Real.sqrt ((k:ℝ)+1) ≤ Real.sqrt (2 * Real.pi * (k:ℝ)) := by
        apply Real.sqrt_le_sqrt
        have hk1R : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1 k hk
        have hπ3 : (0:ℝ) ≤ Real.pi - 3 := by linarith [Real.pi_gt_three]
        have hmul : (0:ℝ) ≤ (Real.pi - 3) * (k:ℝ) := mul_nonneg hπ3 (Nat.cast_nonneg k)
        linarith [hmul, hk1R]
      have hsqrt_pos : (0:ℝ) < Real.sqrt (2 * Real.pi * (k:ℝ)) := by
        have hk1' : (0:ℝ) < (k:ℝ)+1 := by
          have h0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
          linarith
        exact lt_of_lt_of_le (Real.sqrt_pos.mpr hk1') hsqrtge
      have key : ((k:ℝ)+1) * Real.sqrt ((k:ℝ)+1)
          ≤ (2^((-(r+1)).toNat) * (N+(k:ℝ))^((-(r+1)).toNat))
            * Real.sqrt (2 * Real.pi * (k:ℝ)) :=
        mul_le_mul hkp hsqrtge (Real.sqrt_nonneg _)
          (mul_nonneg (pow_nonneg zero_le_two _) (pow_nonneg (hNk0 k) _))
      have hnn1 : (0:ℝ) ≤ (Real.exp N * (Real.exp 1^k / Real.sqrt (2 * Real.pi * (k:ℝ))))
          * (k.factorial:ℝ) := by
        apply mul_nonneg
        · apply mul_nonneg (Real.exp_pos _).le
          exact div_nonneg (pow_nonneg (Real.exp_pos _).le k) (Real.sqrt_nonneg _)
        · exact_mod_cast (Nat.factorial_pos k).le
      calc norm (n + (k:ℂ))^((r+1+(k:ℤ)).toNat) * (((k:ℝ)+1) * Real.sqrt ((k:ℝ)+1))
          ≤ ((N+(k:ℝ))^k / (N+(k:ℝ))^((-(r+1)).toNat)) * (((k:ℝ)+1) * Real.sqrt ((k:ℝ)+1)) :=
            mul_le_mul_of_nonneg_right hAt hSpos.le
        _ = (N+(k:ℝ))^k * (((k:ℝ)+1) * Real.sqrt ((k:ℝ)+1)) / (N+(k:ℝ))^((-(r+1)).toNat) := by
            rw [div_mul_eq_mul_div]
        _ ≤ (Real.exp N * 2^((-(r+1)).toNat)) * (Real.exp 1^k * (k.factorial:ℝ)) := by
            rw [div_le_iff₀ hdenpos]
            refine le_trans (mul_le_mul hPD key hSpos.le hnn1) (le_of_eq ?_)
            have hsqrt_ne : Real.sqrt (2 * Real.pi * (k:ℝ)) ≠ 0 := ne_of_gt hsqrt_pos
            field_simp
    rw [← summable_nat_add_iff K0]
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      ((hH2).mul_left (Real.exp N * 2^((-(r+1)).toNat)))
    have h := hkbd (j+K0) (Nat.le_add_left K0 j)
    have hX : ((((j+(K0+1):ℕ)):ℝ)) = ((((j+K0:ℕ)):ℝ)+1) := by
      have e : j + (K0+1) = (j+K0)+1 := by omega
      rw [e, Nat.cast_add, Nat.cast_one]
    rw [hX]
    have hrpowX : ((((j+K0:ℕ)):ℝ)+1) * Real.sqrt ((((j+K0:ℕ)):ℝ)+1)
        = ((((j+K0:ℕ)):ℝ)+1)^((3/2):ℝ) :=
      hrpow _ (by have h0 : (0:ℝ) ≤ ((((j+K0:ℕ)):ℝ)) := Nat.cast_nonneg _; linarith)
    have step : (Real.exp N * 2^((-(r+1)).toNat)) / (((((j+K0:ℕ)):ℝ)+1) * Real.sqrt ((((j+K0:ℕ)):ℝ)+1))
        = (Real.exp N * 2^((-(r+1)).toNat)) * (1/((((j+K0:ℕ)):ℝ)+1)^((3/2):ℝ)) := by
      rw [← hrpowX, div_eq_mul_one_div]
    exact le_trans h (le_of_eq step)

set_option linter.unusedVariables false in
/-- **Absolute convergence of the shifted series in Entry 12.** Let $r$ be an integer and let $n$
and $a$ be complex numbers. Suppose that $|a| > e$, or that $a = e$ and $r \le -2$, and that
$n + k \ne 0$ for every integer $k \ge 0$ with $r + k < 0$. Then
$$\sum_{k=0}^{\infty} \left| \frac{(n+k)^{r+1+k}}{a^k\, k!} \right| < \infty.$$

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, definition (12.1) and Entry 12,
    printed pp. 66-67 / PDF pp. 76-77.
Proves `Wanted` entry `ramanujan_part1_ch3_entry12_summable_succ_n`.
-/
theorem ramanujan_part1_ch3_entry12_summable_succ_n (r : ℤ) (n a : ℂ)
    (ha : norm a > Real.exp 1 ∨ (a = ↑(Real.exp 1) ∧ r ≤ -2))
    (hn : ∀ k : ℤ, 0 ≤ k → r + k < 0 → n + (k : ℂ) ≠ 0) :
    Summable (fun k : ℕ => norm ((n + (k : ℂ)) ^ (r + 1 + (k : ℤ)) / ((a ^ k) * (k.factorial : ℂ)))) :=
  by apply ramanujan_part1_ch3_entry12_summable_succ_n_general <;> assumption

end Entry12SummableSuccN

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
