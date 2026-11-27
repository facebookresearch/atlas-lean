/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination

/-!
# The number of Farey fractions with a given numerator

The definition `fareyNumeratorCount` counts the possible denominators, and
`fareyNumeratorCount_formula` evaluates the count using Euler's totient and the Möbius function.
-/

namespace MathlibExt.NumberTheory.FareyNumeratorWanted

open Finset ArithmeticFunction

/-- **Number of Farey fractions with a given numerator.** For natural numbers $n$ and $h$, $N_n(h)$
is the number of integers $b$ with $h \le b \le n$ and $\gcd(h, b) = 1$; for $h \ge 1$ this is
the number of fractions with numerator $h$ in the Farey sequence of order $n$. -/
@[expose] public def fareyNumeratorCount (n h : ℕ) : ℕ :=
  ((Finset.Icc h n).filter (fun b => Nat.Coprime h b)).card

private theorem card_coprime_Ioc_eq_sum (h n : ℕ) (hh : 0 < h) :
    (((Ioc 0 n).filter h.Coprime).card : ℚ) =
      ∑ d ∈ h.divisors, (moebius d : ℚ) * (n / d : ℕ) := by
  have indicator (b : ℕ) :
      (if h.Coprime b then 1 else 0 : ℚ) =
        ∑ d ∈ h.divisors, if d ∣ b then (moebius d : ℚ) else 0 := by
    rw [← sum_filter]
    have hfilter : h.divisors.filter (fun d => d ∣ b) = (h.gcd b).divisors := by
      rw [← Nat.divisors_filter_dvd_of_dvd hh.ne' (Nat.gcd_dvd_left h b)]
      ext d
      simp +contextual [Nat.dvd_gcd_iff, Nat.dvd_of_mem_divisors]
    rw [hfilter]
    have hsum := congrArg (fun f : ArithmeticFunction ℚ => f (h.gcd b))
      (coe_moebius_mul_coe_zeta (R := ℚ))
    simpa only [coe_mul_zeta_apply, intCoe_apply, ArithmeticFunction.one_apply, Nat.Coprime]
      using hsum.symm
  rw [natCast_card_filter]
  simp_rw [indicator]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]

private theorem sum_moebius_div_eq (h n : ℕ) :
    (∑ d ∈ h.divisors, (moebius d : ℚ) * (n / d : ℕ)) =
      (∑ d ∈ h.divisors, (moebius d : ℚ) / d) * n -
        ∑ d ∈ h.divisors, (moebius d : ℚ) * ((n % d : ℚ) / d) := by
  rw [sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro d hd
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hdecomp : (n % d : ℚ) + (d : ℚ) * (n / d : ℕ) = n := by
    exact_mod_cast Nat.mod_add_div n d
  have hquot : ((n / d : ℕ) : ℚ) = ((n : ℚ) - (n % d : ℚ)) / d := by
    apply (eq_div_iff hdq).2
    linear_combination hdecomp
  rw [hquot]
  ring

/-- **Formula for the number of Farey fractions with a given numerator.** Let $h$ and $n$ be
natural numbers with $0 < h < n$, and let $N_n(h)$ be the number of integers $b$ with
$h \le b \le n$ and $\gcd(h, b) = 1$ (the number of fractions with numerator $h$ in the Farey
sequence of order $n$). Then
$$
N_n(h) = \frac{n \varphi(h)}{h} - \sum_{d \mid h} \mu(d) \frac{n \bmod d}{d} -
\varphi(h) + \delta_{1h},
$$
where $\varphi$ is Euler's totient function, $\mu$ is the Möbius function, the sum runs over the
positive divisors $d$ of $h$, $(n \bmod d)/d$ is the fractional part of $n/d$, and $\delta_{1h}$ is
$1$ if $h = 1$ and $0$ otherwise.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
Theorem 1. -/
public theorem fareyNumeratorCount_formula (h n : ℕ)
    (hh : 0 < h) (hhn : h < n) :
    (fareyNumeratorCount n h : ℚ) =
      (Nat.totient h : ℚ) * (n : ℚ) / h -
        ∑ d ∈ h.divisors,
          (ArithmeticFunction.moebius d : ℚ) *
            ((n % d : ℚ) / d) -
        (Nat.totient h : ℚ) + (if h = 1 then 1 else 0) := by
  have hone : Ioc 0 h = Ico 1 (1 + h) := by
    ext b
    simp only [mem_Ioc, mem_Ico]
    omega
  have htotient : ((Ioc 0 h).filter h.Coprime).card = h.totient := by
    rw [hone, Nat.filter_coprime_Ico_eq_totient]
  -- At n = h every divisor of h gives a zero remainder.
  have hrem : (∑ d ∈ h.divisors, (moebius d : ℚ) * ((h % d : ℚ) / d)) = 0 := by
    apply sum_eq_zero
    intro d hd
    simp [Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_divisors hd)]
  have hcoef := card_coprime_Ioc_eq_sum h h hh
  rw [htotient, sum_moebius_div_eq, hrem, sub_zero] at hcoef
  have hcoef' : (∑ d ∈ h.divisors, (moebius d : ℚ) / d) = (h.totient : ℚ) / h :=
    (eq_div_iff (by exact_mod_cast hh.ne')).2 hcoef.symm
  have hdisj := disjoint_filter_filter (p := h.Coprime) (q := h.Coprime)
    (Ioc_disjoint_Ioc_of_le (a := 0) (d := n) (le_refl h))
  have htotal : (((Ioc 0 n).filter h.Coprime).card : ℚ) =
      (h.totient : ℚ) + ((Ioc h n).filter h.Coprime).card := by
    rw [← Ioc_union_Ioc_eq_Ioc (Nat.zero_le h) hhn.le, filter_union,
      card_union_of_disjoint hdisj, Nat.cast_add, htotient]
  -- The endpoint h contributes exactly when h = 1.
  have hend : (fareyNumeratorCount n h : ℚ) =
      (((Ioc h n).filter h.Coprime).card : ℚ) + (if h = 1 then 1 else 0) := by
    rw [fareyNumeratorCount, ← insert_left_Ioc hhn.le, filter_insert]
    simp only [show h.Coprime h ↔ h = 1 by simp [Nat.Coprime]]
    split_ifs <;> simp [card_insert_of_notMem, mem_filter, mem_Ioc]
  rw [card_coprime_Ioc_eq_sum h n hh, sum_moebius_div_eq, hcoef'] at htotal
  linear_combination hend - htotal

end MathlibExt.NumberTheory.FareyNumeratorWanted
