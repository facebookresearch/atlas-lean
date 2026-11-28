/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.FieldSimp
import MathlibExt.Algebra.DeepPowerSumCongruences.Moebius
import all MathlibExt.Algebra.DeepPowerSumCongruences.PowerSumExp

/-!
# The Artin–Hasse exponential as a product

For prime $p$ and a natural number $N$, the Artin–Hasse exponential over $\mathbb{Q}$ agrees
through degree $N$ with the product of $(1 - z^d)^{-\mu(d)/d}$ over $1 \le d \le N$ with
$p \nmid d$, where $\mu$ is the Möbius function.

## References

* Samuele Anni, Alexandru Ghitza, and Anna Medvedovsky, *Elementary Symmetric Functions and Deep
  Power-Sum Congruences*, INTEGERS 24 (2024), Article A46, pp. 1–26, §3.6, Proposition 27 and
  Lemma 28.
* Jacob Lurie, *Lecture 7: The Artin-Hasse Exponential*, lecture notes (2018), pp. 2–3,
  Lemma 6, Definition 7 and Exercise 8, for the logarithmic coefficient argument cited in §3.6.
* `MathlibExt.Algebra.DeepPowerSumCongruences.PowerSumExp` supplies `subst_exp_sum` and
  `coeff_subst_exp_congr`; `MathlibExt.Algebra.DeepPowerSumCongruences.Moebius` supplies
  `sum_moebius_divisors_not_dvd_prime`.
-/

namespace MetaMathlibExt

open Finset PowerSeries
open exp_signedPowerSumSeries_eq_sum_partitions

/-- **The Artin–Hasse exponential as a product.** Let $p$ be a prime, let $\mu$ be the Möbius
function and let $F(z) = \exp\big(\sum_{j \ge 0} z^{p^j} / p^j\big) \in \mathbb{Q}[[z]]$ be the
Artin–Hasse exponential. For $d \ge 1$ and $a \in \mathbb{Q}$ write
$(1 - z^d)^a = \exp\big(a \log(1 - z^d)\big)$, where $\log(1 - z^d) = -\sum_{k \ge 1} z^{dk}/k$.
Then for every $N \ge 0$, $F$ has the same coefficients of $z^0, \dots, z^N$ as the finite product
of the series $(1 - z^d)^{-\mu(d)/d}$ over the integers $1 \le d \le N$ not divisible by $p$.
Since the factors with $d > N$ are $1 + O(z^{N+1})$, this is the identity
$F(z) = \prod_{p \nmid d} (1 - z^d)^{-\mu(d)/d}$ read coefficientwise.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 27 (`integers-2024-A46-prop-27`). -/
public theorem artinHasse_eq_prod_one_sub_pow (p : ℕ) [Fact p.Prime] (N : ℕ) :
    PowerSeries.trunc (N + 1) (PowerSeries.subst
      (PowerSeries.mk fun m : ℕ => if p ^ Nat.log p m = m then (m : ℚ)⁻¹ else 0)
      (PowerSeries.exp ℚ) : PowerSeries ℚ) =
    PowerSeries.trunc (N + 1) (∏ d ∈ Finset.Icc 1 N with ¬ p ∣ d,
      (PowerSeries.subst (PowerSeries.mk fun m : ℕ => if m ≠ 0 ∧ d ∣ m then
          (-(ArithmeticFunction.moebius d : ℚ) / d) * (-(d : ℚ) / m) else 0)
        (PowerSeries.exp ℚ) : PowerSeries ℚ)) := by
  let F : PowerSeries ℚ := .mk fun m => if p ^ Nat.log p m = m then (m : ℚ)⁻¹ else 0
  let L (d : ℕ) : PowerSeries ℚ := .mk fun m => if m ≠ 0 ∧ d ∣ m then
    (-(ArithmeticFunction.moebius d : ℚ) / d) * (-(d : ℚ) / m) else 0
  let s := (Icc 1 N).filter fun d => ¬ p ∣ d
  change trunc (N + 1) ((exp ℚ).subst F) = trunc (N + 1) (∏ d ∈ s, (exp ℚ).subst (L d))
  have hF : constantCoeff F = 0 := by simp [F]
  have hL (d : ℕ) : constantCoeff (L d) = 0 := by simp [L]
  rw [← subst_exp_sum L hL s]
  have hsum : constantCoeff (∑ d ∈ s, L d) = 0 := by simp [hL]
  ext n
  by_cases hn : n < N + 1
  · simp only [coeff_trunc, ite_eq_left hn]
    refine coeff_subst_exp_congr hF hsum fun j hj => ?_
    by_cases hj₀ : j = 0
    · rw [hj₀, coeff_zero_eq_constantCoeff, hF, hsum]
    -- In degree j, the surviving logarithms are indexed by the divisors of j prime to p.
    have hdiv : s.filter (· ∣ j) = j.divisors.filter (fun d => ¬ p ∣ d) := by
      ext d
      simp only [s, mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · exact fun ⟨⟨_, hpd⟩, hdj⟩ => ⟨⟨hdj, hj₀⟩, hpd⟩
      · rintro ⟨⟨hdj, _⟩, hpd⟩
        have hjpos := Nat.pos_of_ne_zero hj₀
        exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hdj hjpos, (Nat.le_of_dvd hjpos hdj).trans (by omega)⟩,
          hpd⟩, hdj⟩
    have hcoeff (d : ℕ) (hd : d ∈ s) :
        coeff j (L d) = if d ∣ j then (ArithmeticFunction.moebius d : ℚ) / j else 0 := by
      by_cases hdj : d ∣ j
      · have hd₀ : d ≠ 0 := Nat.ne_of_gt (mem_Icc.mp (mem_filter.mp hd).1).1
        have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd₀
        have hjQ : (j : ℚ) ≠ 0 := by exact_mod_cast hj₀
        simp only [L, coeff_mk, ite_eq_left (And.intro hj₀ hdj), ite_eq_left hdj]
        field_simp
      · have hnot : ¬ (j ≠ 0 ∧ d ∣ j) := fun h => hdj h.2
        simp only [L, coeff_mk, ite_eq_right hnot, ite_eq_right hdj]
    calc
      coeff j F = ((if p ^ Nat.log p j = j then 1 else 0 : ℤ) : ℚ) / j := by
        by_cases h : p ^ Nat.log p j = j <;> simp [F, h, one_div]
      _ = (∑ d ∈ j.divisors with ¬ p ∣ d, (ArithmeticFunction.moebius d : ℚ)) / j := by
        rw [← Int.cast_sum, sum_moebius_divisors_not_dvd_prime (Fact.out : p.Prime) hj₀]
      _ = coeff j (∑ d ∈ s, L d) := by
        rw [map_sum, ← hdiv, div_eq_mul_inv, sum_mul, sum_filter]
        exact sum_congr rfl fun d hd => (hcoeff d hd).symm
  · simp only [coeff_trunc, ite_eq_right hn]

end MetaMathlibExt
