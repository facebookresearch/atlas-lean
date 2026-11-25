/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 5

Binomial recurrence for e^(-x) ∑ (j+1)ⁿ x^(j+1)/j!.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry5

open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)

private theorem entry5_summable (n : ℕ) (x : ℂ) :
    Summable fun j : ℕ => ((↑(j + 1) : ℂ) ^ n * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ)) := by
  simpa using
    (Entry9IiGeneralizedbellgeneratingDefining.ramanujan_part1_ch3_entry9_ii_generalizedbellgenerating_defining
      0 1 x n).summable

/-- **Binomial recurrence for Ramanujan's Bell-type series (Entry 5).** Let $F$ be Ramanujan's
generalized Bell function. For every natural number $n$ and every complex number $x$, write
$f(x, m) = F(0, 1, x; m)$ for natural numbers $m$, and set $f(x, -1) = 1$. Then
$f(x, n) = x \sum_{k=0}^{n} \binom{n}{k} f(x, k-1)$.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 5, printed p. 48 / PDF p.
    58.
Proves `Wanted` entry `ramanujan_part1_ch3_entry5`.
-/
theorem ramanujan_part1_ch3_entry5 (n : ℕ) (x : ℂ) :
    generalizedBellGenerating 0 1 x n = x *
        (Finset.range (n + 1)).sum (fun k => (Nat.choose n k : ℂ) *
            (if k = 0 then 1 else generalizedBellGenerating 0 1 x (k - 1))) := by
  have hLHS : generalizedBellGenerating 0 1 x n = Complex.exp (-x) *
      ∑' (j : ℕ), ((↑(j + 1) : ℂ) ^ n * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ)) := by
    simp only [generalizedBellGenerating, zero_add, one_mul]
  have hsome : ∀ k : ℕ, generalizedBellGenerating 0 1 x k = Complex.exp (-x) *
      ∑' (j : ℕ), ((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ)) := by
    intro k
    simp only [generalizedBellGenerating, zero_add, one_mul]
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : ∀ j : ℕ, ((↑(j + 1) : ℂ) ^ n * (0 : ℂ) ^ (j + 1)
        / (↑(Nat.factorial j) : ℂ)) = 0 := by
      intro j
      rw [zero_pow (by omega : j + 1 ≠ 0), mul_zero, zero_div]
    rw [hLHS, tsum_congr h0, tsum_zero, mul_zero, zero_mul]
  · have hif : ∀ k : ℕ, (Nat.choose n (k + 1) : ℂ) *
        (if k + 1 = 0 then (1 : ℂ) else generalizedBellGenerating 0 1 x (k + 1 - 1))
        = (Nat.choose n (k + 1) : ℂ) * (Complex.exp (-x) *
          ∑' (j : ℕ), ((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ))) := by
      intro k
      have hik : (if k + 1 = 0 then (1 : ℂ) else generalizedBellGenerating 0 1 x (k + 1 - 1))
          = generalizedBellGenerating 0 1 x k := by
        rw [ite_eq_right (by omega), Nat.add_sub_cancel]
      rw [hik, hsome]
    have h0term : (Nat.choose n 0 : ℂ) *
        (if (0 : ℕ) = 0 then (1 : ℂ) else generalizedBellGenerating 0 1 x (0 - 1)) = 1 := by
      rw [ite_eq_left rfl, Nat.choose_zero_right, Nat.cast_one, mul_one]
    have hsplit : (Finset.range (n + 1)).sum (fun k => (Nat.choose n k : ℂ) *
          (if k = 0 then (1 : ℂ) else generalizedBellGenerating 0 1 x (k - 1)))
        = (Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) * (Complex.exp (-x) *
            ∑' (j : ℕ), ((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ)))) + 1 := by
      have step1 : (Finset.range (n + 1)).sum (fun k => (Nat.choose n k : ℂ) *
            (if k = 0 then (1 : ℂ) else generalizedBellGenerating 0 1 x (k - 1)))
          = (Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) *
            (if k + 1 = 0 then (1 : ℂ) else generalizedBellGenerating 0 1 x (k + 1 - 1)))
            + (Nat.choose n 0 : ℂ) * (if (0 : ℕ) = 0 then (1 : ℂ) else generalizedBellGenerating 0 1 x (0 - 1)) :=
        Finset.sum_range_succ' _ _
      have e1 : (Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) *
            (if k + 1 = 0 then (1 : ℂ) else generalizedBellGenerating 0 1 x (k + 1 - 1)))
          = (Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) * (Complex.exp (-x) *
            ∑' (j : ℕ), ((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ)))) :=
        Finset.sum_congr rfl (fun k _ => hif k)
      rw [step1, e1, h0term]
    have hexch : (Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) * (Complex.exp (-x) *
          ∑' (j : ℕ), ((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ))))
        = Complex.exp (-x) * ∑' (j : ℕ), (Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) *
          (((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ)))) := by
      have h1 : ∀ k : ℕ, (Nat.choose n (k + 1) : ℂ) * (Complex.exp (-x) *
            ∑' (j : ℕ), ((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ)))
            = Complex.exp (-x) * ∑' (j : ℕ), (Nat.choose n (k + 1) : ℂ) *
              (((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ))) := by
        intro k
        rw [show (Nat.choose n (k + 1) : ℂ) * (Complex.exp (-x) *
              ∑' (j : ℕ), ((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ)))
              = Complex.exp (-x) * ((Nat.choose n (k + 1) : ℂ) *
                ∑' (j : ℕ), ((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ))) from by
              ring]
        rw [tsum_mul_left]
      have h3 : (Finset.range n).sum (fun k => ∑' (j : ℕ), (Nat.choose n (k + 1) : ℂ) *
            (((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ))))
          = ∑' (j : ℕ), (Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) *
            (((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ)))) :=
        (hasSum_sum (fun k _ => ((entry5_summable k x).mul_left _).hasSum)).tsum_eq.symm
      have h2 : (Finset.range n).sum (fun k => Complex.exp (-x) * ∑' (j : ℕ),
            (Nat.choose n (k + 1) : ℂ) *
            (((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ))))
          = Complex.exp (-x) * ∑' (j : ℕ), (Finset.range n).sum (fun k =>
            (Nat.choose n (k + 1) : ℂ) *
            (((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ)))) := by
        rw [← Finset.mul_sum, h3]
      calc (Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) * (Complex.exp (-x) *
            ∑' (j : ℕ), ((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ))))
          = (Finset.range n).sum (fun k => Complex.exp (-x) * ∑' (j : ℕ),
              (Nat.choose n (k + 1) : ℂ) *
              (((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ)))) :=
            Finset.sum_congr rfl (fun k _ => h1 k)
        _ = Complex.exp (-x) * ∑' (j : ℕ), (Finset.range n).sum (fun k =>
              (Nat.choose n (k + 1) : ℂ) *
              (((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ)))) := h2
    have hP : ∀ j : ℕ, (Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) * ((↑(j + 1) : ℂ)) ^ k)
        = ((((↑(j + 2) : ℂ)) ^ n - 1) / (((↑(j + 1) : ℂ)))) := by
      intro j
      have hj1 : (((↑(j + 1) : ℂ))) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      have hcast2 : ((((j + 2 : ℕ))) : ℂ) = (((↑(j + 1) : ℂ))) + 1 := by
        rw [show j + 2 = (j + 1) + 1 from by omega, Nat.cast_add, Nat.cast_one]
      have hadd := add_pow (((↑(j + 1) : ℂ))) (1 : ℂ) n
      rw [Finset.sum_range_succ'] at hadd
      simp only [pow_zero, one_pow, Nat.choose_zero_right, Nat.cast_one, mul_one] at hadd
      have hfact2 : (Finset.range n).sum (fun m => ((↑(j + 1) : ℂ)) ^ (m + 1) * (Nat.choose n (m + 1) : ℂ))
          = ((↑(j + 1) : ℂ)) * (Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) * ((↑(j + 1) : ℂ)) ^ k) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m _ => by ring)
      rw [hfact2, ← hcast2] at hadd
      have key : ((↑(j + 1) : ℂ)) * ((Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) * ((↑(j + 1) : ℂ)) ^ k))
          = ((((↑(j + 2) : ℂ)) ^ n - 1)) := by
        linear_combination -hadd
      rw [eq_div_iff hj1, mul_comm]
      exact key
    have hterm : ∀ j : ℕ, (Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) *
          (((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ))))
        = ((((↑(j + 2) : ℂ)) ^ n - 1) * x ^ (j + 1) / (↑((j + 1).factorial) : ℂ)) := by
      intro j
      have hj1 : (((↑(j + 1) : ℂ))) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      have hjf : (((↑(Nat.factorial j) : ℂ))) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero j
      have hfact : (↑((j + 1).factorial) : ℂ)
          = (((↑(j + 1) : ℂ))) * (((↑(Nat.factorial j) : ℂ))) := by
        rw [Nat.factorial_succ, Nat.cast_mul]
      have step : (Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) *
            (((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ))))
          = ((Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) * ((↑(j + 1) : ℂ)) ^ k))
            * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ) := by
        have e : (Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) *
              (((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ))))
            = (Finset.range n).sum (fun k => ((Nat.choose n (k + 1) : ℂ) * ((↑(j + 1) : ℂ)) ^ k
              * x ^ (j + 1)) / (↑(Nat.factorial j) : ℂ)) :=
          Finset.sum_congr rfl (fun k _ => by ring)
        rw [e, ← Finset.sum_div, ← Finset.sum_mul]
      rw [step, hP j, hfact]
      field_simp
    have hTU : ∑' (j : ℕ), (Finset.range n).sum (fun k => (Nat.choose n (k + 1) : ℂ) *
          (((↑(j + 1) : ℂ) ^ k * x ^ (j + 1) / (↑(Nat.factorial j) : ℂ))))
        = ∑' (j : ℕ), ((((↑(j + 2) : ℂ)) ^ n - 1) * x ^ (j + 1) / (↑((j + 1).factorial) : ℂ)) :=
      tsum_congr hterm
    have hVsum : Summable fun j : ℕ => (x ^ (j + 1) / (↑((j + 1).factorial) : ℂ)) :=
      (summable_nat_add_iff (f := fun i : ℕ => x ^ i / (↑(i.factorial) : ℂ)) 1).mpr
        (NormedSpace.expSeries_div_summable x)
    have hUshift : Summable fun j : ℕ => x⁻¹ * ((((↑((j + 1) + 1) : ℂ)) ^ n * x ^ ((j + 1) + 1)
        / (↑(((j + 1)).factorial) : ℂ))) :=
      ((summable_nat_add_iff (f := fun i : ℕ => ((↑(i + 1) : ℂ) ^ n * x ^ (i + 1)
        / (↑(i.factorial) : ℂ))) 1).mpr (entry5_summable n x)).mul_left x⁻¹
    have hUsum : Summable fun j : ℕ => ((((↑(j + 2) : ℂ)) ^ n * x ^ (j + 1)
        / (↑((j + 1).factorial) : ℂ))) := by
      refine hUshift.congr (fun j => ?_)
      have c1 : ((j + 1) + 1 : ℕ) = j + 2 := by omega
      have hD : (↑(((j + 1)).factorial) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (j + 1)
      rw [← c1, pow_succ' x (j + 1)]
      field_simp
    have hexp : Complex.exp x = ∑' (i : ℕ), x ^ i / (↑(i.factorial) : ℂ) := by
      conv_lhs => rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ]
      apply tsum_congr
      intro i
      rw [smul_eq_mul, div_eq_mul_inv]
      ring
    have hB : ∑' (j : ℕ), (x ^ (j + 1) / (↑((j + 1).factorial) : ℂ))
        = Complex.exp x - 1 := by
      have hsum := NormedSpace.expSeries_div_summable (𝔸 := ℂ) x
      have hF0 : x ^ 0 / (↑(Nat.factorial 0) : ℂ) = 1 := by simp
      have htail := hsum.tsum_eq_zero_add
      rw [hF0] at htail
      have hVeq : ∀ j : ℕ, (x ^ (j + 1) / (↑((j + 1).factorial) : ℂ))
          = (fun n : ℕ => x ^ n / (↑(n.factorial) : ℂ)) (j + 1) := fun j => rfl
      rw [hexp, tsum_congr hVeq, htail, add_sub_cancel_left]
    have hG : Summable fun i : ℕ => ((↑(i + 1) : ℂ) ^ n * x ^ i / (↑(i.factorial) : ℂ)) := by
      have hmul := (entry5_summable n x).mul_left x⁻¹
      refine hmul.congr (fun i => ?_)
      rw [pow_succ]
      have hD : (↑(i.factorial) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
      field_simp
    have hSS : (∑' (i : ℕ), ((↑(i + 1) : ℂ) ^ n * x ^ (i + 1) / (↑(i.factorial) : ℂ)))
        = x * ∑' (i : ℕ), ((↑(i + 1) : ℂ) ^ n * x ^ i / (↑(i.factorial) : ℂ)) := by
      have e : ∀ i : ℕ, ((↑(i + 1) : ℂ) ^ n * x ^ (i + 1) / (↑(i.factorial) : ℂ))
          = x * (((↑(i + 1) : ℂ) ^ n * x ^ i / (↑(i.factorial) : ℂ))) := by
        intro i
        rw [pow_succ]
        ring
      calc (∑' (i : ℕ), ((↑(i + 1) : ℂ) ^ n * x ^ (i + 1) / (↑(i.factorial) : ℂ)))
          = ∑' (i : ℕ), (x * (((↑(i + 1) : ℂ) ^ n * x ^ i / (↑(i.factorial) : ℂ)))) :=
            tsum_congr e
        _ = x * ∑' (i : ℕ), ((↑(i + 1) : ℂ) ^ n * x ^ i / (↑(i.factorial) : ℂ)) :=
            tsum_mul_left
    have hA : ∑' (j : ℕ), ((((↑(j + 2) : ℂ)) ^ n * x ^ (j + 1) / (↑((j + 1).factorial) : ℂ)))
        = x⁻¹ * (∑' (i : ℕ), ((↑(i + 1) : ℂ) ^ n * x ^ (i + 1) / (↑(i.factorial) : ℂ))) - 1 := by
      have htail := hG.tsum_eq_zero_add
      have hG0 : ((↑((0 : ℕ) + 1) : ℂ)) ^ n * x ^ (0 : ℕ) / (↑(Nat.factorial 0) : ℂ) = 1 := by
        simp
      rw [hG0] at htail
      rw [hSS, ← mul_assoc, inv_mul_cancel₀ hx, one_mul, htail, add_sub_cancel_left]
    have hsplit2 : ∑' (j : ℕ), ((((↑(j + 2) : ℂ)) ^ n - 1) * x ^ (j + 1) / (↑((j + 1).factorial) : ℂ))
        = (∑' (j : ℕ), ((((↑(j + 2) : ℂ)) ^ n * x ^ (j + 1) / (↑((j + 1).factorial) : ℂ))))
          - (∑' (j : ℕ), (x ^ (j + 1) / (↑((j + 1).factorial) : ℂ))) := by
      have e : ∀ j : ℕ, ((((↑(j + 2) : ℂ)) ^ n - 1) * x ^ (j + 1) / (↑((j + 1).factorial) : ℂ))
          = ((((↑(j + 2) : ℂ)) ^ n * x ^ (j + 1) / (↑((j + 1).factorial) : ℂ)))
            - (x ^ (j + 1) / (↑((j + 1).factorial) : ℂ)) := fun j => by ring
      calc ∑' (j : ℕ), ((((↑(j + 2) : ℂ)) ^ n - 1) * x ^ (j + 1) / (↑((j + 1).factorial) : ℂ))
          = ∑' (j : ℕ), (((((↑(j + 2) : ℂ)) ^ n * x ^ (j + 1) / (↑((j + 1).factorial) : ℂ)))
            - (x ^ (j + 1) / (↑((j + 1).factorial) : ℂ))) := tsum_congr e
        _ = (∑' (j : ℕ), ((((↑(j + 2) : ℂ)) ^ n * x ^ (j + 1) / (↑((j + 1).factorial) : ℂ))))
          - (∑' (j : ℕ), (x ^ (j + 1) / (↑((j + 1).factorial) : ℂ))) :=
            (hUsum.hasSum.sub hVsum.hasSum).tsum_eq
    rw [hLHS, hsplit, hexch, hTU, hsplit2, hA, hB]
    have hE : Complex.exp (-x) * Complex.exp x = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    have hx1 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
    generalize (∑' (i : ℕ), ((↑(i + 1) : ℂ) ^ n * x ^ (i + 1) / (↑(i.factorial) : ℂ))) = S
    linear_combination x * hE - (Complex.exp (-x) * S) * hx1

end Entry5

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
