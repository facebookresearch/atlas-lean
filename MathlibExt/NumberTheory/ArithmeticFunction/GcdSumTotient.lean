/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace MetaMathlibExt

/-! # Gcd-sum identity via Euler's totient
-/

private theorem card_filter_dvd_Icc (n d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 n).filter (fun j => d ∣ j)).card = n / d := by
  have h : (Finset.Icc 1 n).filter (fun j => d ∣ j)
      = (Finset.Icc 1 (n / d)).image (fun k => d * k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · intro hj
      obtain ⟨⟨h1j, hjn⟩, hdvdj⟩ := hj
      obtain ⟨k, hk⟩ := hdvdj
      have hk0 : k ≠ 0 := by
        intro hk0
        subst hk0
        simp at hk
        omega
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      refine ⟨k, ⟨hkpos, ?_⟩, hk.symm⟩
      · have hdk : d * k ≤ n := by omega
        rw [Nat.mul_comm] at hdk
        exact (Nat.le_div_iff_mul_le hd).mpr hdk
    · intro hj
      obtain ⟨k, ⟨h1k, hkn⟩, rfl⟩ := hj
      refine ⟨⟨?_, ?_⟩, Dvd.intro k rfl⟩
      · calc 1 ≤ d * 1 := by rw [Nat.mul_one]; exact hd
          _ ≤ d * k := Nat.mul_le_mul_left d h1k
      · have h2 : d * k ≤ d * (n / d) := Nat.mul_le_mul_left d hkn
        have h3 : d * (n / d) ≤ n := by
          rw [Nat.mul_comm]; exact Nat.div_mul_le_self n d
        exact le_trans h2 h3
  rw [h]
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b hab
    simp only at hab
    exact Nat.mul_left_cancel hd hab

/--
**The gcd-sum as a divisor sum of totients.** For every positive integer $n$,
$\sum_{j=1}^{n} \gcd(j, n) = n \sum_{d \mid n} \varphi(d)/d$, where $\varphi$ is Euler's totient
function and $d$ runs over the positive divisors of $n$.

Grouping the terms with $\gcd(j, n) = e$, of which there are $\varphi(n/e)$, shows that the sum
equals $\sum_{e \mid n} e \, \varphi(n/e)$.

Proves `Wanted` entry `gcd_sum_eq_totient_sum`.

Source: Kevin A. Broughan,
"The Gcd-Sum Function,"
Journal of Integer Sequences 4 (2001), Article 01.2.2,
Theorem 2.3 (equation label 6), lines 220–226,
https://cs.uwaterloo.ca/journals/JIS/VOL4/BROUGHAN/gcdsum.tex
-/
theorem gcd_sum_eq_totient_sum
    (n : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.Icc 1 n, (Nat.gcd j n : ℚ)) =
      (n : ℚ) * ∑ d ∈ Nat.divisors n, (Nat.totient d : ℚ) / (d : ℚ) := by
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hterm : ∀ j ∈ Finset.Icc 1 n,
      ((Nat.gcd j n : ℕ) : ℚ) = ∑ d ∈ Nat.divisors (Nat.gcd j n), ((Nat.totient d : ℕ) : ℚ) := by
    intro j hj
    have h := Nat.sum_totient (Nat.gcd j n)
    have hQ : (∑ d ∈ Nat.divisors (Nat.gcd j n), ((Nat.totient d : ℕ) : ℚ))
        = ((Nat.gcd j n : ℕ) : ℚ) := by
      have hcast := congrArg (Nat.cast : ℕ → ℚ) h
      simp only [Nat.cast_sum] at hcast
      exact hcast
    exact hQ.symm
  rw [Finset.sum_congr rfl hterm]
  have hfilter : ∀ j ∈ Finset.Icc 1 n,
      Nat.divisors (Nat.gcd j n) = (Nat.divisors n).filter (fun d => d ∣ j) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjpos : 0 < j := hj1
    have hgcdpos : 0 < Nat.gcd j n := Nat.gcd_pos_of_pos_left n hjpos
    have hgcd : Nat.gcd j n ≠ 0 := ne_of_gt hgcdpos
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · intro hd'
      obtain ⟨hdvd, _⟩ := hd'
      have hdj : d ∣ j := hdvd.trans (Nat.gcd_dvd_left j n)
      have hdn : d ∣ n := hdvd.trans (Nat.gcd_dvd_right j n)
      exact ⟨⟨hdn, hn0⟩, hdj⟩
    · intro hd'
      obtain ⟨⟨hdn, _⟩, hdj⟩ := hd'
      exact ⟨Nat.dvd_gcd hdj hdn, hgcd⟩
  have hrewrite : ∀ j ∈ Finset.Icc 1 n,
      (∑ d ∈ Nat.divisors (Nat.gcd j n), ((Nat.totient d : ℕ) : ℚ))
      = ∑ d ∈ Nat.divisors n, (if d ∣ j then ((Nat.totient d : ℕ) : ℚ) else 0) := by
    intro j hj
    rw [hfilter j hj]
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl hrewrite]
  rw [Finset.sum_comm]
  have hinner : ∀ d ∈ Nat.divisors n,
      (∑ j ∈ Finset.Icc 1 n, (if d ∣ j then ((Nat.totient d : ℕ) : ℚ) else 0))
      = ((Nat.totient d : ℕ) : ℚ) * ((n / d : ℕ) : ℚ) := by
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have : (∑ j ∈ Finset.Icc 1 n, (if d ∣ j then ((Nat.totient d : ℕ) : ℚ) else 0))
        = ∑ j ∈ (Finset.Icc 1 n).filter (fun j => d ∣ j), ((Nat.totient d : ℕ) : ℚ) := by
      rw [Finset.sum_filter]
    rw [this]
    rw [Finset.sum_const, nsmul_eq_mul, card_filter_dvd_Icc n d hdpos]
    ring
  rw [Finset.sum_congr rfl hinner]
  have hfinal : ∀ d ∈ Nat.divisors n,
      ((Nat.totient d : ℕ) : ℚ) * (((n / d : ℕ)) : ℚ)
      = (n : ℚ) * (((Nat.totient d : ℕ) : ℚ) / (d : ℚ)) := by
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdQ : ((d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hdpos
    have hdiv : (((n / d : ℕ)) : ℚ) = (n : ℚ) / (d : ℚ) := Nat.cast_div hdn hdQ
    rw [hdiv]
    field_simp
  rw [Finset.sum_congr rfl hfinal]
  rw [← Finset.mul_sum]

end MetaMathlibExt
