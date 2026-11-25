/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace Nat

/-- **Number of representations as a sum of three squares.** For a natural number $n$, $r_3(n)$
is the number of ordered triples $(x, y, z)$ of integers in the interval $[-n, n]$ with
$x^2 + y^2 + z^2 = n$. Every integer solution of $x^2 + y^2 + z^2 = n$ lies in this interval
(also for $n = 0$), so $r_3(n)$ is the number of all ordered integer solutions.

Source: Primary source: E. T. Mortenson, arXiv:1702.01627v2,
    `Mortenson-AC-Gauss-arxiv-v2.tex` lines 127-131 (span SHA-256
    `2f2704bfc2f61e5fc50b27df3e14542a0ef19ddd4c7580c7f589f23d38ccff12`,
    file SHA-256 `13bccb58b9397a2bf3fb713779f0d76623513aec5c0f313a3cf95cf8466b5cf3`)
    defining `rₛ` by `Rₛ(q) = ∑ₙ rₛ(n) (-q) ^ n = (∑_{m ∈ ℤ} (-1) ^ m q ^ (m ^ 2)) ^ s`
    (ordered signed integer tuples). Ranked source arXiv:2307.05244 `main.tex`
    lines 78-82 (span SHA-256 `08a4b80a1e84386e7dc97f8d87e1a4f84945d55022722618d59beca2382f9942`)
    identifies the equation `x ^ 2 + y ^ 2 + z ^ 2 = n`. -/
def threeSquareRepresentationCount (n : ℕ) : ℕ :=
  ((((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (-(n : ℤ)) (n : ℤ))) ×ˢ
      (Finset.Icc (-(n : ℤ)) (n : ℤ))).filter
      (fun p : (ℤ × ℤ) × ℤ => p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2 = (n : ℤ))).card

/-- **Numbers congruent to 7 modulo 8 are not sums of three squares.** For a natural number $m$,
let $r_3(m)$ denote the number of ordered triples of integers $(x, y, z)$ with
$x^2 + y^2 + z^2 = m$. For every positive natural number $n$ with $n \equiv 7 \pmod 8$,
$r_3(n) = 0$. This is the case $n \equiv 7 \pmod 8$ of Gauss's formula for $r_3$.

Source: arXiv:2307.05244
    `main.tex` lines 191-199 (span SHA-256
    `39c31ed010dd887f8865ff9c7c36f814bf598c58f691b2954a6d0f62ad1fc1e2`). -/
theorem threeSquareRepresentationCount_eq_zero_of_mod_eight_eq_seven
    (n : ℕ) (hn : 0 < n) (h : n % 8 = 7) :
    threeSquareRepresentationCount n = 0 := by
  have _hn : 0 < n := hn
  have key : ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide
  have h8 : ((8 : ℕ) : ZMod 8) = 0 := by decide
  have hn7 : ((n : ℕ) : ZMod 8) = 7 := by
    obtain ⟨k, hk⟩ : ∃ k, n = 8 * k + 7 := ⟨n / 8, by
      have h1 := Nat.div_add_mod n 8
      rw [h] at h1
      exact h1.symm⟩
    rw [hk, Nat.cast_add, Nat.cast_mul, h8, zero_mul, zero_add]
    decide
  have hempty :
      ((((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ
        (Finset.Icc (-(n : ℤ)) (n : ℤ))) ×ˢ
        (Finset.Icc (-(n : ℤ)) (n : ℤ))).filter
        (fun p : (ℤ × ℤ) × ℤ =>
          p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2 = (n : ℤ))) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [Finset.mem_filter] at hp
    have hcongr := congrArg (fun z : ℤ => (z : ZMod 8)) hp.2
    simp only [Int.cast_add, Int.cast_pow, Int.cast_natCast] at hcongr
    rw [hn7] at hcongr
    exact key _ _ _ hcongr
  unfold threeSquareRepresentationCount
  rw [hempty, Finset.card_empty]

/-- **Removing a factor of 4 preserves the three-square count.** For a natural number $m$, let
$r_3(m)$ denote the number of ordered triples of integers $(x, y, z)$ with $x^2 + y^2 + z^2 = m$.
For every positive natural number $n$ divisible by $4$, $r_3(n) = r_3(n/4)$. This is the case
$4 \mid n$ of Gauss's formula for $r_3$.

Source: arXiv:2307.05244
    `main.tex` lines 191-199 (span SHA-256
    `39c31ed010dd887f8865ff9c7c36f814bf598c58f691b2954a6d0f62ad1fc1e2`). -/
theorem threeSquareRepresentationCount_eq_threeSquareRepresentationCount_div_four
    (n : ℕ) (hn : 0 < n) (h : n % 4 = 0) :
    threeSquareRepresentationCount n = threeSquareRepresentationCount (n / 4) := by
  have _hn : 0 < n := hn
  have _h : n % 4 = 0 := h
  have hn4 : n = 4 * (n / 4) := by omega
  have hmpos : 0 < n / 4 := by omega
  have hnZ : (n : ℤ) = 4 * (((n / 4 : ℕ)) : ℤ) := by
    have hcast := congrArg (fun k : ℕ => ((k : ℕ) : ℤ)) hn4
    simpa [Nat.cast_mul, Nat.cast_ofNat] using hcast
  have hmZ : (0 : ℤ) < (((n / 4 : ℕ)) : ℤ) := Nat.cast_pos.mpr hmpos
  have hm0 : (0 : ℤ) ≤ (((n / 4 : ℕ)) : ℤ) := le_of_lt hmZ
  have hm1 : (1 : ℤ) ≤ (((n / 4 : ℕ)) : ℤ) := by
    rw [← Nat.cast_one]
    exact Nat.cast_le.mpr hmpos
  have key4 : ∀ a b c : ZMod 4, a ^ 2 + b ^ 2 + c ^ 2 = 0 →
      a ^ 2 = 0 ∧ b ^ 2 = 0 ∧ c ^ 2 = 0 := by decide
  have h40nat : ((4 : ℕ) : ZMod 4) = 0 := by decide
  have hnZ4 : ((n : ℕ) : ZMod 4) = 0 := by
    rw [hn4, Nat.cast_mul, h40nat, zero_mul]
  have halve : ∀ z : ℤ, (z : ZMod 4) ^ 2 = 0 → ∃ w, z = 2 * w := by
    intro z hz
    have hcast : (((z ^ 2 : ℤ)) : ZMod 4) = 0 := by
      simpa [Int.cast_pow] using hz
    have h4eq : ((((4 : ℕ))) : ℤ) = (4 : ℤ) := by simp
    have hbase : ((((4 : ℕ))) : ℤ) ∣ z ^ 2 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (z ^ 2) 4).mp hcast
    rw [h4eq] at hbase
    obtain ⟨m, hm | hm⟩ : ∃ m : ℤ, z = 2 * m ∨ z = 2 * m + 1 :=
      ⟨z / 2, by omega⟩
    · exact ⟨m, hm⟩
    · exfalso
      obtain ⟨t, ht⟩ := hbase
      have hexpand : (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 := by ring
      rw [hm, hexpand] at ht
      omega
  have mem_of_sq_le : ∀ a' : ℤ, a' ^ 2 ≤ (((n / 4 : ℕ)) : ℤ) →
      a' ∈ Finset.Icc (-(((n / 4 : ℕ)) : ℤ)) (((n / 4 : ℕ)) : ℤ) := by
    intro a' ha'
    have hmm : (((n / 4 : ℕ)) : ℤ) ≤ (((n / 4 : ℕ)) : ℤ) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hm1 hm0
      simpa [one_mul, pow_two] using hmul
    have hle : a' ^ 2 ≤ (((n / 4 : ℕ)) : ℤ) ^ 2 := le_trans ha' hmm
    have habs : |a'| ≤ (((n / 4 : ℕ)) : ℤ) :=
      abs_le_of_sq_le_sq hle hm0
    rw [Finset.mem_Icc]
    exact abs_le.mp habs
  unfold threeSquareRepresentationCount
  refine Eq.symm (Finset.card_bij
    (fun p _ => ((2 * p.1.1, 2 * p.1.2), 2 * p.2)) ?_ ?_ ?_)
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hmem, heq⟩ := hp
    simp only [Finset.mem_product, Finset.mem_Icc] at hmem
    obtain ⟨⟨⟨h1lo, h1hi⟩, ⟨h2lo, h2hi⟩⟩, ⟨h3lo, h3hi⟩⟩ := hmem
    have e1 : (2 * p.1.1 : ℤ) ^ 2 = 4 * p.1.1 ^ 2 := by
      rw [mul_pow, show (2 : ℤ) ^ 2 = 4 from by decide]
    have e2 : (2 * p.1.2 : ℤ) ^ 2 = 4 * p.1.2 ^ 2 := by
      rw [mul_pow, show (2 : ℤ) ^ 2 = 4 from by decide]
    have e3 : (2 * p.2 : ℤ) ^ 2 = 4 * p.2 ^ 2 := by
      rw [mul_pow, show (2 : ℤ) ^ 2 = 4 from by decide]
    have heq2 : (2 * p.1.1) ^ 2 + (2 * p.1.2) ^ 2 + (2 * p.2) ^ 2 =
        (n : ℤ) := by
      rw [e1, e2, e3, ← mul_add, ← mul_add, heq, ← hnZ]
    have h1' : 2 * p.1.1 ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    have h2' : 2 * p.1.2 ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    have h3' : 2 * p.2 ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    refine Finset.mem_filter.mpr ⟨?_, heq2⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨h1', h2'⟩, h3'⟩
  · intro x _ y _ hxy
    have h1 : 2 * x.1.1 = 2 * y.1.1 :=
      congrArg (fun q : (ℤ × ℤ) × ℤ => q.1.1) hxy
    have h2 : 2 * x.1.2 = 2 * y.1.2 :=
      congrArg (fun q : (ℤ × ℤ) × ℤ => q.1.2) hxy
    have h3 : 2 * x.2 = 2 * y.2 :=
      congrArg (fun q : (ℤ × ℤ) × ℤ => q.2) hxy
    have hx1 : x.1.1 = y.1.1 := by omega
    have hx2 : x.1.2 = y.1.2 := by omega
    have hx3 : x.2 = y.2 := by omega
    have h12 : x.1 = y.1 := Prod.ext hx1 hx2
    exact Prod.ext h12 hx3
  · intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨_, hqeq⟩ := hq
    have hc := congrArg (fun z : ℤ => (z : ZMod 4)) hqeq
    simp only [Int.cast_add, Int.cast_pow, Int.cast_natCast] at hc
    rw [hnZ4] at hc
    obtain ⟨ha0, hb0, hc0⟩ := key4 _ _ _ hc
    obtain ⟨a', ha'⟩ := halve q.1.1 ha0
    obtain ⟨b', hb'⟩ := halve q.1.2 hb0
    obtain ⟨c', hc'⟩ := halve q.2 hc0
    have f1 : (q.1.1 : ℤ) ^ 2 = 4 * a' ^ 2 := by
      rw [ha', mul_pow, show (2 : ℤ) ^ 2 = 4 from by decide]
    have f2 : (q.1.2 : ℤ) ^ 2 = 4 * b' ^ 2 := by
      rw [hb', mul_pow, show (2 : ℤ) ^ 2 = 4 from by decide]
    have f3 : (q.2 : ℤ) ^ 2 = 4 * c' ^ 2 := by
      rw [hc', mul_pow, show (2 : ℤ) ^ 2 = 4 from by decide]
    have hsum4 : 4 * (a' ^ 2 + b' ^ 2 + c' ^ 2) =
        4 * (((n / 4 : ℕ)) : ℤ) := by
      have h1 : 4 * a' ^ 2 + 4 * b' ^ 2 + 4 * c' ^ 2 =
          4 * (((n / 4 : ℕ)) : ℤ) := by
        rw [← f1, ← f2, ← f3, hqeq]
        exact hnZ
      rw [← mul_add, ← mul_add] at h1
      exact h1
    have hsum : a' ^ 2 + b' ^ 2 + c' ^ 2 =
        (((n / 4 : ℕ)) : ℤ) := by omega
    have ha_le : a' ^ 2 ≤ (((n / 4 : ℕ)) : ℤ) := by
      have hba : (0 : ℤ) ≤ b' ^ 2 := sq_nonneg b'
      have hca : (0 : ℤ) ≤ c' ^ 2 := sq_nonneg c'
      omega
    have hb_le : b' ^ 2 ≤ (((n / 4 : ℕ)) : ℤ) := by
      have haa : (0 : ℤ) ≤ a' ^ 2 := sq_nonneg a'
      have hca : (0 : ℤ) ≤ c' ^ 2 := sq_nonneg c'
      omega
    have hc_le : c' ^ 2 ≤ (((n / 4 : ℕ)) : ℤ) := by
      have haa : (0 : ℤ) ≤ a' ^ 2 := sq_nonneg a'
      have hba : (0 : ℤ) ≤ b' ^ 2 := sq_nonneg b'
      omega
    have ha_mem := mem_of_sq_le a' ha_le
    have hb_mem := mem_of_sq_le b' hb_le
    have hc_mem := mem_of_sq_le c' hc_le
    refine ⟨((a', b'), c'), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, hsum⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha_mem, hb_mem⟩, hc_mem⟩
    · change ((2 * a', 2 * b'), 2 * c') = q
      rw [← ha', ← hb', ← hc']

end Nat
