/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.Star

@[expose] public section

namespace MetaMathlibExt

/-- **Rational solutions of $x^y = y^x$.** If $x$ and $y$ are positive rational numbers with
$y < x$ and $x^y = y^x$ (as real powers), then there is a positive integer $v$ such that
$x = (1 + 1/v)^{v+1}$ and $y = (1 + 1/v)^{v}$.

The source states $v \in \mathbb{N}$; the reciprocal $1/v$ forces $v \ge 1$.

Source: Hirotaka Kobayashi, Kota Saito, and Wataru Takeda,
"Transcendence of Values of the Iterated Exponential Function at
Algebraic Points," Journal of Integer Sequences 26 (2023),
Article 23.3.3, Lemma (label x^y=y^x), lines 579–589,
https://cs.uwaterloo.ca/journals/JIS/VOL26/Takeda/tak6.tex
quoting Hurwitz.
Proves `Wanted` entry `rational_parametrization_pow_swap`.
-/
theorem rational_parametrization_pow_swap
    (x y : ℚ) (hx : 0 < x) (hy : 0 < y) (hyx : y < x)
    (h : (x : ℝ) ^ (y : ℝ) = (y : ℝ) ^ (x : ℝ)) :
    ∃ v : ℕ, 0 < v ∧
      x = (1 + 1 / (v : ℚ)) ^ (v + 1) ∧ y = (1 + 1 / (v : ℚ)) ^ v := by
  have hyne : y ≠ 0 := ne_of_gt hy
  have hxrpos : (0 : ℝ) < (x : ℚ) := by exact_mod_cast hx
  have hyrpos : (0 : ℝ) < (y : ℚ) := by exact_mod_cast hy
  set r : ℚ := x / y with hrdef
  have hrgt1 : 1 < r := by
    rw [hrdef, lt_div_iff₀ hy]
    simpa using hyx
  have hRpos : (0 : ℝ) < (r : ℚ) := by
    have h0 : (0 : ℚ) < r := lt_trans zero_lt_one hrgt1
    exact_mod_cast h0
  set A : ℕ := r.num.natAbs with hAdef
  set Dd : ℕ := r.den with hDddef
  have hnumpos : 0 < r.num := Rat.num_pos.mpr (lt_trans zero_lt_one hrgt1)
  have hDd : 0 < Dd := by
    rw [hDddef]
    exact Nat.pos_of_ne_zero r.den_nz
  have hdenq : (0 : ℚ) < ((r.den : ℕ) : ℚ) :=
    by exact_mod_cast Nat.pos_of_ne_zero r.den_nz
  have hcastA : ((A : ℕ) : ℚ) = ((r.num : ℤ) : ℚ) := by
    have hnn : 0 ≤ r.num := le_of_lt hnumpos
    have h2 : r.num.natAbs = r.num.toNat := by
      rw [Int.natAbs_eq_iff]
      exact Or.inl (Int.toNat_of_nonneg hnn).symm
    rw [hAdef, h2]
    exact_mod_cast Int.toNat_of_nonneg hnn
  have hAD : Dd < A := by
    have hDdq : (Dd : ℚ) < (A : ℚ) := by
      rw [hDddef, hcastA]
      have h2 := hrgt1
      rw [← Rat.num_div_den r, lt_div_iff₀ hdenq] at h2
      rwa [one_mul] at h2
    exact_mod_cast hDdq
  set k : ℕ := A - Dd with hkdef
  have hk : A = Dd + k := by omega
  have hk1 : 0 < k := by omega
  have hcop : Nat.Coprime k Dd := by
    rw [hkdef]
    exact (Nat.coprime_sub_self_left (le_of_lt hAD)).mpr r.reduced
  have hrval : r = (A : ℚ) / (Dd : ℚ) := by
    rw [hcastA, hDddef]
    exact (Rat.num_div_den r).symm
  have hlog : (y : ℝ) * Real.log (x : ℝ) = (x : ℝ) * Real.log (y : ℝ) := by
    have h2 := congrArg Real.log h
    rwa [Real.log_rpow hxrpos, Real.log_rpow hyrpos] at h2
  have hrr : ((r : ℚ) : ℝ) = (x : ℝ) / (y : ℝ) := by rw [hrdef, Rat.cast_div]
  have hxReq : (x : ℝ) = (r : ℚ) * (y : ℝ) := by
    rw [hrr, div_mul_cancel₀ _ (ne_of_gt hyrpos)]
  have e1 : Real.log (x : ℝ) = Real.log (r : ℚ) + Real.log (y : ℝ) := by
    conv_lhs => rw [hxReq]
    exact Real.log_mul (ne_of_gt hRpos) (ne_of_gt hyrpos)
  have e2 : (y : ℝ) * (Real.log (r : ℚ) + Real.log (y : ℝ))
      = (r : ℚ) * (y : ℝ) * Real.log (y : ℝ) := by
    rw [← e1, ← hxReq]
    exact hlog
  have hlogR : Real.log (r : ℚ) = (((r : ℚ) : ℝ) - 1) * Real.log (y : ℝ) := by
    have key : (y : ℝ) * Real.log (r : ℚ)
        = (y : ℝ) * ((((r : ℚ) : ℝ) - 1) * Real.log (y : ℝ)) := by
      linear_combination e2
    exact mul_left_cancel₀ (ne_of_gt hyrpos) key
  have heqR : ((r : ℚ) : ℝ) = ((y : ℚ) : ℝ) ^ (((r : ℚ) : ℝ) - 1) := by
    rw [Real.rpow_def_of_pos hyrpos]
    have he : Real.log (y : ℚ) * (((r : ℚ) : ℝ) - 1)
        = Real.log ((r : ℚ) : ℝ) := by
      rw [mul_comm]
      exact hlogR.symm
    rw [he]
    exact (Real.exp_log hRpos).symm
  have hDdne : (Dd : ℚ) ≠ 0 := ne_of_gt (by exact_mod_cast hDd)
  have hADd : (A : ℚ) = (Dd : ℚ) + (k : ℚ) := by exact_mod_cast hk
  have hrsub : r - 1 = (k : ℚ) / (Dd : ℚ) := by
    have h1 : (A : ℚ) / (Dd : ℚ) = 1 + (k : ℚ) / (Dd : ℚ) := by
      rw [hADd, add_div, div_self hDdne]
    rw [hrval, h1]
    ring
  have hexp : ((r : ℚ) : ℝ) - 1 = (k : ℝ) / (Dd : ℝ) := by
    have h2 := congrArg ((↑) : ℚ → ℝ) hrsub
    simp only [Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_natCast] at h2
    exact h2
  have hpowR : ((r : ℚ) : ℝ) ^ Dd = ((y : ℚ) : ℝ) ^ k := by
    have hDdR : (Dd : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hDd)
    have e : ((((r : ℚ) : ℝ)) - 1) * (Dd : ℝ) = (k : ℝ) := by
      rw [hexp, div_mul_cancel₀ _ hDdR]
    conv_lhs => rw [heqR]
    rw [← Real.rpow_natCast (((y : ℚ) : ℝ) ^ (((r : ℚ) : ℝ) - 1)) Dd,
      ← Real.rpow_mul (le_of_lt hyrpos), e, Real.rpow_natCast]
  have hq : y ^ k = r ^ Dd := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact hpowR.symm
  have hnum : y.num ^ k = r.num ^ Dd := by
    have h2 := congrArg Rat.num hq
    rwa [Rat.num_pow, Rat.num_pow] at h2
  have hden : y.den ^ k = r.den ^ Dd := by
    have h2 := congrArg Rat.den hq
    rwa [Rat.den_pow, Rat.den_pow] at h2
  have hden' : y.den ^ k = Dd ^ Dd := by
    rw [hDddef]
    exact hden
  have hC : y.num.natAbs ^ k = A ^ Dd := by
    have h2 := congrArg Int.natAbs hnum
    rw [Int.natAbs_pow, Int.natAbs_pow] at h2
    exact h2
  obtain ⟨t, -, htA⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow hcop hC
  obtain ⟨s, -, hsD⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow hcop hden'
  have hs1 : 1 ≤ s := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [h0, zero_pow (ne_of_gt hk1)] at hsD
    exact (ne_of_gt hDd) hsD
  have hts : s < t := by
    by_contra hcon
    simp only [not_lt] at hcon
    have hle := Nat.pow_le_pow_left hcon k
    omega
  have hkone : k = 1 := by
    by_contra hcon
    have hk2 : 2 ≤ k := by omega
    have hbin : s ^ k + k + 1 ≤ (s + 1) ^ k := by
      have hsk : k ≤ s * k := by
        have hle := mul_le_mul_of_nonneg_right (show (1 : ℕ) ≤ s from hs1) (Nat.zero_le k)
        simpa using hle
      have hsub : ({0, 1, k} : Finset ℕ) ⊆ Finset.range (k + 1) := by
        intro m hm
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hm ⊢
        omega
      have h3 : ∑ i ∈ ({0, 1, k} : Finset ℕ), s ^ i * 1 ^ (k - i) * (↑(k.choose i) : ℕ)
          = 1 + s * k + s ^ k := by
        rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
          Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
          Finset.sum_singleton]
        simp only [pow_zero, pow_one, one_pow, Nat.choose_zero_right, Nat.choose_one_right,
          Nat.choose_self]
        ring
      have happ : (s + 1) ^ k
          = ∑ i ∈ Finset.range (k + 1), s ^ i * 1 ^ (k - i) * (↑(k.choose i) : ℕ) :=
        add_pow s 1 k
      have hle : ∑ i ∈ ({0, 1, k} : Finset ℕ), s ^ i * 1 ^ (k - i) * (↑(k.choose i) : ℕ)
          ≤ ∑ i ∈ Finset.range (k + 1), s ^ i * 1 ^ (k - i) * (↑(k.choose i) : ℕ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)
      rw [h3] at hle
      omega
    have htt : (s + 1) ^ k ≤ t ^ k := Nat.pow_le_pow_left (by omega) k
    omega
  rw [hkone] at hk hq
  have hA1 : (A : ℚ) = (Dd : ℚ) + 1 := by exact_mod_cast hk
  have hrval1 : r = 1 + 1 / (Dd : ℚ) := by
    rw [hrval, hA1, add_div, div_self hDdne]
  have hy1 : y = r ^ Dd := by
    simpa [pow_one] using hq
  have hxr : x = r * y := by
    rw [hrdef, div_mul_cancel₀ _ hyne]
  refine ⟨Dd, hDd, ?_, ?_⟩
  · rw [hxr, hy1, hrval1, ← pow_succ']
  · rw [hy1, hrval1]

end MetaMathlibExt
