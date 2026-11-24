/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Factorization.Basic

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Combinatorics.Colex
import Mathlib.Tactic.Ring

/-!
# Signed sums of powers of two

Choosing the sign of the largest power splits the representable integers
of a fixed length into two translates of the preceding range.
For coefficients in `{-1, m}`, the positions carrying `m` encode a binary integer.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Signed power-of-two sums.** For natural numbers $m$, $s$ and $t$, an integer $n$ is a signed
power-of-two sum with coefficients in $\{-1, m\}$ over the range $s \le j \le t$ if
$n = \sum_{j=s}^{t} \lambda_j 2^j$ for some integers $\lambda_j$ with every
$\lambda_j \in \{-1, m\}$.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Lemma 7. -/
public def IsSignedPowTwoSum (m s t : ℕ) (n : ℤ) : Prop :=
  ∃ lam : ℕ → ℤ, (∀ j ∈ Finset.Icc s t, lam j = -1 ∨ lam j = (m : ℤ)) ∧
    n = ∑ j ∈ Finset.Icc s t, lam j * 2 ^ j

/-- **Example of a signed power-of-two sum.** The integer $1$ can be written as
$\sum_{j=0}^{1} \lambda_j 2^j$ with every $\lambda_j \in \{-1, 3\}$, namely
$1 = 3 \cdot 2^0 + (-1) \cdot 2^1$.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Lemma 7. -/
public theorem isSignedPowTwoSum_one : IsSignedPowTwoSum 3 0 1 1 := by
  refine ⟨fun j => if j = 0 then 3 else -1, ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp
  · have hIcc : Finset.Icc 0 1 = {0, 1} := by decide
    rw [hIcc]
    simp

end

namespace one_add_signedPowTwoSum_iff

/-- The sums with exponents from `1` to `k + 1` attain `2 + 4 * q`
for every `q` between `-2 ^ k` and `2 ^ k - 1`. -/
private theorem exists_coefficients (k : ℕ) (q : ℤ)
    (hlo : -(2 : ℤ) ^ k ≤ q) (hhi : q < 2 ^ k) :
    IsSignedPowTwoSum 1 1 (k + 1) (2 + 4 * q) := by
  induction k generalizing q with
  | zero =>
    simp only [pow_zero] at hlo hhi
    obtain rfl | rfl : q = -1 ∨ q = 0 := by omega
    · exact ⟨fun _ => -1, by simp, by decide⟩
    · exact ⟨fun _ => 1, by simp, by decide⟩
  | succ k ih =>
    let sign : ℤ := if q < 0 then -1 else 1
    have hsign : sign = -1 ∨ sign = 1 := by by_cases h : q < 0 <;> simp [sign, h]
    let r := q - sign * 2 ^ k
    have hr : -(2 : ℤ) ^ k ≤ r ∧ r < 2 ^ k := by
      rw [pow_succ] at hlo hhi
      by_cases h : q < 0 <;> simp [r, sign, h] <;> omega
    obtain ⟨lam, hlam, hsum⟩ := ih r hr.1 hr.2
    refine ⟨Function.update lam (k + 2) sign, ?_, ?_⟩
    · intro j hj
      by_cases he : j = k + 2
      · simpa [he] using hsign
      · rw [Function.update_of_ne he]
        apply hlam
        simp only [Finset.mem_Icc] at hj ⊢
        omega
    · have hprev (j : ℕ) (hj : j ∈ Finset.Icc 1 (k + 1)) :
          Function.update lam (k + 2) sign j * 2 ^ j = lam j * 2 ^ j := by
        have := (Finset.mem_Icc.mp hj).2
        rw [Function.update_of_ne (by omega : j ≠ k + 2)]
      rw [Finset.sum_Icc_succ_top (by omega), Function.update_self,
        Finset.sum_congr rfl hprev, ← hsum, pow_succ, pow_succ]
      dsimp [r]
      ring

end one_add_signedPowTwoSum_iff

/-- **Integers that are one plus a signed sum of powers of two.** An integer $n$ can be written as
$n = 1 + \sum_{j=1}^{k} \lambda_j 2^j$ for some $k \ge 1$ and some
$\lambda_1, \dots, \lambda_k \in \{-1, 1\}$ if and only if $n \equiv 3 \pmod 4$.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Lemma 12 (`jis-2024-24.7.5-lem-12`): an integer `n` can be
written as `1 + ∑_{j=1}^{k} λⱼ * 2^j` for some `k ≥ 1` and coefficients
`λⱼ ∈ {-1, 1}` if and only if `n ≡ 3 [ZMOD 4]`. -/
public theorem one_add_signedPowTwoSum_iff (n : ℤ) :
    (∃ k : ℕ, 1 ≤ k ∧ ∃ lam : ℕ → ℤ,
      (∀ j ∈ Finset.Icc 1 k, lam j = -1 ∨ lam j = 1) ∧
      n = 1 + ∑ j ∈ Finset.Icc 1 k, lam j * 2 ^ j) ↔ n ≡ 3 [ZMOD 4] := by
  constructor
  · rintro ⟨k, hk, lam, hlam, hn⟩
    have htail : 4 ∣ ∑ j ∈ Finset.Ioc 1 k, lam j * 2 ^ j := by
      refine Finset.dvd_sum fun j hj => dvd_mul_of_dvd_right ?_ _
      exact pow_dvd_pow (2 : ℤ) (Finset.mem_Ioc.mp hj).1
    have hsign := hlam 1 (Finset.left_mem_Icc.mpr hk)
    rw [Finset.Icc_eq_cons_Ioc hk, Finset.sum_cons, pow_one] at hn
    change n % 4 = 3 % 4
    rcases hsign with h | h <;> rw [h] at hn <;> omega
  · intro hn
    obtain ⟨q, rfl⟩ := Int.modEq_iff_add_fac.mp hn.symm
    have hbound : (q.natAbs : ℤ) < 2 ^ q.natAbs := by
      exact_mod_cast q.natAbs.lt_two_pow_self
    have hq := Int.natAbs_eq q
    obtain ⟨lam, hlam, hsum⟩ :=
      one_add_signedPowTwoSum_iff.exists_coefficients q.natAbs q (by omega) (by omega)
    exact ⟨q.natAbs + 1, by omega, lam, hlam, by omega⟩

namespace isSignedPowTwoSum_extend

open Finset

/-- Starting with all coefficients equal to `-1`, change the coefficients at offsets in `A`
to `m`. The resulting sum is an affine function of the number with those binary digits. -/
private theorem sum_coefficients (m s t : ℕ) (A : Finset ℕ) (hA : A ⊆ range (t + 1 - s)) :
    (∑ j ∈ Icc s t, (if j - s ∈ A then (m : ℤ) else -1) * 2 ^ j) =
      2 ^ s * (((m : ℤ) + 1) * ↑(∑ i ∈ A, 2 ^ i : ℕ) - (2 ^ (t + 1 - s) - 1)) := by
  have hgeom (l : ℕ) : (∑ i ∈ range l, (2 : ℤ) ^ i) = 2 ^ l - 1 := by
    simpa using geom_sum_mul (2 : ℤ) l
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left, pow_add, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
  calc
    _ = 2 ^ s * ∑ i ∈ range (t + 1 - s),
        (((m : ℤ) + 1) * (if i ∈ A then 2 ^ i else 0) - 2 ^ i) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      split_ifs <;> ring
    _ = _ := by
      rw [sum_sub_distrib, ← mul_sum, sum_ite_mem, inter_eq_right.mpr hA, hgeom]

/-- Encode a signed sum by the binary digits that select coefficient `m`. The use of
`t + 1 - s` also accounts for the empty interval. -/
private theorem iff_exists_bits {m s t : ℕ} {n : ℤ} :
    IsSignedPowTwoSum m s t n ↔ ∃ k : ℕ, k < 2 ^ (t + 1 - s) ∧
      n = 2 ^ s * (((m : ℤ) + 1) * k - (2 ^ (t + 1 - s) - 1)) := by
  constructor
  · rintro ⟨lam, hlam, hn⟩
    let A := (range (t + 1 - s)).filter fun i => lam (s + i) = (m : ℤ)
    have hA : A ⊆ range (t + 1 - s) := filter_subset _ _
    refine ⟨∑ i ∈ A, 2 ^ i, Nat.geomSum_lt le_rfl (fun i hi => mem_range.mp (hA hi)), ?_⟩
    rw [hn, ← sum_coefficients m s t A hA]
    apply sum_congr rfl
    intro j hj
    obtain ⟨hs, ht⟩ := mem_Icc.mp hj
    have hj' : j - s < t + 1 - s := by omega
    simp only [A, mem_filter, mem_range, hj', true_and, Nat.add_sub_of_le hs]
    rcases hlam j hj with h | h <;> simp [h]
  · rintro ⟨k, hk, hn⟩
    have hA : k.bitIndices.toFinset ⊆ range (t + 1 - s) := by
      intro i hi
      apply mem_range.mpr
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
        ((Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)).trans_lt hk)
    refine ⟨fun j => if j - s ∈ k.bitIndices.toFinset then m else -1, ?_, ?_⟩
    · intro j hj
      by_cases hi : j - s ∈ k.bitIndices.toFinset <;> simp [hi]
    · simpa only [sum_coefficients m s t _ hA, sum_toFinset_bitIndices_two_pow] using hn

end isSignedPowTwoSum_extend

/-- **Interval and congruence characterization of signed power-of-two sums.** Let $m \ge 1$ and
$s \le t$ be natural numbers and put $L = t - s + 1$. An integer $n$ can be written as
$\sum_{j=s}^{t} \lambda_j 2^j$ with every $\lambda_j \in \{-1, m\}$ if and only if
$-2^s (2^L - 1) \le n \le 2^s m (2^L - 1)$ and $n \equiv -2^s (2^L - 1) \pmod{2^s (m + 1)}$.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Lemma 7 (`jis-2024-24.7.5-lem-7`): for `0 ≤ s ≤ t` and
`m ≥ 1`, the integers of the form `∑_{j=s}^{t} λⱼ * 2^j` with
`λⱼ ∈ {-1, m}` are precisely the integers `n` in the interval
`[-2^s * (2^{t-s+1} - 1), 2^s * m * (2^{t-s+1} - 1)]` satisfying
`n ≡ -2^s * (2^{t-s+1} - 1) [ZMOD 2^s * (m + 1)]`. -/
public theorem isSignedPowTwoSum_iff (m s t : ℕ) (hm : 1 ≤ m)
    (hst : s ≤ t) (n : ℤ) :
    IsSignedPowTwoSum m s t n ↔
      -(2 : ℤ) ^ s * (2 ^ (t - s + 1) - 1) ≤ n ∧
      n ≤ 2 ^ s * (m : ℤ) * (2 ^ (t - s + 1) - 1) ∧
      n ≡ -(2 : ℤ) ^ s * (2 ^ (t - s + 1) - 1) [ZMOD 2 ^ s * ((m : ℤ) + 1)] := by
  let L := t - s + 1
  let lo := -(2 : ℤ) ^ s * (2 ^ L - 1)
  let step := (2 : ℤ) ^ s * ((m : ℤ) + 1)
  have hstep : 0 < step :=
    mul_pos (pow_pos (by decide) _) (add_pos (Int.natCast_pos.mpr hm) zero_lt_one)
  have hsum (k : ℤ) :
      2 ^ s * (((m : ℤ) + 1) * k - (2 ^ L - 1)) = lo + step * k := by
    dsimp [lo, step]
    ring
  have htop : 2 ^ s * (m : ℤ) * (2 ^ L - 1) = lo + step * (2 ^ L - 1) := by
    dsimp [lo, step]
    ring
  rw [isSignedPowTwoSum_extend.iff_exists_bits,
    show t + 1 - s = L by dsimp [L]; omega]
  change (∃ k : ℕ, k < 2 ^ L ∧ n = _) ↔
    lo ≤ n ∧ n ≤ 2 ^ s * (m : ℤ) * (2 ^ L - 1) ∧ n ≡ lo [ZMOD step]
  simp only [hsum, htop]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : (k : ℤ) < 2 ^ L := by exact_mod_cast hk
    refine ⟨le_add_of_nonneg_right (mul_nonneg hstep.le (Int.natCast_nonneg k)), ?_, ?_⟩
    · exact add_le_add_right (mul_le_mul_of_nonneg_left (by omega) hstep.le) lo
    · exact (Int.modEq_iff_add_fac.mpr ⟨(k : ℤ), rfl⟩).symm
  · rintro ⟨hlo, hhi, hmod⟩
    obtain ⟨k, rfl⟩ := Int.modEq_iff_add_fac.mp hmod.symm
    have hk0 : 0 ≤ k := by simpa [hstep] using hlo
    have hk : k ≤ 2 ^ L - 1 :=
      (mul_le_mul_iff_right₀ hstep).mp (le_of_add_le_add_left hhi)
    lift k to ℕ using hk0
    exact ⟨k, by exact_mod_cast (show (k : ℤ) < 2 ^ L by omega), rfl⟩

/-- **Extending a signed power-of-two sum to a longer range.** Let $m \ge 1$, $s$, $t$ and $\alpha$
be natural numbers, let $\beta = \nu_2(m + 1)$ be the exponent of $2$ in $m + 1$, and suppose that
$s + \beta \le t + 1$ and $2^\alpha \equiv 1 \pmod{(m + 1)/2^\beta}$. If an integer $n$ can be
written as $\sum_{j=s}^{t} \lambda_j 2^j$ with every $\lambda_j \in \{-1, m\}$, then $n$ can also be
written as $\sum_{j=s}^{t+\alpha} \mu_j 2^j$ with every $\mu_j \in \{-1, m\}$.

The source's hypothesis $t \ge s + \beta - 1$ is written as $s + \beta \le t + 1$ to cover the
case $\beta = 0$.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024),
Article 24.7.5, Corollary 8 (`jis-2024-24.7.5-cor-8`): fix `m ≥ 1` and let
`β = ν₂(m + 1)`. If `n` is a signed power-of-two sum over `[s, t]` with
`t ≥ s + β - 1`, then `n` is also expressible over `[s, t + α]` whenever
`2^α ≡ 1 [(m + 1) / 2^β]`. -/
public theorem isSignedPowTwoSum_extend (m s t α : ℕ) (hm : 1 ≤ m)
    (hβ : s + (m + 1).factorization 2 ≤ t + 1)
    (hα : 2 ^ α ≡ 1 [ZMOD ((m + 1) / 2 ^ ((m + 1).factorization 2) : ℤ)])
    (n : ℤ) (h : IsSignedPowTwoSum m s t n) :
    IsSignedPowTwoSum m s (t + α) n := by
  let L := t + 1 - s
  have hlen : t + α + 1 - s = L + α := by dsimp [L]; omega
  have hval : (m + 1).factorization 2 ≤ L := by dsimp [L]; omega
  have hmod : 1 ≡ 2 ^ α [MOD ordCompl[2] (m + 1)] := by
    apply Int.natCast_modEq_iff.mp
    simpa only [Int.natCast_ediv, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
      using hα.symm
  have hdvd : m + 1 ∣ 2 ^ (L + α) - 2 ^ L := by
    calc
      m + 1 = ordProj[2] (m + 1) * ordCompl[2] (m + 1) :=
        (Nat.ordProj_mul_ordCompl_eq_self _ _).symm
      _ ∣ 2 ^ L * (2 ^ α - 1) :=
        Nat.mul_dvd_mul (pow_dvd_pow 2 hval) ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod)
      _ = _ := by rw [pow_add, Nat.mul_sub, Nat.mul_one]
  -- Adding d to the encoded binary integer offsets the change in the all-negative sum.
  obtain ⟨d, hd⟩ := hdvd
  have hstep : (m + 1) * d + 2 ^ L = 2 ^ (L + α) := by
    rw [← hd]
    exact Nat.sub_add_cancel (Nat.pow_le_pow_right (by decide) (Nat.le_add_right L α))
  have hstepZ : ((m : ℤ) + 1) * d + 2 ^ L = 2 ^ (L + α) := by exact_mod_cast hstep
  obtain ⟨k, hk, hn⟩ := isSignedPowTwoSum_extend.iff_exists_bits.mp h
  change k < 2 ^ L at hk
  apply isSignedPowTwoSum_extend.iff_exists_bits.mpr
  rw [hlen]
  refine ⟨k + d, ?_, ?_⟩
  · have : d ≤ (m + 1) * d := Nat.le_mul_of_pos_left d (hm.trans (Nat.le_succ m))
    omega
  · rw [hn, Nat.cast_add, ← hstepZ]
    ring

end MetaMathlibExt
