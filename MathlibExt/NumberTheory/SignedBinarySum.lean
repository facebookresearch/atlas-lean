/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Int.ModEq

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# One plus a signed sum of powers of two

Choosing the sign of the largest power splits the representable integers
of a fixed length into two translates of the preceding range.
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

end MetaMathlibExt
