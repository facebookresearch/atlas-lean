/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Third-order recurrences and sums of two prime powers

A congruence obstruction gives infinitely many quadratic sequences of minimal recurrence order
three in which every term fails to be a sum of two prime powers.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Sums of two prime powers.** An integer $n$ is a sum of two prime powers if
$n = p^a + q^b$ for some primes $p$ and $q$ and some natural numbers $a$ and $b$. Since the
exponents may be $0$, the number $1 = p^0$ counts as a prime power here.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3. -/
public def IsSumOfTwoPrimePowers (n : ℤ) : Prop :=
  ∃ p q a b : ℕ, p.Prime ∧ q.Prime ∧ n = (p : ℤ) ^ a + (q : ℤ) ^ b

/-- **$2$ is a sum of two prime powers.** The integer $2$ is a sum of two prime powers, since
$2 = 2^0 + 2^0$.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3. -/
public theorem isSumOfTwoPrimePowers_two : IsSumOfTwoPrimePowers 2 :=
  ⟨2, 2, 0, 0, Nat.prime_two, Nat.prime_two, by norm_num⟩

/-- **Integers below $2$ are not sums of two prime powers.** If $n$ is an integer with $n < 2$,
then $n$ is not a sum of two prime powers, since every prime power $p^a$ is at least $1$.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3. -/
public theorem not_isSumOfTwoPrimePowers_of_lt_two {n : ℤ} (hn : n < 2) :
    ¬ IsSumOfTwoPrimePowers n := by
  rintro ⟨p, q, a, b, hp, hq, rfl⟩
  have hp1 : (1 : ℤ) ≤ (p : ℤ) ^ a :=
    one_le_pow₀ (by exact_mod_cast hp.pos)
  have hq1 : (1 : ℤ) ≤ (q : ℤ) ^ b :=
    one_le_pow₀ (by exact_mod_cast hq.pos)
  omega

namespace infinite_thirdOrderRecurrence_with_infinite_not_isSum

private abbrev modulus : ℕ := 16 * 3 * 5 * 7 * 13 * 17 * 241

-- This representative is 15 modulo 16. Its residues modulo 3, 5, 7, 13, 17 and 241
-- are 2, 1, 1, 4, 4 and 181, respectively.
private abbrev residue : ℕ := 36846671

/-- Once two powers coincide modulo `m`, all later powers repeat the same cycle. -/
private theorem reduce_power {x m start period : ℕ} (hp : 0 < period)
    (h : x ^ (start + period) ≡ x ^ start [MOD m]) (a : ℕ) :
    ∃ i : Fin (start + period), x ^ a ≡ x ^ (i : ℕ) [MOD m] := by
  induction a with
  | zero => exact ⟨⟨0, by omega⟩, .rfl⟩
  | succ a ih =>
    obtain ⟨i, hi⟩ := ih
    have hs : x ^ (a + 1) ≡ x ^ (i.val + 1) [MOD m] := by
      simpa only [pow_succ] using hi.mul_right x
    by_cases hlt : i.val + 1 < start + period
    · exact ⟨⟨_, hlt⟩, hs⟩
    · rw [show i.val + 1 = start + period by omega] at hs
      exact ⟨⟨start, by omega⟩, hs.trans h⟩

/-- For each possible power of two, one of the six odd primes divides the remaining
summand. Powers of that prime can then be ruled out modulo 16. -/
private theorem covering :
    ∀ i : Fin 28, ∃ d ∈ [3, 5, 7, 13, 17, 241], Nat.Prime d ∧ d ∣ modulus ∧
      residue ≡ 2 ^ (i : ℕ) [MOD d] ∧ d ^ 4 ≡ 1 [MOD 16] ∧
      ∀ j : Fin 4, ¬ residue ≡ 2 ^ (i : ℕ) + d ^ (j : ℕ) [MOD 16] := by
  decide +kernel

private theorem exclude_two_pow {q : ℕ} (hq : q.Prime) (a b : ℕ) :
    ¬ (2 ^ a + q ^ b) ≡ residue [MOD modulus] := by
  intro hs
  obtain ⟨i, hi⟩ := reduce_power (x := 2) (start := 4) (period := 24) (by decide)
    (by decide : 2 ^ 28 ≡ 2 ^ 4 [MOD modulus]) a
  obtain ⟨d, _, hd, hdiv, hr, hcycle, hex⟩ := covering i
  have hz : 2 ^ a + q ^ b ≡ 2 ^ a + 0 [MOD d] := by
    simpa only [Nat.add_zero] using ((hs.of_dvd hdiv).trans hr).trans (hi.of_dvd hdiv).symm
  have hdq := Nat.prime_eq_prime_of_dvd_pow hd hq
    (Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' _ hz))
  subst q
  obtain ⟨j, hj⟩ := reduce_power (start := 0) (period := 4) (by decide) hcycle b
  have h16 : 16 ∣ modulus := by decide
  exact hex j ((hs.of_dvd h16).symm.trans ((hi.of_dvd h16).add hj))

private theorem exclude_sum {n : ℕ} (hn : n ≡ residue [MOD modulus]) :
    ¬ IsSumOfTwoPrimePowers (n : ℤ) := by
  rintro ⟨p, q, a, b, hp, hq, he⟩
  have h : n = p ^ a + q ^ b := by exact_mod_cast he
  subst n
  rcases hp.eq_two_or_odd with rfl | hop
  · exact exclude_two_pow hq a b hn
  rcases hq.eq_two_or_odd with rfl | hoq
  · rw [Nat.add_comm] at hn
    exact exclude_two_pow hp b a hn
  have hodd := hn.of_dvd (show 2 ∣ modulus by decide)
  have hp' : p ≡ 1 [MOD 2] := hop
  have hq' : q ≡ 1 [MOD 2] := hoq
  have heven := ((hp'.pow a).add (hq'.pow b)).symm.trans hodd
  simp only [one_pow] at heven
  exact absurd heven (by decide)

private def quadraticSeq (j n : ℕ) : ℕ := modulus * (j + n ^ 2) + residue

private theorem third_order (j : ℕ) :
    (LinearRecurrence.mk 3 (![1, -3, 3] : Fin 3 → ℤ)).IsSolution
      (fun n => (quadraticSeq j n : ℤ)) := by
  intro n
  simp [Fin.sum_univ_succ, quadraticSeq]
  ring

private theorem no_second_order (j : ℕ) (d : Fin 2 → ℤ)
    (h : (LinearRecurrence.mk 2 d).IsSolution (fun n => (quadraticSeq j n : ℤ))) : False := by
  have step (n : ℕ) :
      (modulus : ℤ) * (j + ((n : ℤ) + 2) ^ 2) + residue =
        d 0 * (modulus * ((j : ℤ) + (n : ℤ) ^ 2) + residue) +
        d 1 * (modulus * ((j : ℤ) + ((n : ℤ) + 1) ^ 2) + residue) := by
    simpa [quadraticSeq, Fin.sum_univ_two] using h n
  -- The second and first differences of the recurrence determine both coefficients.
  have hsum : (modulus : ℤ) * 2 * (d 0 + d 1 - 1) = 0 := by
    linear_combination -step 2 + 2 * step 1 - step 0
  have hdiff : (modulus : ℤ) * (d 0 + 3 * d 1 - 5) = 0 := by
    linear_combination step 0 - step 1
  have hs := (mul_eq_zero.mp hsum).resolve_left (by decide)
  have hd := (mul_eq_zero.mp hdiff).resolve_left (by decide)
  have h₀ := step 0
  rw [show d 0 = -1 by omega, show d 1 = 2 by omega] at h₀
  ring_nf at h₀
  omega

end infinite_thirdOrderRecurrence_with_infinite_not_isSum

open infinite_thirdOrderRecurrence_with_infinite_not_isSum in
/-- **Third-order recurrences with infinitely many terms not sums of two prime powers.** There
are infinitely many sequences $(s_n)_{n \ge 0}$ of positive integers with all of the following
properties: each value is taken by $s_n$ for only finitely many $n$; there are integers
$c_0, c_1, c_2$ with $c_0 \ne 0$ and $s_{n+3} = c_0 s_n + c_1 s_{n+1} + c_2 s_{n+2}$ for all
$n \ge 0$; there are no integers $d_0, d_1$ with $s_{n+2} = d_0 s_n + d_1 s_{n+1}$ for all
$n \ge 0$; and $s_k$ is not a sum of two prime powers for infinitely many $k$.

The condition that each value is taken only finitely often excludes trivial examples such as
periodic sequences taking the value $1$ infinitely often: no integer below $2$ is a sum of two
prime powers.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Corollary 1
(`jis-2026-26.2.3-cor-1`). -/
public theorem infinite_thirdOrderRecurrence_with_infinite_not_isSum :
    Set.Infinite {s : ℕ → ℕ |
      (∀ n : ℕ, 0 < s n) ∧ (∀ m : ℕ, Set.Finite {k : ℕ | s k = m}) ∧
      (∃ c : Fin 3 → ℤ, c 0 ≠ 0 ∧
        (LinearRecurrence.mk 3 c).IsSolution (fun n => (s n : ℤ))) ∧
      (¬ ∃ d : Fin 2 → ℤ,
        (LinearRecurrence.mk 2 d).IsSolution (fun n => (s n : ℤ))) ∧
      Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (s k : ℤ)}} := by
  apply Set.infinite_of_injective_forall_mem (f := quadraticSeq)
  · intro j k he
    have h := congrFun he 0
    simpa [quadraticSeq] using h
  · intro j
    refine ⟨fun n => by simp [quadraticSeq, residue], ?_, ⟨![1, -3, 3], by decide, third_order j⟩,
      fun ⟨d, h⟩ => no_second_order j d h, ?_⟩
    · intro m
      apply (Set.finite_le_nat m).subset
      intro k hk
      change quadraticSeq j k = m at hk
      change k ≤ m
      rw [← hk]
      have hk' : k ≤ k ^ 2 := Nat.le_self_pow (by decide) k
      simp only [quadraticSeq, modulus, residue]
      omega
    · convert Set.infinite_univ (α := ℕ) using 1
      exact Set.eq_univ_of_forall fun n => exclude_sum Nat.ModEq.modulus_mul_add

end

end MetaMathlibExt
