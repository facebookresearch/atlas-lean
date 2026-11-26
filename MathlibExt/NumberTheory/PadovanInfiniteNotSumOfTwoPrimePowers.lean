/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PadovanSequence
public import MathlibExt.NumberTheory.ThirdOrderPrimePowers
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Tactic.Ring

/-!
# Infinitely many Padovan numbers are not sums of two prime powers

The shifted Padovan terms at indices $45752 + 967206240t$ are odd and satisfy
congruences that rule out a power of two plus any other prime power.
-/

namespace MetaMathlibExt

namespace shiftedPadovan_infinite_not_isSumOfTwoPrimePowers

private abbrev firstIndex : ℕ := 45752
private abbrev progressionStep : ℕ := 967206240

/-- Advance the triple of consecutive terms by one step modulo `m`. -/
private def step (m : ℕ) (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (s.2.1, s.2.2, (s.2.1 + s.1) % m)

private def state (m n : ℕ) : ℕ × ℕ × ℕ :=
  (step m)^[n] (1 % m, 0, 1 % m)

private theorem state_eq (m n : ℕ) :
    state m n = (shiftedPadovanSequence n % m, shiftedPadovanSequence (n + 1) % m,
      shiftedPadovanSequence (n + 2) % m) := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    rw [state, Function.iterate_succ_apply']
    change step m (state m n) = _
    simp only [ih, step, show n + 1 + 2 = n + 3 by omega, shiftedPadovanSequence_add_three,
      ← Nat.add_mod]

/-- A return to the initial state modulo `m` certifies the corresponding
residue at every index of the progression. -/
private theorem progression_modEq (t m period r : ℕ) (hdiv : period ∣ progressionStep)
    (hperiod : state m period = state m 0) (hr : (state m (firstIndex % period)).1 = r)
    (hlt : r < m) : shiftedPadovanSequence (firstIndex + t * progressionStep) ≡ r [MOD m] := by
  obtain ⟨q, hq⟩ := hdiv
  have hindex :
      firstIndex + t * progressionStep =
        firstIndex % period + period * (firstIndex / period + t * q) := by
    rw [hq]
    conv_lhs => rw [← Nat.mod_add_div firstIndex period]
    ring
  have hfixed : (step m)^[period] (state m 0) = state m 0 := hperiod
  have hs : state m (firstIndex + t * progressionStep) = state m (firstIndex % period) := by
    rw [hindex, state, Function.iterate_add_apply, Function.iterate_mul]
    exact congrArg ((step m)^[firstIndex % period]) (Function.iterate_fixed hfixed _)
  have h := congrArg Prod.fst (state_eq m (firstIndex + t * progressionStep))
  rw [hs, hr] at h
  change shiftedPadovanSequence (firstIndex + t * progressionStep) % m = r % m
  rw [Nat.mod_eq_of_lt hlt]
  exact h.symm

private abbrev oddModuli : List ℕ := [3, 7, 13, 85, 241]
private abbrev oddModulus : ℕ := oddModuli.prod
private abbrev residue : ℕ := 4384979

set_option maxRecDepth 1000000 in
private theorem state_period_241 : state 241 58080 = state 241 0 := by
  decide +kernel

set_option maxRecDepth 1000000 in
private theorem state_residue_241 : (state 241 (firstIndex % 58080)).1 = 225 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem progression_odd_modulus (t : ℕ) :
    shiftedPadovanSequence (firstIndex + t * progressionStep) ≡ residue [MOD oddModulus] := by
  have h (m : ℕ) (hm : m ∈ oddModuli) :
      shiftedPadovanSequence (firstIndex + t * progressionStep) ≡ residue [MOD m] := by
    simp only [oddModuli, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact progression_modEq t 3 13 2 (by decide) (by decide) (by decide) (by decide)
    · exact progression_modEq t 7 48 4 (by decide) (by decide) (by decide) (by decide)
    · exact progression_modEq t 13 183 1 (by decide) (by decide) (by decide) (by decide)
    · exact progression_modEq t 85 288 84 (by decide) (by decide) (by decide) (by decide)
    · exact progression_modEq t 241 58080 225 (by decide) state_period_241
        state_residue_241 (by decide)
  have hcoprime : oddModuli.Pairwise Nat.Coprime := by decide
  have combined :=
    (Nat.modEq_list_map_prod_iff (s := id) hcoprime).mpr h
  simpa only [List.map_id] using combined

private theorem pow_mod_period {x m period : ℕ} (h : x ^ period ≡ 1 [MOD m]) (a : ℕ) :
    x ^ a ≡ x ^ (a % period) [MOD m] := by
  calc
    x ^ a = x ^ (a % period + period * (a / period)) :=
      congrArg (x ^ ·) (Nat.mod_add_div a period).symm
    _ = x ^ (a % period) * (x ^ period) ^ (a / period) := by rw [pow_add, pow_mul]
    _ ≡ x ^ (a % period) [MOD m] := by
      simpa using (h.pow (a / period)).mul_left (x ^ (a % period))

/-- For each possible exponent of 2 modulo 24, one row forces a divisor of
the other prime power and rules out powers of that prime modulo a second modulus.
The last entry in each row is the period of that prime's powers modulo the second modulus. -/
private theorem covering :
    ∀ i : Fin 24, ∃ row ∈ [(3, 85, 16), (5, 13, 4), (17, 13, 6), (7, 85, 16), (13, 7, 2),
        (241, 5, 1)],
      let (p, m, period) := row
      p.Prime ∧ p ∣ oddModulus ∧ residue ≡ 2 ^ (i : ℕ) [MOD p] ∧
      m ∣ oddModulus ∧ 0 < period ∧ p ^ period ≡ 1 [MOD m] ∧
      ∀ j : Fin period, ¬ residue ≡ 2 ^ (i : ℕ) + p ^ (j : ℕ) [MOD m] := by
  decide +kernel

private theorem exclude_two_pow {q a b : ℕ} (hq : q.Prime)
    (hs : 2 ^ a + q ^ b ≡ residue [MOD oddModulus]) : False := by
  have ha := pow_mod_period (by decide : 2 ^ 24 ≡ 1 [MOD oddModulus]) a
  let i : Fin 24 := ⟨a % 24, Nat.mod_lt _ (by decide)⟩
  obtain ⟨⟨p, m, period⟩, _, hp, hpdvd, hr, hmdvd, hpos, hcycle, hex⟩ := covering i
  have hz : 2 ^ a + q ^ b ≡ 2 ^ a + 0 [MOD p] := by
    simpa only [add_zero] using ((hs.of_dvd hpdvd).trans hr).trans (ha.of_dvd hpdvd).symm
  have hqeq := Nat.prime_eq_prime_of_dvd_pow hp hq
    (Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' _ hz))
  subst q
  let j : Fin period := ⟨b % period, Nat.mod_lt _ hpos⟩
  exact hex j ((hs.of_dvd hmdvd).symm.trans ((ha.of_dvd hmdvd).add (pow_mod_period hcycle b)))

private theorem exclude_sum {n : ℕ} (h2 : n ≡ 1 [MOD 2]) (hmod : n ≡ residue [MOD oddModulus]) :
    ¬ IsSumOfTwoPrimePowers (n : ℤ) := by
  rintro ⟨p, q, a, b, hp, hq, he⟩
  have heq : n = p ^ a + q ^ b := by exact_mod_cast he
  subst n
  rcases hp.eq_two_or_odd with rfl | hoddP
  · exact exclude_two_pow hq hmod
  rcases hq.eq_two_or_odd with rfl | hoddQ
  · rw [add_comm] at hmod
    exact exclude_two_pow hp hmod
  have hp' : p ≡ 1 [MOD 2] := hoddP
  have hq' : q ≡ 1 [MOD 2] := hoddQ
  have heven := ((hp'.pow a).add (hq'.pow b)).symm.trans h2
  simp only [one_pow] at heven
  exact absurd heven (by decide)

end shiftedPadovan_infinite_not_isSumOfTwoPrimePowers

open shiftedPadovan_infinite_not_isSumOfTwoPrimePowers in
/-- **Infinitely many Padovan numbers are not sums of two prime powers.** Let $(a_n)_{n \ge 0}$ be
the shifted Padovan sequence, given by $a_0 = 1$, $a_1 = 0$, $a_2 = 1$ and
$a_{n+3} = a_{n+1} + a_n$, so that $a_{n+2} = P_n$ is the $n$-th Padovan number, where
$P_0 = P_1 = P_2 = 1$ and $P_{n+3} = P_{n+1} + P_n$. There are infinitely many natural numbers
$k$ such that $a_k$ is not a sum of two prime powers.

The paper proves the stronger statement that $P_k$ is not a sum of two prime powers for every
sufficiently large $k \equiv 45750 \pmod{967206240}$, that is, $a_k$ is not one for every
sufficiently large $k \equiv 45752 \pmod{967206240}$; that form is not stated here.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 3
(`jis-2026-26.2.3-thm-3`). -/
public theorem shiftedPadovan_infinite_not_isSumOfTwoPrimePowers :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (shiftedPadovanSequence k : ℤ)} := by
  apply Set.infinite_of_injective_forall_mem (f := fun t => firstIndex + t * progressionStep)
  · intro t s h
    exact Nat.mul_right_cancel (by decide) (Nat.add_left_cancel h)
  · intro t
    exact exclude_sum (progression_modEq t 2 7 1 (by decide) (by decide) (by decide) (by decide))
      (progression_odd_modulus t)

end MetaMathlibExt
