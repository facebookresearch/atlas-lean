/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PerrinSequence
public import MathlibExt.NumberTheory.ThirdOrderPrimePowers
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Infinitely many Perrin numbers are not sums of two prime powers

The Perrin sequence is periodic modulo every positive integer. For indices in
one arithmetic progression, its residues modulo the primes $3$, $5$, $17$, $7$,
$13$ and $241$ force any prime-power decomposition to use one of those primes,
and extra congruences modulo $160$, $31$, $7$ and $5$ rule out each of those
primes. The main result is that infinitely many Perrin numbers are not sums of
two prime powers.
-/

namespace MetaMathlibExt

namespace perrin_infinite_not_isSumOfTwoPrimePowers

/-- The first index of the arithmetic progression of Perrin indices used here:
the smallest index in the progression from the source. -/
private abbrev firstIndex : ℕ := 472190

/-- The step of the arithmetic progression of Perrin indices used here: the
least common multiple of the periods of the Perrin sequence modulo
$2, 3, 5, 17, 7, 13, 241, 160$ and $31$. -/
private abbrev progressionStep : ℕ := 320145265440

/-- One step of the Perrin recurrence, applied to a triple of consecutive
terms reduced modulo `m`. -/
private def stepOf (m : ℕ) (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (s.2.1, s.2.2, (s.2.1 + s.1) % m)

/-- The triple of consecutive Perrin terms starting at `n`, reduced modulo
`m`, computed by iterating the recurrence. -/
private def triples (m : ℕ) (n : ℕ) : ℕ × ℕ × ℕ :=
  (stepOf m)^[n] (3 % m, 0, 2 % m)

private theorem triples_succ (m n : ℕ) :
    triples m (n + 1) = stepOf m (triples m n) :=
  Function.iterate_succ_apply' _ _ _

private theorem triples_eq (m n : ℕ) :
    triples m n =
      (perrinSequence n % m, perrinSequence (n + 1) % m,
        perrinSequence (n + 2) % m) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [triples_succ, ih]
      change (perrinSequence (n + 1) % m, perrinSequence (n + 2) % m,
        (perrinSequence (n + 1) % m + perrinSequence n % m) % m) = _
      have hrec : perrinSequence (n + 3) =
          perrinSequence (n + 1) + perrinSequence n := by
        have h := perrinSequence.eq_4 (n := n)
        simpa using h
      rw [show n + 1 + 2 = n + 3 by omega, hrec]
      congr 1
      congr 1
      exact (Nat.add_mod _ _ _).symm

/-- If the triple of Perrin terms repeats after `P` steps modulo `m`, it also
repeats after `P` steps starting from any index. -/
private theorem triples_add_period (m P : ℕ) (hP : triples m P = triples m 0)
    (n : ℕ) :
    triples m (n + P) = triples m n := by
  unfold triples at *
  rw [Function.iterate_add_apply, hP]
  simp

/-- The conclusion of `triples_add_period`, iterated over any number of
periods. -/
private theorem triples_add_mul_period (m P : ℕ) (hP : triples m P = triples m 0)
    (q n : ℕ) :
    triples m (n + q * P) = triples m n := by
  induction q with
  | zero => simp
  | succ q ih =>
      have h1 : n + (q + 1) * P = (n + q * P) + P := by ring
      rw [h1, triples_add_period m P hP, ih]

/-- Equality of triples modulo `m` gives the corresponding congruence of
Perrin terms. -/
private theorem modEq_of_triples (m : ℕ) {a b : ℕ} (h : triples m a = triples m b) :
    perrinSequence a ≡ perrinSequence b [MOD m] := by
  have h' := congrArg Prod.fst h
  rw [triples_eq m a, triples_eq m b] at h'
  exact h'

/-- The period of the Perrin sequence modulo each modulus used below, checked
by evaluating the triple iteration. -/
private theorem period_two : triples 2 7 = triples 2 0 := by decide

private theorem period_three : triples 3 13 = triples 3 0 := by decide

private theorem period_five : triples 5 24 = triples 5 0 := by decide

set_option maxRecDepth 100000 in
private theorem period_seventeen : triples 17 288 = triples 17 0 := by decide

private theorem period_seven : triples 7 48 = triples 7 0 := by decide

set_option maxRecDepth 100000 in
private theorem period_thirteen : triples 13 183 = triples 13 0 := by decide

set_option maxRecDepth 1000000 in
private theorem period_twoFortyOne : triples 241 58080 = triples 241 0 := by decide

set_option maxRecDepth 100000 in
private theorem period_oneSixty : triples 160 336 = triples 160 0 := by decide

set_option maxRecDepth 100000 in
private theorem period_thirtyOne : triples 31 993 = triples 31 0 := by decide

/-- The value of the first component of the triple at the residue of
`firstIndex` modulo the period, for each modulus used below. -/
private theorem triples_two : (triples 2 5).1 = 1 := by decide

private theorem triples_three : (triples 3 4).1 = 2 := by decide

private theorem triples_five : (triples 5 14).1 = 1 := by decide

set_option maxRecDepth 100000 in
private theorem triples_seventeen : (triples 17 158).1 = 13 := by decide

private theorem triples_seven : (triples 7 14).1 = 2 := by decide

private theorem triples_thirteen : (triples 13 50).1 = 4 := by decide

set_option maxRecDepth 100000 in
private theorem triples_twoFortyOne : (triples 241 7550).1 = 177 := by decide

private theorem triples_oneSixty : (triples 160 110).1 = 1 := by decide

set_option maxRecDepth 100000 in
private theorem triples_thirtyOne : (triples 31 515).1 = 11 := by decide

/-- A Perrin value reduced modulo `m`, read off from the triple at the same
index. -/
private theorem value_modEq (m r v : ℕ) (hstate : (triples m r).1 = v) (hvlt : v < m) :
    perrinSequence r ≡ v [MOD m] := by
  have h : perrinSequence r % m = v := by
    have h' := congrArg Prod.fst (triples_eq m r)
    rw [hstate] at h'
    exact h'.symm
  change perrinSequence r % m = v % m
  rw [h, Nat.mod_eq_of_lt hvlt]

/-- The residue of the Perrin term at `firstIndex` modulo `m`, obtained from
the period and the triple at the residue of the index. -/
private theorem firstIndex_modEq (m P r v : ℕ) (hP : triples m P = triples m 0)
    (hk0 : firstIndex = r + (firstIndex / P) * P) (hv : perrinSequence r ≡ v [MOD m]) :
    perrinSequence firstIndex ≡ v [MOD m] := by
  have h : triples m firstIndex = triples m r := by
    rw [hk0]
    exact triples_add_mul_period m P hP (firstIndex / P) r
  exact (modEq_of_triples m h).trans hv

private theorem firstIndex_mod_two : perrinSequence firstIndex ≡ 1 [MOD 2] :=
  firstIndex_modEq 2 7 5 1 period_two (by decide)
    (value_modEq 2 5 1 triples_two (by norm_num))

private theorem firstIndex_mod_three : perrinSequence firstIndex ≡ 2 [MOD 3] :=
  firstIndex_modEq 3 13 4 2 period_three (by decide)
    (value_modEq 3 4 2 triples_three (by norm_num))

private theorem firstIndex_mod_five : perrinSequence firstIndex ≡ 1 [MOD 5] :=
  firstIndex_modEq 5 24 14 1 period_five (by decide)
    (value_modEq 5 14 1 triples_five (by norm_num))

private theorem firstIndex_mod_seventeen :
    perrinSequence firstIndex ≡ 13 [MOD 17] :=
  firstIndex_modEq 17 288 158 13 period_seventeen (by decide)
    (value_modEq 17 158 13 triples_seventeen (by norm_num))

private theorem firstIndex_mod_seven : perrinSequence firstIndex ≡ 2 [MOD 7] :=
  firstIndex_modEq 7 48 14 2 period_seven (by decide)
    (value_modEq 7 14 2 triples_seven (by norm_num))

private theorem firstIndex_mod_thirteen : perrinSequence firstIndex ≡ 4 [MOD 13] :=
  firstIndex_modEq 13 183 50 4 period_thirteen (by decide)
    (value_modEq 13 50 4 triples_thirteen (by norm_num))

private theorem firstIndex_mod_twoFortyOne :
    perrinSequence firstIndex ≡ 177 [MOD 241] :=
  firstIndex_modEq 241 58080 7550 177 period_twoFortyOne (by decide)
    (value_modEq 241 7550 177 triples_twoFortyOne (by norm_num))

private theorem firstIndex_mod_oneSixty : perrinSequence firstIndex ≡ 1 [MOD 160] :=
  firstIndex_modEq 160 336 110 1 period_oneSixty (by decide)
    (value_modEq 160 110 1 triples_oneSixty (by norm_num))

private theorem firstIndex_mod_thirtyOne :
    perrinSequence firstIndex ≡ 11 [MOD 31] :=
  firstIndex_modEq 31 993 515 11 period_thirtyOne (by decide)
    (value_modEq 31 515 11 triples_thirtyOne (by norm_num))

/-- Advancing the index by one progression step preserves the Perrin term
modulo `m`, whenever the period `P` divides the step. -/
private theorem add_step_modEq (m P : ℕ) (hP : triples m P = triples m 0)
    (hdiv : P ∣ progressionStep) (n : ℕ) :
    perrinSequence (n + progressionStep) ≡ perrinSequence n [MOD m] := by
  obtain ⟨q, hq⟩ := hdiv
  have h : triples m (n + progressionStep) = triples m n := by
    rw [hq, mul_comm P q]
    exact triples_add_mul_period m P hP q n
  exact modEq_of_triples m h

/-- Advancing the index by any number of progression steps preserves the
Perrin term modulo `m`. -/
private theorem add_mul_step_modEq (m P : ℕ) (hP : triples m P = triples m 0)
    (hdiv : P ∣ progressionStep) (t n : ℕ) :
    perrinSequence (n + t * progressionStep) ≡ perrinSequence n [MOD m] := by
  induction t with
  | zero =>
      simp only [Nat.zero_mul, Nat.add_zero]
      exact Nat.ModEq.refl _
  | succ t ih =>
      have h1 : n + (t + 1) * progressionStep =
          (n + t * progressionStep) + progressionStep := by ring
      rw [h1]
      exact (add_step_modEq m P hP hdiv _).trans ih

/-- If `x ^ b ≡ 1` modulo `d`, then `x ^ a` modulo `d` depends only on `a`
modulo `b`. -/
private theorem pow_modEq_of_cycle {x d b a a' : ℕ} (hc : x ^ b ≡ 1 [MOD d])
    (h : a ≡ a' [MOD b]) : x ^ a ≡ x ^ a' [MOD d] := by
  have key : ∀ e : ℕ, x ^ e ≡ x ^ (e % b) [MOD d] := by
    intro e
    have he : e = b * (e / b) + e % b := (Nat.div_add_mod e b).symm
    conv_lhs => rw [he, pow_add, pow_mul]
    have hc' : (x ^ b) ^ (e / b) ≡ 1 ^ (e / b) [MOD d] := hc.pow _
    rw [one_pow] at hc'
    simpa using hc'.mul_right (x ^ (e % b))
  have hmod : a % b = a' % b := h
  have hxy : x ^ (a % b) = x ^ (a' % b) := by rw [hmod]
  exact (key a).trans (hxy ▸ (key a').symm)

/-- Once two powers coincide modulo `m`, all later powers repeat the same
cycle, and the representative keeps the exponent's residue class modulo any
divisor of the cycle length. -/
private theorem reduce_power_congr {x m start period b : ℕ} (hp : 0 < period)
    (hper : b ∣ period) (h : x ^ (start + period) ≡ x ^ start [MOD m]) (a : ℕ) :
    ∃ i : Fin (start + period),
      x ^ a ≡ x ^ (i : ℕ) [MOD m] ∧ (i : ℕ) ≡ a [MOD b] := by
  induction a with
  | zero => exact ⟨⟨0, by omega⟩, .rfl, Nat.ModEq.refl _⟩
  | succ a ih =>
      obtain ⟨i, hi, hic⟩ := ih
      have hs : x ^ (a + 1) ≡ x ^ (i.val + 1) [MOD m] := by
        simpa only [pow_succ] using hi.mul_right x
      have hic' : (i.val + 1) ≡ (a + 1) [MOD b] := hic.add_right 1
      by_cases hlt : i.val + 1 < start + period
      · exact ⟨⟨_, hlt⟩, hs, hic'⟩
      · have hEq : i.val + 1 = start + period := by omega
        rw [hEq] at hs hic'
        have hstart : (start : ℕ) ≡ (a + 1) [MOD b] := by
          have hper0 : period ≡ 0 [MOD b] := Nat.modEq_zero_iff_dvd.mpr hper
          have h1 : (start + period) ≡ start [MOD b] := by
            simpa using hper0.add_left start
          exact h1.symm.trans hic'
        exact ⟨⟨start, by omega⟩, hs.trans h, hstart⟩

/-- The cycle form of `reduce_power_congr`, without the residue class. -/
private theorem reduce_power {x m start period : ℕ} (hp : 0 < period)
    (h : x ^ (start + period) ≡ x ^ start [MOD m]) (a : ℕ) :
    ∃ i : Fin (start + period), x ^ a ≡ x ^ (i : ℕ) [MOD m] := by
  obtain ⟨i, hi, -⟩ := reduce_power_congr hp (one_dvd _) h a
  exact ⟨i, hi⟩

/-- The congruences in the source's covering system: every exponent lies in
at least one of the six residue classes. -/
private theorem covering (a : ℕ) :
    (a ≡ 1 [MOD 2]) ∨ (a ≡ 0 [MOD 4]) ∨ (a ≡ 6 [MOD 8]) ∨ (a ≡ 1 [MOD 3]) ∨
      (a ≡ 2 [MOD 12]) ∨ (a ≡ 18 [MOD 24]) := by
  have hdec : ∀ r : Fin 24, (r : ℕ) ≡ 1 [MOD 2] ∨ (r : ℕ) ≡ 0 [MOD 4] ∨
      (r : ℕ) ≡ 6 [MOD 8] ∨ (r : ℕ) ≡ 1 [MOD 3] ∨ (r : ℕ) ≡ 2 [MOD 12] ∨
      (r : ℕ) ≡ 18 [MOD 24] := by decide
  have hlt : a % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have ha : a ≡ a % 24 [MOD 24] := (Nat.mod_modEq a 24).symm
  obtain h | h | h | h | h | h := hdec ⟨a % 24, hlt⟩
  · exact Or.inl ((ha.of_dvd (by norm_num : 2 ∣ 24)).trans h)
  · exact Or.inr (Or.inl ((ha.of_dvd (by norm_num : 4 ∣ 24)).trans h))
  · exact Or.inr (Or.inr (Or.inl ((ha.of_dvd (by norm_num : 8 ∣ 24)).trans h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ((ha.of_dvd (by norm_num : 3 ∣ 24)).trans h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((ha.of_dvd (by norm_num : 12 ∣ 24)).trans h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((ha.of_dvd (by norm_num : 24 ∣ 24)).trans h)))))

/-- For the prime $3$, no power of $2$ in the required class plus a power of
$3$ is $1$ modulo $160$. -/
private theorem check_oneSixty_three : ∀ i : Fin 9, ∀ j : Fin 8, (i : ℕ) ≡ 1 [MOD 2] →
    ¬ (1 : ℕ) ≡ 2 ^ (i : ℕ) + 3 ^ (j : ℕ) [MOD 160] := by decide

/-- For the prime $5$, no power of $2$ in the required class plus a power of
$5$ is $11$ modulo $31$. -/
private theorem check_thirtyOne_five : ∀ i : Fin 20, ∀ j : Fin 3, (i : ℕ) ≡ 0 [MOD 4] →
    ¬ (11 : ℕ) ≡ 2 ^ (i : ℕ) + 5 ^ (j : ℕ) [MOD 31] := by decide

/-- For the prime $17$, no power of $2$ in the required class plus a power of
$17$ is $1$ modulo $160$. -/
private theorem check_oneSixty_seventeen : ∀ i : Fin 13, ∀ j : Fin 4,
    (i : ℕ) ≡ 6 [MOD 8] →
    ¬ (1 : ℕ) ≡ 2 ^ (i : ℕ) + 17 ^ (j : ℕ) [MOD 160] := by decide

/-- For the prime $7$, no power of $2$ in the required class plus a power of
$7$ is $1$ modulo $160$. -/
private theorem check_oneSixty_seven : ∀ i : Fin 17, ∀ j : Fin 4, (i : ℕ) ≡ 1 [MOD 3] →
    ¬ (1 : ℕ) ≡ 2 ^ (i : ℕ) + 7 ^ (j : ℕ) [MOD 160] := by decide

/-- For the prime $13$, no power of $2$ in the required class plus a power of
$13$ is $2$ modulo $7$. -/
private theorem check_seven_thirteen : ∀ i : Fin 12, ∀ j : Fin 2, (i : ℕ) ≡ 2 [MOD 12] →
    ¬ (2 : ℕ) ≡ 2 ^ (i : ℕ) + 13 ^ (j : ℕ) [MOD 7] := by decide

/-- For the prime $241$, no power of $2$ in the required class plus a power
of $241$ is $1$ modulo $5$. -/
private theorem check_five_twoFortyOne : ∀ i : Fin 24, ∀ j : Fin 1,
    (i : ℕ) ≡ 18 [MOD 24] →
    ¬ (1 : ℕ) ≡ 2 ^ (i : ℕ) + 241 ^ (j : ℕ) [MOD 5] := by decide

/-- One row of the covering argument: if the exponent of $2$ lies in the
row's class, the Perrin term agrees with a power of $2$ modulo the row's
prime, so the other prime power must be a power of that prime; the extra
modulus then rules out the sum. -/
private theorem exclude_row {k d ad blen Q R : ℕ}
    (startTwo periodTwo startD periodD : ℕ) (a b : ℕ)
    (hkd : perrinSequence k ≡ 2 ^ ad [MOD d])
    (hQ : perrinSequence k ≡ R [MOD Q]) (hdprime : d.Prime)
    (hcyc : 2 ^ blen ≡ 1 [MOD d]) (ha : a ≡ ad [MOD blen])
    (hTwoCyc : 2 ^ (startTwo + periodTwo) ≡ 2 ^ startTwo [MOD Q])
    (hper : blen ∣ periodTwo) (hTwoPos : 0 < periodTwo)
    (hDCyc : d ^ (startD + periodD) ≡ d ^ startD [MOD Q]) (hDPos : 0 < periodD)
    (hcheck : ∀ i : Fin (startTwo + periodTwo), ∀ j : Fin (startD + periodD),
      (i : ℕ) ≡ ad [MOD blen] → ¬ R ≡ 2 ^ (i : ℕ) + d ^ (j : ℕ) [MOD Q])
    {q : ℕ} (hq : q.Prime)
    (heq : perrinSequence k = 2 ^ a + q ^ b) : False := by
  have h2a : (2 : ℕ) ^ a ≡ 2 ^ ad [MOD d] := pow_modEq_of_cycle hcyc ha
  have hEk : perrinSequence k ≡ 2 ^ a [MOD d] := hkd.trans h2a.symm
  have hEqd : perrinSequence k ≡ 2 ^ a + q ^ b [MOD d] := by
    rw [heq]
  have hz : (2 : ℕ) ^ a + q ^ b ≡ 2 ^ a + 0 [MOD d] := by
    simpa using hEqd.symm.trans hEk
  have hdq := Nat.prime_eq_prime_of_dvd_pow hdprime hq
    (Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' _ hz))
  subst q
  obtain ⟨i, hi2, hic⟩ := reduce_power_congr hTwoPos hper hTwoCyc a
  obtain ⟨j, hj⟩ := reduce_power hDPos hDCyc b
  have hEqQ : perrinSequence k ≡ 2 ^ a + d ^ b [MOD Q] := by
    rw [heq]
  have hsum : (2 : ℕ) ^ a + d ^ b ≡ 2 ^ (i : ℕ) + d ^ (j : ℕ) [MOD Q] := hi2.add hj
  have hR : R ≡ 2 ^ (i : ℕ) + d ^ (j : ℕ) [MOD Q] := hQ.symm.trans (hEqQ.trans hsum)
  exact hcheck i j (hic.trans ha) hR

set_option maxRecDepth 100000 in
private theorem prime_twoFortyOne : Nat.Prime 241 := by decide

/-- A Perrin term satisfying the six prime congruences and the four extra
congruences cannot be a power of $2$ plus a prime power. -/
private theorem exclude_two_pow (k : ℕ)
    (h3 : perrinSequence k ≡ 2 [MOD 3]) (h5 : perrinSequence k ≡ 1 [MOD 5])
    (h17 : perrinSequence k ≡ 13 [MOD 17]) (h7 : perrinSequence k ≡ 2 [MOD 7])
    (h13 : perrinSequence k ≡ 4 [MOD 13])
    (h241 : perrinSequence k ≡ 177 [MOD 241])
    (h160 : perrinSequence k ≡ 1 [MOD 160])
    (h31 : perrinSequence k ≡ 11 [MOD 31])
    {q : ℕ} (hq : q.Prime) (a b : ℕ)
    (heq : perrinSequence k = 2 ^ a + q ^ b) : False := by
  rcases covering a with ha | ha | ha | ha | ha | ha
  · exact exclude_row 5 4 0 8 a b h3 h160 (by decide) (by decide) ha (by decide)
      (by norm_num) (by norm_num) (by decide) (by norm_num) check_oneSixty_three hq heq
  · exact exclude_row 0 20 0 3 a b h5 h31 (by decide) (by decide) ha (by decide)
      (by norm_num) (by norm_num) (by decide) (by norm_num) check_thirtyOne_five hq heq
  · exact exclude_row 5 8 0 4 a b h17 h160 (by decide) (by decide) ha (by decide)
      (by norm_num) (by norm_num) (by decide) (by norm_num) check_oneSixty_seventeen hq heq
  · exact exclude_row 5 12 0 4 a b h7 h160 (by decide) (by decide) ha (by decide)
      (by norm_num) (by norm_num) (by decide) (by norm_num) check_oneSixty_seven hq heq
  · exact exclude_row 0 12 0 2 a b h13 h7 (by decide) (by decide) ha (by decide)
      (by norm_num) (by norm_num) (by decide) (by norm_num) check_seven_thirteen hq heq
  · exact exclude_row 0 24 0 1 a b h241 h5 prime_twoFortyOne (by decide) ha (by decide)
      (by norm_num) (by norm_num) (by decide) (by norm_num) check_five_twoFortyOne hq heq

/-- A Perrin term satisfying the congruences above is not a sum of two prime
powers. -/
private theorem exclude_sum (k : ℕ)
    (h2 : perrinSequence k ≡ 1 [MOD 2])
    (h3 : perrinSequence k ≡ 2 [MOD 3]) (h5 : perrinSequence k ≡ 1 [MOD 5])
    (h17 : perrinSequence k ≡ 13 [MOD 17]) (h7 : perrinSequence k ≡ 2 [MOD 7])
    (h13 : perrinSequence k ≡ 4 [MOD 13])
    (h241 : perrinSequence k ≡ 177 [MOD 241])
    (h160 : perrinSequence k ≡ 1 [MOD 160])
    (h31 : perrinSequence k ≡ 11 [MOD 31]) :
    ¬ IsSumOfTwoPrimePowers (perrinSequence k : ℤ) := by
  rintro ⟨p, q, a, b, hp, hq, he⟩
  have hNat : perrinSequence k = p ^ a + q ^ b := by exact_mod_cast he
  rcases hp.eq_two_or_odd with rfl | hop
  · exact exclude_two_pow k h3 h5 h17 h7 h13 h241 h160 h31 hq a b hNat
  rcases hq.eq_two_or_odd with rfl | hoq
  · rw [Nat.add_comm] at hNat
    exact exclude_two_pow k h3 h5 h17 h7 h13 h241 h160 h31 hp b a hNat
  have hp' : p ≡ 1 [MOD 2] := hop
  have hq' : q ≡ 1 [MOD 2] := hoq
  rw [hNat] at h2
  have heven := ((hp'.pow a).add (hq'.pow b)).symm.trans h2
  simp only [one_pow] at heven
  exact absurd heven (by decide)

end perrin_infinite_not_isSumOfTwoPrimePowers

/-- **Infinitely many Perrin numbers are not sums of two prime powers.** Let $(E_n)_{n \ge 0}$ be
the Perrin sequence, given by $E_0 = 3$, $E_1 = 0$, $E_2 = 2$ and $E_{n+3} = E_{n+1} + E_n$.
There are infinitely many natural numbers $k$ such that $E_k$ is not a sum of two prime powers.

The paper, which indexes the sequence in the same way, proves the stronger statement that this
holds for every sufficiently large $k \equiv 472190 \pmod{967206240}$; that form is not stated
here.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 5
(`jis-2026-26.2.3-thm-5`). -/
public theorem perrin_infinite_not_isSumOfTwoPrimePowers :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (perrinSequence k : ℤ)} := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun t => perrin_infinite_not_isSumOfTwoPrimePowers.firstIndex +
      t * perrin_infinite_not_isSumOfTwoPrimePowers.progressionStep)
  · intro t s h
    have h1 : t * perrin_infinite_not_isSumOfTwoPrimePowers.progressionStep =
        s * perrin_infinite_not_isSumOfTwoPrimePowers.progressionStep :=
      Nat.add_left_cancel h
    exact Nat.mul_right_cancel (by norm_num) h1
  · intro t
    have hmod : ∀ m P : ℕ,
        perrin_infinite_not_isSumOfTwoPrimePowers.triples m P =
          perrin_infinite_not_isSumOfTwoPrimePowers.triples m 0 →
        P ∣ perrin_infinite_not_isSumOfTwoPrimePowers.progressionStep →
        perrinSequence (perrin_infinite_not_isSumOfTwoPrimePowers.firstIndex +
          t * perrin_infinite_not_isSumOfTwoPrimePowers.progressionStep) ≡
          perrinSequence perrin_infinite_not_isSumOfTwoPrimePowers.firstIndex [MOD m] :=
      fun m P hP hdiv =>
        perrin_infinite_not_isSumOfTwoPrimePowers.add_mul_step_modEq m P hP hdiv t _
    exact perrin_infinite_not_isSumOfTwoPrimePowers.exclude_sum
      (perrin_infinite_not_isSumOfTwoPrimePowers.firstIndex +
        t * perrin_infinite_not_isSumOfTwoPrimePowers.progressionStep)
      ((hmod 2 7 perrin_infinite_not_isSumOfTwoPrimePowers.period_two
        (by norm_num)).trans
        perrin_infinite_not_isSumOfTwoPrimePowers.firstIndex_mod_two)
      ((hmod 3 13 perrin_infinite_not_isSumOfTwoPrimePowers.period_three
        (by norm_num)).trans
        perrin_infinite_not_isSumOfTwoPrimePowers.firstIndex_mod_three)
      ((hmod 5 24 perrin_infinite_not_isSumOfTwoPrimePowers.period_five
        (by norm_num)).trans
        perrin_infinite_not_isSumOfTwoPrimePowers.firstIndex_mod_five)
      ((hmod 17 288 perrin_infinite_not_isSumOfTwoPrimePowers.period_seventeen
        (by norm_num)).trans
        perrin_infinite_not_isSumOfTwoPrimePowers.firstIndex_mod_seventeen)
      ((hmod 7 48 perrin_infinite_not_isSumOfTwoPrimePowers.period_seven
        (by norm_num)).trans
        perrin_infinite_not_isSumOfTwoPrimePowers.firstIndex_mod_seven)
      ((hmod 13 183 perrin_infinite_not_isSumOfTwoPrimePowers.period_thirteen
        (by norm_num)).trans
        perrin_infinite_not_isSumOfTwoPrimePowers.firstIndex_mod_thirteen)
      ((hmod 241 58080 perrin_infinite_not_isSumOfTwoPrimePowers.period_twoFortyOne
        (by norm_num)).trans
        perrin_infinite_not_isSumOfTwoPrimePowers.firstIndex_mod_twoFortyOne)
      ((hmod 160 336 perrin_infinite_not_isSumOfTwoPrimePowers.period_oneSixty
        (by norm_num)).trans
        perrin_infinite_not_isSumOfTwoPrimePowers.firstIndex_mod_oneSixty)
      ((hmod 31 993 perrin_infinite_not_isSumOfTwoPrimePowers.period_thirtyOne
        (by norm_num)).trans
        perrin_infinite_not_isSumOfTwoPrimePowers.firstIndex_mod_thirtyOne)

end MetaMathlibExt


