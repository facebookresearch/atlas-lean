/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.Field.ZMod

/-! # Periodicity and zero indices of Lucas sequences modulo three -/

namespace MetaMathlibExt

private theorem zmodThree_cases (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = -1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private theorem zmodThree_mul_self {a : ZMod 3} (ha : a ≠ 0) : a * a = 1 := by
  rcases zmodThree_cases a with h | rfl | rfl
  · exact (ha h).elim
  · decide
  · decide

/-- A scaling relation at two consecutive seeds propagates by the recurrence. -/
private theorem scaledShift (u : ℕ → ZMod 3) {p q : ZMod 3}
    (hrec : ∀ n, u (n + 2) = p * u (n + 1) - q * u n)
    {r : ℕ} {c : ZMod 3} (h0 : u r = c * u 0) (h1 : u (1 + r) = c * u 1)
    (n : ℕ) : u (n + r) = c * u n := by
  induction n using Nat.twoStepInduction with
  | zero => simpa only [Nat.zero_add] using h0
  | one => exact h1
  | more n ih0 ih1 =>
    rw [show n + 2 + r = n + r + 2 by ac_rfl, hrec (n + r), hrec n,
      show n + r + 1 = n + 1 + r by ac_rfl, ih0, ih1, mul_sub, mul_left_comm p c,
      mul_left_comm q c]

/-- Two shifts undo the scaling, and one shift preserves the zero pattern. -/
private theorem period_and_zeros (u : ℕ → ZMod 3) {r : ℕ} (hr : 0 < r) {c : ZMod 3}
    (hc : c * c = 1) (hshift : ∀ n, u (n + r) = c * u n)
    (hsmall : ∀ j < r, u j = 0 ↔ j = 0) :
    (∀ n, u (n + (r + r)) = u n) ∧ ∀ n, u n = 0 ↔ r ∣ n := by
  have hc0 : c ≠ 0 := by
    intro h
    exact zero_ne_one (by simpa only [h, zero_mul] using hc)
  refine ⟨fun n => ?_, fun n => ?_⟩
  · rw [← Nat.add_assoc, hshift (n + r), hshift n, ← mul_assoc, hc, one_mul]
  · have reduce (a k : ℕ) : u (a + r * k) = 0 ↔ u a = 0 := by
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, hshift, mul_eq_zero, or_iff_right hc0, ih]
    have hn := reduce (n % r) (n / r)
    rw [Nat.mod_add_div] at hn
    exact hn.trans ((hsmall _ (Nat.mod_lt _ hr)).trans Nat.dvd_iff_mod_eq_zero.symm)

/-- **Lucas sequences modulo 3.** Let $U = U(P, Q)$ be the Lucas sequence with integer parameters
$P$ and $Q \ne 0$, let $D = P^2 - 4Q$, and suppose $3 \nmid \gcd(P, Q)$. Then $U$ is periodic
modulo $3$ from index $1$ on: there is $k > 0$ with $U_{n+k} \equiv U_n \pmod 3$ for every
$n \ge 1$. If $3 \mid Q$, then $3 \nmid U_n$ for every $n \ge 1$. If $3 \mid P$, then for every
$n \ge 0$, $3 \mid U_n$ if and only if $2 \mid n$. If $3 \nmid P$ and $Q \equiv -1 \pmod 3$,
then for every $n \ge 0$, $3 \mid U_n$ if and only if $4 \mid n$. If $3 \nmid P$ and
$Q \equiv 1 \pmod 3$, then for every $n \ge 0$, $3 \mid U_n$ if and only if $3 \mid n$; moreover
$3 \mid D$.

The periodicity need not start at $n = 0$: for $P = 1$ and $Q = 3$, $U$ is $0, 1, 1, 1, \dots$
modulo $3$. The source's values $\rho(3) = 2, 4, 3$ of the rank of apparition are the least
positive indices these equivalences give.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.8 (`integers-2025-A107-lem-2-8`). -/
public theorem lucasU_mod_three
    (L : LucasSequenceParams) (h3 : ¬ 3 ∣ Int.gcd L.p L.q) :
    (∃ k : ℕ, 0 < k ∧ ∀ n, 1 ≤ n → lucasU L (n + k) ≡ lucasU L n [ZMOD 3]) ∧
      (3 ∣ L.q → ∀ n, 1 ≤ n → ¬ 3 ∣ lucasU L n) ∧
      (3 ∣ L.p → ∀ n, 3 ∣ lucasU L n ↔ 2 ∣ n) ∧
      (¬ 3 ∣ L.p → L.q ≡ -1 [ZMOD 3] → ∀ n, 3 ∣ lucasU L n ↔ 4 ∣ n) ∧
      (¬ 3 ∣ L.p → L.q ≡ 1 [ZMOD 3] →
        (∀ n, 3 ∣ lucasU L n ↔ 3 ∣ n) ∧ 3 ∣ L.p ^ 2 - 4 * L.q) := by
  let p : ZMod 3 := L.p
  let q : ZMod 3 := L.q
  let u (n : ℕ) : ZMod 3 := lucasU L n
  have hp : p = 0 ↔ 3 ∣ L.p := ZMod.intCast_zmod_eq_zero_iff_dvd L.p 3
  have hq : q = 0 ↔ 3 ∣ L.q := ZMod.intCast_zmod_eq_zero_iff_dvd L.q 3
  have hu (n : ℕ) : u n = 0 ↔ 3 ∣ lucasU L n := ZMod.intCast_zmod_eq_zero_iff_dvd _ 3
  have hmod (n m : ℕ) : u n = u m ↔ lucasU L n ≡ lucasU L m [ZMOD 3] :=
    ZMod.intCast_eq_intCast_iff _ _ 3
  have hqneg : q = -1 ↔ L.q ≡ -1 [ZMOD 3] := by
    rw [← show ((-1 : ℤ) : ZMod 3) = -1 by decide]
    exact ZMod.intCast_eq_intCast_iff L.q (-1) 3
  have hqone : q = 1 ↔ L.q ≡ 1 [ZMOD 3] := by
    rw [← Int.cast_one]
    exact ZMod.intCast_eq_intCast_iff L.q 1 3
  have hD : p * p - q = 0 ↔ 3 ∣ L.p ^ 2 - 4 * L.q := by
    have hcast : ((L.p ^ 2 - 4 * L.q : ℤ) : ZMod 3) = p * p - q := by
      rw [Int.cast_sub, Int.cast_pow, Int.cast_mul, pow_two,
        show ((4 : ℤ) : ZMod 3) = 1 by decide, one_mul]
    rw [← hcast]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ 3
  have hrec (n : ℕ) : u (n + 2) = p * u (n + 1) - q * u n := by
    simpa only [Int.cast_sub, Int.cast_mul] using
      congrArg (fun a : ℤ => (a : ZMod 3)) (lucasU_add_two L n)
  have u0 : u 0 = 0 := rfl
  have u1 : u 1 = 1 := rfl
  have u2 : u 2 = p := by rw [hrec 0, u0, u1, mul_one, mul_zero, sub_zero]
  have u3 : u 3 = p * p - q := by rw [hrec 1, u2, u1, mul_one]
  have not_both (hp0 : p = 0) (hq0 : q = 0) : False :=
    h3 (Int.dvd_gcd (c := 3) (hp.mp hp0) (hq.mp hq0))
  -- If Q vanishes, start the geometric progression at U₁, not U₀.
  have q_zero (hq0 : q = 0) :
      (∀ n, 1 ≤ n → u (n + 2) = u n) ∧ ∀ n, 1 ≤ n → u n ≠ 0 := by
    have hp0 : p ≠ 0 := fun h => not_both h hq0
    have hpow (n : ℕ) : u (n + 1) = p ^ n := by
      induction n with
      | zero => simpa only [pow_zero] using u1
      | succ n ih =>
        change u (n + 2) = p ^ (n + 1)
        rw [hrec, hq0, zero_mul, sub_zero, ih, pow_succ']
    refine ⟨?_, ?_⟩
    · intro n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [show m.succ + 2 = (m + 2) + 1 by omega, hpow (m + 2), hpow m, pow_add, pow_two,
        zmodThree_mul_self hp0, mul_one]
    · intro n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [hpow]
      exact pow_ne_zero _ hp0
  have p_zero (hp0 : p = 0) : (∀ n, u (n + 4) = u n) ∧ ∀ n, u n = 0 ↔ 2 ∣ n := by
    refine period_and_zeros u (r := 2) (by decide) (c := -q) ?_ (scaledShift u hrec ?_ ?_) ?_
    · rw [neg_mul_neg]
      exact zmodThree_mul_self (not_both hp0)
    · simp only [u2, u0, hp0, mul_zero]
    · simp only [u3, u1, hp0, zero_mul, zero_sub, mul_one]
    · intro j hj
      have hj' : j = 0 ∨ j = 1 := by omega
      rcases hj' with rfl | rfl <;> simp [u0, u1]
  have q_neg (hp0 : p ≠ 0) (hq' : q = -1) :
      (∀ n, u (n + 8) = u n) ∧ ∀ n, u n = 0 ↔ 4 ∣ n := by
    have v3 : u 3 = -1 := by rw [u3, zmodThree_mul_self hp0, hq']; decide
    have v4 : u 4 = 0 := by rw [hrec 2, v3, u2, hq', mul_comm p (-1), sub_self]
    refine period_and_zeros u (r := 4) (by decide) (c := -1) (by decide)
      (scaledShift u hrec (by rw [v4, u0, mul_zero]) ?_) ?_
    · rw [hrec 3, v4, v3, hq', u1]
      simp
    · intro j hj
      have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hj' with rfl | rfl | rfl | rfl <;> simp [u0, u1, u2, v3, hp0]
  have q_one (hp0 : p ≠ 0) (hq' : q = 1) :
      (∀ n, u (n + 6) = u n) ∧ ∀ n, u n = 0 ↔ 3 ∣ n := by
    have v3 : u 3 = 0 := by rw [u3, zmodThree_mul_self hp0, hq', sub_self]
    refine period_and_zeros u (r := 3) (by decide) (c := -p) ?_
      (scaledShift u hrec (by rw [v3, u0, mul_zero]) ?_) ?_
    · rw [neg_mul_neg, zmodThree_mul_self hp0]
    · simp only [hrec 2, v3, u2, hq', u1, mul_zero, one_mul, zero_sub, mul_one]
    · intro j hj
      have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hj' with rfl | rfl | rfl <;> simp [u0, u1, u2, hp0]
  simp only [← hmod, ← hp, ← hq, ← hu, ← hqneg, ← hqone, ← hD]
  refine ⟨?_, fun h => (q_zero h).2, fun h => (p_zero h).2, fun h h' => (q_neg h h').2,
    fun h h' => ⟨(q_one h h').2, by rw [zmodThree_mul_self h, h', sub_self]⟩⟩
  by_cases hp0 : p = 0
  · exact ⟨4, by decide, fun n _ => (p_zero hp0).1 n⟩
  rcases zmodThree_cases q with h | h | h
  · exact ⟨2, by decide, (q_zero h).1⟩
  · exact ⟨6, by decide, fun n _ => (q_one hp0 h).1 n⟩
  · exact ⟨8, by decide, fun n _ => (q_neg hp0 h).1 n⟩

end MetaMathlibExt
