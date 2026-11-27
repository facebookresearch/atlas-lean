/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic

/-! # Periodicity and zero indices of Lucas sequences modulo two

## References

- Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
  INTEGERS 25 (2025), Article A107, pp. 1–32, Lemma 2.7.
  The positive-index convention for periodicity accounts for the case of even `Q`.
- R. D. Carmichael, *On Sequences of Integers Defined by Recurrence Relations*,
  Quart. J. Pure Appl. Math. 48 (1920), 343–372, especially pp. 344–345.
  Somer and Křížek cite this for periodicity when the modulus is coprime to `Q`.
-/

namespace MetaMathlibExt

private theorem zeros_of_period (u : ℕ → ZMod 2) {k : ℕ} (hk : 0 < k)
    (hperiod : ∀ n, u (n + k) = u n) (hsmall : ∀ j < k, u j = 0 ↔ j = 0)
    (n : ℕ) : u n = 0 ↔ k ∣ n := by
  have reduce (j m : ℕ) : u (j + k * m) = u j := by
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, ← Nat.add_assoc, hperiod, ih]
  have hn := reduce (n % k) (n / k)
  rw [Nat.mod_add_div] at hn
  exact (congrArg (· = 0) hn).to_iff.trans
    ((hsmall _ (Nat.mod_lt _ hk)).trans Nat.dvd_iff_mod_eq_zero.symm)

/-- **Lucas sequences modulo 2.** Let $U = U(P, Q)$ be the Lucas sequence with integer parameters
$P$ and $Q \ne 0$, let $D = P^2 - 4Q$, and suppose $2 \nmid \gcd(P, Q)$. Then $U$ is periodic
modulo $2$ from index $1$ on: there is $k > 0$ with $U_{n+k} \equiv U_n \pmod 2$ for every
$n \ge 1$. If $P$ is odd and $Q$ is even, then $U_n$ is odd for every $n \ge 1$. If $P$ is even
and $Q$ is odd, then for every $n \ge 0$, $2 \mid U_n$ if and only if $2 \mid n$; moreover
$2 \mid D$. If $P$ and $Q$ are both odd, then for every $n \ge 0$, $2 \mid U_n$ if and only if
$3 \mid n$.

The periodicity need not start at $n = 0$: for $P = 1$ and $Q = 2$, $U$ is $0, 1, 1, 1, \dots$
modulo $2$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.7 (`integers-2025-A107-lem-2-7`). -/
public theorem lucasU_mod_two
    (L : LucasSequenceParams) (h2 : ¬ 2 ∣ Int.gcd L.p L.q) :
    (∃ k : ℕ, 0 < k ∧ ∀ n, 1 ≤ n → lucasU L (n + k) ≡ lucasU L n [ZMOD 2]) ∧
      (Odd L.p → Even L.q → ∀ n, 1 ≤ n → ¬ 2 ∣ lucasU L n) ∧
      (Even L.p → Odd L.q →
        (∀ n, 2 ∣ lucasU L n ↔ 2 ∣ n) ∧ 2 ∣ L.p ^ 2 - 4 * L.q) ∧
      (Odd L.p → Odd L.q → ∀ n, 2 ∣ lucasU L n ↔ 3 ∣ n) := by
  let p : ZMod 2 := L.p
  let q : ZMod 2 := L.q
  let u (n : ℕ) : ZMod 2 := lucasU L n
  have hu (n : ℕ) : u n = 0 ↔ 2 ∣ lucasU L n := ZMod.intCast_zmod_eq_zero_iff_dvd _ 2
  have hmod (n m : ℕ) : u n = u m ↔ lucasU L n ≡ lucasU L m [ZMOD 2] :=
    ZMod.intCast_eq_intCast_iff _ _ 2
  have hrec (n : ℕ) : u (n + 2) = p * u (n + 1) - q * u n := by
    simpa only [Int.cast_sub, Int.cast_mul] using
      congrArg (fun a : ℤ => (a : ZMod 2)) (lucasU_add_two L n)
  have u0 : u 0 = 0 := rfl
  have u1 : u 1 = 1 := rfl
  have u2 : u 2 = p := by rw [hrec 0, u0, u1, mul_one, mul_zero, sub_zero]
  have odd_even (hP : Odd L.p) (hQ : Even L.q) (n : ℕ) (hn : 1 ≤ n) : u n = 1 := by
    have hp : p = 1 := hP.intCast_zmod_two
    have hq : q = 0 := hQ.intCast_zmod_two
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    clear hn
    induction m with
    | zero => exact u1
    | succ m ih =>
      change u (m + 2) = 1
      rwa [hrec m, hp, hq, one_mul, zero_mul, sub_zero]
  have even_odd (hP : Even L.p) (hQ : Odd L.q) :
      (∀ n, u (n + 2) = u n) ∧ (∀ n, u n = 0 ↔ 2 ∣ n) := by
    have hp : p = 0 := hP.intCast_zmod_two
    have hq : q = 1 := hQ.intCast_zmod_two
    have hperiod (n : ℕ) : u (n + 2) = u n := by
      rw [hrec, hp, hq, zero_mul, one_mul, zero_sub, CharTwo.neg_eq]
    refine ⟨hperiod, zeros_of_period u (by decide) hperiod ?_⟩
    intro j hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl <;> simp [u0, u1]
  have odd_odd (hP : Odd L.p) (hQ : Odd L.q) :
      (∀ n, u (n + 3) = u n) ∧ (∀ n, u n = 0 ↔ 3 ∣ n) := by
    have hp : p = 1 := hP.intCast_zmod_two
    have hq : q = 1 := hQ.intCast_zmod_two
    have hperiod (n : ℕ) : u (n + 3) = u n := by
      rw [show n + 3 = (n + 1) + 2 by rfl, hrec (n + 1), hrec n, hp, hq]
      simp only [one_mul]
      rw [sub_right_comm, sub_self, zero_sub, CharTwo.neg_eq]
    refine ⟨hperiod, zeros_of_period u (by decide) hperiod ?_⟩
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl <;> simp [u0, u1, u2, hp]
  refine ⟨?_, ?_, ?_, fun hP hQ n => (hu n).symm.trans ((odd_odd hP hQ).2 n)⟩
  · rcases Int.even_or_odd L.p with hP | hP <;> rcases Int.even_or_odd L.q with hQ | hQ
    · exact (h2 (Int.dvd_gcd (c := 2) (even_iff_two_dvd.mp hP) (even_iff_two_dvd.mp hQ))).elim
    · exact ⟨2, by decide, fun n _ => (hmod _ _).mp ((even_odd hP hQ).1 n)⟩
    · refine ⟨1, by decide, fun n hn => (hmod _ _).mp ?_⟩
      rw [odd_even hP hQ (n + 1) (by omega), odd_even hP hQ n hn]
    · exact ⟨3, by decide, fun n _ => (hmod _ _).mp ((odd_odd hP hQ).1 n)⟩
  · intro hP hQ n hn hd
    exact one_ne_zero ((odd_even hP hQ n hn).symm.trans ((hu n).mpr hd))
  · intro hP hQ
    refine ⟨fun n => (hu n).symm.trans ((even_odd hP hQ).2 n), ?_⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    rw [Int.cast_sub, Int.cast_pow, Int.cast_mul]
    change p ^ 2 - (4 : ZMod 2) * q = 0
    have hp : p = 0 := hP.intCast_zmod_two
    simp [hp, show (4 : ZMod 2) = 0 by decide]

end MetaMathlibExt
