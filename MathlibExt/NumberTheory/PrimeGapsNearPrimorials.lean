/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Primorial
public import MathlibExt.NumberTheory.ConsecutivePrime

@[expose] public section

namespace MetaMathlibExt

/-! # Prime gaps near primorials
-/

/-- **Primes just above a primorial, general form.** Let $q$ and $r$ be natural numbers such
that no prime $s$ satisfies $q < s < r$, and let $q\#$ be the primorial of $q$, the product of
all primes at most $q$. If $p$ is a prime with $q\# + 1 < p < q\# + r^2$, then $p - q\#$ is
prime.

Neither $q$ nor $r$ needs to be prime, and $q < r$ is not assumed. -/
theorem prime_sub_primorial_prime_of_between_consecutive_primes_general
    {q r p : ℕ}
    (hconsecutive : ∀ s : ℕ, q < s → s < r → ¬ Nat.Prime s)
    (hp : Nat.Prime p)
    (hlower : primorial q + 1 < p)
    (hupper : p < primorial q + r ^ 2) :
    Nat.Prime (p - primorial q) := by
  have hNpos : 0 < primorial q := primorial_pos q
  have hNp : primorial q < p := by omega
  have hd2 : 2 ≤ p - primorial q := by omega
  have hplt : p - primorial q < r ^ 2 := by omega
  have hpeq : primorial q + (p - primorial q) = p :=
    Nat.add_sub_cancel' (le_of_lt hNp)
  have key : ∀ t : ℕ, Nat.Prime t → t ∣ (p - primorial q) → r ≤ t := by
    intro t ht htd
    by_contra! hlt
    rcases le_or_gt t q with hsq | hsq
    · have htN : t ∣ primorial q := (ht.dvd_primorial_iff).mpr hsq
      have htp : t ∣ p := by
        have hadd : t ∣ primorial q + (p - primorial q) := Nat.dvd_add htN htd
        rwa [hpeq] at hadd
      rcases (Nat.dvd_prime hp).mp htp with h1 | h1
      · exact ht.ne_one h1
      · have htle : t ≤ primorial q := Nat.le_of_dvd hNpos htN
        omega
    · exact hconsecutive t hsq hlt ht
  rw [Nat.prime_def_le_sqrt]
  refine ⟨hd2, fun m hm2 hmsqrt hmdvd => ?_⟩
  obtain ⟨t, htprime, htm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have htd : t ∣ (p - primorial q) := dvd_trans htm hmdvd
  have htm_le : t ≤ m := Nat.le_of_dvd (by omega : 0 < m) htm
  have hmm : m * m ≤ p - primorial q := Nat.le_sqrt.mp hmsqrt
  have hlt_mm : m * m < r * r := by
    calc m * m ≤ p - primorial q := hmm
    _ < r ^ 2 := hplt
    _ = r * r := pow_two r
  have hmr : m < r := by
    by_contra! hcon
    have hle : r * r ≤ m * m := Nat.mul_le_mul hcon hcon
    omega
  have htr : t < r := lt_of_le_of_lt htm_le hmr
  have hle := key t htprime htd
  omega

set_option linter.unusedVariables false in
/--
**Primes just above a primorial (Čejchan–Křížek–Somer).** Let $q < r$ be consecutive primes,
so that no prime lies strictly between them, and let $q\#$ be the primorial of $q$, the product
of all primes at most $q$. If $p$ is a prime with $q\# + 1 < p < q\# + r^2$, then $p - q\#$ is
prime.

Source: Antonín Čejchan, Michal Křížek, and Lawrence Somer, "On Remarkable
Properties of Primes Near Factorials and Primorials," Journal of Integer
Sequences 25 (2022), Article 22.1.4, Theorem (label T3), lines 471–477,
https://cs.uwaterloo.ca/journals/JIS/VOL25/Krizek/krizek3.tex
It follows from `prime_sub_primorial_prime_of_between_consecutive_primes_general`; the hypotheses
`hq`, `hr` and `hqr` are unused and keep the source's shape.
Proves `Wanted` entry `prime_sub_primorial_prime_of_between_consecutive_primes`.
-/
theorem prime_sub_primorial_prime_of_between_consecutive_primes
    {q r p : ℕ}
    (hq : Nat.Prime q)
    (hr : Nat.Prime r)
    (hqr : q < r)
    (hconsecutive : ∀ s : ℕ, q < s → s < r → ¬ Nat.Prime s)
    (hp : Nat.Prime p)
    (hlower : primorial q + 1 < p)
    (hupper : p < primorial q + r ^ 2) :
    Nat.Prime (p - primorial q) := by
  exact prime_sub_primorial_prime_of_between_consecutive_primes_general hconsecutive hp hlower hupper

/-- **Primes just above a primorial, for a consecutive-prime pair.** Let $q < r$ be consecutive
primes and let $q\#$ be the primorial of $q$, the product of all primes at most $q$. If $p$ is a
prime with $q\# + 1 < p < q\# + r^2$, then $p - q\#$ is prime. -/
theorem AreConsecutivePrimes.prime_sub_primorial_prime {q r p : ℕ}
    (hqr : AreConsecutivePrimes q r) (hp : Nat.Prime p)
    (hlower : primorial q + 1 < p) (hupper : p < primorial q + r ^ 2) :
    Nat.Prime (p - primorial q) :=
  prime_sub_primorial_prime_of_between_consecutive_primes_general
    (fun s hqs hsr hs => (hqr.2.2.2 s hs).elim (fun h => by omega) (fun h => by omega)) hp hlower hupper

end MetaMathlibExt
