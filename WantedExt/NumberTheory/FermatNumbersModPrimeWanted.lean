/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Fermat
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Fermat numbers modulo a prime (statements)

Statement-only targets from Klaška, *Fermat Numbers Modulo a Prime*. Fermat numbers are
`Nat.fermatNumber n = 2 ^ 2 ^ n + 1`. The paper's preperiod `h(p)` and period `k(p)` of
`n ↦ F_n mod p` are encoded as in `Nat.fermatNumber_mod_prime_exact_preperiod_period`
(`MathlibExt/NumberTheory/FermatResiduePeriod.lean`): the tail from `h` is periodic, no
earlier tail has a positive period, and every positive period of the tail from `h` is a
multiple of `k`. The index `ind_g(a)` with respect to a primitive root `g` is encoded by an
exponent `i` with `g ^ i = a`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Among `F_0, …, F_p` two Fermat numbers are congruent modulo `p`; stated for every
positive modulus (pigeonhole), the paper takes `p` prime.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Lemma 2 (`jis-2025-25.8.7-lem-2`). -/
public theorem_wanted fermatNumber_modEq_exists_repeat (p : ℕ) (hp : 0 < p) :
    ∃ i j, i < j ∧ j ≤ p ∧ Nat.fermatNumber i ≡ Nat.fermatNumber j [MOD p]

/-- A congruence `F_i ≡ F_j (mod m)` propagates to `F_{i+t} ≡ F_{j+t} (mod m)` for every
`t`; stated for every modulus and all `i, j` (the paper takes `p` prime and `i < j`).

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Lemma 4 (i) (`jis-2025-25.8.7-lem-4`). -/
public theorem_wanted fermatNumber_modEq_add (m i j : ℕ)
    (h : Nat.fermatNumber i ≡ Nat.fermatNumber j [MOD m]) (t : ℕ) :
    Nat.fermatNumber (i + t) ≡ Nat.fermatNumber (j + t) [MOD m]

/-- If `F_j ≢ F_{j+t} (mod m)` for every `t ≥ 1` and `i ≤ j`, then `F_i ≢ F_{i+t} (mod m)`
for every `t ≥ 1`; stated for every modulus and `i ≤ j` (the paper takes `p` prime and
`i < j`).

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Lemma 4 (ii) (`jis-2025-25.8.7-lem-4`). -/
public theorem_wanted fermatNumber_not_modEq_add_of_le (m i j : ℕ) (hij : i ≤ j)
    (h : ∀ t, 0 < t → ¬ Nat.fermatNumber j ≡ Nat.fermatNumber (j + t) [MOD m]) :
    ∀ t, 0 < t → ¬ Nat.fermatNumber i ≡ Nat.fermatNumber (i + t) [MOD m]

/-- Coincidences among Fermat residues: if `h` and `k` are the preperiod and period of
`n ↦ F_n mod p` (tail from `h` periodic with period `k`, no earlier tail periodic, every
period of the tail from `h` a multiple of `k`), then for `i < j`,
`F_i ≡ F_j (mod p)` if and only if `i ≥ h` and `i ≡ j (mod k)`.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Lemma 6 (`jis-2025-25.8.7-lem-6`). -/
public theorem_wanted fermatNumber_modEq_iff_preperiod_period (p : ℕ) (hp : p.Prime)
    (h k : ℕ) (hk : 0 < k)
    (hper : Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) k)
    (hpre : ∀ h' < h, ¬ ∃ kp : ℕ, 0 < kp ∧
      Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h' + n) : ZMod p)) kp)
    (hmin : ∀ kp : ℕ, 0 < kp →
      Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) kp → k ∣ kp)
    (i j : ℕ) (hij : i < j) :
    Nat.fermatNumber i ≡ Nat.fermatNumber j [MOD p] ↔ h ≤ i ∧ i ≡ j [MOD k]

/-- If `g` is a primitive root modulo the prime `p` and `g ^ i = a`, then
`gcd(p - 1, i) = (p - 1) / ord_p(a)`; stated for every exponent `i` with `g ^ i = a`
(the paper's `ind_g(a) ∈ {1, …, p - 1}` is one of them).

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Lemma 8 (iv) (`jis-2025-25.8.7-lem-8`). -/
public theorem_wanted gcd_card_sub_one_exponent_eq_div_orderOf (p : ℕ) (hp : p.Prime)
    (g a : ZMod p) (hg : IsPrimitiveRoot g (p - 1)) (i : ℕ) (hi : g ^ i = a) :
    Nat.gcd (p - 1) i = (p - 1) / orderOf a

/-- For coprime `α, β` and every positive `γ` there is a positive `c` coprime to `γ` with
`c ≡ β (mod α)`; positivity of `α, β` is not needed.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Lemma 10 (`jis-2025-25.8.7-lem-10`). -/
public theorem_wanted exists_coprime_modEq_of_coprime (α β γ : ℕ) (hγ : 0 < γ)
    (hαβ : Nat.Coprime α β) :
    ∃ c, 0 < c ∧ Nat.Coprime c γ ∧ c ≡ β [MOD α]

/-- For a prime `p` and a nonzero residue `a`, some primitive root `g` modulo `p` satisfies
`ind_g(a) = (p - 1) / ord_p(a)`, i.e. `g ^ ((p - 1) / ord_p(a)) = a`.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Proposition 11 (`jis-2025-25.8.7-prop-11`). -/
public theorem_wanted exists_primitiveRoot_pow_card_sub_one_div_orderOf (p : ℕ)
    (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) :
    ∃ g : ZMod p, IsPrimitiveRoot g (p - 1) ∧ g ^ ((p - 1) / orderOf a) = a

/-- If `g` is a primitive root modulo the prime `p` and `g ^ i = a`, then `i ∣ p - 1` if and
only if `i = (p - 1) / ord_p(a)`; stated for every exponent `i` with `g ^ i = a` (for `i`
outside the paper's range `{1, …, p - 1}` both sides are false).

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Proposition 13 (`jis-2025-25.8.7-prop-13`). -/
public theorem_wanted exponent_dvd_card_sub_one_iff (p : ℕ) (hp : p.Prime)
    (g a : ZMod p) (hg : IsPrimitiveRoot g (p - 1)) (i : ℕ) (hi : g ^ i = a) :
    i ∣ p - 1 ↔ i = (p - 1) / orderOf a

/-- For an odd prime `p` with `p - 1 = 2^r u`, `u` odd, there is exactly one pair `(s, t)`
with `s ≤ r`, `t ∣ u` and `2^s t = ind_g(2)` for some primitive root `g` modulo `p`
(encoded as `g ^ (2^s t) = 2`; `1 ≤ 2^s t ≤ p - 1` holds because `2^s t ∣ p - 1`).

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Corollary 14 (`jis-2025-25.8.7-cor-14`); also Theorem 15 (i). -/
public theorem_wanted existsUnique_twoAdic_index_of_two (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (r u : ℕ) (hu : Odd u) (hpu : p - 1 = 2 ^ r * u) :
    ∃! st : ℕ × ℕ, st.1 ≤ r ∧ st.2 ∣ u ∧
      ∃ g : ZMod p, IsPrimitiveRoot g (p - 1) ∧ g ^ (2 ^ st.1 * st.2) = 2

/-- Preperiod and period of Fermat residues from the index of `2`: for an odd prime `p` with
`p - 1 = 2^r u`, `u` odd, and `s ≤ r`, `t ∣ u` with `g ^ (2^s t) = 2` for a primitive root
`g`, the sequence `n ↦ F_n mod p` has exact preperiod `r - s` and primitive period
`ord_{u/t}(2)`.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Theorem 15 (ii) and (iii) (`jis-2025-25.8.7-thm-15`). -/
public theorem_wanted fermatNumber_mod_prime_preperiod_period_of_index (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (r u : ℕ) (hu : Odd u) (hpu : p - 1 = 2 ^ r * u)
    (s t : ℕ) (hs : s ≤ r) (ht : t ∣ u) (g : ZMod p) (hg : IsPrimitiveRoot g (p - 1))
    (hgi : g ^ (2 ^ s * t) = 2) :
    Function.Periodic (fun n : ℕ => (Nat.fermatNumber (r - s + n) : ZMod p))
        (orderOf (2 : ZMod (u / t))) ∧
      (∀ h < r - s, ¬ ∃ kp : ℕ, 0 < kp ∧
        Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) kp) ∧
      (∀ kp : ℕ, 0 < kp →
        Function.Periodic (fun n : ℕ => (Nat.fermatNumber (r - s + n) : ZMod p)) kp →
          orderOf (2 : ZMod (u / t)) ∣ kp)

/-- An odd prime `p` divides `F_n` if and only if `ord_p(2) = 2^{n+1}`.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Lemma 17 (`jis-2025-25.8.7-lem-17`). -/
public theorem_wanted prime_dvd_fermatNumber_iff_orderOf_two (n p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    p ∣ Nat.fermatNumber n ↔ orderOf (2 : ZMod p) = 2 ^ (n + 1)

/-- An odd prime `p` divides some Fermat number if and only if the primitive period `k(p)` of
`n ↦ F_n mod p` equals `1`. The paper's set `F` is the set of primes dividing some `F_n`
(`n ≥ 0`). `k` is the primitive period of the tail from `h`: that tail is periodic with
period `k > 0` and every positive period of it is a multiple of `k`. The paper takes `h = h(p)`,
the pre-period; the primitive period is the same for every `h ≥ h(p)` and no tail from
`h < h(p)` is periodic, so `h` is left free.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Proposition 18 (`jis-2025-25.8.7-prop-18`). -/
public theorem_wanted exists_prime_dvd_fermatNumber_iff_period_eq_one (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (h k : ℕ) (hk : 0 < k)
    (hper : Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) k)
    (hmin : ∀ kp : ℕ, 0 < kp →
      Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) kp → k ∣ kp) :
    (∃ n : ℕ, p ∣ Nat.fermatNumber n) ↔ k = 1

/-- The `2`-part of `ord_p(2)` by residue class: if `p ≡ 7 (mod 8)` then `ord_p(2)` is odd;
if `p ≡ 3 (mod 8)` then `2 ∥ ord_p(2)`; if `p ≡ 5 (mod 8)` then `4 ∥ ord_p(2)`.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Theorem 22, order statements (`jis-2025-25.8.7-thm-22`). -/
public theorem_wanted orderOf_two_twoAdic_of_mod_eight (p : ℕ) (hp : p.Prime) :
    (p % 8 = 7 → ¬ 2 ∣ orderOf (2 : ZMod p)) ∧
      (p % 8 = 3 → 2 ∣ orderOf (2 : ZMod p) ∧ ¬ 4 ∣ orderOf (2 : ZMod p)) ∧
      (p % 8 = 5 → 4 ∣ orderOf (2 : ZMod p) ∧ ¬ 8 ∣ orderOf (2 : ZMod p))

/-- Every preperiod occurs among primes `p ≡ 1 (mod 8)`: for every `v` there is such a prime
for which `n ↦ F_n mod p` has exact preperiod `v` (the tail from `v` has a positive period
and no earlier tail does).

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Theorem 23 (`jis-2025-25.8.7-thm-23`). -/
public theorem_wanted exists_prime_one_mod_eight_fermat_preperiod (v : ℕ) :
    ∃ p : ℕ, p.Prime ∧ p % 8 = 1 ∧
      (∃ k : ℕ, 0 < k ∧
        Function.Periodic (fun n : ℕ => (Nat.fermatNumber (v + n) : ZMod p)) k) ∧
      ∀ h < v, ¬ ∃ kp : ℕ, 0 < kp ∧
        Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) kp

end

end MetaMathlibExt
