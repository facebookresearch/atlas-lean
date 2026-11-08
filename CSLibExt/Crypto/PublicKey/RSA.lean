/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Totient

/-!
# Textbook RSA: correctness via Fermat and the Chinese remainder theorem

Plain ("textbook") RSA over the modulus `n = p q` of two distinct primes encrypts `m : ZMod n` as
`m ^ e` and decrypts `c` as `c ^ d`, where `e d ≡ 1` modulo `p - 1` and modulo `q - 1`; the usual
choice `e d ≡ 1 [MOD φ(n)]` is a special case (`Key.ofTotient`), and so is `e d ≡ 1` modulo
the Carmichael exponent `lcm (p - 1) (q - 1)`.

* `pow_eq_self_of_modEq`: in `ZMod p` for a prime `p`, `x ^ k = x` for **every** `x` (zero
  included) when `k ≥ 1` and `k ≡ 1 [MOD p - 1]` (Fermat's little theorem).
* `Key.decrypt_encrypt` (**correctness of textbook RSA**, Katz and Lindell, Section 11.5.1,
  "plain RSA"):
  `(m ^ e) ^ d = m` for every `m : ZMod n`, including messages not coprime to `n`. The proof
  applies `pow_eq_self_of_modEq` in each factor and transports it through Mathlib's ring
  isomorphism `ZMod.chineseRemainder : ZMod (p q) ≃+* ZMod p × ZMod q`.
* `Key.decrypt_encrypt_nat`: the same statement on natural numbers `m < n`, with `%`.
* `Key.crtDecrypt_eq` (**RSA-CRT decryption**): decrypting with the reduced exponents
  `d_p ≡ d [MOD p - 1]` and `d_q ≡ d [MOD q - 1]` in `ZMod p` and `ZMod q` and recombining with the
  Chinese remainder theorem gives `c ^ d`. `Key.crtDecrypt_mod_eq` is the standard choice
  `d_p = d % (p - 1)`, `d_q = d % (q - 1)` for odd primes.

Textbook RSA is deterministic and therefore not CPA-secure; its security (RSA assumption, padding)
is not treated here.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Sections 8.2.4 and 11.5.1.
-/

@[expose] public section

namespace Cslib.Crypto.PublicKey.RSA

/-- **Fermat**: in `ZMod p` for a prime `p`, `x ^ k = x` for every `x` when `k ≥ 1` and
`k ≡ 1 [MOD p - 1]`. -/
theorem pow_eq_self_of_modEq {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k)
    (hmod : k ≡ 1 [MOD p - 1]) (x : ZMod p) : x ^ k = x := by
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hk).mp hmod.symm
  have hk' : k = 1 + (p - 1) * t := by omega
  by_cases hx : x = 0
  · subst hx
    exact zero_pow (by omega)
  · rw [hk', pow_add, pow_one, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, mul_one]

/-- Exponents congruent modulo `p - 1` (and at least `1`) give the same powers in `ZMod p`. -/
theorem pow_eq_pow_of_modEq {p : ℕ} [Fact p.Prime] {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : a ≡ b [MOD p - 1]) (x : ZMod p) : x ^ a = x ^ b := by
  wlog hle : a ≤ b generalizing a b
  · exact (this hb ha hab.symm (by omega)).symm
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp hab
  have hb' : b = a + (p - 1) * t := by omega
  by_cases hx : x = 0
  · subst hx
    rw [zero_pow (by omega), zero_pow (by omega)]
  · rw [hb', pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, mul_one]

/-- The reduced exponent `d mod (p - 1)` is positive for an odd prime `p`: otherwise `p - 1`
divides `e d`, contradicting `e d ≡ 1`. -/
theorem one_le_mod {p e d : ℕ} (hp : 2 < p) (hed : e * d ≡ 1 [MOD p - 1]) :
    1 ≤ d % (p - 1) := by
  by_contra h
  have hd : d % (p - 1) = 0 := by omega
  have : e * d % (p - 1) = 0 := by rw [Nat.mul_mod, hd, mul_zero, Nat.zero_mod]
  rw [Nat.ModEq, this, Nat.one_mod_eq_one.mpr (by omega)] at hed
  exact absurd hed (by omega)

/-- A textbook RSA key: distinct primes `p`, `q` and exponents `e`, `d` with `e d ≡ 1` modulo
`p - 1` and modulo `q - 1`. -/
structure Key where
  /-- The first prime factor of the modulus. -/
  p : ℕ
  /-- The second prime factor of the modulus. -/
  q : ℕ
  hp : p.Prime
  hq : q.Prime
  hpq : p ≠ q
  /-- The public (encryption) exponent. -/
  e : ℕ
  /-- The private (decryption) exponent. -/
  d : ℕ
  hed_p : e * d ≡ 1 [MOD p - 1]
  hed_q : e * d ≡ 1 [MOD q - 1]

namespace Key

variable (key : Key)

/-- The modulus `n = p q`. -/
def n : ℕ := key.p * key.q

/-- Encryption `m ↦ m ^ e` modulo `n`. -/
def encrypt (m : ZMod key.n) : ZMod key.n := m ^ key.e

/-- Decryption `c ↦ c ^ d` modulo `n`. -/
def decrypt (c : ZMod key.n) : ZMod key.n := c ^ key.d

theorem coprime : key.p.Coprime key.q := (Nat.coprime_primes key.hp key.hq).mpr key.hpq

/-- The Chinese remainder isomorphism `ZMod n ≃+* ZMod p × ZMod q`. -/
def crt : ZMod key.n ≃+* ZMod key.p × ZMod key.q := ZMod.chineseRemainder key.coprime

theorem one_le_ed : 1 ≤ key.e * key.d := by
  rcases Nat.eq_zero_or_pos (key.e * key.d) with h | h
  · have hp2 := key.hp.two_le
    have := key.hed_p
    rw [h, Nat.ModEq, Nat.zero_mod] at this
    rcases Nat.lt_or_ge 2 key.p with hp | hp
    · rw [Nat.one_mod_eq_one.mpr (by omega)] at this
      exact absurd this (by omega)
    · -- `p = 2`: use `q`, which is then an odd prime
      have hq2 : 2 < key.q := by
        have := key.hq.two_le
        have : key.q ≠ 2 := fun h => key.hpq (by omega)
        omega
      have := key.hed_q
      rw [h, Nat.ModEq, Nat.zero_mod, Nat.one_mod_eq_one.mpr (by omega)] at this
      exact absurd this (by omega)
  · exact h

/-- `x ^ k = x` in `ZMod n` as soon as it holds in both CRT components. -/
theorem pow_eq_self_of_crt {k : ℕ} (x : ZMod key.n)
    (h : (key.crt x).1 ^ k = (key.crt x).1 ∧ (key.crt x).2 ^ k = (key.crt x).2) :
    x ^ k = x :=
  key.crt.injective (by rw [map_pow, Prod.pow_def, h.1, h.2])

/-- `x ^ (e d) = x` for every `x : ZMod n`. -/
theorem pow_ed (x : ZMod key.n) : x ^ (key.e * key.d) = x := by
  have := Fact.mk key.hp
  have := Fact.mk key.hq
  exact key.pow_eq_self_of_crt x ⟨pow_eq_self_of_modEq key.one_le_ed key.hed_p _,
    pow_eq_self_of_modEq key.one_le_ed key.hed_q _⟩

/-- **Correctness of textbook RSA**: decryption inverts encryption on every message, including
messages that are not coprime to `n`. -/
theorem decrypt_encrypt (m : ZMod key.n) : key.decrypt (key.encrypt m) = m := by
  rw [decrypt, encrypt, ← pow_mul, key.pow_ed]

/-- Encryption is a bijection of `ZMod n`, inverted by `c ↦ c ^ d`. -/
theorem encrypt_bijective : Function.Bijective key.encrypt := by
  refine ⟨Function.LeftInverse.injective key.decrypt_encrypt, fun c => ⟨key.decrypt c, ?_⟩⟩
  rw [decrypt, encrypt, ← pow_mul, mul_comm, key.pow_ed]

theorem n_pos : 0 < key.n := Nat.mul_pos key.hp.pos key.hq.pos

/-- **Correctness of textbook RSA** on natural numbers: for `m < n`,
`(m ^ e mod n) ^ d mod n = m`. -/
theorem decrypt_encrypt_nat {m : ℕ} (hm : m < key.n) :
    (m ^ key.e % key.n) ^ key.d % key.n = m := by
  have h := key.decrypt_encrypt m
  simp only [decrypt, encrypt] at h
  have hcast : (((m ^ key.e % key.n) ^ key.d % key.n : ℕ) : ZMod key.n) = (m : ZMod key.n) := by
    push_cast [ZMod.natCast_mod]
    exact h
  have hval := congrArg ZMod.val hcast
  rwa [ZMod.val_natCast_of_lt (Nat.mod_lt _ key.n_pos), ZMod.val_natCast_of_lt hm] at hval

/-- **RSA-CRT decryption**: compute `c ^ d_p` in `ZMod p` and `c ^ d_q` in `ZMod q` and
recombine with the Chinese remainder theorem. -/
def crtDecrypt (dp dq : ℕ) (c : ZMod key.n) : ZMod key.n :=
  key.crt.symm ((key.crt c).1 ^ dp, (key.crt c).2 ^ dq)

theorem one_le_d : 1 ≤ key.d := by
  have := key.one_le_ed
  rcases Nat.eq_zero_or_pos key.d with h | h
  · rw [h, mul_zero] at this
    omega
  · exact h

/-- **RSA-CRT decryption is correct**: with reduced exponents `d_p ≡ d [MOD p - 1]` and
`d_q ≡ d [MOD q - 1]` (both at least `1`), CRT decryption equals `c ^ d`. -/
theorem crtDecrypt_eq {dp dq : ℕ} (hdp : 1 ≤ dp) (hdq : 1 ≤ dq) (hp : dp ≡ key.d [MOD key.p - 1])
    (hq : dq ≡ key.d [MOD key.q - 1]) (c : ZMod key.n) :
    key.crtDecrypt dp dq c = key.decrypt c := by
  have := Fact.mk key.hp
  have := Fact.mk key.hq
  rw [crtDecrypt, decrypt, RingEquiv.symm_apply_eq, map_pow, Prod.pow_def,
    pow_eq_pow_of_modEq hdp key.one_le_d hp, pow_eq_pow_of_modEq hdq key.one_le_d hq]

/-- **RSA-CRT decryption with the standard exponents** `d_p = d mod (p - 1)` and
`d_q = d mod (q - 1)` is correct for odd primes. -/
theorem crtDecrypt_mod_eq (hp : 2 < key.p) (hq : 2 < key.q) (c : ZMod key.n) :
    key.crtDecrypt (key.d % (key.p - 1)) (key.d % (key.q - 1)) c = key.decrypt c :=
  key.crtDecrypt_eq (one_le_mod hp key.hed_p) (one_le_mod hq key.hed_q) (Nat.mod_modEq _ _)
    (Nat.mod_modEq _ _) c

/-- A key from the textbook condition `e d ≡ 1 [MOD φ(p q)]`. -/
def ofTotient (p q e d : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hed : e * d ≡ 1 [MOD Nat.totient (p * q)]) : Key where
  p := p
  q := q
  hp := hp
  hq := hq
  hpq := hpq
  e := e
  d := d
  hed_p := by
    rw [Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hpq), Nat.totient_prime hp,
      Nat.totient_prime hq] at hed
    exact Nat.ModEq.of_mul_right _ hed
  hed_q := by
    rw [Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hpq), Nat.totient_prime hp,
      Nat.totient_prime hq] at hed
    exact Nat.ModEq.of_mul_left _ hed

end Key

end Cslib.Crypto.PublicKey.RSA
