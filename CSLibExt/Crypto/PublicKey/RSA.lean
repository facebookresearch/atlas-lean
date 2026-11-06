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

/-- **Fermat's little theorem with exponents congruent to one.** Let $p$ be a prime and let
$k \ge 1$ be a natural number with $k \equiv 1 \pmod{p - 1}$. Then $x^k = x$ for every
$x \in \mathbb{Z}/p\mathbb{Z}$. -/
theorem pow_eq_self_of_modEq {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k)
    (hmod : k ≡ 1 [MOD p - 1]) (x : ZMod p) : x ^ k = x := by
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hk).mp hmod.symm
  have hk' : k = 1 + (p - 1) * t := by omega
  by_cases hx : x = 0
  · subst hx
    exact zero_pow (by omega)
  · rw [hk', pow_add, pow_one, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, mul_one]

/-- **Fermat's little theorem for congruent exponents.** Let $p$ be a prime and let $a$ and $b$
be natural numbers with $a, b \ge 1$ and $a \equiv b \pmod{p - 1}$. Then $x^a = x^b$ for every
$x \in \mathbb{Z}/p\mathbb{Z}$. -/
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

/-- **Positivity of the reduced RSA exponent.** Let $p$, $e$ and $d$ be natural numbers with
$p > 2$ and $ed \equiv 1 \pmod{p - 1}$. Then $d \bmod (p - 1) \ge 1$.

Otherwise $p - 1$ divides $ed$, contradicting $ed \equiv 1 \pmod{p - 1}$. -/
theorem one_le_mod {p e d : ℕ} (hp : 2 < p) (hed : e * d ≡ 1 [MOD p - 1]) :
    1 ≤ d % (p - 1) := by
  by_contra h
  have hd : d % (p - 1) = 0 := by omega
  have : e * d % (p - 1) = 0 := by rw [Nat.mul_mod, hd, mul_zero, Nat.zero_mod]
  rw [Nat.ModEq, this, Nat.one_mod_eq_one.mpr (by omega)] at hed
  exact absurd hed (by omega)

/-- **RSA key.** A textbook RSA key consists of distinct primes $p$ and $q$ and natural numbers $e$
(the public exponent) and $d$ (the private exponent) such that $ed \equiv 1 \pmod{p - 1}$ and
$ed \equiv 1 \pmod{q - 1}$. -/
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

/-- **RSA modulus.** The modulus of an RSA key with primes $p$ and $q$ is $n = pq$. -/
def n : ℕ := key.p * key.q

/-- **RSA encryption.** For an RSA key with modulus $n = pq$ and public exponent $e$, encryption is
the map $\mathbb{Z}/n\mathbb{Z} \to \mathbb{Z}/n\mathbb{Z}$ given by $m \mapsto m^e$. -/
def encrypt (m : ZMod key.n) : ZMod key.n := m ^ key.e

/-- **RSA decryption.** For an RSA key with modulus $n = pq$ and private exponent $d$, decryption is
the map $\mathbb{Z}/n\mathbb{Z} \to \mathbb{Z}/n\mathbb{Z}$ given by $c \mapsto c^d$. -/
def decrypt (c : ZMod key.n) : ZMod key.n := c ^ key.d

theorem coprime : key.p.Coprime key.q := (Nat.coprime_primes key.hp key.hq).mpr key.hpq

/-- **Chinese remainder isomorphism for an RSA modulus.** For an RSA key with distinct primes $p$,
$q$ and modulus $n = pq$, this is the ring isomorphism
$\mathbb{Z}/n\mathbb{Z} \cong \mathbb{Z}/p\mathbb{Z} \times \mathbb{Z}/q\mathbb{Z}$ of the Chinese
remainder theorem, sending $x$ to $(x \bmod p, x \bmod q)$. -/
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

/-- **Checking a power identity through the Chinese remainder theorem.** Let an RSA key have
primes $p$ and $q$ and modulus $n$, let $k$ be a natural number and $x \in \mathbb{Z}/n\mathbb{Z}$,
and let $(x_p, x_q) \in \mathbb{Z}/p\mathbb{Z} \times \mathbb{Z}/q\mathbb{Z}$ be the image of $x$
under the Chinese remainder isomorphism. If $x_p^k = x_p$ and $x_q^k = x_q$, then $x^k = x$. -/
theorem pow_eq_self_of_crt {k : ℕ} (x : ZMod key.n)
    (h : (key.crt x).1 ^ k = (key.crt x).1 ∧ (key.crt x).2 ^ k = (key.crt x).2) :
    x ^ k = x :=
  key.crt.injective (by rw [map_pow, Prod.pow_def, h.1, h.2])

/-- **RSA exponent identity.** For an RSA key with modulus $n$ and exponents $e$ and $d$, every
$x \in \mathbb{Z}/n\mathbb{Z}$ satisfies $x^{ed} = x$. -/
theorem pow_ed (x : ZMod key.n) : x ^ (key.e * key.d) = x := by
  have := Fact.mk key.hp
  have := Fact.mk key.hq
  exact key.pow_eq_self_of_crt x ⟨pow_eq_self_of_modEq key.one_le_ed key.hed_p _,
    pow_eq_self_of_modEq key.one_le_ed key.hed_q _⟩

/-- **Correctness of textbook RSA**: decryption inverts encryption on every message, including
messages that are not coprime to `n`. -/
theorem decrypt_encrypt (m : ZMod key.n) : key.decrypt (key.encrypt m) = m := by
  rw [decrypt, encrypt, ← pow_mul, key.pow_ed]

/-- **RSA encryption is a bijection.** For an RSA key with modulus $n = pq$ and public exponent
$e$, the encryption map $m \mapsto m^e$ is a bijection from $\mathbb{Z}/n\mathbb{Z}$ to itself. -/
theorem encrypt_bijective : Function.Bijective key.encrypt := by
  refine ⟨Function.LeftInverse.injective key.decrypt_encrypt, fun c => ⟨key.decrypt c, ?_⟩⟩
  rw [decrypt, encrypt, ← pow_mul, mul_comm, key.pow_ed]

theorem n_pos : 0 < key.n := Nat.mul_pos key.hp.pos key.hq.pos

/-- **Correctness of textbook RSA on natural numbers.** For an RSA key with modulus $n = pq$ and
exponents $e$, $d$, every natural number $m < n$ satisfies $(m^e \bmod n)^d \bmod n = m$. -/
theorem decrypt_encrypt_nat {m : ℕ} (hm : m < key.n) :
    (m ^ key.e % key.n) ^ key.d % key.n = m := by
  have h := key.decrypt_encrypt m
  simp only [decrypt, encrypt] at h
  have hcast : (((m ^ key.e % key.n) ^ key.d % key.n : ℕ) : ZMod key.n) = (m : ZMod key.n) := by
    push_cast [ZMod.natCast_mod]
    exact h
  have hval := congrArg ZMod.val hcast
  rwa [ZMod.val_natCast_of_lt (Nat.mod_lt _ key.n_pos), ZMod.val_natCast_of_lt hm] at hval

/-- **RSA-CRT decryption.** Let $(p, q, e, d)$ be an RSA key with modulus $n = pq$. For natural
numbers $d_p$, $d_q$ and $c \in \mathbb{Z}/n\mathbb{Z}$, let $c_p$ and $c_q$ be the images of $c$ in
$\mathbb{Z}/p\mathbb{Z}$ and $\mathbb{Z}/q\mathbb{Z}$. RSA-CRT decryption of $c$ with the exponents
$d_p$ and $d_q$ is the element of $\mathbb{Z}/n\mathbb{Z}$ that corresponds to the pair
$(c_p^{d_p}, c_q^{d_q})$ under the Chinese remainder isomorphism
$\mathbb{Z}/n\mathbb{Z} \cong \mathbb{Z}/p\mathbb{Z} \times \mathbb{Z}/q\mathbb{Z}$. -/
def crtDecrypt (dp dq : ℕ) (c : ZMod key.n) : ZMod key.n :=
  key.crt.symm ((key.crt c).1 ^ dp, (key.crt c).2 ^ dq)

theorem one_le_d : 1 ≤ key.d := by
  have := key.one_le_ed
  rcases Nat.eq_zero_or_pos key.d with h | h
  · rw [h, mul_zero] at this
    omega
  · exact h

/-- **RSA-CRT decryption is correct.** Let $(p, q, e, d)$ be an RSA key with modulus $n = pq$, and
let $d_p, d_q \ge 1$ be natural numbers with $d_p \equiv d \pmod{p - 1}$ and
$d_q \equiv d \pmod{q - 1}$. Then for every $c \in \mathbb{Z}/n\mathbb{Z}$, RSA-CRT decryption of
$c$ with the exponents $d_p$ and $d_q$ equals the RSA decryption $c^d$. -/
theorem crtDecrypt_eq {dp dq : ℕ} (hdp : 1 ≤ dp) (hdq : 1 ≤ dq) (hp : dp ≡ key.d [MOD key.p - 1])
    (hq : dq ≡ key.d [MOD key.q - 1]) (c : ZMod key.n) :
    key.crtDecrypt dp dq c = key.decrypt c := by
  have := Fact.mk key.hp
  have := Fact.mk key.hq
  rw [crtDecrypt, decrypt, RingEquiv.symm_apply_eq, map_pow, Prod.pow_def,
    pow_eq_pow_of_modEq hdp key.one_le_d hp, pow_eq_pow_of_modEq hdq key.one_le_d hq]

/-- **RSA-CRT decryption with the standard exponents.** Let $(p, q, e, d)$ be an RSA key with
modulus $n = pq$ in which both primes are odd, that is $p > 2$ and $q > 2$. Then for every
$c \in \mathbb{Z}/n\mathbb{Z}$, RSA-CRT decryption of $c$ with the exponents
$d_p = d \bmod (p - 1)$ and $d_q = d \bmod (q - 1)$ equals the RSA decryption $c^d$. -/
theorem crtDecrypt_mod_eq (hp : 2 < key.p) (hq : 2 < key.q) (c : ZMod key.n) :
    key.crtDecrypt (key.d % (key.p - 1)) (key.d % (key.q - 1)) c = key.decrypt c :=
  key.crtDecrypt_eq (one_le_mod hp key.hed_p) (one_le_mod hq key.hed_q) (Nat.mod_modEq _ _)
    (Nat.mod_modEq _ _) c

/-- **RSA key from the totient condition.** Given distinct primes $p$ and $q$ and natural
numbers $e$ and $d$ with $ed \equiv 1 \pmod{\varphi(pq)}$, where $\varphi$ is Euler's totient
function, this is the RSA key with primes $p$ and $q$, public exponent $e$ and private exponent
$d$. Its conditions $ed \equiv 1 \pmod{p - 1}$ and $ed \equiv 1 \pmod{q - 1}$ hold because
$\varphi(pq) = (p - 1)(q - 1)$. -/
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
