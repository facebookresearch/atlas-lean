/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.DeterministicEav
public import CSLibExt.Crypto.PublicKey.RSA

/-!
# Insecurity of textbook RSA: malleability and deterministic encryption

Textbook ("plain") RSA (`Cslib.Crypto.PublicKey.RSA.Key`) encrypts `m : ZMod n` as `m ^ e`.
This file records two standard reasons why it is not a secure encryption scheme.

* **Malleability** (Katz and Lindell, Section 11.5.1): `Key.encrypt_mul` states
  `encrypt (m₁ * m₂) = encrypt m₁ * encrypt m₂` in `ZMod n`, for every pair of messages, including
  messages not coprime to `n`. Hence anyone holding only the public key can turn a ciphertext of
  an unknown `m` into a ciphertext of `m * r` for any chosen `r` (`Key.decrypt_mul_encrypt`).
  `Key.decrypt_mul` is the same statement for decryption.
* **Textbook RSA is not eavesdropping-secure** (Katz and Lindell, Section 11.2.1).
  The generic eavesdropping experiment for deterministic public-key encryption and the
  re-encryption adversary live in `CSLibExt.Crypto.PublicKey.DeterministicEav`; that adversary
  wins with probability `1` whenever its two messages are eligible (equal-length) and have
  distinct encryptions. RSA messages are elements of `ZMod n`, a fixed-length message space, so
  every challenge pair is equal-length-eligible (`RSA.Eligible` is `True`). `rsa_eavAdvantage`
  applies the generic result to textbook RSA, under the public key `Key.publicKey` from
  `CSLibExt.Crypto.PublicKey.RSA`, with messages `1` and `-1`, which have distinct encryptions
  because encryption is a bijection and `n > 2`: for every key generation distribution, textbook
  RSA has eavesdropping advantage `1/2`.

**Plaintext space.** Katz and Lindell's plain RSA (Section 11.5.1) has plaintext space
`Z*_N`, the units of `ZMod N`. `CSLibExt.Crypto.PublicKey.RSA` models the broader space of all
residues `ZMod n` (correctness holds there too). The attack uses only the messages `1` and `-1`,
which are units for every modulus (`attackMsgs_isUnit`), so it is a valid adversary against the
textbook scheme on `Z*_N`, not only against the all-residue model.

Since eavesdropping security is implied by CPA security (for public-key schemes the two are
equivalent, Katz and Lindell, Proposition 11.3), textbook RSA is not CPA-secure. The same holds
for every deterministic public-key scheme with two distinct eligible (equal-length) messages of
distinct encryptions (in particular every correct one with two distinct messages of the same
length); a scheme in which every eligible pair encrypts alike, e.g. a single-message scheme or a
correct scheme with one message of each length, is eavesdropping-secure. The CPA implication is
not formalized here: there is no generic CPA game, by design.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Sections 11.2.1 and 11.5.1.
-/

@[expose] public section

namespace Cslib.Crypto.PublicKey.RSA

/-! ### Malleability -/

namespace Key

variable (key : Key)

/-- **Malleability of textbook RSA** (Katz and Lindell, Section 11.5.1): encryption is
multiplicative, `(m₁ m₂) ^ e = m₁ ^ e m₂ ^ e` in `ZMod n`, for all messages. -/
theorem encrypt_mul (m₁ m₂ : ZMod key.n) :
    key.encrypt (m₁ * m₂) = key.encrypt m₁ * key.encrypt m₂ :=
  mul_pow m₁ m₂ key.e

/-- Decryption of textbook RSA is multiplicative as well (Katz and Lindell, Section 11.5.1). -/
theorem decrypt_mul (c₁ c₂ : ZMod key.n) :
    key.decrypt (c₁ * c₂) = key.decrypt c₁ * key.decrypt c₂ :=
  mul_pow c₁ c₂ key.d

/-- **Mauling a ciphertext** (Katz and Lindell, Section 11.5.1): multiplying a ciphertext `c` of
`m` by the encryption of a chosen `r`, which needs only the public key, gives a ciphertext that
decrypts to `m * r`. -/
theorem decrypt_mul_encrypt (m r : ZMod key.n) :
    key.decrypt (key.encrypt m * key.encrypt r) = m * r := by
  rw [← encrypt_mul, decrypt_encrypt]

end Key

/-! ### Textbook RSA is not eavesdropping-secure -/

/-- The challenge-pair eligibility relation for textbook RSA: every pair is eligible. The
equal-length condition of `PubK^eav` (Katz and Lindell, Section 11.2.1) holds for every pair
because RSA messages are elements of `ZMod n`, a fixed-length message space (every message is
encoded with the bit length of `n`). -/
def Eligible (pk : PubKey) (_ _ : ZMod pk.n) : Prop := True

/-- The challenge messages `1` and `-1` of the RSA eavesdropping attack. Both are units of
`ZMod n` (`attackMsgs_isUnit`), so they lie in the textbook plaintext space `Z*_N` of plain RSA
(Katz and Lindell, Section 11.5.1), inside the all-residue model `ZMod n`. -/
def attackMsgs (pk : PubKey) : ZMod pk.n × ZMod pk.n := (1, -1)

/-- Both attack messages are units, i.e. valid plaintexts of textbook RSA, whose plaintext space
is `Z*_N` (Katz and Lindell, Section 11.5.1), for every public key. -/
theorem attackMsgs_isUnit (pk : PubKey) : IsUnit (attackMsgs pk).1 ∧ IsUnit (attackMsgs pk).2 :=
  ⟨isUnit_one, isUnit_one.neg⟩

/-- The two attack messages `1` and `-1` have distinct encryptions under every textbook RSA key,
because encryption is a bijection of `ZMod n` and `1 ≠ -1` there (`n > 2`). -/
theorem encrypt_attackMsgs_ne (key : Key) :
    key.publicKey.encrypt (attackMsgs key.publicKey).1 ≠
      key.publicKey.encrypt (attackMsgs key.publicKey).2 := by
  change key.encrypt 1 ≠ key.encrypt (-1)
  have : Fact (2 < key.n) := ⟨key.two_lt_n⟩
  exact key.encrypt_bijective.injective.ne (ZMod.neg_one_ne_one).symm

/-- The eavesdropping attack on textbook RSA (Katz and Lindell, Section 11.2.1): submit the units
`1` and `-1` (valid plaintexts of the textbook scheme on `Z*_N`, and an eligible pair, since
`ZMod n` is a fixed-length message space), re-encrypt `-1` under the public key, and compare with
the challenge. -/
def attack : EavAdversary PubKey (fun pk => ZMod pk.n) (fun pk => ZMod pk.n) Unit Eligible :=
  reEncrypt PubKey.encrypt attackMsgs fun _ => trivial

/-- **Textbook RSA is not eavesdropping-secure** (Katz and Lindell, Sections 11.2.1 and 11.5.1):
for every distribution `gen` of RSA keys, the adversary that submits the equal-length messages `1`
and `-1`, re-encrypts `-1` under the public key and compares, has eavesdropping advantage `1/2`.
Both messages are units (`attackMsgs_isUnit`), so this holds for the textbook scheme on `Z*_N`
(Section 11.5.1), not only for the broader all-residue model `ZMod n` of `RSA.lean`. By
Proposition 11.3 of Katz and Lindell (CPA security implies eavesdropping security), textbook RSA
is therefore not CPA-secure either; that step is not formalized here. -/
theorem rsa_eavAdvantage (gen : PMF Key) :
    eavAdvantage PubKey.encrypt Key.publicKey gen attack = 1 / 2 :=
  eavAdvantage_reEncrypt _ _ gen _ _ encrypt_attackMsgs_ne

/-- Textbook RSA has an eavesdropping adversary with advantage `1/2`, for every key
distribution, in the game whose challenge pairs are equal-length-eligible (`Eligible`); the
adversary challenges only on the units `1` and `-1`, valid plaintexts of the textbook scheme on
`Z*_N` (Katz and Lindell, Section 11.5.1). -/
theorem exists_rsa_eavAdvantage_eq_half (gen : PMF Key) :
    ∃ A : EavAdversary PubKey (fun pk => ZMod pk.n) (fun pk => ZMod pk.n) Unit Eligible,
      eavAdvantage PubKey.encrypt Key.publicKey gen A = 1 / 2 :=
  ⟨_, rsa_eavAdvantage gen⟩

end Cslib.Crypto.PublicKey.RSA
