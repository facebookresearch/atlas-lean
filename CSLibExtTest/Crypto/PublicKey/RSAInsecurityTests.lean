/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.RSAInsecurity
public import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the insecurity of textbook RSA

Key `p = 61`, `q = 53` (`n = 3233`), `e = 17`, `d = 2753`.

* Malleability: `65 ↦ 2790`, `2 ↦ 1752`, `130 ↦ 3017 = 2790 * 1752 mod 3233`, checked by
  `decide`, and an attacker that multiplies the ciphertext `2790` by the encryption of `2`
  obtains a ciphertext of `130`.
* Eavesdropping: an explicit adversary choosing `66` and `65` and comparing the challenge with the
  hard-coded ciphertext `2790` of `65` wins with probability `1` on this key; the generic
  re-encryption adversary does too, for this key and for every key distribution.
* Public key: `key.publicKey = (3233, 17)` encrypts `65` to `2790`.
* Eligibility: RSA messages live in the fixed-length space `ZMod n`, so every challenge pair, e.g.
  `(66, 65)`, is eligible (`RSA.Eligible` is `True`).
* Plaintext space: every challenge message is a unit mod `3233 = 61 * 53`, i.e. a valid textbook
  plaintext in `Z*_N`: `66 = 2 * 3 * 11` and `65 = 5 * 13` for `eve`, `1` and `-1` for `attack`
  (`-1 ↦ 3232`, since `e = 17` is odd); `0`, the message of an earlier version, is not a unit.

The generic deterministic-encryption lemmas are tested in `DeterministicEavTests`.
-/

@[expose] public section

namespace Cslib.Crypto.RSAInsecurityTests

open Cslib.Crypto.PublicKey RSA

/-- The textbook example key `n = 61 * 53 = 3233`, `e = 17`, `d = 2753`. -/
def key : RSA.Key where
  p := 61
  q := 53
  hp := by norm_num
  hq := by norm_num
  hpq := by decide
  e := 17
  d := 2753
  hed_p := by decide
  hed_q := by decide

/-- The public key of `key` is `(3233, 17)`. -/
example : key.publicKey = ⟨3233, 17⟩ := rfl

/-- Encryption under the public key alone: `65 ↦ 2790`. -/
example : key.publicKey.encrypt 65 = 2790 := by decide

/-- Concrete encryptions: `65 ↦ 2790`, `2 ↦ 1752`, `130 ↦ 3017`. -/
example : key.encrypt 65 = 2790 ∧ key.encrypt 2 = 1752 ∧ key.encrypt 130 = 3017 := by
  decide

/-- Malleability on concrete values, by computation: `E(65 * 2) = E(65) * E(2)`. -/
example : key.encrypt (65 * 2) = key.encrypt 65 * key.encrypt 2 := by decide

/-- ... and `2790 * 1752 = 3017` in `ZMod 3233`, so the product of ciphertexts is the
ciphertext of the product. -/
example : (2790 * 1752 : ZMod key.n) = 3017 := by decide

/-- A message sharing the factor `61` with `n`: `E(61 * 3) = E(61) * E(3)`, by the theorem. -/
example : key.encrypt (61 * 3) = key.encrypt 61 * key.encrypt 3 := key.encrypt_mul 61 3

/-- Decryption is multiplicative too. -/
example : key.decrypt (2790 * 1752) = key.decrypt 2790 * key.decrypt 1752 :=
  key.decrypt_mul 2790 1752

/-- Mauling the ciphertext `2790` of `65` with the public encryption of `2` gives a ciphertext
that decrypts to `130`. -/
example : key.decrypt (2790 * key.encrypt 2) = 130 := by
  have h : (2790 : ZMod key.n) = key.encrypt 65 := by decide
  rw [h, key.decrypt_mul_encrypt]
  decide

/-- An explicit eavesdropper: it submits `66` and `65` and guesses `true` (message `65`) exactly
when the challenge is the precomputed ciphertext `2790 = 65 ^ 17 mod 3233`. -/
def eve : EavAdversary PubKey (fun pk => ZMod pk.n) (fun pk => ZMod pk.n) Unit RSA.Eligible where
  choose _ _ := (66, 65)
  eligible _ _ := trivial
  guess _ c _ := decide (c.val = 2790)

/-- Every RSA challenge pair is eligible, e.g. `(66, 65)` under `key`. -/
example : RSA.Eligible key.publicKey 66 65 := trivial

/-- `eve`'s challenge messages `66` and `65` are units mod `3233`, i.e. valid textbook RSA
plaintexts in `Z*_N`. -/
example : IsUnit (66 : ZMod key.n) ∧ IsUnit (65 : ZMod key.n) :=
  ⟨(ZMod.isUnit_iff_coprime 66 3233).mpr (by norm_num),
    (ZMod.isUnit_iff_coprime 65 3233).mpr (by norm_num)⟩

/-- `61` shares a factor with `n = 3233`, so it is not a valid textbook plaintext (not a unit). -/
example : ¬ IsUnit (61 : ZMod key.n) := fun h =>
  absurd ((ZMod.isUnit_iff_coprime 61 3233).mp h) (by norm_num)

/-- `0` is not a valid textbook plaintext either. -/
example : ¬ IsUnit (0 : ZMod key.n) := by
  have : Fact (1 < key.n) := ⟨by decide⟩
  exact not_isUnit_zero

/-- The attack's messages under `key` are `1` and `3232 = -1`, both units. -/
example : attackMsgs key.publicKey = (1, 3232) ∧ IsUnit (attackMsgs key.publicKey).1 ∧
    IsUnit (attackMsgs key.publicKey).2 :=
  ⟨by decide, attackMsgs_isUnit _⟩

/-- Their encryptions are distinct: `1 ↦ 1` and `-1 ↦ 3232`. -/
example : key.publicKey.encrypt 1 = 1 ∧ key.publicKey.encrypt (-1) = 3232 := by decide

/-- `eve` wins the eavesdropping game on `key` with probability `1`. -/
theorem eve_eavGame :
    eavGame PubKey.encrypt Key.publicKey (PMF.pure key) eve = PMF.pure true := by
  rw [eavGame, PMF.pure_bind,
    ← PMF.map_const (Cslib.Probability.PMF.uniformOfFintype (Unit × Bool)) true]
  congr 1
  funext ω
  revert ω
  decide

/-- Hence `eve` has eavesdropping advantage `1/2` on `key`. -/
example : eavAdvantage PubKey.encrypt Key.publicKey (PMF.pure key) eve = 1 / 2 := by
  rw [eavAdvantage, eve_eavGame, PMF.pure_apply_self]
  norm_num

/-- The generic re-encryption adversary with the unit messages `1` and `-1` wins with
probability `1` on `key`. -/
example : eavGame PubKey.encrypt Key.publicKey (PMF.pure key)
    attack = PMF.pure true :=
  eavGame_reEncrypt _ _ _ _ _ encrypt_attackMsgs_ne

/-- The RSA theorem specialised to the point distribution on `key`. -/
example : eavAdvantage PubKey.encrypt Key.publicKey (PMF.pure key)
    attack = 1 / 2 :=
  rsa_eavAdvantage _

end Cslib.Crypto.RSAInsecurityTests
