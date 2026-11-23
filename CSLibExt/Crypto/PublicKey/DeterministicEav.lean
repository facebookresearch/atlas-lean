/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Probability.PMF

/-!
# Eavesdropping insecurity of deterministic public-key encryption

A small, scheme-independent eavesdropping experiment `PubK^eav` (Katz and Lindell,
Section 11.2.1) for an arbitrary **deterministic** public-key encryption function
`Enc : (pk : PK) → M pk → C pk`, with key pairs `K`, public-key projection `pub : K → PK` and key
generation distribution `gen : PMF K`. Message and ciphertext types may depend on the public key
(e.g. `ZMod n` for an RSA modulus `n`).

Katz and Lindell require the two challenge messages to have equal length. The experiment is
therefore parametrized by an eligibility relation `Eligible : (pk : PK) → M pk → M pk → Prop` on
challenge pairs, and an adversary must prove that every pair it submits is eligible, so the game
only ever challenges eligible pairs. `EqualLength len` is the textbook relation for a message length
function `len`; a fixed-length message space (such as `ZMod n` in textbook RSA) may use `True`.

* `EavAdversary`, `eavGame`, `eavAdvantage`: the experiment and the advantage
  `|Pr[A wins] - 1/2|`.
* `reEncrypt Enc msgs hel`: the adversary that submits the eligible pair `msgs pk`, encrypts the
  second message itself and compares the result with the challenge ciphertext.
* `eavGame_reEncrypt`: `reEncrypt` wins with probability `1` whenever, for every key pair, the
  two chosen eligible messages have distinct encryptions; `eavAdvantage_reEncrypt` turns this into
  advantage `1/2`, and `eavAdvantage_reEncrypt_of_injective` derives the hypothesis from
  injectivity of encryption (e.g. correctness of decryption) and two distinct eligible messages.

Both hypotheses matter. A deterministic scheme in which every eligible pair has the same
encryption leaks nothing and is eavesdropping-secure: for example one whose message type has at
most one element (`M pk = Unit` with constant encryption), or a correct scheme whose message
space has exactly one message of each length, where the only eligible pairs are `(m, m)`. The
result is that every deterministic scheme with two eligible (equal-length) messages of distinct
encryptions, in particular every correct deterministic scheme with two distinct messages of the
same length, is not eavesdropping-secure, hence not CPA-secure (Katz and Lindell,
Proposition 11.3; that step is not formalized here: there is no generic CPA game in this file, by
design).

Wave 2: migrate to `CSLibExt.Crypto.Framework` games. The experiment duplicates the shape of
`Cslib.Crypto.PublicKey.ElGamal.eavGame`, generalized to deterministic schemes with
key-dependent message and ciphertext types and an eligibility relation on challenge pairs. The
textbook RSA instance is in `CSLibExt.Crypto.PublicKey.RSAInsecurity`.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 11.2.1.
-/

@[expose] public section

namespace Cslib.Crypto.PublicKey

variable {K PK : Type*} {M C : PK → Type*}

/-- The message selected by the challenge bit: `m.2` for `true`, `m.1` for `false`. -/
def pick {α : Type*} (m : α × α) (b : Bool) : α := if b then m.2 else m.1

/-- The equal-length eligibility relation of `PubK^eav` (Katz and Lindell, Section 11.2.1) for a
message length function `len`: two messages may be challenged together iff they have the same
length. -/
def EqualLength (len : (pk : PK) → M pk → ℕ) (pk : PK) (m₁ m₂ : M pk) : Prop :=
  len pk m₁ = len pk m₂

/-- An eavesdropping adversary against a public-key scheme with public keys `PK`, message types
`M pk` and ciphertext types `C pk`, with random coins in `R`, whose challenge pairs must satisfy
the eligibility relation `Eligible` (equal length in Katz and Lindell, Section 11.2.1): from the
public key it chooses two eligible messages, and from the public key and the challenge ciphertext
it guesses which one was encrypted.

Wave 2: migrate to `CSLibExt.Crypto.Framework` games. -/
structure EavAdversary (PK : Type*) (M C : PK → Type*) (R : Type*)
    (Eligible : (pk : PK) → M pk → M pk → Prop) where
  /-- The two challenge messages, as a function of the public key and the coins. -/
  choose : (pk : PK) → R → M pk × M pk
  /-- Every challenge pair is eligible (e.g. its two messages have equal length). -/
  eligible : ∀ pk r, Eligible pk (choose pk r).1 (choose pk r).2
  /-- The guess of the challenge bit. -/
  guess : (pk : PK) → C pk → R → Bool

variable {R : Type*} [Fintype R] [Nonempty R] {Eligible : (pk : PK) → M pk → M pk → Prop}

/-- The eavesdropping experiment `PubK^eav` (Katz and Lindell, Section 11.2.1) for a
**deterministic** public-key encryption function `Enc : (pk : PK) → M pk → C pk`: a key pair
`k` is drawn from `gen`, the adversary sees the public key `pub k`, the coins `r` and the
challenge bit `b` are uniform, the adversary submits an eligible pair (enforced by
`EavAdversary.eligible`), the challenge is `Enc (pub k) m_b`, and the game outputs whether the
guess equals `b`. Encryption uses no randomness.

Wave 2: migrate to `CSLibExt.Crypto.Framework` games. -/
noncomputable def eavGame (Enc : (pk : PK) → M pk → C pk) (pub : K → PK) (gen : PMF K)
    (A : EavAdversary PK M C R Eligible) : PMF Bool :=
  gen.bind fun k => (Cslib.Probability.PMF.uniformOfFintype (R × Bool)).map fun ω =>
    A.guess (pub k) (Enc (pub k) (pick (A.choose (pub k) ω.1) ω.2)) ω.1 == ω.2

/-- The eavesdropping advantage `|Pr[A wins] - 1/2|` (Katz and Lindell, Section 11.2.1). -/
noncomputable def eavAdvantage (Enc : (pk : PK) → M pk → C pk) (pub : K → PK) (gen : PMF K)
    (A : EavAdversary PK M C R Eligible) : ℝ :=
  |(eavGame Enc pub gen A true).toReal - 1 / 2|

variable [∀ pk, DecidableEq (C pk)]

/-- The **re-encryption adversary** against a deterministic scheme (Katz and Lindell,
Section 11.2.1): it submits the eligible messages `msgs pk` (eligibility is `hel`), encrypts the
second one itself, and guesses `true` exactly when the challenge ciphertext equals that
encryption. It uses no coins. -/
def reEncrypt (Enc : (pk : PK) → M pk → C pk) (msgs : (pk : PK) → M pk × M pk)
    (hel : ∀ pk, Eligible pk (msgs pk).1 (msgs pk).2) :
    EavAdversary PK M C Unit Eligible where
  choose pk _ := msgs pk
  eligible pk _ := hel pk
  guess pk c _ := decide (c = Enc pk (msgs pk).2)

/-- **Deterministic encryption with two distinguishable eligible messages is not
eavesdropping-secure** (Katz and Lindell, Section 11.2.1): if for every key pair the two chosen
messages are eligible (e.g. of equal length) and have distinct encryptions, the re-encryption
adversary wins the eavesdropping game with probability `1`. -/
theorem eavGame_reEncrypt (Enc : (pk : PK) → M pk → C pk) (pub : K → PK) (gen : PMF K)
    (msgs : (pk : PK) → M pk × M pk) (hel : ∀ pk, Eligible pk (msgs pk).1 (msgs pk).2)
    (hne : ∀ k, Enc (pub k) (msgs (pub k)).1 ≠ Enc (pub k) (msgs (pub k)).2) :
    eavGame Enc pub gen (reEncrypt Enc msgs hel) = PMF.pure true := by
  have h : ∀ k, (fun ω : Unit × Bool =>
      (reEncrypt Enc msgs hel).guess (pub k)
        (Enc (pub k) (pick ((reEncrypt Enc msgs hel).choose (pub k) ω.1) ω.2)) ω.1 == ω.2) =
      fun _ => true := by
    intro k
    funext ω
    rcases ω with ⟨_, _ | _⟩ <;> simp [reEncrypt, pick, hne k]
  have h' : (Cslib.Probability.PMF.uniformOfFintype (Unit × Bool)).map (fun _ => true) =
      PMF.pure true :=
    PMF.map_const _ _
  simp only [eavGame, h, h', PMF.bind_const]

/-- **Deterministic encryption with two distinguishable eligible messages has eavesdropping
advantage `1/2`** (Katz and Lindell, Section 11.2.1): if for every key pair the two chosen
messages are eligible (e.g. of equal length) and have distinct encryptions, the re-encryption
adversary attains the maximal advantage. -/
theorem eavAdvantage_reEncrypt (Enc : (pk : PK) → M pk → C pk) (pub : K → PK) (gen : PMF K)
    (msgs : (pk : PK) → M pk × M pk) (hel : ∀ pk, Eligible pk (msgs pk).1 (msgs pk).2)
    (hne : ∀ k, Enc (pub k) (msgs (pub k)).1 ≠ Enc (pub k) (msgs (pub k)).2) :
    eavAdvantage Enc pub gen (reEncrypt Enc msgs hel) = 1 / 2 := by
  rw [eavAdvantage, eavGame_reEncrypt Enc pub gen msgs hel hne, PMF.pure_apply_self]
  norm_num

/-- A deterministic scheme with an injective encryption function and, for every key, two
distinct eligible (e.g. equal-length) messages has eavesdropping advantage `1/2` (Katz and
Lindell, Section 11.2.1). -/
theorem eavAdvantage_reEncrypt_of_injective (Enc : (pk : PK) → M pk → C pk) (pub : K → PK)
    (gen : PMF K) (msgs : (pk : PK) → M pk × M pk)
    (hel : ∀ pk, Eligible pk (msgs pk).1 (msgs pk).2) (hinj : ∀ pk, Function.Injective (Enc pk))
    (hne : ∀ k, (msgs (pub k)).1 ≠ (msgs (pub k)).2) :
    eavAdvantage Enc pub gen (reEncrypt Enc msgs hel) = 1 / 2 :=
  eavAdvantage_reEncrypt Enc pub gen msgs hel fun k => (hinj (pub k)).ne (hne k)

end Cslib.Crypto.PublicKey
