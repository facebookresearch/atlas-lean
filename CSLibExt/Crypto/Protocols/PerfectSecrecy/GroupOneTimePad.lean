/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Crypto.Protocols.PerfectSecrecy.Basic

/-!
# The group one-time pad is perfectly secret

`groupOTP G` encrypts `m` as `k * m` with a uniform key `k` in a finite group `G` and decrypts
`c` as `k⁻¹ * c`. Every ciphertext is uniform whatever the message
(`groupOTP_ciphertextDist_eq_uniform`), so the scheme is perfectly secret in the sense of CSLib's
`EncScheme.PerfectlySecret` (`groupOTP_perfectlySecret`; Katz and Lindell, Lemma 11.15).

This generalizes CSLib's bitstring one-time pad (`otp`, `otp_perfectlySecret` in
`Cslib/Crypto/Protocols/PerfectSecrecy/OneTimePad.lean`), whose proofs it follows with XOR
replaced by multiplication by the key. In ElGamal the mask `h ^ y` plays the role of the key
(`CSLibExt/Crypto/PublicKey/ElGamal.lean`).

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 11.4.1.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.PerfectSecrecy

open Cslib.Probability.PMF

universe u

variable (G : Type u) [Group G] [Fintype G]

/-- **The group one-time pad.** Let $G$ be a finite group. The group one-time pad on $G$ is the
private-key encryption scheme with messages, keys and ciphertexts in $G$ whose key $k$ is drawn
uniformly from $G$, which encrypts a message $m$ as $k m$, and which decrypts a ciphertext $c$
as $k^{-1} c$. -/
noncomputable def groupOTP : EncScheme G G G :=
  .ofPure (Cslib.Probability.PMF.uniformOfFintype G) (· * ·) (fun k c => k⁻¹ * c) fun k m => by simp

/-- **Group one-time pad ciphertexts are uniform.** Let $G$ be a finite group. For every
message $m \in G$, the ciphertext of $m$ under the group one-time pad on $G$, whose key is
drawn uniformly from $G$, is uniformly distributed on $G$. -/
theorem groupOTP_ciphertextDist_eq_uniform (m : G) :
    (groupOTP G).ciphertextDist m = Cslib.Probability.PMF.uniformOfFintype G := by
  change (Cslib.Probability.PMF.uniformOfFintype G).bind (fun k => PMF.pure (k * m)) = _
  have h : (fun k : G => PMF.pure (k * m)) = PMF.pure ∘ ⇑(Equiv.mulRight m) := rfl
  rw [h, PMF.bind_pure_comp, uniformOfFintype_map_equiv]

/-- **The group one-time pad is perfectly secret.** Let $G$ be a finite group. The group
one-time pad on $G$ is perfectly secret: for every probability distribution on messages in $G$
and every ciphertext $c$ that occurs with positive probability, the conditional distribution
of the message given that the ciphertext is $c$ equals the prior distribution of the message.

Source: Katz and Lindell, Lemma 11.15. -/
theorem groupOTP_perfectlySecret : (groupOTP G).PerfectlySecret :=
  (EncScheme.perfectlySecret_iff_ciphertextIndist _).mpr fun m₀ m₁ =>
    (groupOTP_ciphertextDist_eq_uniform G m₀).trans
      (groupOTP_ciphertextDist_eq_uniform G m₁).symm

end Cslib.Crypto.Protocols.PerfectSecrecy
