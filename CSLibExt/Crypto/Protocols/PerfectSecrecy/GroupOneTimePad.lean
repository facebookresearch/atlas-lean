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

/-- The group one-time pad: `Enc_k(m) = k * m` with `k` uniform on `G`. -/
noncomputable def groupOTP : EncScheme G G G :=
  .ofPure (Cslib.Probability.PMF.uniformOfFintype G) (· * ·) (fun k c => k⁻¹ * c) fun k m => by simp

/-- Every ciphertext of the group one-time pad is uniform, whatever the message. -/
theorem groupOTP_ciphertextDist_eq_uniform (m : G) :
    (groupOTP G).ciphertextDist m = Cslib.Probability.PMF.uniformOfFintype G := by
  change (Cslib.Probability.PMF.uniformOfFintype G).bind (fun k => PMF.pure (k * m)) = _
  have h : (fun k : G => PMF.pure (k * m)) = PMF.pure ∘ ⇑(Equiv.mulRight m) := rfl
  rw [h, PMF.bind_pure_comp, uniformOfFintype_map_equiv]

/-- **The group one-time pad is perfectly secret** (Katz and Lindell, Lemma 11.15). -/
theorem groupOTP_perfectlySecret : (groupOTP G).PerfectlySecret :=
  (EncScheme.perfectlySecret_iff_ciphertextIndist _).mpr fun m₀ m₁ =>
    (groupOTP_ciphertextDist_eq_uniform G m₀).trans
      (groupOTP_ciphertextDist_eq_uniform G m₁).symm

end Cslib.Crypto.Protocols.PerfectSecrecy
