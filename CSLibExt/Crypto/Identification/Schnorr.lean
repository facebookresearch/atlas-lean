/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.DiffieHellman
public import Cslib.Probability.PMF
public import Mathlib.Algebra.Field.ZMod

/-!
# The Schnorr identification scheme: completeness, special soundness, zero knowledge

In a commutative group `G` with an element `g` of order dividing `q`, the prover knows `x` with
`y = g ^ x` (exponents in `ZMod q`, `gpow`). One run of the protocol:
the prover sends `I = g ^ k` for a uniform `k`, the verifier sends a uniform challenge `r`, the
prover answers `s = r x + k`, and the verifier accepts when `g ^ s * (y ^ r)⁻¹ = I`.

* `accepts_honest` (**completeness**): honest transcripts are always accepted.
* `extract_spec` (**special soundness**): for `q` prime, from two accepting transcripts
  `(I, r, s)` and `(I, r', s')` with the same commitment and `r ≠ r'`, the extractor
  `(s - s') / (r - r')` is a discrete logarithm of `y`, whenever `g ^ q = 1` and `y ^ q = 1`: the
  two transcripts determine a discrete logarithm of `y`.
* `transcript_eq_simulate` (**honest-verifier zero knowledge**, perfect): the distribution of honest
  transcripts equals that of the simulator, which samples `r` and `s` uniformly and sets
  `I = g ^ s * (y ^ r)⁻¹` without knowing `x`.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 12.5 (the Schnorr identification scheme, Figure 12.2). Completeness is the scheme's
  correctness; transcript simulation and extraction from two accepting transcripts are the
  ingredients of the security proof of Theorem 12.11.
-/

@[expose] public section

namespace Cslib.Crypto.Identification.Schnorr

open Cslib.Crypto.PublicKey

variable {G : Type*} [CommGroup G] {q : ℕ} (g y : G)

/-- The verifier's check on a transcript `(I, r, s)`: `g ^ s * (y ^ r)⁻¹ = I`. -/
def Accepts (I : G) (r s : ZMod q) : Prop := gpow g s * (gpow y r)⁻¹ = I

/-- The prover's answer `s = r x + k`. -/
def respond (x k r : ZMod q) : ZMod q := r * x + k

private theorem gpow_sub [NeZero q] {g : G} (hg : g ^ q = 1) (a b : ZMod q) :
    gpow g (a - b) = gpow g a * (gpow g b)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← gpow_add hg, sub_add_cancel]

/-- **Completeness**: the honest transcript `(g ^ k, r, r x + k)` is accepted. -/
theorem accepts_honest [NeZero q] {g : G} (hg : g ^ q = 1) (x k r : ZMod q) :
    Accepts g (gpow g x) (gpow g k) r (respond x k r) := by
  rw [Accepts, respond, gpow_add hg, mul_comm r x, gpow_mul hg, mul_comm, ← mul_assoc,
    inv_mul_cancel, one_mul]

/-- The knowledge extractor: `(s - s') / (r - r')`. -/
def extract (r s r' s' : ZMod q) : ZMod q := (s - s') * (r - r')⁻¹

/-- **Special soundness**: for `q` prime, `g ^ q = 1` and `y ^ q = 1`, two accepting transcripts
with the same commitment and different challenges reveal a discrete logarithm of `y`. -/
theorem extract_spec [Fact q.Prime] {g y : G} (hg : g ^ q = 1) (hy : y ^ q = 1) {I : G}
    {r s r' s' : ZMod q} (hrr : r ≠ r') (h₁ : Accepts g y I r s) (h₂ : Accepts g y I r' s') :
    gpow g (extract r s r' s') = y := by
  have hsub : gpow g (s - s') = gpow y (r - r') := by
    rw [gpow_sub hg, gpow_sub hy]
    rw [Accepts, mul_inv_eq_iff_eq_mul] at h₁ h₂
    rw [h₁, h₂, ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  have hunit : IsUnit (r - r') := isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hrr)
  have hone : gpow y (1 : ZMod q) = y := by
    rw [gpow, ZMod.val_one, pow_one]
  rw [extract, gpow_mul hg, hsub, ← gpow_mul hy,
    ZMod.mul_inv_of_unit _ hunit, hone]

/-! ### Honest-verifier zero knowledge -/

section ZeroKnowledge

variable [NeZero q]

/-- The honest transcript for secret key `x`, prover randomness `k` and challenge `r`. -/
def honestTranscript (x : ZMod q) (kr : ZMod q × ZMod q) : G × ZMod q × ZMod q :=
  (gpow g kr.1, kr.2, respond x kr.1 kr.2)

/-- The simulated transcript for challenge `r` and answer `s`: `(g ^ s * (y ^ r)⁻¹, r, s)`. -/
def simTranscript (rs : ZMod q × ZMod q) : G × ZMod q × ZMod q :=
  (gpow g rs.2 * (gpow y rs.1)⁻¹, rs.1, rs.2)

/-- The distribution of honest transcripts with uniform `k` and `r`. -/
noncomputable def transcript (x : ZMod q) : PMF (G × ZMod q × ZMod q) :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod q × ZMod q)).map (honestTranscript g x)

/-- The simulator's distribution, with uniform `r` and `s`; it uses only the public key `y`. -/
noncomputable def simulate : PMF (G × ZMod q × ZMod q) :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod q × ZMod q)).map (simTranscript g y)

/-- **Perfect honest-verifier zero knowledge**: when `g ^ q = 1`, honest transcripts and simulated
transcripts have the same distribution. -/
theorem transcript_eq_simulate {g : G} (hg : g ^ q = 1) (x : ZMod q) :
    transcript g x = simulate g (gpow g x) := by
  let e : ZMod q × ZMod q ≃ ZMod q × ZMod q :=
    { toFun := fun kr => (kr.2, respond x kr.1 kr.2)
      invFun := fun rs => (rs.2 - rs.1 * x, rs.1)
      left_inv := fun kr => by simp [respond]
      right_inv := fun rs => by simp [respond] }
  have hcomp : honestTranscript g x = simTranscript g (gpow g x) ∘ e := by
    funext kr
    simp only [honestTranscript, simTranscript, Function.comp, e, Equiv.coe_fn_mk, respond]
    congr 1
    rw [gpow_add hg, mul_comm kr.2 x, gpow_mul hg, mul_comm, ← mul_assoc, inv_mul_cancel,
      one_mul]
  rw [transcript, simulate, hcomp, ← PMF.map_comp, Cslib.Probability.PMF.uniformOfFintype_map_equiv]

end ZeroKnowledge

end Cslib.Crypto.Identification.Schnorr
