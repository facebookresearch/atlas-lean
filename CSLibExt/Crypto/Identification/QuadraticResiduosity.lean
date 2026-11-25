/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Identification.RewindingSimulator
public import CSLibExt.Crypto.Identification.SequentialRepetition

/-!
# The zero-knowledge proof of quadratic residuosity

The first zero-knowledge proof system, by Goldwasser, Micali and Rackoff (SIAM J. Comput. 1989,
Section 5), proves that `y` is a quadratic residue modulo `x` without revealing a square root.
In each of `m` rounds the prover sends a random quadratic residue `u = r²`, the verifier sends a
random bit, and the prover answers with a square root of `u` (bit `0`) or of `u y` (bit `1`); the
verifier checks the square. Here the protocol is stated in any finite commutative group `G` (the
units modulo `x` in GMR), with the witness a square root `s` of `y` and the answers `r` and `r s`.

One round is a Sigma protocol with challenge set `Bool` (`QR.sigma`), and:
* `QR.sigma_complete` (**completeness**), `QR.sigma_specialSound` (two accepting answers for the
  same `u` give the square root `w₁ w₀⁻¹` of `y`);
* `QR.winProb_cheatGame_le_half` and `QR.winProb_seqCheatGame_le` (**soundness error `1/2` per
  round and `2^{-m}` over `m` rounds**, GMR Claim 1: "it cannot be the case that both `u` and
  `u y` have square roots");
* `QR.sigma_specialHVZK` (**perfect special honest-verifier zero knowledge**, with GMR's
  simulator: a random `w` and `u = w²` or `w² y⁻¹`);
* `QR.abs_winProb_simulatorK_sub_le_half_pow` (**zero knowledge against an arbitrary verifier,
  one round**): the rewinding simulator with `k` attempts is within `2^{-k}` of the real view, by
  `SigmaProtocol.abs_winProb_simulatorK_sub_le`.

**Scope.** GMR's Theorem 1 states perfect zero knowledge of the `m`-round protocol with a simulator
that repeats attempts until success; here one round is simulated, with `k` attempts. The
statistical zero-knowledge proof for quadratic non-residuosity (GMR Section 6) is not formalized.

## References

* S. Goldwasser, S. Micali and C. Rackoff, *The knowledge complexity of interactive proof
  systems*, SIAM J. Comput. 18 (1989), 186-208, Section 5 (the protocol, Claim 1 and Theorem 1).
-/

@[expose] public section

namespace Cslib.Crypto.Identification

namespace QR

open Cslib.Crypto.Framework

variable {G : Type*} [CommGroup G] [DecidableEq G]

/-- **The quadratic-residuosity protocol as a Sigma protocol** (Goldwasser, Micali and Rackoff,
SIAM J. Comput. 1989, Section 5, one round): statements `y`, witnesses `s` with `s ^ 2 = y`; the
prover's coins are `r`, its commitment `u = r ^ 2`; on the bit `0` it answers `r` and on the bit
`1` it answers `r * s`; the verifier accepts `w` when `w ^ 2 = u` (bit `0`) or `w ^ 2 = u * y`
(bit `1`). -/
def sigma : SigmaProtocol G G G G Bool G where
  Rel y s := s ^ 2 = y
  commit _ _ r := r ^ 2
  respond _ s r b := if b then r * s else r
  verify y u b w := decide (w ^ 2 = if b then u * y else u)

theorem sigma_verify_eq_true_iff {y u w : G} {b : Bool} :
    (sigma (G := G)).verify y u b w = true ↔ w ^ 2 = if b then u * y else u :=
  decide_eq_true_iff

/-- **Completeness of the quadratic-residuosity protocol**: with a square root `s` of `y`, the
honest answers are accepted: `r ^ 2 = u` and `(r s) ^ 2 = u y`. -/
theorem sigma_complete : (sigma (G := G)).Complete := by
  rintro y s (hs : s ^ 2 = y) r b
  rw [sigma_verify_eq_true_iff]
  cases b
  · rfl
  · change (r * s) ^ 2 = r ^ 2 * y
    rw [mul_pow, hs]

/-- **The extractor of the quadratic-residuosity protocol**: from answers to both bits, `w₁ w₀⁻¹`,
where `w₀` answers the bit `0` and `w₁` the bit `1`. -/
def extract (_y _u : G) (b : Bool) (w : G) (_b' : Bool) (w' : G) : G :=
  if b then w * w'⁻¹ else w' * w⁻¹

/-- **Special soundness of the quadratic-residuosity protocol**: if `w₀ ^ 2 = u` and
`w₁ ^ 2 = u y`, then `(w₁ w₀⁻¹) ^ 2 = y` (GMR, proof of Claim 1). -/
theorem sigma_specialSound : (sigma (G := G)).SpecialSound extract := by
  intro y u b w b' w' hne h h'
  rw [sigma_verify_eq_true_iff] at h h'
  change (extract y u b w b' w') ^ 2 = y
  cases b <;> cases b'
  · exact absurd rfl hne
  · simp only [extract, Bool.false_eq_true, ite_false, ite_true] at h h' ⊢
    rw [mul_pow, inv_pow, h, h', mul_inv_cancel_comm]
  · simp only [extract, Bool.false_eq_true, ite_false, ite_true] at h h' ⊢
    rw [mul_pow, inv_pow, h, h', mul_inv_cancel_comm]
  · exact absurd rfl hne

/-- **Non-squares have no witness.** -/
theorem forall_not_rel_of_not_isSquare {y : G} (hy : ¬ IsSquare y) :
    ∀ s, ¬ (sigma (G := G)).Rel y s := fun s hs => hy ⟨s, by rw [← hs, sq]⟩

/-- **Soundness error `1/2` per round** (GMR, Claim 1): if `y` is not a square, a cheating prover
is accepted in one round with probability at most `1/2`. -/
theorem winProb_cheatGame_le_half {R : Type*} [Fintype R] [Nonempty R] {y : G}
    (hy : ¬ IsSquare y) (a : R → G) (z : R → Bool → G) :
    winProb (sigma.cheatGame y a z) ≤ 1 / 2 := by
  have := sigma.winProb_cheatGame_le sigma_specialSound (forall_not_rel_of_not_isSquare hy) a z
  simpa using this

/-- **Soundness error `2^{-m}` over `m` rounds** (GMR, Claim 1: "the probability that `B` will say
'convinced' is at most `1/2^m`"): if `y` is not a square, an adaptive cheating prover passes all
`m` rounds with probability at most `1 / 2 ^ m`. -/
theorem winProb_seqCheatGame_le {R : Type*} [Fintype R] [Nonempty R] {y : G}
    (hy : ¬ IsSquare y) (a : R → List Bool → G) (z : R → List Bool → Bool → G) (m : ℕ) :
    winProb (sigma.seqCheatGame y a z m) ≤ 1 / 2 ^ m := by
  have := sigma.winProb_seqCheatGame_le sigma_specialSound
    (forall_not_rel_of_not_isSquare hy) a z m
  simpa using this

section Finite

variable [Fintype G]

/-- **GMR's per-challenge simulator**: for the bit `b`, a uniform `w` and the commitment
`w ^ 2` (bit `0`) or `w ^ 2 * y⁻¹` (bit `1`), computed from `y` alone (GMR, proof of Theorem 1). -/
noncomputable def simAt (y : G) (b : Bool) : PMF (G × G) :=
  (Cslib.Probability.PMF.uniformOfFintype G).map fun w =>
    (if b then w ^ 2 * y⁻¹ else w ^ 2, w)

/-- **Perfect special honest-verifier zero knowledge of the quadratic-residuosity protocol**: for
a square `y = s ^ 2` and each bit `b`, the honest pair `(r ^ 2, answer)` has exactly the
distribution of `simAt y b`; for `b = 1` substitute `w = r s`. -/
theorem sigma_specialHVZK : (sigma (G := G)).SpecialHVZK simAt := by
  rintro y s (hs : s ^ 2 = y) b
  rw [SigmaProtocol.challengeTranscript, simAt]
  cases b
  · rfl
  · have hcomp : (fun r : G => (sigma.commit y s r, sigma.respond y s r true)) =
        (fun w : G => (if true then w ^ 2 * y⁻¹ else w ^ 2, w)) ∘ Equiv.mulRight s := by
      funext r
      simp only [sigma, Function.comp, Equiv.coe_mulRight, ite_true, Prod.mk.injEq, and_true]
      rw [mul_pow, hs, mul_inv_cancel_right]
    rw [hcomp, ← PMF.map_comp, Cslib.Probability.PMF.uniformOfFintype_map_equiv]

/-- **Zero knowledge of the quadratic-residuosity protocol against an arbitrary verifier, one
round** (GMR, Theorem 1, truncated form): for a square `y`, every verifier (its bit any function
of `u` and of its coins) and every test `T` of its view, the rewinding simulator with `k` attempts,
which never sees a square root of `y`, and the real interaction pass `T` with probabilities that
differ by at most `1 / 2 ^ k`. -/
theorem abs_winProb_simulatorK_sub_le_half_pow {R : Type*} [Fintype R] [Nonempty R] {y s : G}
    (hs : s ^ 2 = y) (Vstar : G → R → Bool) (T : R × G × G → Bool) (k : ℕ) :
    |winProb ((SigmaProtocol.simulatorK simAt y Vstar k).map fun o => o.elim false T) -
        winProb ((sigma.realViewDist y s Vstar).map T)| ≤ 1 / 2 ^ k := by
  have := sigma.abs_winProb_simulatorK_sub_le sigma_specialHVZK (x := y) (w := s) hs Vstar T k
  norm_num at this ⊢
  simpa [inv_pow] using this

end Finite

end QR

end Cslib.Crypto.Identification
