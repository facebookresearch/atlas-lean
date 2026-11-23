/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Identification.Sigma
public import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Sigma protocols

**Schnorr as a Sigma protocol.** In `ZMod 11` written multiplicatively, with generator
`g = ofAdd 1`, witness `x = 7`, statement `y = g ^ 7` and commitment randomness `k = 3`: the
answers to the challenges `2` and `9` are `6` and `0`, both transcripts verify, a wrong answer is
rejected, and the Sigma-protocol extractor recovers `x = 7`. Schnorr is special HVZK with the
per-challenge simulator `sigmaSimAt`; a simulator that ignores the challenge (always simulating
challenge `0`) is not, because the honest pair `(g ^ 3, 6)` for challenge `2` is outside its
support.

**A second Sigma protocol.** `lin p a` is a Sigma protocol for `a * x = y` in `ZMod p`
(Schnorr in the additive group, with the linear map `x ↦ a * x`). It is complete, specially sound
and perfectly HVZK. With `a = 0` the statement `y = 1` has no witness, and the cheating prover that
commits `0` and answers `0` wins exactly when the challenge is `0`, with probability `1/5` in
`ZMod 5`: the soundness-error bound `1 / |Ch|` is attained.
-/

@[expose] public section

namespace Cslib.Crypto.SigmaTests

open Finset Cslib.Crypto.Framework Cslib.Crypto.Identification Cslib.Crypto.PublicKey

/-! ### Schnorr as a Sigma protocol -/

section Schnorr

/-- `ZMod 11`, written multiplicatively. -/
abbrev G11 := Multiplicative (ZMod 11)

/-- The generator. -/
abbrev g : G11 := Multiplicative.ofAdd 1

theorem g_pow : g ^ 11 = 1 := by decide

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The statement `y = g ^ 7`. -/
def y : {y : G11 // y ^ 11 = 1} := ⟨gpow g (7 : ZMod 11), by decide⟩

example : (Schnorr.sigma 11 g).Rel y 7 := rfl

example : ¬ (Schnorr.sigma 11 g).Rel y 6 :=
  show ¬ gpow g (6 : ZMod 11) = gpow g (7 : ZMod 11) by decide

example : (Schnorr.sigma 11 g).respond y 7 3 2 = 6 ∧ (Schnorr.sigma 11 g).respond y 7 3 9 = 0 := by
  decide

example : (Schnorr.sigma 11 g).verify y (gpow g (3 : ZMod 11)) 2 6 = true := by decide

example : (Schnorr.sigma 11 g).verify y (gpow g (3 : ZMod 11)) 9 0 = true := by decide

/-- A wrong answer is rejected. -/
example : (Schnorr.sigma 11 g).verify y (gpow g (3 : ZMod 11)) 2 5 = false := by decide

example : (Schnorr.sigma 11 g).verify y ((Schnorr.sigma 11 g).commit y 7 3) 2
    ((Schnorr.sigma 11 g).respond y 7 3 2) = true :=
  Schnorr.sigma_complete g_pow y 7 rfl 3 2

/-- Special soundness extracts a witness from the two accepting transcripts. -/
example : (Schnorr.sigma 11 g).Rel y (Schnorr.sigmaExtract y (gpow g (3 : ZMod 11)) 2 6 9 0) :=
  Schnorr.sigma_specialSound g_pow y _ 2 6 9 0 (by decide) (by decide) (by decide)

/-- The extracted witness is the secret `7`: `(6 - 0) / (2 - 9) = 6 / 4 = 7` in `ZMod 11`. -/
example : Schnorr.sigmaExtract y (gpow g (3 : ZMod 11)) 2 6 9 0 = 7 := by
  rw [Schnorr.sigmaExtract, Schnorr.extract, show (2 : ZMod 11) - 9 = 4 by decide,
    ZMod.inv_eq_of_mul_eq_one 11 4 3 (by decide)]
  decide

example : (Schnorr.sigma 11 g).HVZK fun y => Schnorr.simulate g y.1 := Schnorr.sigma_hvzk g_pow

example : (Schnorr.sigma 11 g).StatHVZK (fun y => Schnorr.simulate g y.1) 0 :=
  (Schnorr.sigma_hvzk g_pow).statHVZK_zero

example : (Schnorr.sigma 11 g).SpecialHVZK (Schnorr.sigmaSimAt 11 g) :=
  Schnorr.sigma_specialHVZK g_pow

/-- Special HVZK yields HVZK with the uniform-challenge simulator. -/
example : (Schnorr.sigma 11 g).HVZK
    (SigmaProtocol.uniformChallengeSim (Schnorr.sigmaSimAt 11 g)) :=
  (Schnorr.sigma_specialHVZK g_pow).hvzk

/-- The honest commitment–answer pair for coins `3` and challenge `2` is `(g ^ 3, 6)`. -/
theorem mem_challengeTranscript :
    (gpow g (3 : ZMod 11), (6 : ZMod 11)) ∈
      ((Schnorr.sigma 11 g).challengeTranscript y 7 2).support := by
  rw [SigmaProtocol.challengeTranscript, PMF.support_map]
  exact ⟨3, by simp, by decide⟩

/-- The per-challenge simulator for challenge `2` produces that pair, without the witness. -/
example : (gpow g (3 : ZMod 11), (6 : ZMod 11)) ∈ (Schnorr.sigmaSimAt 11 g y 2).support := by
  rw [← Schnorr.sigma_specialHVZK g_pow y 7 rfl 2]
  exact mem_challengeTranscript

/-- Special HVZK is not vacuous: a simulator that ignores the challenge and always simulates
challenge `0` is not special HVZK, since `(g ^ 3, 6)` is not in its support. -/
example : ¬ (Schnorr.sigma 11 g).SpecialHVZK fun y _ => Schnorr.sigmaSimAt 11 g y 0 := by
  intro h
  have hmem := mem_challengeTranscript
  rw [h y 7 rfl 2] at hmem
  dsimp only at hmem
  rw [Schnorr.sigmaSimAt, PMF.support_map] at hmem
  obtain ⟨s, -, hs⟩ := hmem
  revert hs
  revert s
  decide

/-- The simulated transcript for challenge `2` and answer `6`. -/
def t₀ : G11 × ZMod 11 × ZMod 11 := Schnorr.simTranscript (q := 11) g y.1 (2, 6)

/-- A simulated transcript, produced without the witness, verifies. -/
example : (Schnorr.sigma 11 g).verify y t₀.1 t₀.2.1 t₀.2.2 = true :=
  (Schnorr.sigma 11 g).verify_of_mem_support_sim (Schnorr.sigma_complete g_pow)
    (Schnorr.sigma_hvzk g_pow) (x := y) (w := (7 : ZMod 11)) rfl
    (by
      rw [Schnorr.simulate, PMF.support_map]
      exact ⟨(2, 6), by simp, rfl⟩)

end Schnorr

/-! ### A second Sigma protocol: linear preimages in `ZMod p` -/

section Linear

variable (p : ℕ) [Fact p.Prime]

/-- A Sigma protocol for `a * x = y` in `ZMod p`: commit `a * k`, answer `e * x + k`, accept
when `a * z = t + e * y`. -/
def lin (a : ZMod p) :
    SigmaProtocol (ZMod p) (ZMod p) (ZMod p) (ZMod p) (ZMod p) (ZMod p) where
  Rel y x := a * x = y
  commit _ _ k := a * k
  respond _ x k e := e * x + k
  verify y t e z := decide (a * z = t + e * y)

/-- The extractor `(z - z') / (e - e')`. -/
def linExtract (_y _t e z e' z' : ZMod p) : ZMod p := (z - z') * (e - e')⁻¹

theorem lin_complete (a : ZMod p) : (lin p a).Complete := by
  rintro y x rfl k e
  simp only [lin, decide_eq_true_eq]
  ring

theorem lin_specialSound (a : ZMod p) : (lin p a).SpecialSound (linExtract p) := by
  intro y t e z e' z' he h₁ h₂
  simp only [lin, decide_eq_true_eq] at h₁ h₂ ⊢
  have hne : e - e' ≠ 0 := sub_ne_zero.mpr he
  calc a * linExtract p y t e z e' z' = (a * z - a * z') * (e - e')⁻¹ := by
        rw [linExtract]; ring
    _ = (e - e') * y * (e - e')⁻¹ := by rw [h₁, h₂]; ring
    _ = y := by field_simp

/-- The simulator: uniform `(e, z)` and the commitment `a * z - e * y`. -/
noncomputable def linSim (a y : ZMod p) : PMF (ZMod p × ZMod p × ZMod p) :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod p × ZMod p)).map fun ez =>
    (a * ez.2 - ez.1 * y, ez.1, ez.2)

theorem lin_hvzk (a : ZMod p) : (lin p a).HVZK (linSim p a) := by
  rintro y x rfl
  let e : ZMod p × ZMod p ≃ ZMod p × ZMod p :=
    { toFun := fun ke => (ke.2, ke.2 * x + ke.1)
      invFun := fun ez => (ez.2 - ez.1 * x, ez.1)
      left_inv := fun ke => by simp
      right_inv := fun ez => by simp }
  have hcomp : (lin p a).honestTranscript (a * x) x =
      (fun ez : ZMod p × ZMod p => (a * ez.2 - ez.1 * (a * x), ez.1, ez.2)) ∘ e := by
    funext ke
    simp only [SigmaProtocol.honestTranscript, lin, Function.comp, e, Equiv.coe_fn_mk,
      Prod.mk.injEq, and_true]
    ring
  rw [SigmaProtocol.transcript, linSim, hcomp, ← PMF.map_comp,
    Cslib.Probability.PMF.uniformOfFintype_map_equiv]

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

example : (lin 5 3).verify 1 ((lin 5 3).commit 1 2 4) 3 ((lin 5 3).respond 1 2 4 3) = true :=
  lin_complete 5 3 1 2 (show (3 : ZMod 5) * 2 = 1 by decide) 4 3

example : (lin 5 3).verify 1 (3 * 4) 3 1 = false := by decide

/-- The extractor recovers the witness `2` of `3 * x = 1` from the two accepting transcripts with
commitment `3 * 4 = 2`, challenges `3, 1` and answers `0, 1`. -/
example : (lin 5 3).Rel 1 (linExtract 5 1 2 3 0 1 1) :=
  lin_specialSound 5 3 1 2 3 0 1 1 (by decide) (by decide) (by decide)

example : linExtract 5 1 2 3 0 1 1 = 2 := by
  rw [linExtract, show (3 : ZMod 5) - 1 = 2 by decide,
    ZMod.inv_eq_of_mul_eq_one 5 2 3 (by decide)]
  decide

/-- With `a = 0` the statement `1` has no witness, so every cheating prover wins with probability
at most `1/5`. -/
example (R : Type) [Fintype R] [Nonempty R] (t : R → ZMod 5) (z : R → ZMod 5 → ZMod 5) :
    winProb ((lin 5 0).cheatGame 1 t z) ≤ 1 / Fintype.card (ZMod 5) :=
  (lin 5 0).winProb_cheatGame_le (lin_specialSound 5 0)
    (fun w (hw : (0 : ZMod 5) * w = 1) => by simp at hw) t z

/-- The bound is attained: commit `0`, answer `0`; the verifier accepts exactly on challenge `0`. -/
example : winProb ((lin 5 0).cheatGame 1 (fun _ : Unit => 0) fun _ _ => 0) = 1 / 5 := by
  rw [SigmaProtocol.cheatGame, winProb_map_uniform]
  have hc : (univ.filter fun ω : Unit × ZMod 5 =>
      (lin 5 0).verify 1 ((fun _ : Unit => (0 : ZMod 5)) ω.1) ω.2
        ((fun _ _ => (0 : ZMod 5)) ω.1 ω.2) = true).card = 1 := by decide
  rw [hc]
  simp [ZMod.card]

end Linear

end Cslib.Crypto.SigmaTests
