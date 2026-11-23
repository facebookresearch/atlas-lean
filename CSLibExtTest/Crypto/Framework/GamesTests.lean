/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Games
public import CSLibExt.Crypto.Protocols.PerfectSecrecy.GroupOneTimePad

/-!
# Tests for the generic games

Toy instances only; they exercise the generic experiments, not existing schemes.

* **Private-key CPA.** The group one-time pad (CSLib's `EncScheme` `groupOTP`, embedded by
  `SymmEncScheme.ofEncScheme`) has CPA advantage `0` against every eavesdropper (no queries), but
  advantage `1/2` against a one-query adversary in any nontrivial finite group: the query bound is
  what separates the two. The identity scheme (a trivial deterministic scheme) has advantage `1/2`
  already against an eavesdropper.
* **Private-key CCA.** The group one-time pad loses to one decryption query on a mauled challenge
  (advantage `1/2`), while an adversary that asks for the decryption of the challenge itself gets
  `⊥` and has advantage `0`.
* **Public-key CPA.** The identity scheme has advantage `1/2`; a scheme whose ciphertext ignores
  the message has advantage `0` against every adversary.
* **MAC.** With the key as the tag: a one-query forger on a fresh message wins with probability
  `1`, replaying the queried message wins with probability `0` (also in the strong game), and a
  blind guess wins with probability `1/2`.
* **Signatures.** With the secret key as the signature: a one-query forger wins with probability
  `1`, a replay with probability `0`.
-/

@[expose] public section

namespace Cslib.Crypto.FrameworkTests.Games

open Cslib.Crypto.Framework FreeM OracleComp Cslib.Crypto.Protocols.PerfectSecrecy

/-! ### The group one-time pad as a `SymmEncScheme` -/

section OTP

variable (G : Type) [Group G] [Fintype G] [DecidableEq G]

/-- The group one-time pad, embedded from CSLib's `EncScheme`. -/
noncomputable abbrev otp : SymmEncScheme G G G := SymmEncScheme.ofEncScheme (groupOTP G)

omit [DecidableEq G] in
theorem otp_correct : (otp G).Correct := SymmEncScheme.correct_ofEncScheme _

omit [DecidableEq G] in
theorem otp_enc (k m : G) : (otp G).enc k m = PMF.pure (k * m) := rfl

omit [DecidableEq G] in
theorem otp_dec (k c : G) : (otp G).dec k c = some (k⁻¹ * c) := rfl

omit [DecidableEq G] in
theorem otp_gen : (otp G).gen = Cslib.Probability.PMF.uniformOfFintype G := rfl

omit [DecidableEq G] in
/-- **The one-time pad is eavesdropping-secure**: against every adversary that makes no
encryption queries, the two challenge worlds are identical. -/
theorem otp_cpaExp_true_eq_false {R : Type} (A : CPAAdversary G G R) (hA : A.QueryBounded 0) :
    cpaExp (otp G) A true = cpaExp (otp G) A false := by
  simp only [cpaExp]
  rw [PMF.bind_comm (otp G).gen A.coins, PMF.bind_comm (otp G).gen A.coins]
  congr 1
  funext r
  obtain ⟨out, hout, hcont⟩ := eq_pure_of_isQueryBoundedWith_zero (hA r)
  choose g hg using fun c => eq_pure_of_isQueryBoundedWith_zero (hcont c)
  have hg' : ∀ c, out.2 c = .pure (g c) := fun c => (hg c).1
  have key : ∀ m : G, ((otp G).gen.bind fun k => evalPMF ((otp G).enc k) (out.2 (k * m))) =
      (Cslib.Probability.PMF.uniformOfFintype G).map g := by
    intro m
    simp only [hg', evalPMF, otp_gen]
    rw [show (fun k : G => PMF.pure (g (k * m))) = PMF.pure ∘ (g ∘ ⇑(Equiv.mulRight m)) from rfl,
      PMF.bind_pure_comp, ← PMF.map_comp, Cslib.Probability.PMF.uniformOfFintype_map_equiv]
  simp only [hout, evalPMF, PMF.pure_bind, otp_enc]
  exact (key _).trans (key _).symm

omit [DecidableEq G] in
/-- The one-time pad has CPA advantage `0` against eavesdroppers. -/
theorem otp_cpaAdvantage_eq_zero {R : Type} (A : CPAAdversary G G R) (hA : A.QueryBounded 0) :
    cpaAdvantage (otp G) A = 0 := by
  rw [cpaAdvantage_eq, otp_cpaExp_true_eq_false G A hA]
  simp

/-- The one-query attack: ask for the encryption of `1` (which is the key), challenge with
`(1, g)`, and guess `1` exactly when the challenge differs from the key. -/
noncomputable def otpAttacker (g : G) : CPAAdversary G G Unit where
  coins := PMF.pure ()
  run _ := .liftBind (1 : G) fun y => .pure ((1, g), fun c => .pure (decide (c ≠ y)))

omit [Fintype G] in
theorem otpAttacker_queryBounded (g : G) : (otpAttacker G g).QueryBounded 1 :=
  fun _ _ _ => trivial

omit [Fintype G] in
/-- The attacker makes a query, so it is not an eavesdropper. -/
theorem otpAttacker_not_queryBounded_zero (g : G) : ¬ (otpAttacker G g).QueryBounded 0 :=
  fun h => h ()

theorem otpAttacker_cpaExp {g : G} (hg : g ≠ 1) (b : Bool) :
    cpaExp (otp G) (otpAttacker G g) b = PMF.pure b := by
  simp only [cpaExp, otpAttacker, evalPMF, otp_enc, PMF.pure_bind]
  cases b <;> simp [hg]

/-- **One encryption query breaks the one-time pad**: CPA advantage `1/2`. -/
theorem otpAttacker_cpaAdvantage {g : G} (hg : g ≠ 1) :
    cpaAdvantage (otp G) (otpAttacker G g) = 1 / 2 := by
  rw [cpaAdvantage_eq, otpAttacker_cpaExp G hg, otpAttacker_cpaExp G hg]
  norm_num [advantage]

/-- The CCA attack on the one-time pad: no encryption queries, one decryption query on the
challenge multiplied by `g`, which decrypts to `m_b * g`. -/
noncomputable def otpCCAAttacker (g : G) : CCAAdversary G G Unit where
  coins := PMF.pure ()
  run _ := .pure ((1, g), fun c =>
    .liftBind (.inr (c * g)) fun (ans : Option G) => .pure (decide (ans = some (g * g))))

theorem otpCCAAttacker_ccaExp {g : G} (hg : g ≠ 1) (b : Bool) :
    ccaExp (otp G) (otpCCAAttacker G g) b = PMF.pure b := by
  simp only [ccaExp, otpCCAAttacker, evalPMF, ccaOracle, otp_enc, otp_dec, PMF.pure_bind]
  cases b <;> simp [hg, mul_assoc, eq_comm (a := g)]

/-- **One decryption query breaks the one-time pad**: CCA advantage `1/2`, although its CPA
advantage against eavesdroppers is `0` (`otp_cpaAdvantage_eq_zero`). -/
theorem otpCCAAttacker_ccaAdvantage {g : G} (hg : g ≠ 1) :
    ccaAdvantage (otp G) (otpCCAAttacker G g) = 1 / 2 := by
  rw [ccaAdvantage_eq, otpCCAAttacker_ccaExp G hg, otpCCAAttacker_ccaExp G hg]
  norm_num [advantage]

omit [Fintype G] in
theorem otpCCAAttacker_queryBounded (g : G) : (otpCCAAttacker G g).QueryBounded 1 :=
  fun _ _ _ => trivial

/-- An adversary that asks for the decryption of the challenge itself and guesses `1` when it is
`g`. The oracle answers `⊥`, so it always guesses `0`. -/
noncomputable def challengeDecrypter (g : G) : CCAAdversary G G Unit where
  coins := PMF.pure ()
  run _ := .pure ((1, g), fun c =>
    .liftBind (.inr c) fun (ans : Option G) => .pure (decide (ans = some g)))

theorem challengeDecrypter_ccaExp (g : G) (b : Bool) :
    ccaExp (otp G) (challengeDecrypter G g) b = PMF.pure false := by
  simp only [ccaExp, challengeDecrypter, evalPMF, ccaOracle, otp_enc, PMF.pure_bind]
  simp

theorem challengeDecrypter_ccaAdvantage (g : G) :
    ccaAdvantage (otp G) (challengeDecrypter G g) = 0 := by
  rw [ccaAdvantage_eq, challengeDecrypter_ccaExp, challengeDecrypter_ccaExp]
  simp

end OTP

/-- A concrete nontrivial instance: the one-time pad on `ZMod 2` written multiplicatively. -/
example : cpaAdvantage (otp (Multiplicative (ZMod 2)))
    (otpAttacker _ (Multiplicative.ofAdd 1)) = 1 / 2 :=
  otpAttacker_cpaAdvantage _ (by decide)

/-! ### A trivial deterministic scheme -/

/-- The identity scheme on bits: `Enc_k(m) = m`. -/
noncomputable def idScheme : SymmEncScheme Bool Unit Bool where
  gen := PMF.pure ()
  enc _ m := PMF.pure m
  dec _ c := some c

theorem idScheme_correct : idScheme.Correct := by
  intro k _ m c hc
  simp only [idScheme, PMF.support_pure, Set.mem_singleton_iff] at hc
  simp [idScheme, hc]

/-- The eavesdropper that challenges with `(0, 1)` and outputs the ciphertext. -/
noncomputable def idAdversary : CPAAdversary Bool Bool Unit where
  coins := PMF.pure ()
  run _ := .pure ((false, true), fun c => .pure c)

theorem idAdversary_queryBounded : idAdversary.QueryBounded 0 := fun _ _ => trivial

/-- **The identity scheme has CPA advantage `1/2`**, already without queries. -/
theorem idScheme_cpaAdvantage : cpaAdvantage idScheme idAdversary = 1 / 2 := by
  rw [cpaAdvantage_eq]
  have h : ∀ b, cpaExp idScheme idAdversary b = PMF.pure b := by
    intro b
    simp only [cpaExp, idScheme, idAdversary, evalPMF, PMF.pure_bind]
    cases b <;> rfl
  rw [h, h]
  norm_num [advantage]

/-! ### Public-key encryption -/

/-- The identity public-key scheme on bits. -/
noncomputable def idPKE : PKEScheme Bool Unit Unit Bool where
  gen := PMF.pure ((), ())
  enc _ m := PMF.pure m
  dec _ c := some c

/-- The adversary that challenges with `(0, 1)` and outputs the ciphertext. -/
noncomputable def idPubAdversary : PubCPAAdversary Bool Unit Bool Unit where
  coins := PMF.pure ()
  choose _ _ := (false, true)
  guess _ c _ := c

theorem idPKE_pubCpaAdvantage : pubCpaAdvantage idPKE idPubAdversary = 1 / 2 := by
  rw [pubCpaAdvantage_eq]
  have h : ∀ b, pubCpaExp idPKE idPubAdversary b = PMF.pure b := by
    intro b; cases b <;> simp [pubCpaExp, idPKE, idPubAdversary, PMF.pure_map]
  rw [h, h]
  norm_num [advantage]

/-- A public-key scheme whose ciphertext carries no information. -/
noncomputable def blindPKE : PKEScheme Bool Unit Unit Unit where
  gen := PMF.pure ((), ())
  enc _ _ := PMF.pure ()
  dec _ _ := none

/-- Every adversary has advantage `0` against a scheme whose ciphertext ignores the message. -/
theorem blindPKE_pubCpaAdvantage {R : Type} (A : PubCPAAdversary Bool Unit Unit R) :
    pubCpaAdvantage blindPKE A = 0 := by
  rw [pubCpaAdvantage_eq, show pubCpaExp blindPKE A true = pubCpaExp blindPKE A false from rfl]
  simp

/-! ### Message authentication codes -/

/-- The MAC whose tag is the key itself, with a uniform one-bit key. -/
noncomputable def keyMAC : MACScheme Bool Bool Bool where
  gen := Cslib.Probability.PMF.uniformOfFintype Bool
  tag k _ := PMF.pure k
  verify k _ t := t == k

theorem keyMAC_correct : keyMAC.Correct := by
  intro k _ m t ht
  simp only [keyMAC, PMF.support_pure, Set.mem_singleton_iff] at ht
  simp [keyMAC, ht]

/-- Ask for the tag of `0` and forge it on `1`. -/
noncomputable def freshForger : MACForger Bool Bool Unit where
  coins := PMF.pure ()
  forge _ := .liftBind false fun t => .pure (true, t)

/-- Ask for the tag of `0` and output it again on `0`. -/
noncomputable def replayForger : MACForger Bool Bool Unit where
  coins := PMF.pure ()
  forge _ := .liftBind false fun t => .pure (false, t)

/-- Without queries, guess the tag `1` on `1`. -/
noncomputable def blindForger : MACForger Bool Bool Unit where
  coins := PMF.pure ()
  forge _ := .pure (true, true)

theorem freshForger_queryBounded : freshForger.QueryBounded 1 := fun _ _ => trivial

theorem macAdvantage_freshForger : macAdvantage keyMAC freshForger = 1 := by
  simp only [macAdvantage, macGame, keyMAC, freshForger, evalLog, PMF.pure_bind, PMF.pure_map]
  simp

/-- A replayed message is not a forgery: the freshness check is not vacuous. -/
theorem macAdvantage_replayForger : macAdvantage keyMAC replayForger = 0 := by
  simp only [macAdvantage, macGame, keyMAC, replayForger, evalLog, PMF.pure_bind, PMF.pure_map]
  simp

theorem macStrongGame_replayForger : winProb (macStrongGame keyMAC replayForger) = 0 := by
  simp only [macStrongGame, keyMAC, replayForger, evalLog, PMF.pure_bind, PMF.pure_map]
  simp

/-- A blind guess of the one-bit tag succeeds with probability `1/2`. -/
theorem macAdvantage_blindForger : macAdvantage keyMAC blindForger = 1 / 2 := by
  have h : macGame keyMAC blindForger = fairCoin := by
    simp only [macGame, keyMAC, blindForger, evalLog, PMF.pure_bind, PMF.pure_map]
    rw [fairCoin]
    conv_rhs => rw [← PMF.bind_pure (Cslib.Probability.PMF.uniformOfFintype Bool)]
    congr 1
    funext k
    cases k <;> rfl
  rw [macAdvantage, h, winProb_fairCoin]

/-! ### Digital signatures -/

/-- The signature scheme that publishes its one-bit key and signs with it. -/
noncomputable def keySig : SigScheme Bool Bool Bool Bool where
  gen := PMF.pure (true, true)
  sign sk _ := PMF.pure sk
  verify pk _ σ := σ == pk

/-- Ask for a signature on `0` and output it on `1`. -/
noncomputable def freshSigForger : SigForger Bool Bool Bool Unit where
  coins := PMF.pure ()
  forge _ _ := .liftBind false fun σ => .pure (true, σ)

/-- Ask for a signature on `0` and output it on `0`. -/
noncomputable def replaySigForger : SigForger Bool Bool Bool Unit where
  coins := PMF.pure ()
  forge _ _ := .liftBind false fun σ => .pure (false, σ)

/-- The forger is one-time (Katz and Lindell, Section 12.6.1). -/
theorem freshSigForger_queryBounded : freshSigForger.QueryBounded 1 := fun _ _ _ => trivial

theorem sigAdvantage_freshSigForger : sigAdvantage keySig freshSigForger = 1 := by
  simp only [sigAdvantage, sigGame, keySig, freshSigForger, evalLog, PMF.pure_bind, PMF.pure_map]
  simp

theorem sigAdvantage_replaySigForger : sigAdvantage keySig replaySigForger = 0 := by
  simp only [sigAdvantage, sigGame, keySig, replaySigForger, evalLog, PMF.pure_bind, PMF.pure_map]
  simp

end Cslib.Crypto.FrameworkTests.Games
