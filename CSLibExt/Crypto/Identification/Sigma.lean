/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Advantage
public import CSLibExt.Crypto.Identification.Schnorr

/-!
# Sigma protocols: completeness, special soundness, (special) honest-verifier zero knowledge

A **Sigma protocol** for a relation `Rel : X → W → Prop` (statements `x : X`, witnesses `w : W`) is
a three-move public-coin protocol: the prover, holding `(x, w)` and random coins `k : K`, sends a
commitment `a = commit x w k : Cm`; the verifier sends a uniform challenge `e : Ch`; the prover
answers `z = respond x w k e : Z`; and the verifier accepts when `verify x a e z = true`.
`SigmaProtocol X W K Cm Ch Z` bundles the four algorithms with the relation. The prover's coins and
the challenge are uniform over finite types, the coin convention of
`Cslib.Crypto.Signatures.Lamport` and `Cslib.Crypto.Identification.Schnorr`.

The three properties are predicates on the abstraction:
* `Complete`: for every `(x, w)` in the relation, every honest transcript is accepted.
* `SpecialSound ext`: from two accepting transcripts `(a, e, z)`, `(a, e', z')` with the same
  commitment and `e ≠ e'`, the extractor `ext` computes a witness.
* `HVZK sim` (perfect honest-verifier zero knowledge): for every `(x, w)` in the relation, the
  distribution `transcript x w` of honest transcripts equals the distribution `sim x` produced by a
  simulator that sees only the statement. `StatHVZK sim ε` is the statistical version: no
  distinguisher tells the two distributions apart with advantage more than `ε`
  (`HVZK.statHVZK_zero`: perfect implies `ε = 0`).
* `SpecialHVZK sim` (perfect **special** honest-verifier zero knowledge): the simulator also
  receives the challenge `e`, and for every `(x, w)` in the relation and **every** challenge `e`
  the honest commitment–response distribution `challengeTranscript x w e` (uniform prover coins,
  challenge fixed to `e`) equals `sim x e`. `HVZK` only asks for equality on average over a
  uniform challenge. `SpecialHVZK.hvzk`: special HVZK implies HVZK, with the simulator
  `uniformChallengeSim sim` that draws a uniform challenge and runs `sim` on it.

Consequences proved for every Sigma protocol:
* `verify_of_mem_support_transcript`: under completeness, honest transcripts are accepted with
  probability one.
* `verify_of_mem_support_sim`: under completeness and perfect HVZK, simulated transcripts for a
  true statement are accepted with probability one.
* `exists_witness_of_verify_of_verify`: under special soundness, a statement with two accepting
  transcripts sharing a commitment has a witness.
* `winProb_cheatGame_le` (**soundness error for false statements**): under special soundness, a
  cheating prover for a statement with no witness at all convinces the verifier with probability
  at most `1 / |Ch|`. This is soundness for the language of true statements, not knowledge
  soundness: it says nothing about a prover that does not know an existing witness, which needs a
  rewinding (knowledge-extraction) experiment that this file does not define.

**Schnorr.** `Schnorr.sigma q g` is the Schnorr identification protocol of
`Cslib.Crypto.Identification.Schnorr` as a Sigma protocol for the discrete-logarithm relation
`gpow g x = y`, with statements `y` in `{y // y ^ q = 1}`. `Schnorr.sigma_complete`,
`Schnorr.sigma_specialSound` (with extractor `Schnorr.sigmaExtract`) and `Schnorr.sigma_hvzk` are
bridges to that file's `accepts_honest`, `extract_spec` and `transcript_eq_simulate`; nothing is
re-proved. `Schnorr.sigma_specialHVZK` proves special HVZK with the per-challenge simulator
`Schnorr.sigmaSimAt` (for challenge `r`: a uniform answer `s` and the commitment
`g ^ s * (y ^ r)⁻¹`, the simulator of `Schnorr.simulate` with the challenge fixed).

Fiat–Shamir (from a Sigma protocol to a signature scheme) is out of scope: it needs the
random-oracle model, which the Framework defers.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 12.5 (identification schemes and the Schnorr identification scheme, Figure 12.2; the
  security proof of Theorem 12.11 uses transcript simulation and extraction from two accepting
  transcripts, the two properties abstracted here, but Theorem 12.11 itself, security against
  impersonation under the discrete-logarithm assumption, is not proved here).
* I. Damgård, *On Σ-protocols*, lecture notes, Aarhus University, 2010 (the definitions of
  special soundness and special honest-verifier zero knowledge, formalized as `SpecialSound` and
  `SpecialHVZK`).
-/

@[expose] public section

namespace Cslib.Crypto.Identification

open Finset Cslib.Crypto.Framework

/-- A **Sigma protocol** (three-move public-coin protocol) for the relation `Rel`:
statements in `X`, witnesses in `W`, prover coins in `K`, commitments in `Cm`, challenges in `Ch`
and responses in `Z`. The identification schemes of Katz and Lindell, Section 12.5, have this
shape. -/
structure SigmaProtocol (X W K Cm Ch Z : Type*) where
  /-- The relation: `w` is a witness for the statement `x`. -/
  Rel : X → W → Prop
  /-- The prover's first message, from the statement, the witness and its coins. -/
  commit : X → W → K → Cm
  /-- The prover's answer to the challenge. -/
  respond : X → W → K → Ch → Z
  /-- The verifier's check on a transcript `(a, e, z)` for the statement `x`. -/
  verify : X → Cm → Ch → Z → Bool

namespace SigmaProtocol

variable {X W K Cm Ch Z : Type*} (P : SigmaProtocol X W K Cm Ch Z)

/-- **Completeness**: for every statement–witness pair in the relation, all prover coins and all
challenges, the honest transcript is accepted. -/
def Complete : Prop :=
  ∀ x w, P.Rel x w → ∀ k e, P.verify x (P.commit x w k) e (P.respond x w k e) = true

/-- **Special soundness** with extractor `ext`: from two accepting transcripts `(a, e, z)` and
`(a, e', z')` for `x` with the same commitment and different challenges, `ext x a e z e' z'` is a
witness for `x`. -/
def SpecialSound (ext : X → Cm → Ch → Z → Ch → Z → W) : Prop :=
  ∀ x a e z e' z', e ≠ e' → P.verify x a e z = true → P.verify x a e' z' = true →
    P.Rel x (ext x a e z e' z')

/-- Special soundness: a statement with two accepting transcripts that share a commitment and
differ in the challenge has a witness. -/
theorem exists_witness_of_verify_of_verify {ext : X → Cm → Ch → Z → Ch → Z → W}
    (hP : P.SpecialSound ext) {x : X} {a : Cm} {e e' : Ch} {z z' : Z} (he : e ≠ e')
    (h₁ : P.verify x a e z = true) (h₂ : P.verify x a e' z' = true) : ∃ w, P.Rel x w :=
  ⟨_, hP x a e z e' z' he h₁ h₂⟩

section Transcripts

variable [Fintype K] [Nonempty K] [Fintype Ch] [Nonempty Ch]

/-- The honest transcript for the statement `x`, the witness `w`, coins `k` and challenge `e`. -/
def honestTranscript (x : X) (w : W) (ke : K × Ch) : Cm × Ch × Z :=
  (P.commit x w ke.1, ke.2, P.respond x w ke.1 ke.2)

/-- The distribution of honest transcripts: uniform prover coins and a uniform challenge (an
honest verifier). -/
noncomputable def transcript (x : X) (w : W) : PMF (Cm × Ch × Z) :=
  (Cslib.Probability.PMF.uniformOfFintype (K × Ch)).map (P.honestTranscript x w)

/-- **Perfect honest-verifier zero knowledge** with simulator `sim`: for every statement–witness
pair in the relation, the honest transcripts and the simulator's output, computed from the
statement alone, have the same distribution. -/
def HVZK (sim : X → PMF (Cm × Ch × Z)) : Prop :=
  ∀ x w, P.Rel x w → P.transcript x w = sim x

/-- **Statistical honest-verifier zero knowledge** with simulator `sim` and error `ε`: for every
statement–witness pair in the relation, no distinguisher `D` tells honest transcripts from
simulated ones with advantage more than `ε`. -/
def StatHVZK (sim : X → PMF (Cm × Ch × Z)) (ε : ℝ) : Prop :=
  ∀ x w, P.Rel x w → ∀ D : Cm × Ch × Z → Bool,
    advantage ((P.transcript x w).map D) ((sim x).map D) ≤ ε

/-- The honest commitment–response distribution for the statement `x`, the witness `w` and a
**fixed** challenge `e`: uniform prover coins `k`, output `(commit x w k, respond x w k e)`. -/
noncomputable def challengeTranscript (x : X) (w : W) (e : Ch) : PMF (Cm × Z) :=
  (Cslib.Probability.PMF.uniformOfFintype K).map fun k => (P.commit x w k, P.respond x w k e)

/-- **Perfect special honest-verifier zero knowledge** with simulator `sim` (Damgård, *On
Σ-protocols*): the simulator receives the statement and the challenge `e`, and for every
statement–witness pair in the relation and **every** challenge `e`, the honest
commitment–response distribution for `e` equals `sim x e`. This is stronger than `HVZK`, which
only constrains a uniform challenge; `SpecialHVZK.hvzk` derives `HVZK` from it. -/
def SpecialHVZK (sim : X → Ch → PMF (Cm × Z)) : Prop :=
  ∀ x w, P.Rel x w → ∀ e, P.challengeTranscript x w e = sim x e

/-- The uniform-challenge simulator built from a per-challenge simulator `sim`: draw a uniform
challenge `e`, then `(a, z) ← sim x e`, and output `(a, e, z)`. -/
noncomputable def uniformChallengeSim (sim : X → Ch → PMF (Cm × Z)) (x : X) :
    PMF (Cm × Ch × Z) :=
  (Cslib.Probability.PMF.uniformOfFintype Ch).bind fun e =>
    (sim x e).map fun az => (az.1, e, az.2)

/-- **Special HVZK implies HVZK**: averaging a per-challenge simulator over a uniform challenge
(`uniformChallengeSim`) simulates the honest transcripts, since sampling the coins and the
challenge jointly is sampling the challenge first and then the coins
(`Cslib.Probability.PMF.uniformOfFintype_prod`). -/
theorem SpecialHVZK.hvzk {P : SigmaProtocol X W K Cm Ch Z} {sim : X → Ch → PMF (Cm × Z)}
    (h : P.SpecialHVZK sim) : P.HVZK (uniformChallengeSim sim) := by
  intro x w hw
  rw [transcript, ← Cslib.Probability.PMF.uniformOfFintype_map_equiv (Equiv.prodComm Ch K),
    ← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.map_comp, PMF.map_bind,
    uniformChallengeSim]
  congr 1
  funext e
  rw [← h x w hw e, challengeTranscript, PMF.map_comp, PMF.map_comp]
  rfl

/-- Perfect honest-verifier zero knowledge is statistical zero knowledge with error `0`. -/
theorem HVZK.statHVZK_zero {P : SigmaProtocol X W K Cm Ch Z} {sim : X → PMF (Cm × Ch × Z)}
    (h : P.HVZK sim) : P.StatHVZK sim 0 := by
  intro x w hw D
  rw [h x w hw, advantage, sub_self, abs_zero]

/-- Under completeness, every transcript in the support of the honest distribution is accepted. -/
theorem verify_of_mem_support_transcript (hP : P.Complete) {x : X} {w : W} (hw : P.Rel x w)
    {t : Cm × Ch × Z} (ht : t ∈ (P.transcript x w).support) :
    P.verify x t.1 t.2.1 t.2.2 = true := by
  rw [transcript, PMF.support_map] at ht
  obtain ⟨ke, -, rfl⟩ := ht
  exact hP x w hw ke.1 ke.2

/-- Under completeness and perfect honest-verifier zero knowledge, for a statement with a witness
every simulated transcript is accepted, although the simulator never sees the witness. -/
theorem verify_of_mem_support_sim (hP : P.Complete) {sim : X → PMF (Cm × Ch × Z)}
    (hZK : P.HVZK sim) {x : X} {w : W} (hw : P.Rel x w) {t : Cm × Ch × Z}
    (ht : t ∈ (sim x).support) : P.verify x t.1 t.2.1 t.2.2 = true :=
  P.verify_of_mem_support_transcript hP hw (by rwa [hZK x w hw])

end Transcripts

/-! ### Soundness error -/

section Soundness

variable {R : Type*} [Fintype R] [Nonempty R] [Fintype Ch] [Nonempty Ch]

/-- The experiment of a cheating prover for the statement `x` with coins in `R`: from its coins
`r` it sends the commitment `a r`; on the uniform challenge `e` it answers `z r e`; the
experiment outputs whether the verifier accepts. -/
noncomputable def cheatGame (x : X) (a : R → Cm) (z : R → Ch → Z) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (R × Ch)).map fun ω => P.verify x (a ω.1) ω.2 (z ω.1 ω.2)

/-- **Soundness error for false statements**: under special soundness, a cheating prover for a
statement `x` with **no witness at all** (`hx`) answers at most one challenge per commitment, so it
convinces the honest verifier with probability at most `1 / |Ch|`.

This is soundness for the language of true statements, not knowledge soundness. The hypothesis
`hx` says that `x` is false, which is much stronger than saying that the prover does not know an
existing witness. In the Schnorr setting with a generator `g` of the order-`q` subgroup every
statement has a witness, so `hx` never holds there, and this theorem does not model the
impersonator of Katz and Lindell, Theorem 12.11. A knowledge-soundness statement needs a rewinding
(knowledge-extraction) experiment, which is not defined here. -/
theorem winProb_cheatGame_le {ext : X → Cm → Ch → Z → Ch → Z → W} (hP : P.SpecialSound ext)
    {x : X} (hx : ∀ w, ¬ P.Rel x w) (a : R → Cm) (z : R → Ch → Z) :
    winProb (P.cheatGame x a z) ≤ 1 / Fintype.card Ch := by
  classical
  rw [cheatGame, winProb_map_uniform]
  have hone : ∀ r : R, (univ.filter fun e : Ch => P.verify x (a r) e (z r e) = true).card ≤ 1 := by
    intro r
    refine Finset.card_le_one.mpr fun e he e' he' => ?_
    by_contra hne
    simp only [mem_filter, mem_univ, true_and] at he he'
    exact hx _ (hP x (a r) e (z r e) e' (z r e') hne he he')
  have hcard : (univ.filter fun ω : R × Ch => P.verify x (a ω.1) ω.2 (z ω.1 ω.2) = true).card ≤
      Fintype.card R := by
    rw [card_filter, Fintype.sum_prod_type]
    calc ∑ r : R, ∑ e : Ch, (if P.verify x (a r) e (z r e) = true then 1 else 0)
        = ∑ r : R, (univ.filter fun e : Ch => P.verify x (a r) e (z r e) = true).card := by
          simp only [card_filter]
      _ ≤ ∑ _r : R, 1 := sum_le_sum fun r _ => hone r
      _ = Fintype.card R := by simp
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hC : (0 : ℝ) < Fintype.card Ch := by exact_mod_cast Fintype.card_pos
  rw [Fintype.card_prod, Nat.cast_mul, div_le_div_iff₀ (mul_pos hR hC) hC]
  have : ((univ.filter fun ω : R × Ch => P.verify x (a ω.1) ω.2 (z ω.1 ω.2) = true).card : ℝ) ≤
      Fintype.card R := by exact_mod_cast hcard
  nlinarith

end Soundness

end SigmaProtocol

/-! ### Schnorr identification as a Sigma protocol -/

namespace Schnorr

open Cslib.Crypto.PublicKey

variable {G : Type*} [CommGroup G] [DecidableEq G]

/-- The **Schnorr identification protocol** as a Sigma protocol (Katz and Lindell, Section 12.5,
Figure 12.2): statements are group elements `y` with `y ^ q = 1`, witnesses are discrete
logarithms `x` with `g ^ x = y`, the prover's coins and the challenge are in `ZMod q`, the
commitment is `g ^ k`, the answer is `r x + k`, and the verifier checks `Schnorr.Accepts`
(`sigma_verify_eq_true_iff`). -/
def sigma (q : ℕ) (g : G) :
    SigmaProtocol {y : G // y ^ q = 1} (ZMod q) (ZMod q) G (ZMod q) (ZMod q) where
  Rel y x := gpow g x = y.1
  commit _ _ k := gpow g k
  respond _ x k r := respond x k r
  verify y I r s := decide (gpow g s * (gpow y.1 r)⁻¹ = I)

/-- The **per-challenge Schnorr simulator**: for the challenge `r`, a uniform answer `s` and the
commitment `g ^ s * (y ^ r)⁻¹`, computed from the statement `y` alone. It is `Schnorr.simulate`
with the challenge fixed to `r`. -/
noncomputable def sigmaSimAt (q : ℕ) [NeZero q] (g : G) (y : {y : G // y ^ q = 1}) (r : ZMod q) :
    PMF (G × ZMod q) :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod q)).map fun s => (gpow g s * (gpow y.1 r)⁻¹, s)

variable {q : ℕ} {g : G}

/-- The Sigma-protocol verifier is `Schnorr.Accepts`. -/
theorem sigma_verify_eq_true_iff {y : {y : G // y ^ q = 1}} {I : G} {r s : ZMod q} :
    (sigma q g).verify y I r s = true ↔ Accepts g y.1 I r s :=
  decide_eq_true_iff

/-- **Completeness** of Schnorr as a Sigma protocol, from `Schnorr.accepts_honest`. -/
theorem sigma_complete [NeZero q] (hg : g ^ q = 1) : (sigma q g).Complete := by
  rintro ⟨y, hy⟩ x rfl k r
  exact sigma_verify_eq_true_iff.2 (accepts_honest hg x k r)

/-- The Schnorr extractor `(s - s') / (r - r')`, which ignores the statement and the commitment. -/
def sigmaExtract {q : ℕ} (_y : {y : G // y ^ q = 1}) (_I : G) (r s r' s' : ZMod q) : ZMod q :=
  extract r s r' s'

/-- **Special soundness** of Schnorr as a Sigma protocol, from `Schnorr.extract_spec`. -/
theorem sigma_specialSound [Fact q.Prime] (hg : g ^ q = 1) :
    (sigma q g).SpecialSound sigmaExtract := by
  rintro ⟨y, hy⟩ I r s r' s' hrr h₁ h₂
  exact extract_spec hg hy hrr (sigma_verify_eq_true_iff.1 h₁) (sigma_verify_eq_true_iff.1 h₂)

/-- The honest transcripts of the Sigma protocol are those of `Schnorr.transcript`. -/
theorem sigma_transcript [NeZero q] (y : {y : G // y ^ q = 1}) (x : ZMod q) :
    (sigma q g).transcript y x = transcript g x :=
  rfl

/-- **Perfect honest-verifier zero knowledge** of Schnorr as a Sigma protocol, with the simulator
`Schnorr.simulate`, from `Schnorr.transcript_eq_simulate`. -/
theorem sigma_hvzk [NeZero q] (hg : g ^ q = 1) :
    (sigma q g).HVZK fun y => simulate g y.1 := by
  rintro ⟨y, hy⟩ x rfl
  rw [sigma_transcript]
  exact transcript_eq_simulate hg x

/-- **Perfect special honest-verifier zero knowledge** of Schnorr as a Sigma protocol, with the
per-challenge simulator `sigmaSimAt`: for every challenge `r`, the prover's answer `r x + k` is
uniform when `k` is, and the commitment `g ^ k` is then `g ^ s * (y ^ r)⁻¹`. -/
theorem sigma_specialHVZK [NeZero q] (hg : g ^ q = 1) :
    (sigma q g).SpecialHVZK (sigmaSimAt q g) := by
  rintro ⟨y, hy⟩ x rfl r
  have hcomp : (fun k : ZMod q => ((sigma q g).commit ⟨gpow g x, hy⟩ x k,
      (sigma q g).respond ⟨gpow g x, hy⟩ x k r)) =
      (fun s : ZMod q => (gpow g s * (gpow (gpow g x) r)⁻¹, s)) ∘ Equiv.addLeft (r * x) := by
    funext k
    simp only [sigma, Function.comp, Equiv.coe_addLeft, respond, Prod.mk.injEq, and_true]
    rw [gpow_add hg, mul_comm r x, gpow_mul hg, mul_comm (gpow (gpow g x) r) (gpow g k),
      mul_inv_cancel_right]
  rw [SigmaProtocol.challengeTranscript, hcomp, ← PMF.map_comp,
    Cslib.Probability.PMF.uniformOfFintype_map_equiv]
  rfl

end Schnorr

end Cslib.Crypto.Identification
