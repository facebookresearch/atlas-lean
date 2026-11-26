/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Asymptotic
public import CSLibExt.Crypto.Protocols.Commitment.Binding
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Polynomial commitments and fresh evaluation prediction

Kate, Zaverucha and Goldberg, *Polynomial Commitments*, CACR 2010-10 (December 1, 2010),
§3.1, Definition 3.1, pp. 5–6. See also Thaler, *Proofs, Arguments, and Zero-Knowledge*,
§7.3.1 (July 18, 2023 manuscript), for the role of the degree bound and the evaluation point.

The report specifies six operations, two different binding events and prediction at an unqueried
point. It does not give an oracle interface for choosing the disclosed points. The class-relative
security predicate uses a batch chosen before commitment; a separate transcript law allows a batch
requested after seeing the commitment. Neither models sequential adaptive requests or proves an
equivalence of request policies. The prediction point may depend on the entire view. The
transcript length is visible. Observing the *actual* degree budget can change the prior even
without a commitment. The information-theoretic comparison is therefore with the same disclosed
indices and values, including their number, not necessarily with a fresh uniform value. These are
definitions, not security theorems for a construction.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.Commitment

open Cslib.Crypto.Framework

/-- Formal polynomials over the prime field with degree at most `t`, including zero. Using
strict degree less than `t + 1` gives exactly `t + 1` freely chosen coefficients. -/
abbrev PolynomialCommitmentMessage (p : Nat.Primes) (t : ℕ) :=
  ↥(Polynomial.degreeLT (ZMod p.val) (t + 1))

/-- Distributional interface for the six operations at degree bound `t`. Setup at security
parameter `κ` samples a public/secret key pair; the public key determines the prime and all the
remaining operations. The full commitment and verifier are an ordinary correct commitment
scheme. Full opening returns the polynomial and decommitment, and witness creation attaches the
requested index and the polynomial's value to a sampled witness. Every supported honest witness
verifies. Keys range over well-formed public keys; no subsequent operation takes the setup
secret. The PMFs and Boolean functions specify distributions and decisions, not a uniform
implementation or time bound. -/
structure PolynomialCommitmentScheme (t : ℕ) where
  PublicKey : Type
  SecretKey : Type
  prime : PublicKey → Nat.Primes
  Digest : PublicKey → Type
  Opening : PublicKey → Type
  Witness : PublicKey → Type
  setup : ℕ → PMF (PublicKey × SecretKey)
  full : (k : PublicKey) →
    Scheme (PolynomialCommitmentMessage (prime k) t) (Digest k) (Opening k)
  witness : (k : PublicKey) → PolynomialCommitmentMessage (prime k) t →
    ZMod (prime k).val → Opening k → PMF (Witness k)
  verifyEval : (k : PublicKey) → Digest k → ZMod (prime k).val →
    ZMod (prime k).val → Witness k → Bool
  correctEval : ∀ k f c d, (c, d) ∈ ((full k).commit f).support →
    ∀ i w, w ∈ (witness k f i d).support → verifyEval k c i (f.val.eval i) w = true

namespace PolynomialCommitmentScheme

variable {t : ℕ} (S : PolynomialCommitmentScheme t)

local instance (p : Nat.Primes) : NeZero p.val := ⟨p.property.ne_zero⟩

/-- Full opening reveals exactly the original polynomial and its decommitment information. -/
def polynomialCommitmentOpen (k : S.PublicKey) (_c : S.Digest k)
    (f : PolynomialCommitmentMessage (S.prime k) t) (d : S.Opening k) := (f, d)

/-- An honest evaluation opening consists of the requested index, the true value there and a
witness sampled with the same decommitment information as the full opening. -/
noncomputable def polynomialCommitmentEvaluation (k : S.PublicKey)
    (f : PolynomialCommitmentMessage (S.prime k) t) (i : ZMod (S.prime k).val) (d : S.Opening k) :=
  (S.witness k f i d).map fun w => (i, f.val.eval i, w)

/-- For every well-formed key and every honest commitment outcome, the full opening verifies;
at every requested index each possible honest evaluation opening reports that index and the
correct value and verifies against the same commitment. -/
theorem polynomialCommitmentHonest (k : S.PublicKey) (f : PolynomialCommitmentMessage (S.prime k) t)
    {c d} (h : (c, d) ∈ ((S.full k).commit f).support) :
    (S.full k).Accepts (S.polynomialCommitmentOpen k c f d).1 c
      (S.polynomialCommitmentOpen k c f d).2 ∧
    ∀ i a, a ∈ (S.polynomialCommitmentEvaluation k f i d).support →
      a.1 = i ∧ a.2.1 = f.val.eval i ∧ S.verifyEval k c a.1 a.2.1 a.2.2 = true := by
  refine ⟨(S.full k).accepts_of_mem_support h, ?_⟩
  intro i a ha
  rw [polynomialCommitmentEvaluation, PMF.support_map] at ha
  obtain ⟨w, hw, rfl⟩ := ha
  exact ⟨rfl, rfl, S.correctEval k f c d h i w hw⟩

/-- A polynomial binding conflict is the ordinary full-opening binding event, with bounded
formal polynomials as messages. Both openings must verify for one commitment and their
polynomials must differ; a difference in decommitment information alone does not count. -/
abbrev PolynomialBindingConflict (k : S.PublicKey) := BindingWin (S.full k)

/-- An evaluation binding conflict has one commitment and one index. Both evaluations must
verify, and it is their field values, not their witnesses, that must differ. -/
def EvaluationBindingConflict (k : S.PublicKey) (out : S.Digest k × ZMod (S.prime k).val ×
    (ZMod (S.prime k).val × S.Witness k) × (ZMod (S.prime k).val × S.Witness k)) : Prop :=
  let (c, i, (y, w), (z, u)) := out
  S.verifyEval k c i y w = true ∧ S.verifyEval k c i z u = true ∧ y ≠ z

/-- A public batch of distinct field indices in order, leaving room for a fresh prediction.
Honest disclosure uses only the prefix of length at most the sampled polynomial's natural
degree. When the batch is chosen is specified by the sampling experiment, not by this type. -/
structure PolynomialCommitmentBatch (p : Nat.Primes) where
  indices : List (ZMod p.val)
  distinct : indices.Nodup
  room : indices.length < p.val

/-- The disclosed indices are the initial segment of the requested batch limited by the
actual natural degree, not by the setup bound. A constant has no disclosures at any bound. -/
def polynomialCommitmentDisclosedIndices {p : Nat.Primes} (Q : PolynomialCommitmentBatch p)
    (f : PolynomialCommitmentMessage p t) := Q.indices.take f.val.natDegree

/-- The observer sees the commitment and the ordered list of honest triples (index, value,
witness), including the length of this list. Neither the polynomial nor the decommitment is
supplied as a separate input. This record alone implies no secrecy. -/
abbrev PolynomialCommitmentView (k : S.PublicKey) := S.Digest k ×
  List (ZMod (S.prime k).val × ZMod (S.prime k).val × S.Witness k)

/-- Honest transcript for one request batch selected *after* seeing the commitment. Given the
public key, draw a uniform bounded polynomial and commit to it. The request rule receives the
commitment, not the polynomial or decommitment; it chooses the whole ordered batch before any
answers are returned. Record the sampled polynomial, the requested batch (including its unserved
tail), and the view containing the commitment and honest replies. This is not an adaptive oracle. -/
noncomputable def polynomialCommitmentRequestedTrace (k : S.PublicKey)
    (request : S.Digest k → PMF (PolynomialCommitmentBatch (S.prime k))) :
    PMF (PolynomialCommitmentMessage (S.prime k) t ×
      PolynomialCommitmentBatch (S.prime k) × S.PolynomialCommitmentView k) := by
  classical
  let e := Polynomial.degreeLTEquiv (ZMod (S.prime k).val) (t + 1)
  let μ := (Cslib.Probability.PMF.uniformOfFintype (Fin (t + 1) → ZMod (S.prime k).val)).map e.symm
  exact μ.bind fun f => ((S.full k).commit f).bind fun cd => (request cd.1).bind fun Q =>
    let answers := (polynomialCommitmentDisclosedIndices Q f).mapM fun i =>
      S.polynomialCommitmentEvaluation k f i cd.2
    answers.map fun a => (f, Q, cd.1, a)

/-- Joint law of the polynomial and visible transcript for a fixed public key and a batch
specified before commitment. The polynomial is uniform on all formal polynomials of degree at
most `t`, not conditioned on exact degree. For one honest commitment, witnesses use the same
opening information and fresh witness coins. The visible prefix has length the minimum of batch
size and natural degree (zero for constants and zero). The request ignores the commitment. -/
noncomputable def polynomialCommitmentObservation (k : S.PublicKey)
    (Q : PolynomialCommitmentBatch (S.prime k)) :
    PMF (PolynomialCommitmentMessage (S.prime k) t × S.PolynomialCommitmentView k) :=
  (S.polynomialCommitmentRequestedTrace k fun _ => PMF.pure Q).map fun a => (a.1, a.2.2)

/-- A prediction rule can randomize its batch and retain its coins by selecting a continuation
with the batch. After seeing the commitment and all honest answers it selects an index and a
field-value guess, possibly at random. Neither stage receives the polynomial as a separate input. -/
abbrev PolynomialCommitmentPredictor := (k : S.PublicKey) →
  PMF (PolynomialCommitmentBatch (S.prime k) ×
    (S.PolynomialCommitmentView k → PMF (ZMod (S.prime k).val × ZMod (S.prime k).val)))

/-- A fresh prediction is correct at its chosen index and that index occurs nowhere in the
visible list of answers. In particular a correct answer copied at a disclosed index is not a
successful fresh prediction. -/
def PolynomialCommitmentFreshPrediction (k : S.PublicKey)
    (f : PolynomialCommitmentMessage (S.prime k) t)
    (v : S.PolynomialCommitmentView k) (iy : ZMod (S.prime k).val × ZMod (S.prime k).val) : Prop :=
  iy.1 ∉ v.2.map Prod.fst ∧ f.val.eval iy.1 = iy.2

/-- Absolute fresh-prediction success, averaged over setup, the uniform bounded polynomial,
honest commitment and witness coins, and the prediction rule. A previously disclosed index
never counts, even if its value is repeated correctly. -/
noncomputable def polynomialCommitmentPrediction (κ : ℕ)
    (A : S.PolynomialCommitmentPredictor) : ℝ := by
  classical
  exact winProb ((S.setup κ).bind fun ks => (A ks.1).bind fun rule =>
    (S.polynomialCommitmentObservation ks.1 rule.1).bind fun fv =>
      (rule.2 fv.2).map fun iy => decide (S.PolynomialCommitmentFreshPrediction ks.1 fv.1 fv.2 iy))

/-- A uniform independent field guess agrees with any fixed target value with probability
`1 / p`. This blind baseline is positive and does not involve a commitment or a witness. -/
theorem polynomialCommitmentBlindGuess (p : Nat.Primes) (y : ZMod p.val) :
    winProb ((Cslib.Probability.PMF.uniformOfFintype (ZMod p.val)).map fun z => decide (z = y)) =
      1 / (p.val : ℝ) := by
  have single : (Finset.univ.filter fun z : ZMod p.val => z = y) = {y} := by ext; simp
  rw [winProb_map_uniform]
  simp [single]

/-- Unconditional fresh-value hiding at a given parameter: at each generated public key and
for every fixed batch and fresh index, adding the commitment and witnesses to the disclosed
index/value list does not change the conditional distribution of the target value. The
cross-multiplied equation uses joint masses, so no conditional probability at a null view is
needed. In particular, information-theoretic hiding is not impossibility of a lucky guess. -/
def PolynomialCommitmentUnconditionalHiding (κ : ℕ) : Prop :=
  ∀ k ∈ ((S.setup κ).map Prod.fst).support, ∀ (Q : PolynomialCommitmentBatch (S.prime k))
    (v : S.PolynomialCommitmentView k) (i y : ZMod (S.prime k).val), i ∉ v.2.map Prod.fst →
    let μ := S.polynomialCommitmentObservation k Q
    let bare := fun a : S.PolynomialCommitmentView k => a.2.map fun x => (x.1, x.2.1)
    (μ.map (fun a => (a.2, a.1.val.eval i))) (v, y) * (μ.map (fun a => bare a.2)) (bare v) =
      (μ.map Prod.snd) v * (μ.map (fun a => (bare a.2, a.1.val.eval i))) (bare v, y)

/-- Probability of a report satisfying a predicate: draw the setup key pair, discard the secret
key and test a report sampled from the law at that public key. -/
noncomputable def polynomialCommitmentReportProbability (κ : ℕ) {O : S.PublicKey → Type}
    (bad : ∀ k, O k → Prop) (law : ∀ k, PMF (O k)) : ℝ := by
  classical
  exact winProb ((S.setup κ).bind fun ks => (law ks.1).map fun o => decide (bad ks.1 o))

/-- Conditional laws of the two full openings reported for one commitment, given the public key.
They may be randomized but are not given the discarded secret key. -/
abbrev PolynomialBindingReports := (k : S.PublicKey) → PMF (S.Digest k ×
  (PolynomialCommitmentMessage (S.prime k) t × S.Opening k) ×
  (PolynomialCommitmentMessage (S.prime k) t × S.Opening k))

/-- Conditional laws of one commitment and two evaluation claims sharing an index, given the
public key. These reports need not be honest outputs of the commitment or witness operations. -/
abbrev EvaluationBindingReports := (k : S.PublicKey) → PMF (S.Digest k × ZMod (S.prime k).val ×
  (ZMod (S.prime k).val × S.Witness k) × (ZMod (S.prime k).val × S.Witness k))

end PolynomialCommitmentScheme

/-- Choose class-relative fresh prediction or unconditional no-additional-information hiding
in the pre-commitment batch model. Both binding requirements stay class-relative. -/
inductive PolynomialCommitmentHidingMode where
  | computational
  | unconditional

/-- Class-relative security for the **pre-commitment batch** experiment. At parameter `κ`,
setup at bound `t κ` supplies the prime as part of the public key. Each binding conflict must
have negligible probability for every family in its supplied report class. In computational
mode every family in a third supplied class must have negligible absolute fresh-prediction
success; in unconditional mode the full view must give exactly no extra information beyond the
public evaluations. These arbitrary classes are not a definition of PPT. Empty classes impose
no computational tests; nonempty classes need not include all uniform PPT rules. In computational
mode, if the predictor class includes an independent uniform guess at an always-fresh index,
the setup average of `1 / p` must be negligible. Unconditional hiding imposes no such bound on
absolute prediction success. -/
def PolynomialCommitmentRelativeBatch {t : ℕ → ℕ} (S : (κ : ℕ) → PolynomialCommitmentScheme (t κ))
    (polyClass : ((κ : ℕ) → (S κ).PolynomialBindingReports) → Prop)
    (evalClass : ((κ : ℕ) → (S κ).EvaluationBindingReports) → Prop)
    (predictionClass : ((κ : ℕ) → (S κ).PolynomialCommitmentPredictor) → Prop)
    (mode : PolynomialCommitmentHidingMode) : Prop :=
  AsymptoticallySecure
    (fun κ => (S κ).polynomialCommitmentReportProbability κ (S κ).PolynomialBindingConflict)
    polyClass ∧
  AsymptoticallySecure
    (fun κ => (S κ).polynomialCommitmentReportProbability κ (S κ).EvaluationBindingConflict)
    evalClass ∧
  match mode with
  | .computational =>
    AsymptoticallySecure (fun κ => (S κ).polynomialCommitmentPrediction κ) predictionClass
  | .unconditional => ∀ κ, (S κ).PolynomialCommitmentUnconditionalHiding κ

end Cslib.Crypto.Protocols.Commitment
