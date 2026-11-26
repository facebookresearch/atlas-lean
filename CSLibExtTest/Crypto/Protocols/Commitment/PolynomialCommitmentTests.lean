/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.Protocols.Commitment.PolynomialCommitment
import Mathlib.Tactic.NormNum.Prime

/-! # Polynomial commitments: honest operations and boundary cases

The example commits in the clear and verifies by equality and ordinary polynomial evaluation.
It illustrates correctness only. No security assumption or security property is asserted.
-/

namespace Cslib.Crypto.Protocols.Commitment.PolynomialCommitmentTests

open Polynomial PolynomialCommitmentScheme

private abbrev five : Nat.Primes := ⟨5, by decide⟩

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩

private noncomputable def transparent (t : ℕ) : PolynomialCommitmentScheme t where
  PublicKey := Unit
  SecretKey := Unit
  prime _ := five
  Digest _ := Polynomial (ZMod 5)
  Opening _ := Bool
  Witness _ := Bool
  setup _ := PMF.pure ((), ())
  full _ := {
    commit := fun f => (Cslib.Probability.PMF.uniformOfFintype Bool).map fun d => (f.val, d)
    verify := fun f c _ => decide (f.val = c)
    correct := by
      rintro f c d h
      rw [PMF.support_map] at h
      obtain ⟨_, _, h⟩ := h
      exact decide_eq_true (congrArg Prod.fst h) }
  witness _ _ _ d := PMF.pure d
  verifyEval _ c i y _ := decide (c.eval i = y)
  correctEval := by
    rintro k f c d h i w _
    rw [PMF.support_map] at h
    obtain ⟨_, _, h⟩ := h
    have hc : f.val = c := congrArg Prod.fst h
    simp [← hc]

private noncomputable def linear : PolynomialCommitmentMessage five 2 :=
  ⟨X + C 2, by
    change (X + C (2 : ZMod 5)) ∈ degreeLT (ZMod 5) 3
    rw [mem_degreeLT]
    exact (degree_add_le _ _).trans_lt
      (max_lt (by rw [degree_X]; decide) (degree_C_le.trans_lt (by decide)))⟩

private def batch : PolynomialCommitmentBatch five := ⟨[0, 1], by decide, by decide⟩

-- A genuinely nonconstant message: over F₅, f(4) = 1 though the setup permits quadratics.
example : linear.val.eval 4 = 1 := by change (X + C (2 : ZMod 5)).eval 4 = 1; simp; decide

example (b : Bool) : (linear.val, b) ∈ (((transparent 2).full ()).commit linear).support := by
  change (_, b) ∈ ((Cslib.Probability.PMF.uniformOfFintype Bool).map
    fun d => ((linear.val : Polynomial (ZMod 5)), d)).support
  rw [PMF.support_map]
  exact ⟨b, by simp [Cslib.Probability.PMF.uniformOfFintype], rfl⟩

example (b : Bool) :
    (4, 1, b) ∈ ((transparent 2).polynomialCommitmentEvaluation () linear 4 b).support := by
  have he : linear.val.eval 4 = 1 := by change (X + C (2 : ZMod 5)).eval 4 = 1; simp; decide
  change ((4 : ZMod 5), (1 : ZMod 5), b) ∈
    ((PMF.pure b).map fun w => ((4 : ZMod 5), linear.val.eval 4, w)).support
  rw [PMF.support_map]
  exact ⟨b, by simp, by rw [he]⟩

example (b : Bool) : ((transparent 2).full ()).Accepts linear linear.val b ∧
    (transparent 2).verifyEval () linear.val 4 1 b = true := by
  change decide (linear.val = linear.val) = true ∧ decide (linear.val.eval 4 = 1) = true
  simp [linear]; decide

-- Different ancillary data cannot make an equal message or an equal evaluation value conflict.
example (S : PolynomialCommitmentScheme 2) (k : S.PublicKey) (c : S.Digest k)
    (f : PolynomialCommitmentMessage (S.prime k) 2) (d d' : S.Opening k) :
    ¬ S.PolynomialBindingConflict k (c, (f, d), (f, d')) := fun h => h.2.2 rfl

example (S : PolynomialCommitmentScheme 2) (k : S.PublicKey) (c : S.Digest k)
    (i y : ZMod (S.prime k).val) (w w' : S.Witness k) :
    ¬ S.EvaluationBindingConflict k (c, i, (y, w), (y, w')) := fun h => h.2.2 rfl

example : polynomialCommitmentDisclosedIndices batch linear = [0] := by
  simp [polynomialCommitmentDisclosedIndices, batch, linear]

example : polynomialCommitmentDisclosedIndices batch
    (0 : PolynomialCommitmentMessage five 2) = [] := by
  simp [polynomialCommitmentDisclosedIndices]

example (a : ZMod 5) : ∃ f : PolynomialCommitmentMessage five 0,
    f.val = C a ∧ polynomialCommitmentDisclosedIndices batch f = [] := by
  refine ⟨⟨C a, ?_⟩, rfl, ?_⟩
  · rw [mem_degreeLT]; exact degree_C_le.trans_lt (by decide)
  · simp [polynomialCommitmentDisclosedIndices]

-- The bound is inclusive, but larger degrees are excluded.
example : (X ^ 2 : Polynomial (ZMod 5)) ∈ degreeLT (ZMod 5) 3 := by
  rw [mem_degreeLT, degree_X_pow]; decide

example : (X ^ 3 : Polynomial (ZMod 5)) ∉ degreeLT (ZMod 5) 3 := by
  rw [mem_degreeLT, degree_X_pow]; simp

-- Formal equality is not pointwise equality on a finite field. This uses no commitment.
example : (X ^ 5 : Polynomial (ZMod 5)) ≠ X ∧
    ∀ i : ZMod 5, (X ^ 5 : Polynomial (ZMod 5)).eval i = X.eval i := by
  constructor
  · intro h
    simpa using congrArg natDegree h
  · simp only [eval_pow, eval_X]; decide

-- A correct value counts at a fresh index, not at one already disclosed.
example (b : Bool) : ¬ (transparent 2).PolynomialCommitmentFreshPrediction () linear
    (linear.val, [(0, linear.val.eval 0, b)]) (0, linear.val.eval 0) := by
  simp [PolynomialCommitmentFreshPrediction]

example (b : Bool) : (transparent 2).PolynomialCommitmentFreshPrediction () linear
    (linear.val, [(0, linear.val.eval 0, b)]) (1, linear.val.eval 1) := by
  refine ⟨?_, rfl⟩
  change (1 : ZMod 5) ∉ [0]
  decide

-- The requested batch is actually sampled from the policy at the observed commitment.
example {t : ℕ} (S : PolynomialCommitmentScheme t) (k : S.PublicKey)
    (request : S.Digest k → PMF (PolynomialCommitmentBatch (S.prime k)))
    (f : PolynomialCommitmentMessage (S.prime k) t) (Q : PolynomialCommitmentBatch (S.prime k))
    (v : S.PolynomialCommitmentView k)
    (h : (f, Q, v) ∈ (S.polynomialCommitmentRequestedTrace k request).support) :
    Q ∈ (request v.1).support := by
  simp only [polynomialCommitmentRequestedTrace, PMF.support_bind, Set.mem_iUnion,
    PMF.support_map, Set.mem_image] at h
  obtain ⟨_, _, cd, _, Q', hQ, a, _, eq⟩ := h
  have hb : Q' = Q := congrArg (fun z => z.2.1) eq
  have hc : cd.1 = v.1 := congrArg (fun z => z.2.2.1) eq
  rw [← hb, ← hc]
  exact hQ

-- Empty report and predictor classes make no computational assertion about the interface.
example {t : ℕ → ℕ} (S : (n : ℕ) → PolynomialCommitmentScheme (t n)) :
    PolynomialCommitmentRelativeBatch S (fun _ => False) (fun _ => False) (fun _ => False)
      .computational :=
  ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩

example : ¬ Cslib.Crypto.Framework.NegligibleAdv (fun _ => 1 / (5 : ℝ)) :=
  Cslib.Crypto.Framework.not_negligibleAdv_const (by norm_num)

end Cslib.Crypto.Protocols.Commitment.PolynomialCommitmentTests
