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
Finite observation laws distinguish prediction probability from unconditional hiding. These
are distributional boundary checks, not security claims about a cryptographic construction.
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

private def noQueries : PolynomialCommitmentBatch five := ⟨[], by simp, by decide⟩

private abbrev Message := PolynomialCommitmentMessage five 0

private noncomputable def prior : PMF Message :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin 1 → ZMod 5)).map (degreeLTEquiv (ZMod 5) 1).symm

private theorem prior_full (f : Message) : f ∈ prior.support := by
  rw [prior, PMF.support_map]
  exact ⟨(degreeLTEquiv (ZMod 5) 1) f, by simp [Cslib.Probability.PMF.uniformOfFintype],
    (degreeLTEquiv (ZMod 5) 1).symm_apply_apply f⟩

private def reveal (f : Message) : Message × Polynomial (ZMod 5) ×
    List (ZMod 5 × ZMod 5 × Bool) := (f, f.val, [])

private theorem transparentObservation :
    (transparent 0).polynomialCommitmentObservation () noQueries =
      prior.map reveal := by
  classical
  have pmfPure {α : Type} (a : α) : (pure a : PMF α) = PMF.pure a := rfl
  simp [polynomialCommitmentObservation, polynomialCommitmentRequestedTrace,
    polynomialCommitmentDisclosedIndices, noQueries, transparent, prior, PMF.map_bind,
    PMF.map_comp, Function.comp_def, PMF.bind_map, pmfPure, PMF.pure_map, reveal]
  rfl

private noncomputable def fixedGuess := (transparent 0).polynomialCommitmentUniformRule
  (fun _ => noQueries) (fun _ _ => 0)

private theorem fixedGuess_probability (κ : ℕ) :
    (transparent 0).polynomialCommitmentPrediction κ fixedGuess = 1 / 5 := by
  refine Eq.trans ((transparent 0).polynomialCommitmentPredictionAverage κ
    (fun _ => noQueries) (fun _ _ => 0) ?_) ?_
  · rintro ⟨⟨⟩, ⟨⟩⟩ _ fv hf
    rw [transparentObservation] at hf
    change fv ∈ (prior.map reveal).support at hf
    rw [PMF.support_map] at hf
    obtain ⟨f, _, rfl⟩ := hf
    change (0 : ZMod 5) ∉ []
    simp
  · change ∑' ks : Unit × Unit, ((PMF.pure ((), ())) ks).toReal * (1 / 5 : ℝ) = 1 / 5
    rw [tsum_eq_single ((), ())]
    · simp
    · intro ks h
      exact (h (Subsingleton.elim _ _)).elim

-- The fixed-prime computational branch fails for every class admitting this mathematical rule.
example (P E A) (hA : A (fun _ : ℕ => fixedGuess)) :
    ¬ PolynomialCommitmentRelativeBatch (fun _ : ℕ => transparent 0) P E A .computational := by
  intro h
  have hn := h.2.2 (fun _ => fixedGuess) hA
  simp_rw [fixedGuess_probability] at hn
  exact Cslib.Crypto.Framework.not_negligibleAdv_const (by norm_num) hn

private abbrev View := Polynomial (ZMod 5) × List (ZMod 5 × ZMod 5 × Bool)

-- At degree zero the evaluation-only view is empty. The transparent commitment distinguishes
-- the zero and one constants, violating conditional independence without any prediction rule.
private theorem transparent_not_hiding (κ : ℕ) :
    ¬ (transparent 0).PolynomialCommitmentUnconditionalHiding κ := by
  classical
  intro hh
  let v : View := (0, [])
  let bare (u : View) := u.2.map fun x => (x.1, x.2.1)
  let μ := prior.map reveal
  have supported (f : Message) : reveal f ∈ μ.support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨f, prior_full f, rfl⟩
  have hj : (μ.map (fun a => (a.2, a.1.val.eval 0))) (v, 1) = 0 := by
    by_contra hn
    obtain ⟨a, ha, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr hn)
    obtain ⟨f, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
    have hf : f.val = 0 := congrArg (fun z => z.1.1) he
    have hy : f.val.eval 0 = 1 := congrArg Prod.snd he
    rw [hf] at hy
    simp at hy
  have hv : (μ.map Prod.snd) v ≠ 0 := (PMF.mem_support_iff _ _).mp <|
    (PMF.mem_support_map_iff _ _ _).mpr ⟨reveal 0, supported 0, rfl⟩
  let one : Message := ⟨C 1, mem_degreeLT.mpr (degree_C_le.trans_lt (by decide))⟩
  have hb : (μ.map (fun a => (bare a.2, a.1.val.eval 0))) (bare v, 1) ≠ 0 :=
    (PMF.mem_support_iff _ _).mp <| (PMF.mem_support_map_iff _ _ _).mpr
      ⟨reveal one, supported one, by simp [reveal, one, bare, v]⟩
  have eq := hh () (by simp [transparent]; rfl) noQueries v 0 1 (by decide)
  rw [transparentObservation] at eq
  change (μ.map (fun a => (a.2, a.1.val.eval 0))) (v, 1) * (μ.map (fun a => bare a.2)) (bare v) =
    (μ.map Prod.snd) v * (μ.map (fun a => (bare a.2, a.1.val.eval 0))) (bare v, 1) at eq
  rw [hj, zero_mul] at eq
  exact mul_ne_zero hv hb eq.symm

example (P E A) :
    ¬ PolynomialCommitmentRelativeBatch (fun _ : ℕ => transparent 0) P E A .unconditional :=
  fun h => transparent_not_hiding 0 (h.2.2 0)

-- Constant commitment and witness. Both verifiers accept; this illustrates no extra information
-- only, not binding. Honest evaluations still carry their actual indices and values.
private noncomputable def uninformative (t : ℕ) : PolynomialCommitmentScheme t where
  PublicKey := Unit
  SecretKey := Unit
  prime _ := five
  Digest _ := Unit
  Opening _ := Unit
  Witness _ := Unit
  setup _ := PMF.pure ((), ())
  full _ := Scheme.ofPure (fun _ => ((), ())) (fun _ _ _ => true) (fun _ => rfl)
  witness _ _ _ _ := PMF.pure ()
  verifyEval _ _ _ _ _ := true
  correctEval := by intros; rfl

private abbrev UnitView := Unit × List (ZMod 5 × ZMod 5 × Unit)
private def strip (v : UnitView) := v.2.map fun x => (x.1, x.2.1)

private theorem strip_injective : Function.Injective strip := by
  let restore (b : List (ZMod 5 × ZMod 5)) : UnitView := ((), b.map fun q => (q.1, q.2, ()))
  have undo : Function.LeftInverse restore strip := by
    rintro ⟨⟨⟩, xs⟩
    simp [restore, strip, List.map_map, Function.comp_def]
  exact undo.injective

private theorem strip_pair (v u : UnitView) (y z : ZMod 5) :
    (strip v, y) = (strip u, z) ↔ (v, y) = (u, z) := by
  simp only [Prod.mk.injEq, strip_injective.eq_iff]

private theorem sameMass {Ω α β : Type} (μ : PMF Ω) (f : Ω → α) (g : Ω → β) (x : α) (y : β)
    (equiv : ∀ a, x = f a ↔ y = g a) : μ.map f x = μ.map g y := by
  classical
  simp only [PMF.map_apply]
  exact tsum_congr fun a => by rw [propext (equiv a)]

example (t κ : ℕ) : (uninformative t).PolynomialCommitmentUnconditionalHiding κ := by
  rintro ⟨⟩ _ Q v i y _
  let μ : PMF (PolynomialCommitmentMessage five t × UnitView) :=
    (uninformative t).polynomialCommitmentObservation () Q
  let val := fun a : PolynomialCommitmentMessage five t × UnitView => a.1.val.eval i
  change (μ.map (fun a => (a.2, val a))) (v, y) * (μ.map (fun a => strip a.2)) (strip v) =
    (μ.map Prod.snd) v * (μ.map (fun a => (strip a.2, val a))) (strip v, y)
  rw [sameMass μ (fun a => strip a.2) Prod.snd (strip v) v (fun _ => strip_injective.eq_iff),
    sameMass μ (fun a => (strip a.2, val a)) (fun a => (a.2, val a)) (strip v, y) (v, y)
      (fun a => strip_pair v a.2 y (val a)), mul_comm]

end Cslib.Crypto.Protocols.Commitment.PolynomialCommitmentTests
