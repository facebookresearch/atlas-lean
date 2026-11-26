/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.PublicKey.HomomorphicEvaluation
import Cslib.Computability.Circuit.Depth
import Mathlib.Tactic.FinCases

/-!
# Tests of the homomorphic evaluation interface

A product of two Boolean algebras projects homomorphically to the first factor. The tuples
below are public data with an irrelevant random coordinate, not a cryptographic construction.
-/

namespace Cslib.Crypto.HomomorphicTests

open Cslib.Circuits Cslib.Crypto.Framework Cslib.Crypto.Homomorphic Computability

private def pairCode : Encoding (Bool × Bool) Bool where
  encode x := [x.1, x.2]
  decode | [a, b] => some (a, b) | _ => none
  decode_encode _ := rfl

private abbrev bits : Spaces Boolean.signature where
  Message := Bool
  SecretKey := Bool
  Ciphertext := Bool × Bool
  gates := Boolean.interpretation
  messageCode := encodingBoolBool
  secretCode := encodingBoolBool
  cipherCode := pairCode

private def productGates : Interpretation Boolean.signature (Bool × Bool) := fun op x =>
  (Boolean.interpretation op (Prod.fst ∘ x), Boolean.interpretation op (Prod.snd ∘ x))

private def project : Homomorphism productGates Boolean.interpretation where
  map := Prod.fst
  homomorphic _ _ := rfl

private noncomputable def tags (m : Bool) : PMF (Bool × Bool) :=
  (Probability.PMF.uniformOfFintype Bool).map fun b => (m, b)

private theorem first_of_tag {m : Bool} {x : Bool × Bool} (h : x ∈ (tags m).support) : x.1 = m := by
  obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff ..).mp h
  rfl

private noncomputable def fixture : Scheme bits where
  PublicKey := Bool
  publicCode := encodingBoolBool
  pke := { gen := PMF.pure (true, false), enc := fun _ m => tags m,
           dec := fun _ x => some x.1 }
  fresh_correct := fun _ _ _ _ hx => congrArg some (first_of_tag hx)
  evaluate _ c x := PMF.pure (c.eval productGates x 0)

-- Every circuit, not just a projection: projection from the product algebra commutes with gates.
private theorem eval_first {t : ℕ} (c : Circuit Boolean.signature t 1)
    (m : Fin t → Bool) (x : Fin t → Bool × Bool) (hx : ∀ i, x i ∈ (tags (m i)).support) :
    (c.eval productGates x 0).1 = c.eval bits.gates m 0 := by
  have h : Prod.fst ∘ x = m := funext fun i => first_of_tag (hx i)
  exact (congrFun (c.map_eval project x) 0).trans (congrArg (fun y => c.eval bits.gates y 0) h)

private theorem correct : Correct (A := fun _ => bits) (fun _ => fixture) (fun _ _ => Set.univ) := by
  refine ⟨_, negligibleAdv_zero, ?_⟩
  intro n t c hc kp hk m x hx
  simp [fixture, PMF.pure_map, eval_first c m x hx]

-- A Boolean wiring circuit really computes the tagged result, including the framing bits.
private def decoder : DecryptionCircuit :=
  ⟨8, 5, .wiring _ ![0, 0, 0, 4, 2]⟩

private theorem implements : decoder.Implements fixture := by
  intro sk x
  refine ⟨le_rfl, le_rfl, ?_⟩
  funext i
  fin_cases i <;> rfl

-- This proves functionality on the basis, not a polynomial-time implementation of the fixture.
example : EvaluatesBasis (A := fun _ => bits) (fun _ => fixture) :=
  ⟨correct, 13, fun _ => ⟨decoder, by simp [decoder], implements⟩⟩

-- At parameter n this evaluator discards the answer only on arity n + 1. Each fixed
-- circuit therefore has at most one exceptional parameter, independently of its inputs.
private noncomputable def diagonal (n : ℕ) : Scheme bits :=
  { fixture with evaluate := fun {t} pk c x =>
      if t = n + 1 then PMF.pure (false, false) else fixture.evaluate pk c x }

example : FixedCircuitCorrect (A := fun _ => bits) diagonal (fun _ _ => Set.univ) := by
  intro t c
  refine ⟨fun n => if t = n + 1 then 1 else 0, ?_, ?_⟩
  · refine ⟨fun n => if t = n + 1 then 1 else 0, fun k => ⟨t, fun n hn => ?_⟩, fun n => ?_⟩
    · simp only [show t ≠ n + 1 by omega, ↓reduceIte]
      positivity
    · by_cases h : t = n + 1 <;> simp [h]
  · intro n hc kp hk m x hx
    by_cases h : t = n + 1
    · simp only [h, ↓reduceIte]
      exact winProb_le_one _
    · simp [diagonal, h, fixture, PMF.pure_map, eval_first c m x hx]

-- No negligible bound works simultaneously for all circuits of this same family: project
-- the first input at arity n + 1 on a supported all-true tuple at every n.
example : ¬ Correct (A := fun _ => bits) diagonal (fun _ _ => Set.univ) := by
  rintro ⟨ε, hε, hb⟩
  apply not_negligibleAdv_const (δ := 1) (by norm_num) (hε.mono ?_)
  intro n
  have hx : (true, true) ∈ (tags true).support := by
    apply (PMF.mem_support_map_iff ..).mpr
    exact ⟨true, by simp [PMF.mem_support_iff], rfl⟩
  have bound := hb n (n + 1) (Circuit.wiring _ (fun _ => 0)) (Set.mem_univ _) (true, false)
    ((PMF.mem_support_pure_iff ..).mpr rfl) (fun _ => true) (fun _ => (true, true)) (fun _ => hx)
  simpa [diagonal, fixture, PMF.pure_map] using bound

-- The second coordinate can be true on a single fair tape out of all length-n tapes. Evaluation
-- that fails just on that tag still violates correctness: the ciphertext tuple is fixed first.
private noncomputable def rare (n : ℕ) (m : Bool) : PMF (Bool × Bool) := by
  classical
  exact (Probability.PMF.uniformOfFintype (BitString n)).map fun r => (m, decide (r = fun _ => true))

private noncomputable def broken (n : ℕ) : Scheme bits := by
  classical
  exact { fixture with
    pke := { fixture.pke with enc := fun _ m => rare n m }
    fresh_correct := by
      intro kp hk m x hx
      obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff ..).mp hx
      rfl
    evaluate := fun _ c x =>
      if ∃ i, (x i).2 = true then PMF.pure (false, false) else PMF.pure (c.eval productGates x 0) }

private theorem broken_not_fixed : ¬ FixedCircuitCorrect (A := fun _ => bits) broken
    (fun _ _ => Set.univ) := by
  classical
  intro hcorrect
  obtain ⟨ε, hε, h⟩ := hcorrect 1 (Circuit.id Boolean.signature 1)
  apply not_negligibleAdv_const (δ := 1) (by norm_num) (hε.mono ?_)
  intro n
  have hx : (true, true) ∈ (rare n true).support := by
    apply (PMF.mem_support_map_iff ..).mpr
    refine ⟨fun _ => true, ?_, by simp⟩
    simp [PMF.mem_support_iff]
  have bound := h n (Set.mem_univ _) (true, false) ((PMF.mem_support_pure_iff ..).mpr rfl)
    (fun _ => true) (fun _ => (true, true)) (fun _ => hx)
  simpa [broken, fixture, PMF.pure_map, Circuit.id] using bound

example : ¬ Correct (A := fun _ => bits) broken (fun _ _ => Set.univ) :=
  fun h => broken_not_fixed h.toFixedCircuitCorrect

-- An empty class imposes no evaluation obligation. This is not the class used by full evaluation.
example (E : ℕ → Scheme bits) : Correct (A := fun _ => bits) E (fun _ _ => ∅) :=
  ⟨_, negligibleAdv_zero, fun _ _ _ hc => False.elim hc⟩

-- By contrast the nullary constant-true circuit has one (empty) input tuple, not zero
-- possible tuples. Returning false on that tuple really does violate a zero error bound.
private def nullaryTrue : Circuit Boolean.signature 0 1 :=
  ⟨.gate .empty ⟨.const true, Fin.elim0⟩, fun _ => .gate 0⟩

example : ¬ EvaluationErrorAtMost
    { fixture with evaluate := fun _ _ _ => PMF.pure (false, false) } nullaryTrue 0 := by
  intro h
  have bound := h (true, false) ((PMF.mem_support_pure_iff ..).mpr rfl)
    Fin.elim0 Fin.elim0 (fun i => i.elim0)
  have value : nullaryTrue.eval bits.gates Fin.elim0 0 = true := rfl
  apply not_le_of_gt (zero_lt_one : (0 : ℝ) < 1)
  simpa [fixture, value, PMF.pure_map] using bound

-- The last input port carries an unused frame terminator. Removing it changes neither the
-- computed bits nor the output capacity, but the framed input no longer fits.
private def shortDecoder : DecryptionCircuit := ⟨7, 5, .wiring _ ![0, 0, 0, 4, 2]⟩

example (sk : Bool) (x : Bool × Bool) :
    let frame := MetaMathlibExt.BitstringEncoding.delimit
    let input := frame (bits.secretCode.encode sk) ++ frame (bits.cipherCode.encode x)
    let output := frame (answer bits.messageCode (fixture.pke.dec sk x))
    input.length = shortDecoder.inputs + 1 ∧ output.length = shortDecoder.outputs ∧
      shortDecoder.circuit.eval Boolean.interpretation (fun i => input[i.val]?.getD false) =
        fun j => output[j.val]?.getD false := by
  refine ⟨rfl, rfl, ?_⟩
  funext i
  fin_cases i <;> rfl

example : ¬ shortDecoder.Implements fixture := by
  intro h
  have impossible : 8 ≤ 7 := (h false (true, false)).1
  omega

-- A shared circuit is more than a common size bound: two decoders that disagree on the same
-- words cannot both be computed by it. Flip both the represented message and the fresh encoding.
private noncomputable def flipped : Scheme bits where
  PublicKey := Bool
  publicCode := encodingBoolBool
  pke := { gen := PMF.pure (true, false), enc := fun _ m => tags (!m),
           dec := fun _ x => some (!x.1) }
  fresh_correct := by
    intro kp hk m x hx
    simp [first_of_tag hx]
  evaluate _ c x := PMF.pure (!(c.eval Boolean.interpretation (fun i => !(x i).1) 0), false)

private theorem incompatible (D : DecryptionCircuit) : ¬ (D.Implements fixture ∧ D.Implements flipped) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨_, length, e₁⟩ := h₁ false (true, false)
  have e₂ := (h₂ false (true, false)).2.2
  change 5 ≤ D.outputs at length
  have heq := congrFun (e₁.symm.trans e₂) (⟨3, by omega⟩ : Fin D.outputs)
  exact Bool.noConfusion heq

example (tag : Encoding Boolean.Op Bool) : ¬ LeveledFullyHomomorphic (A := fun _ => bits)
    (fun d _ => if d.val = 1 then fixture else flipped) tag := by
  rintro ⟨_, ⟨_, D, hD⟩, _⟩
  exact incompatible (D 0) ⟨(hD 0).2 1, (hD 0).2 2⟩

-- The same two-gate NOT chain is outside level one and inside level two.
private def doubleNot : Circuit Boolean.signature 1 1 :=
  ⟨.gate (.gate .empty ⟨.not, fun _ => .input 0⟩) ⟨.not, fun _ => .gate 0⟩, fun _ => .gate 1⟩

example : ¬ doubleNot.depth ≤ 1 ∧ doubleNot.depth ≤ 2 := by decide

-- The shared witness really supplies ordinary compact evaluation at each level (2.1.3).
example {σ : Signature} {A : ℕ → Spaces σ} {E : ℕ+ → (n : ℕ) → Scheme (A n)}
    {tag : Encoding σ.Op Bool} (h : LeveledFullyHomomorphic E tag) (d : ℕ+) :
    CompactlyEvaluates (E d) fun _ _ => {c | c.depth ≤ d.val} := by
  obtain ⟨_, ⟨p, D, hD⟩, hc, _⟩ := h
  exact ⟨hc d, p, fun n => ⟨D n, (hD n).1, (hD n).2 d⟩⟩

-- One input, one gate and depth at most one do not control the syntax of an infinite basis:
-- symbol j has j+1 incoming wires, all of which can read the very same input.
private abbrev wide : Signature := ⟨ℕ, fun j => j + 1⟩

private def repeatedInput (j : ℕ) : Circuit wide 1 1 :=
  ⟨.gate .empty ⟨j, fun _ => .input 0⟩, fun _ => .gate 0⟩

example (j : ℕ) : (repeatedInput j).size = 1 ∧ (repeatedInput j).depth ≤ 1 ∧
    j ≤ (circuitCode unaryEncodingNat (repeatedInput j)).length := by
  refine ⟨rfl, (repeatedInput j).depth_le_size, ?_⟩
  have htag : (unaryEncodingNat.encode j).length = j := unary_decode_encode_nat j
  simp only [repeatedInput, circuitCode, circuitCode.program, List.length_append,
    MetaMathlibExt.BitstringEncoding.length_delimit, htag]
  omega

-- This is a model restriction, not a lower bound on the running time of every evaluator.
example {A : ℕ → Spaces wide} (E : ℕ+ → (n : ℕ) → Scheme (A n)) :
    ¬ LeveledOverBasis E unaryEncodingNat := fun h =>
  (not_finite_iff_infinite.mpr inferInstance : ¬ Finite ℕ) h.2.2.1

-- No decryption circuit, however wired, can accommodate an unbounded raw ciphertext field.
private abbrev words : Spaces Boolean.signature :=
  { bits with Ciphertext := List Bool, cipherCode := encodingList Bool }

example (E : ℕ → Scheme words) : ¬ Compact (A := fun _ => words) E := by
  rintro ⟨_, h⟩
  obtain ⟨D, _, hD⟩ := h 1
  have cap := (hD false (List.replicate D.inputs false)).1
  simp [words, bits, MetaMathlibExt.BitstringEncoding.length_delimit, encodingList] at cap
  omega

-- With one fair bit, the identity machine on the encoded input halts in one step. The
-- output is [false,false] or [false,true], not a point mass; false frames the empty argument.
example : SamplesWithin Turing.SingleTapeTM.idComputer 1 1 []
    ((Probability.PMF.uniformOfFintype (BitString 1)).map fun r => [false, r 0]) := by
  refine ⟨_, rfl, fun r => ?_⟩
  simp only [MetaMathlibExt.BitstringEncoding.delimit, List.ofFn_succ, List.ofFn_zero,
    List.cons_append, List.nil_append]
  exact ⟨1, le_rfl, Relation.RelatesInSteps.single rfl⟩

-- An interpretation of the *same* finite gate symbols by constant false cannot compute even
-- the unary constant true function: it preserves the all-false input valuation.
private def weak : Interpretation Boolean.signature Bool := fun _ _ => false

private theorem weak_incomplete : ¬ weak.IsComplete := by
  intro h
  let z : Fin 1 → Bool := fun _ => false
  let collapse : Homomorphism weak weak := ⟨fun _ => false, fun _ _ => rfl⟩
  obtain ⟨c, hc⟩ := h.exists_computes_single (n := 1) (fun _ => true)
  have h₀ : false = c.eval weak z 0 := congrFun (c.map_eval collapse z) 0
  have h₁ : c.eval weak z 0 = true := congrFun (hc z) 0
  exact Bool.noConfusion (h₀.trans h₁)

private abbrev weakBits : Spaces Boolean.signature := { bits with gates := weak }

example (E : ℕ → Scheme weakBits) (tag : Encoding Boolean.Op Bool) :
    ¬ FullyHomomorphic (A := fun _ => weakBits) E tag := fun h => weak_incomplete (h.1 0)

-- The machine must actually halt: even a deterministic point mass cannot be sampled in zero steps.
example (T : Turing.SingleTapeTM Bool) (arg : List Bool) (k : ℕ) :
    ¬ SamplesWithin T k 0 arg (PMF.pure []) := by
  rintro ⟨draw, _, run⟩
  have heq := Relation.RelatesWithinSteps.zero (run (fun _ => false))
  exact Option.some_ne_none _ (congrArg Turing.SingleTapeTM.Cfg.state heq)

end Cslib.Crypto.HomomorphicTests
