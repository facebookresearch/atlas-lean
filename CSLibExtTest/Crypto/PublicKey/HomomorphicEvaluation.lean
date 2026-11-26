/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.PublicKey.HomomorphicEvaluation
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
private theorem correct : Correct (A := fun _ => bits) (fun _ => fixture) (fun _ _ => Set.univ) := by
  refine ⟨_, negligibleAdv_zero, ?_⟩
  intro n kp hk t c hc m x hx
  have h : Prod.fst ∘ x = m := funext fun i => first_of_tag (hx i)
  have e := congrFun (c.map_eval project x) 0
  change (c.eval productGates x 0).1 = c.eval bits.gates (Prod.fst ∘ x) 0 at e
  rw [h] at e
  simp [fixture, PMF.pure_map, e]

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

example : ¬ Correct (A := fun _ => bits) broken (fun _ _ => Set.univ) := by
  classical
  rintro ⟨ε, hε, h⟩
  apply not_negligibleAdv_const (δ := 1) (by norm_num) (hε.mono ?_)
  intro n
  have hx : (true, true) ∈ (rare n true).support := by
    apply (PMF.mem_support_map_iff ..).mpr
    refine ⟨fun _ => true, ?_, by simp⟩
    simp [PMF.mem_support_iff]
  have bound := h n (true, false) ((PMF.mem_support_pure_iff ..).mpr rfl) 1
    (Circuit.id Boolean.signature 1) (Set.mem_univ _)
    (fun _ => true) (fun _ => (true, true)) (fun _ => hx)
  simpa [broken, fixture, PMF.pure_map, Circuit.id] using bound

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
  rintro ⟨_, _, ⟨_, D, hD⟩, _⟩
  exact incompatible (D 0) ⟨(hD 0).2 1, (hD 0).2 2⟩

-- The same two-gate NOT chain is outside level one and inside level two.
private def doubleNot : Circuit Boolean.signature 1 1 :=
  ⟨.gate (.gate .empty ⟨.not, fun _ => .input 0⟩) ⟨.not, fun _ => .gate 0⟩, fun _ => .gate 1⟩

example : ¬ doubleNot.depth ≤ 1 ∧ doubleNot.depth ≤ 2 := by decide

-- The shared witness really supplies ordinary compact evaluation at each level (2.1.3).
example {σ : Signature} {A : ℕ → Spaces σ} {E : ℕ+ → (n : ℕ) → Scheme (A n)}
    {tag : Encoding σ.Op Bool} (h : LeveledFullyHomomorphic E tag) (d : ℕ+) :
    CompactlyEvaluates (E d) fun _ _ => {c | c.depth ≤ d.val} := by
  obtain ⟨_, _, ⟨p, D, hD⟩, hc, _⟩ := h
  exact ⟨hc d, p, fun n => ⟨D n, (hD n).1, (hD n).2 d⟩⟩

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
    ¬ FullyHomomorphic (A := fun _ => weakBits) E tag := fun h => weak_incomplete (h.2.1 0)

-- The machine must actually halt: even a deterministic point mass cannot be sampled in zero steps.
example (T : Turing.SingleTapeTM Bool) (arg : List Bool) (k : ℕ) :
    ¬ SamplesWithin T k 0 arg (PMF.pure []) := by
  rintro ⟨draw, _, run⟩
  have heq := Relation.RelatesWithinSteps.zero (run (fun _ => false))
  exact Option.some_ne_none _ (congrArg Turing.SingleTapeTM.Cfg.state heq)

end Cslib.Crypto.HomomorphicTests
