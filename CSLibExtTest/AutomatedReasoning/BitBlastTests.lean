/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.AutomatedReasoning.StringConstraints.BitBlast
public meta import CSLibExt.AutomatedReasoning.StringConstraints.BitBlast

/-! End-to-end checks run the word-to-CNF translation and the verified DPLL solver. -/

@[expose] public section

open Cslib.AutomatedReasoning.StringConstraints

namespace BitBlastTests

/-- A repeated variable must reuse its bit, not introduce a fresh bit per occurrence. -/
def repeated (b : Bool) : List (WordEq Bool (Fin 1)) :=
  [⟨[.inr 0, .inr 0], [.inl true, .inl b]⟩]

example : fixedLengthSatB (fun _ => 1) (repeated true) = true := by decide
example : fixedLengthSatB (fun _ => 1) (repeated false) = false := by decide

/-- The same variable is shared across all equations in a system. -/
def contradictory : List (WordEq Bool (Fin 1)) :=
  [⟨[.inr 0], [.inl true]⟩, ⟨[.inr 0], [.inl false]⟩]

example : fixedLengthSatB (fun _ => 1) contradictory = false := by decide

/-- Empty substitutions are valid, including at concatenation boundaries. -/
def epsilon : List (WordEq Bool (Fin 1)) :=
  [⟨[.inr 0, .inl true], [.inl true]⟩]

example : fixedLengthSatB (fun _ => 0) epsilon = true := by decide
example : fixedLengthSatB (fun _ => 1) epsilon = false := by decide

example : fixedLengthSatB (fun _ : Fin 0 => 0) [⟨[], []⟩] = true := by decide
example : fixedLengthSatB (fun _ : Fin 0 => 0) [⟨[], [.inl true]⟩] = false := by decide
example : fixedLengthSatB (fun _ : Fin 0 => 0) [] = true := by decide

#eval [fixedLengthSatB (fun _ => 1) (repeated true),
  fixedLengthSatB (fun _ => 1) (repeated false),
  fixedLengthSatB (fun _ => 1) contradictory,
  fixedLengthSatB (fun _ => 0) epsilon,
  fixedLengthSatB (fun _ => 1) epsilon]

example : boundedWordSatB 0 (repeated true) = false := by decide
example : boundedWordSatB 1 (repeated true) = true := by decide
example : boundedWordSatB 2 (repeated false) = false := by decide
example : boundedWordSatB 2 contradictory = false := by decide
example : boundedWordSatB 0 epsilon = true := by decide
example : boundedWordSatB 0 ([] : List (WordEq Bool (Fin 0))) = true := by decide

example : patternMatchB ([.inr 0, .inr 0] : List (Bool ⊕ Fin 2))
    [true, true] = true := by decide
example : patternMatchB ([.inr 0, .inr 0] : List (Bool ⊕ Fin 2))
    [true, false] = false := by decide
example : patternMatchB ([.inr 0] : List (Bool ⊕ Fin 2)) [] = true := by decide
example : patternMatchB ([] : List (Bool ⊕ Fin 0)) [] = true := by decide
example : patternMatchB ([] : List (Bool ⊕ Fin 0)) [true] = false := by decide

/-- A successful SAT run yields a solution in the original formula semantics. -/
example : ∃ σ : Fin 1 → List Bool, (∀ i, (σ i).length ≤ 1) ∧
    Sat σ (andChain ((repeated true).map WordEq.toFormula)) :=
  (boundedWordSatB_formula_iff 1 (repeated true)).mp (by decide)

/-- Unbounded pattern UNSAT follows from the proved sufficient bound. -/
example : ¬ ∃ σ : Fin 2 → List Bool,
    evalWord σ [.inr 0, .inr 0] = [true, false] := by
  intro h
  have ht := (patternMatchB_iff [.inr 0, .inr 0] [true, false]).mpr h
  have hf : patternMatchB ([.inr 0, .inr 0] : List (Bool ⊕ Fin 2))
      [true, false] = false := by decide
  rw [hf] at ht
  contradiction

example : (lengthProfiles 0 0).length = 1 := by decide
example : (lengthProfiles 2 2).length = 9 := by decide
example : (blastSystem (fun _ => 1) (repeated true)).length = 5 := by decide
example : (blastSystem (fun _ => 0) (repeated true)).length = 2 := by decide
example : decodeAssignment (fun _ : Fin 1 => 1) (fun _ => true) 0 = [true] := by decide

private def smallWords : List (List (Bool ⊕ Fin 2)) :=
  let symbols : List (Bool ⊕ Fin 2) := [.inl false, .inl true, .inr 0, .inr 1]
  [[]] ++ symbols.map (fun x => [x]) ++
    symbols.flatMap (fun x => symbols.map (fun y => [x, y]))

private def smallImages : List (List Bool) := [[], [false], [true]]

/-- Independent finite reference: enumerate actual strings, not SAT bits or profiles. -/
private def bruteBounded (e : WordEq Bool (Fin 2)) : Bool :=
  smallImages.any (fun x => smallImages.any (fun y =>
    let σ : Fin 2 → List Bool := fun i => if i = 0 then x else y
    decide (evalWord σ e.lhs = evalWord σ e.rhs)))

private def bruteFixed (ℓ : Fin 2 → ℕ) (e : WordEq Bool (Fin 2)) : Bool :=
  smallImages.any (fun x => smallImages.any (fun y =>
    let σ : Fin 2 → List Bool := fun i => if i = 0 then x else y
    decide (x.length = ℓ 0 ∧ y.length = ℓ 1 ∧ evalWord σ e.lhs = evalWord σ e.rhs)))

-- Finite differential tests, not general correctness proofs: 441 equations, 1764 fixed profiles.
#guard smallWords.length = 21
#guard smallWords.all (fun l => smallWords.all (fun r =>
  boundedWordSatB 1 [⟨l, r⟩] == bruteBounded ⟨l, r⟩))
#guard smallWords.all (fun l => smallWords.all (fun r =>
  (lengthProfiles 2 1).all (fun ℓ => fixedLengthSatB ℓ [⟨l, r⟩] == bruteFixed ℓ ⟨l, r⟩)))

-- Execute the exported Decidable procedures after proof erasure, as clients do.
#guard @decide _ (decidableBoundedWordEq 1 (repeated true))
#guard !(@decide _ (decidablePatternMatch
  ([.inr 0, .inr 0] : List (Bool ⊕ Fin 1)) [true]))

end BitBlastTests
