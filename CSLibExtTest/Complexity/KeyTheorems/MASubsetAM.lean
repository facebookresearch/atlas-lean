/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Complexity.KeyTheorems.MASubsetAM
import MathlibExt.Computability.TuringMachine.Program

open Cslib.Complexity.Classes
open MetaMathlibExt BitstringEncoding ComplexityTheory TM2Program
open Turing

namespace MetaMathlibExt.Complexity.KeyTheorems.MASubsetAM.Tests

private abbrev VerifierInput := List Bool × List Bool × List Bool

private def constantMachine (b : Bool) : FinTM2 where
  K := Unit
  Γ _ := Bool
  k₀ := ()
  k₁ := ()
  Λ := Unit
  σ := Bool
  main := ()
  initialState := false
  m _ := .pop () (fun _ a => a.isSome) <|
    .branch id (.goto fun _ => ()) (.push () (fun _ => b) .halt)

private theorem constant_run (b : Bool) (bs : List Bool) (v : Bool) :
    Run (constantMachine b).m (bs.length + 1)
      ⟨some (), v, fun _ => bs⟩ ⟨none, false, fun _ => [b]⟩ := by
  induction bs generalizing v with
  | nil => exact Run.single rfl
  | cons a bs ih =>
    exact (ih true).head (c := ⟨some (), v, fun _ => a :: bs⟩) rfl

private theorem isPolyTime_constant (b : Bool) : IsPolyTime (fun _ : VerifierInput => b) := by
  refine ⟨{
    tm := constantMachine b
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.X + 1
    outputsFun := fun input => ⟨⟨(bitEncode input).length + 1, ?_⟩, ?_⟩ }⟩
  · change Run (constantMachine b).m _ (initList (constantMachine b) ((bitEncode input).map id))
      (haltList (constantMachine b) ([b].map id))
    erw [List.map_id, List.map_id]
    exact constant_run b (bitEncode input) false
  · change (bitEncode input).length + 1 ≤
      (Polynomial.X + 1 : Polynomial ℕ).eval (bitEncode input).length
    simp

-- These two cases exercise both truth values with zero coins and an empty witness.
example (b : Bool) : (fun _ : List Bool => b) ∈ AM := by
  apply ma_subset_am
  refine ⟨0, 0, fun _ => b, isPolyTime_constant b, ?_⟩
  cases b <;> intro x <;> simp

end MetaMathlibExt.Complexity.KeyTheorems.MASubsetAM.Tests
