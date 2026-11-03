/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.PolynomialEncoding.UnaryNat

open Turing Function MetaMathlibExt.TM2Program
open MetaMathlibExt.BitstringEncoding
open Cslib.Complexity.Karp Cslib.Complexity.SatVerifier
open Cslib.Complexity.PolynomialEncoding.UnaryNat

set_option maxRecDepth 10000

private def initial (n : Nat) (out : List Bool) : ∀ k, List (EmitSS.Γ k)
  | .A => cnt EmitSS.U n
  | .O => out
  | .Y => [.cl, .bit true]
  | _ => []

private def drive (framed : Bool) : Nat → TM2.Cfg EmitSS.Γ Lab Bool →
    Option (TM2.Cfg EmitSS.Γ Lab Bool)
  | 0, _ => none
  | fuel + 1, c =>
    if c.l = some .done then some c
    else (TM2.step (prog framed) c).bind (drive framed fuel)

private def check (framed : Bool) (n : Nat) (out : List Bool) : Bool :=
  match drive framed (710 * n + 307)
      ⟨some (.emit .hv), true, initial n out⟩ with
  | none => false
  | some c => decide (c.l = some .done ∧
      c.stk .O = (if framed then delimit (Computability.encodeNat n)
        else Computability.encodeNat n) ++ out ∧
      c.stk .A = [] ∧ c.stk .H = [] ∧ c.stk .T = [] ∧ c.stk .X = [] ∧
      c.stk .Y = [.cl, .bit true])

private def checkTwice (a b : Nat) (out : List Bool) : Bool :=
  match drive true (710 * a + 307)
      ⟨some (.emit .hv), false, initial a out⟩ with
  | none => false
  | some first =>
    decide (first.stk .A = [] ∧ first.stk .H = [] ∧ first.stk .T = []) &&
    match drive true (710 * b + 307)
        ⟨some (.emit .hv), first.var, update first.stk .A (cnt EmitSS.U b)⟩ with
    | none => false
    | some second => decide (second.l = some .done ∧
        second.stk .O = delimit (Computability.encodeNat b) ++
          delimit (Computability.encodeNat a) ++ out ∧
        second.stk .A = [] ∧ second.stk .H = [] ∧ second.stk .T = [] ∧
        second.stk .X = [] ∧ second.stk .Y = [.cl, .bit true])

example : check true 0 [true, false] = true := by decide
example : check false 0 [false, true] = true := by decide
example : check true 1 [] = true := by decide
example : check false 2 [true, true] = true := by decide
example : check true 31 [false] = true := by decide
example : check false 32 [true] = true := by decide
example : checkTwice 0 2 [true, false] = true := by decide
example : checkTwice 5 8 [false, true] = true := by decide

example (n : Nat) : ∃ w S, RunLe (prog false) (710 * n + 306)
    ⟨some (.emit .hv), false, initial n []⟩ ⟨some .done, w, S⟩ ∧
    S .O = Computability.encodeNat n := by
  obtain ⟨w, S, hr, ho, _⟩ := run_raw n [] false (initial n [])
    rfl rfl rfl rfl rfl
  exact ⟨w, S, hr, by simpa using ho⟩

example {J L : Type} [DecidableEq J] {Γ : J → Type}
    (E : MetaMathlibExt.TM2Embedding.SEmb EmitSS.Γ Γ)
    (φ : Lab → L) {M : L → TM2.Stmt Γ L Bool}
    (hm : MetaMathlibExt.TM2Embedding.Embeds E φ (prog false) M)
    (n : Nat) (T : ∀ j, List (Γ j))
    (hs : MetaMathlibExt.TM2Embedding.Agree E (initial n []) T) :
    ∃ w V, RunLe M (710 * n + 306)
      ⟨some (φ (.emit .hv)), false, T⟩ ⟨some (φ .done), w, V⟩ ∧
      MetaMathlibExt.TM2Embedding.Frame E T V := by
  obtain ⟨w, U, hr, _⟩ := run_raw n [] false (initial n [])
    rfl rfl rfl rfl rfl
  obtain ⟨V, hv, _, hf⟩ := MetaMathlibExt.TM2Embedding.runLe_embed φ hm hr hs
  exact ⟨w, V, hv, hf⟩
