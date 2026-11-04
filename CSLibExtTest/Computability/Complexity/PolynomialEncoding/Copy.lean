/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy

open Turing Function MetaMathlibExt.TM2Program
open Cslib.Complexity.PolynomialEncoding

private def prog : Fin 3 → TM2.Stmt (fun _ : Fin 4 => Option Bool) (Fin 3) Bool
  | 0 => moveB 0 2 id some 0 1
  | 1 => splitB 2 0 1 id some some 1 2
  | _ => .halt

private def initialStacks (bits : List Bool) (k : Fin 4) : List (Option Bool) :=
  if k = 0 then bits.map some ++ [none, some false]
  else if k = 1 then [some true]
  else if k = 2 then [none, some true]
  else [some false, none]

private def checkCopy (bits : List Bool) : Bool :=
  let result := (flip bind (TM2.step prog))^[2 * bits.length + 2]
    (some ⟨some 0, true, initialStacks bits⟩)
  match result with
  | none => false
  | some c => decide (c.l = some 2 ∧ c.var = false ∧
      c.stk 0 = initialStacks bits 0 ∧ c.stk 2 = initialStacks bits 2 ∧
      c.stk 1 = bits.map some ++ initialStacks bits 1 ∧
      c.stk 3 = initialStacks bits 3)

example : checkCopy [] = true := by decide
example : checkCopy [false] = true := by decide
example : checkCopy [true, false, false] = true := by decide
example : checkCopy [false, true, false, true] = true := by decide

example (bits : List Bool) :
    ∃ S, Run prog (2 * bits.length + 2)
      ⟨some 0, true, initialStacks bits⟩ ⟨some 2, false, S⟩ ∧
      S 0 = initialStacks bits 0 ∧ S 2 = initialStacks bits 2 ∧
      S 1 = bits.map some ++ initialStacks bits 1 ∧
      ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → S k = initialStacks bits k := by
  apply copyB_run (a := 0) (b := 1) (t := 2)
    (da := id) (dt := id) (ga := some) (gb := some) (gt := some)
    (first := 0) (second := 1) (next := 2) rfl rfl
    (by decide) (by decide) (by decide) (fun _ => rfl) (fun _ => rfl)
    bits [none, some false] true (initialStacks bits)
  · simp [initialStacks]
  · rfl
  · simp [EndsBitBlock, initialStacks]
