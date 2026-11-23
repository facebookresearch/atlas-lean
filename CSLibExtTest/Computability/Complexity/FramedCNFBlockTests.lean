/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.FramedCNF.Block

open Turing Cslib.Complexity.FramedCNF
open MetaMathlibExt.BitstringEncoding

private def prog : Fin 3 → TM2.Stmt (fun _ : Bool => Bool) (Fin 3) Bool
  | 0 => Block.read false true some id 0 1 2
  | _ => .halt

private def result (steps : ℕ) (input output : List Bool) :=
  ((fun o => o.bind (TM2.step prog))^[steps]
    (some ⟨some 0, false, fun k => if k then output else input⟩)).map
      (fun c => (c.l, c.stk false, c.stk true))

-- Empty block ends immediately and preserves the suffix.
example : result 1 [false, true] [true] =
    some (some 1, [true], [true]) := by decide

-- A nonempty block is reversed above the existing destination contents.
example : result 3 (delimit [true, false] ++ [true, true]) [true] =
    some (some 1, [true, true], [false, true, true]) := by decide

-- No terminator, truncated pair, and a complete pair without terminator.
example : result 1 [] [] = some (some 2, [], []) := by decide
example : result 1 [true] [] = some (some 2, [], []) := by decide
example : result 2 [true, false] [] =
    some (some 2, [], [false]) := by decide

-- The public theorem applies to every payload and an arbitrary suffix.
example (payload tail out : List Bool) : ∃ S',
    MetaMathlibExt.TM2Program.Run prog (payload.length + 1)
      ⟨some 0, false, fun k =>
        if k then out else delimit payload ++ tail⟩
      ⟨some 1, false, S'⟩ ∧ S' false = tail ∧
      S' true = payload.reverse ++ out ∧
      ∀ k, k ≠ false → k ≠ true → S' k =
        (if k then out else delimit payload ++ tail) := by
  simpa using Block.run_delimit (M := prog) (a := false) (b := true)
    (d := some) (g := id) (self := 0) (good := 1) (bad := 2)
    rfl (by decide) id (fun _ => rfl) payload tail false
    (fun k => if k then out else delimit payload ++ tail) (by simp)
