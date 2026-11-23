/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.SSVerifierArithmetic

/-! Actual bounded machine executions, including carry and empty output. -/

open Turing MetaMathlibExt.TM2Program Cslib.Complexity.Karp
open Cslib.Complexity.SatVerifier Computability
namespace Cslib.Complexity.SSVerifierArithmetic.Tests

set_option maxRecDepth 4000

private abbrev Cfg := TM2.Cfg (fun _ : SSVerify.K => Sym) Lab Bool

private def initial (m n : ℕ) : Cfg :=
  ⟨some (.inr 0), false,
    SSVerify.st ((pairInput m n).map .bit) [] [] [] []⟩

private def tick (c : Cfg) : Cfg :=
  if c.l = some (.inr 3) then c else (TM2.step prog c).getD c

private def correct (fuel m n : ℕ) : Bool :=
  let c := tick^[fuel] (initial m n)
  c.l == some (.inr 3) && c.stk .A == (encodeNat (m + n)).map .bit &&
    [SSVerify.K.X, .W, .T, .B, .P, .Q].all (fun k => (c.stk k).isEmpty)

example : correct 20 0 0 = true := by decide
example : correct 0 0 0 = false := by decide
example : correct 40 0 1 = true := by decide
example : correct 60 7 1 = true := by decide
example : correct 60 3 5 = true := by decide
example : correct 100 31 1 = true := by decide
example : correct 100 1 32 = true := by decide

example (m n : ℕ) :
    ∃ v, RunLe prog
      ((pairInput m n).length * (2 * (pairInput m n).length + 6) +
        2 * (pairInput m n).length + 8)
      (initial m n)
      ⟨some (.inr 3), v,
        SSVerify.st [] [] [] ((encodeNat (m + n)).map .bit) []⟩ :=
  run m n false

end Cslib.Complexity.SSVerifierArithmetic.Tests
