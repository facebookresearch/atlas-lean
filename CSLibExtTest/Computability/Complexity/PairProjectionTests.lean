/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.PairProjection
meta import CSLibExt.Computability.Complexity.PairProjection -- shake: keep (executable #guard tests)

/-! Executable boundary checks for the actual first-projection machine and its encoding chain. -/

open Turing Function MetaMathlibExt Cslib.Complexity Cslib.Complexity.DenseSAT

private def runFuel (M : FinTM2) : ℕ → M.Cfg → M.Cfg
  | 0, c => c
  | n + 1, c => match M.step c with
    | none => c
    | some d => runFuel M n d

private def projectRaw (x w : List Bool) : Bool × List Bool × Bool :=
  let c := runFuel PairProjection.tm (2 * x.length + w.length + 5)
    (initList PairProjection.tm (Verifier.pairEncode (x, w)))
  (c.l.isNone && !c.var, c.stk PairProjection.tm.k₁,
    (c.stk PairProjection.Stk.inp).isEmpty && (c.stk PairProjection.Stk.stash).isEmpty)

#guard projectRaw [] [] = (true, [], true)
#guard projectRaw [] [true, false, true] = (true, [], true)
#guard projectRaw [true, false, false] [] = (true, [true, false, false], true)
#guard projectRaw [false, true, true] [true, false] = (true, [false, true, true], true)
#guard (runFuel PairProjection.tm 4
  (initList PairProjection.tm (Verifier.pairEncode ([], [])))).l.isSome

-- The theorem checks the full final configuration, not merely the output stack.
example : TM2Program.RunLe PairProjection.tm.m 13
    (initList PairProjection.tm (Verifier.pairEncode ([false, true, true], [true, false])))
    (haltList PairProjection.tm [false, true, true]) :=
  PairProjection.run [false, true, true] [true, false]

-- Exercise all three machines, not a pure parser substituted for the canonical conversion.
private def projectCanonical (x w : List Bool) : List Bool :=
  let a := runFuel Converter.tm (2 * x.length + 2 * w.length + 5)
    (initList Converter.tm (BitstringEncoding.bitEncode (x, w)))
  let b := runFuel PairProjection.tm (2 * x.length + w.length + 5)
    (initList PairProjection.tm (a.stk Converter.tm.k₁))
  let c := runFuel EncodeBits.tm (2 * x.length + 2)
    (initList EncodeBits.tm (b.stk PairProjection.tm.k₁))
  c.stk EncodeBits.tm.k₁

#guard projectCanonical [] [] = []
#guard projectCanonical [] [true, false] = []
#guard projectCanonical [false, true, true] [] =
  [true, false, false, true, true, false, true, true, false]
#guard projectCanonical [false, true, true] [false, false, true] =
  BitstringEncoding.bitEncode [false, true, true]

-- The final output is the encoded bit list, not the raw list.
example : BitstringEncoding.bitEncode ([true] : List Bool) ≠ [true] := by decide
example : IsPolyTime (Prod.fst : List Bool × List Bool → List Bool) := isPolyTime_fst
