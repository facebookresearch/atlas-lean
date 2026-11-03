/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.Karp.PartitionComplete

/-!
# Executing both total PARTITION reductions

Boundary computations, phase-isolation checks, and canonical NP consumers.
-/

open Turing Function MetaMathlibExt BitstringEncoding
open MetaMathlibExt.Complexity.NPComplete.Partition
open Cslib.Complexity.Karp

-- Concrete evaluation traverses the actual finite programs, not run lemmas.
set_option maxRecDepth 20000

private def execute {K L : Type} [DecidableEq K] [DecidableEq L]
    {Γ : K → Type} (M : L → TM2.Stmt Γ L Bool) (done : L) (out : K) :
    Nat → TM2.Cfg Γ L Bool → Option (List (Γ out))
  | 0, _ => none
  | n + 1, c =>
    if c.l = some done then some (c.stk out)
    else (TM2.step M c).bind (execute M done out n)

private def membership (x : List Bool) : Option (List Bool) :=
  execute MembershipMachine.prog .done (.core (.double .O))
    (100 * (x.length + 1) ^ 2 + 1)
    ⟨some (.norm .loop), false, update (fun _ => []) (.norm .input) x⟩

private def hardness (x : List Bool) : Option (List Bool) :=
  execute HardnessMachine.prog .done (.core .O)
    (60 * (x.length + 1) ^ 2 + 1)
    ⟨some .copy1, false, update (fun _ => []) .raw x⟩

example : membership [] = some (encodeSS [] 0) := by decide
example : hardness (encodeSS [] 0) =
    some (bitEncode ([0, 0] : List ℕ)) := by decide

-- Canonical and noncanonical PARTITION inputs, including parity boundaries.
example : membership (bitEncode ([0, 0] : List ℕ)) =
    some (encodeSS [0, 0] 0) := by decide
example : membership (bitEncode ([1] : List ℕ)) =
    some (encodeSS [2] 1) := by decide
example : membership (bitEncode ([1, 2] : List ℕ)) =
    some (encodeSS [2, 4] 3) := by decide
example : membership (bitEncode ([0, 2, 2] : List ℕ)) =
    some (encodeSS [0, 4, 4] 4) := by decide
example : membership [true, false, false, true, false, false] =
    some (encodeSS [4, 4] 4) := by decide
example : membership [true] = some noSS := by decide
example : membership [false, true] = some noSS := by decide

-- The source codec rejects empty, malformed, and noncanonical inputs.
example : hardness [] = some (bitEncode ([1] : List ℕ)) := by decide
example : hardness [true] = some (bitEncode ([1] : List ℕ)) := by decide
example : hardness [false, true] = some (bitEncode ([1] : List ℕ)) := by decide
example : hardness [true, false, false, false] =
    some (bitEncode ([1] : List ℕ)) := by decide
example : hardness (encodeSS [] 1) =
    some (bitEncode ([0, 2] : List ℕ)) := by decide
example : hardness (encodeSS [0, 2, 2] 2) =
    some (bitEncode ([4, 4, 0, 2, 2] : List ℕ)) := by decide
example : hardness (encodeSS [1, 2] 0) =
    some (bitEncode ([3, 0, 1, 2] : List ℕ)) := by decide
example : hardness (encodeSS [1, 2] 3) =
    some (bitEncode ([3, 6, 1, 2] : List ℕ)) := by decide
example : hardness (encodeSS [1, 2] 4) =
    some (bitEncode ([3, 8, 1, 2] : List ℕ)) := by decide
example : membership (bitEncode ([1024, 1024] : List ℕ)) =
    some (encodeSS [2048, 2048] 2048) := by decide

-- No live component label aliases a continuation, including the sum exits.
example (l : SSVerify.Lab) :
    MembershipCore.sumLabel l = .double (.scan .start) ↔
      l = .yes ∨ l = .no := by
  cases l <;> simp [MembershipCore.sumLabel]
example (l : SSVerify.Lab) :
    HardnessCore.sumLabel l = .targetStart ↔ l = .yes ∨ l = .no := by
  cases l <;> simp [HardnessCore.sumLabel]
example (l : DoubleStream.Lab) :
    MembershipCore.doubleLabel l = .prefix ↔ l = .done := by
  cases l <;> simp [MembershipCore.doubleLabel]
example (l : Cslib.Complexity.PolynomialEncoding.ListNatMachine.Lab) :
    MembershipMachine.normLabel l = .move1 ↔ l = .good := by
  cases l <;> simp [MembershipMachine.normLabel]
example (l : Cslib.Complexity.PolynomialEncoding.ListNatMachine.Lab) :
    HardnessMachine.normLabel l = .nonempty ↔ l = .good := by
  cases l <;> simp [HardnessMachine.normLabel]
example (l : MembershipCore.Lab) :
    MembershipMachine.coreLabel l = .done ↔ l = .done := by
  cases l <;> simp [MembershipMachine.coreLabel]
example (l : HardnessCore.Lab) :
    HardnessMachine.coreLabel l = .done ↔ l = .done := by
  cases l <;> simp [HardnessMachine.coreLabel]

-- Useful consumers require unconditional canonical complexity statements.
example : partitionDec ∈ ComplexityTheory.NP := partition_npComplete.1
example (L : ComplexityTheory.DecisionProblem) (h : L ∈ ComplexityTheory.NP) :
    Cslib.CookLevin.PolyManyOneRed L partitionDec := partition_npComplete.2 L h
example : ComplexityTheory.IsPolyTime reduceToSubsetSum :=
  MembershipMachine.isPolyTime_reduceToSubsetSum
example : ComplexityTheory.IsPolyTime reduceFromSubsetSum :=
  HardnessMachine.isPolyTime_reduceFromSubsetSum
