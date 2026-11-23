/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.GenericGroup.BSGS
public import Mathlib.Data.Nat.Sqrt

/-!
# Tests for baby-step giant-step discrete logarithm

Concrete runs of `bsgs` against the fixed-encoding oracle `oracleOf`, checked by
`decide`: `q = 7` with two explicit encoding permutations and several targets
(including `x = 0` and `x.val = q - 1`), the `q = 2` edge case, and a
queries-length spot check.
-/

@[expose] public section

namespace CSLibExtTest.Crypto.Framework.GenericGroup.BSGSTests

open CSLibExt.Crypto.Framework.GenericGroup
open Cslib.Crypto.Framework.GenericGroup
open Cslib.Crypto.Framework

instance : Fact (1 < 7) := ⟨by decide⟩
instance : Fact (1 < 2) := ⟨by decide⟩

/-- First test encoding on `ZMod 7`: swap labels `0` and `1`. -/
def encA : Equiv.Perm (ZMod 7) := Equiv.swap 0 1

/-- Second test encoding on `ZMod 7`: swap labels `2` and `5`. -/
def encB : Equiv.Perm (ZMod 7) := Equiv.swap 2 5

/-- Test encoding on `ZMod 2`: swap labels `0` and `1`. -/
def enc2 : Equiv.Perm (ZMod 2) := Equiv.swap 0 1

theorem hm7 : bsgsM 7 = 3 := by
  show Nat.sqrt (7 - 1) + 1 = 3
  have hsqrt : Nat.sqrt 6 = 2 := (Nat.eq_sqrt.mpr ⟨by decide, by decide⟩).symm
  rw [show (7 - 1 : Nat) = 6 from rfl, hsqrt]

theorem hm2 : bsgsM 2 = 2 := by
  show Nat.sqrt (2 - 1) + 1 = 2
  rw [show (2 - 1 : Nat) = 1 from rfl, Nat.sqrt_one]

example : OracleComp.run (oracleOf encA) (bsgs (encA 0) (encA 1) (encA 0))
    = some (0 : ZMod 7) := by
  simp only [bsgs_eq, hm7]
  decide

example : OracleComp.run (oracleOf encA) (bsgs (encA 0) (encA 1) (encA 1))
    = some (1 : ZMod 7) := by
  simp only [bsgs_eq, hm7]
  decide

example : OracleComp.run (oracleOf encA) (bsgs (encA 0) (encA 1) (encA 3))
    = some (3 : ZMod 7) := by
  simp only [bsgs_eq, hm7]
  decide

example : OracleComp.run (oracleOf encA) (bsgs (encA 0) (encA 1) (encA 6))
    = some (6 : ZMod 7) := by
  simp only [bsgs_eq, hm7]
  decide

example : OracleComp.run (oracleOf encB) (bsgs (encB 0) (encB 1) (encB 0))
    = some (0 : ZMod 7) := by
  simp only [bsgs_eq, hm7]
  decide

example : OracleComp.run (oracleOf encB) (bsgs (encB 0) (encB 1) (encB 2))
    = some (2 : ZMod 7) := by
  simp only [bsgs_eq, hm7]
  decide

example : OracleComp.run (oracleOf encB) (bsgs (encB 0) (encB 1) (encB 6))
    = some (6 : ZMod 7) := by
  simp only [bsgs_eq, hm7]
  decide

example : OracleComp.run (oracleOf enc2) (bsgs (enc2 0) (enc2 1) (enc2 0))
    = some (0 : ZMod 2) := by
  simp only [bsgs_eq, hm2]
  decide

example : OracleComp.run (oracleOf enc2) (bsgs (enc2 0) (enc2 1) (enc2 1))
    = some (1 : ZMod 2) := by
  simp only [bsgs_eq, hm2]
  decide

example : (OracleComp.queries (oracleOf encA) (bsgs (encA 0) (encA 1) (encA 3))).length
    ≤ 2 * bsgsM 7 := by
  simp only [bsgs_eq, hm7]
  decide

end CSLibExtTest.Crypto.Framework.GenericGroup.BSGSTests
