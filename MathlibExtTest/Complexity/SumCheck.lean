/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.SumCheck
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

@[expose] public section

open Polynomial

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Boundary check (completeness): the honest prover for
`p = X` over `ZMod 5` is accepted at challenge `3` for the
true sum `0 + 1 = 1`. -/
example : accept1 (X : (ZMod 5)[X]) (X : (ZMod 5)[X])
    (1 : ZMod 5) (3 : ZMod 5) :=
  sumcheck1_complete _ _ (by simp [eval_X]) _

/-- Boundary check (soundness): the constant prover `q = 1`
against `p = 0` over `ZMod 5` agrees at no challenge, within
the degree bound `0`. -/
example : (Finset.univ.filter
      (fun r : ZMod 5 => (1 : (ZMod 5)[X]).eval r
        = (0 : (ZMod 5)[X]).eval r)).card ≤ 0 :=
  sumcheck1_sound (0 : (ZMod 5)[X]) (1 : (ZMod 5)[X]) 0
    (by simp) (by simp) one_ne_zero
