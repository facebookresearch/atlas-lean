/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.SumCheck
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open Polynomial

namespace MathlibExtTest.Complexity.SumCheck

open MathlibExt.Complexity.SumCheck

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Boundary check (completeness): the honest prover for
`p = X` over `ZMod 5`, with degree bound `1`, is accepted at
challenge `3` for the true sum `0 + 1 = 1`. -/
example : accept1 1 (X : (ZMod 5)[X]) (X : (ZMod 5)[X])
    (1 : ZMod 5) (3 : ZMod 5) :=
  sumcheck1_complete natDegree_X_le (by simp [eval_X]) _

/-- Boundary check (root bound): the constant prover `q = 1`
against `p = 0` over `ZMod 5` agrees at no challenge, within
the degree bound `0`. -/
example : (Finset.univ.filter
      (fun r : ZMod 5 => (1 : (ZMod 5)[X]).eval r
        = (0 : (ZMod 5)[X]).eval r)).card ≤ 0 :=
  card_agree_le (0 : (ZMod 5)[X]) (1 : (ZMod 5)[X]) 0
    (by simp) (by simp) one_ne_zero

/-- Regression: over `ZMod 5`, the over-degree message `1 - X ^ 4` for the false claim
`p = 0`, `H = 1` passes the Boolean-sum check and agrees with `p` at every nonzero
challenge, so a verifier without the degree check would accept four challenges. -/
theorem overDegree_passes_sum_and_agrees :
    (1 - X ^ 4 : (ZMod 5)[X]).eval 0 + (1 - X ^ 4 : (ZMod 5)[X]).eval 1 = 1 ∧
      ∀ r : ZMod 5, r ≠ 0 →
        (1 - X ^ 4 : (ZMod 5)[X]).eval r = (0 : (ZMod 5)[X]).eval r := by
  refine ⟨by simp, fun r hr => ?_⟩
  have h4 : r ^ 4 = 1 := ZMod.pow_card_sub_one_eq_one hr
  simp [h4]

/-- Regression: the degree check rejects `1 - X ^ 4` at every challenge, because a
polynomial of degree `0` is constant while `1 - X ^ 4` takes the values `1` at `0` and `0`
at `1`. -/
theorem overDegree_rejected (r : ZMod 5) :
    ¬ accept1 0 (0 : (ZMod 5)[X]) (1 - X ^ 4) 1 r := by
  rintro ⟨hdeg, -, -⟩
  have h := congrArg (eval 1) (eq_C_of_natDegree_le_zero hdeg)
  have h1 : (1 - X ^ 4 : (ZMod 5)[X]).eval 1 = 0 := by simp
  have h0 : (1 - X ^ 4 : (ZMod 5)[X]).coeff 0 = 1 := by simp [coeff_one, coeff_X_pow]
  rw [eval_C, h1, h0] at h
  exact zero_ne_one h

/-- Soundness on the regression case: for the false claim `p = 0`, `H = 1` with degree
bound `0`, the verifier accepts `1 - X ^ 4` at no challenge. -/
theorem overDegree_accepted_nowhere :
    (Finset.univ.filter
      (fun r : ZMod 5 => accept1 0 (0 : (ZMod 5)[X]) (1 - X ^ 4) 1 r)).card ≤ 0 :=
  sumcheck1_sound (by simp) (by simp) _

end MathlibExtTest.Complexity.SumCheck
