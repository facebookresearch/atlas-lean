/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RouletteExpectation
import Mathlib.Tactic

@[expose] public section

namespace RussianRoulette

/-- Test target kernel: `T 0 1 = 2`, else `0`. -/
noncomputable def testT (a b : ℕ) : ℝ := if a = 0 ∧ b = 1 then 2 else 0

/-- Test conditional kernel: `P 0 1 = P 1 1 = 1`, else `0`. -/
noncomputable def testP (a b : ℕ) : ℝ :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 1) then 1 else 0

/-- Test sampling kernel from `stepKernel` with stop probability `1 / 2`. -/
noncomputable def testQ : ℕ → ℕ → ℝ :=
  stepKernel (fun _ : ℕ => (1 / 2 : ℝ)) testP

/-- Test emission: constantly `1`. -/
noncomputable def testE : ℕ → ℝ := fun _ => 1

/-- Test length-two path visiting `0` then `1`. -/
def testX : Fin 2 → ℕ := fun k => if k = 0 then 0 else 1

example {S : Type*} (T Q : S → S → ℝ) (E : S → ℝ) :
    pathScore T Q E [] = 0 := rfl

example {S : Type*} (T Q : S → S → ℝ) (E : S → ℝ) (x : S) :
    pathScore T Q E [x] = E x := rfl

example : pathScore testT testQ testE [0] = 1 := by
  simp [pathScore, testE]

example : pathScore testT testQ testE [0, 1] = 5 := by
  simp [pathScore, testT, testP, testQ, testE, stepKernel]
  norm_num

example : pathScore testT testQ testE [0, 1, 1] = 5 := by
  simp [pathScore, testT, testP, testQ, testE, stepKernel]
  norm_num

example : List.ofFn testX = [0, 1] := by
  decide

example : pathScore testT testQ testE (List.ofFn testX)
    = ∑ k : Fin 2, ratioWeight testT testQ
        (fun j : Fin (k.val + 1) =>
          testX ⟨j.val, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt k.2)⟩)
        * testE (testX k) :=
  pathScore_ofFn (n := 1) testT testQ testE testX

example : pathScore testT testQ testE (List.ofFn testX) = 5 := by
  have hofn : List.ofFn testX = [0, 1] := by decide
  rw [hofn]
  simp [pathScore, testT, testP, testQ, testE, stepKernel]
  norm_num

end RussianRoulette

end
public section
