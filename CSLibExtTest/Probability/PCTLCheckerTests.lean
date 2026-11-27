/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Probability.PCTLChecker
public import Mathlib.Tactic.NormNum
meta import CSLibExt.Probability.PCTLChecker

namespace Cslib.Probability.CheckerTests

open Cslib.Probability

/-- Local copy of the half/half branch chain from the reachability
tests: from `0`, move to the target `1` or the sink `2` with
probability `1/2` each; both are absorbing. -/
def branchDTMC : DTMC (Fin 3) where
  val := fun s t =>
    if s = 0 then (if t = 0 then 0 else 1 / 2)
    else if t = s then 1 else 0
  property := by
    refine Matrix.mem_rowStochastic_iff_sum.mpr ⟨?_, ?_⟩
    · intro s t
      fin_cases s <;> fin_cases t <;> norm_num
    · intro s
      fin_cases s <;> simp [Fin.sum_univ_three]; norm_num

/-- Comparison directions at unequal values. -/
example : Cmp.eval .le (1 / 2 : ℚ) 1 = true :=
  (cmp_eval_correct .le _ _).mpr (show (1 / 2 : ℚ) ≤ 1 by norm_num)
example : Cmp.eval .lt (1 / 2 : ℚ) 1 = true :=
  (cmp_eval_correct .lt _ _).mpr (show (1 / 2 : ℚ) < 1 by norm_num)
example : Cmp.eval .eq (1 / 2 : ℚ) 1 = false := by
  cases h : Cmp.eval .eq (1 / 2 : ℚ) 1 with
  | false => rfl
  | true => exact absurd ((cmp_eval_correct .eq _ _).mp h) (by norm_num : ¬ ((1 / 2 : ℚ) = 1))
example : Cmp.eval .ge (1 / 2 : ℚ) 1 = false := by
  cases h : Cmp.eval .ge (1 / 2 : ℚ) 1 with
  | false => rfl
  | true => exact absurd ((cmp_eval_correct .ge _ _).mp h) (by norm_num : ¬ ((1 / 2 : ℚ) ≥ 1))
example : Cmp.eval .gt (1 / 2 : ℚ) 1 = false := by
  cases h : Cmp.eval .gt (1 / 2 : ℚ) 1 with
  | false => rfl
  | true => exact absurd ((cmp_eval_correct .gt _ _).mp h) (by norm_num : ¬ ((1 / 2 : ℚ) > 1))

/-- Comparison directions at equal values. -/
example : Cmp.eval .le (1 / 2 : ℚ) (1 / 2) = true :=
  (cmp_eval_correct .le _ _).mpr (show (1 / 2 : ℚ) ≤ 1 / 2 by norm_num)
example : Cmp.eval .lt (1 / 2 : ℚ) (1 / 2) = false := by
  cases h : Cmp.eval .lt (1 / 2 : ℚ) (1 / 2) with
  | false => rfl
  | true => exact absurd ((cmp_eval_correct .lt _ _).mp h) (by norm_num : ¬ ((1 / 2 : ℚ) < 1 / 2))
example : Cmp.eval .eq (1 / 2 : ℚ) (1 / 2) = true :=
  (cmp_eval_correct .eq _ _).mpr (show (1 / 2 : ℚ) = 1 / 2 by norm_num)
example : Cmp.eval .ge (1 / 2 : ℚ) (1 / 2) = true :=
  (cmp_eval_correct .ge _ _).mpr (show (1 / 2 : ℚ) ≥ 1 / 2 by norm_num)
example : Cmp.eval .gt (1 / 2 : ℚ) (1 / 2) = false := by
  cases h : Cmp.eval .gt (1 / 2 : ℚ) (1 / 2) with
  | false => rfl
  | true => exact absurd ((cmp_eval_correct .gt _ _).mp h) (by norm_num : ¬ ((1 / 2 : ℚ) > 1 / 2))

/-- The zero matrix is not stochastic and the guarded bounded-until
checker rejects it, even at a target state with horizon zero. -/
example : checkBoundedUntilG (fun _ _ => (0 : ℚ) : Fin 1 → Fin 1 → ℚ)
    {0} {0} 0 0 .eq 1 = false :=
  checkBoundedUntilG_invalid {0} {0} _
    (by simp [stochastic] : stochastic (fun _ _ => (0 : ℚ) : Fin 1 → Fin 1 → ℚ) = false)
    0 0 .eq 1

/-- On the branch chain the horizon-`3` until probability from `0` is
`1/2`, computed by the rational recursion. -/
example : branchDTMC.hitProb {0, 2} {1} 3 0 = 1 / 2 := by
  rw [← hitProbC_eq]
  norm_num [hitProbC, Fin.sum_univ_three, branchDTMC, DTMC.P]

/-- The guarded checker confirms the branch value with the equality
comparison at horizon `3`. -/
example : checkBoundedUntilG branchDTMC.P {0, 2} {1} 3 0 .eq (1 / 2) = true := by
  rw [checkBoundedUntilG_correct]
  show branchDTMC.hitProb {0, 2} {1} 3 0 = 1 / 2
  rw [← hitProbC_eq]
  norm_num [hitProbC, Fin.sum_univ_three, branchDTMC, DTMC.P]

/-- Executable behavior, checked in the kernel: the guarded
bounded-until checker on the raw branch matrix. -/
example :
    checkBoundedUntilG branchDTMC.P {0, 2} {1} 3 0 .eq (1 / 2) = true := by
  decide +kernel

/-- Executable behavior: the guarded next-step checker. -/
example : checkNextG branchDTMC.P {1} 0 .eq (1 / 2) = true := by
  decide +kernel

/-- A matrix with a negative entry (rows still summing to `1`) is not
stochastic. -/
def negRow : Fin 2 → Fin 2 → ℚ :=
  fun s t => if s = 0 then (if t = 0 then 2 else -1) else (if t = 0 then 0 else 1)

example : stochastic negRow = false := by
  decide +kernel

/-- The tabulated checker, executed in the kernel on the branch chain
(values as `Fin 3` states). -/
example :
    checkBoundedUntilTab branchDTMC.P {0, 2} {1} 3 0 .eq (1 / 2) = true := by
  decide +kernel

/-- The whole tabulated row at horizon `3` on the branch chain,
checked in the kernel. -/
example : hitTab branchDTMC.P {0, 2} {1} 3 = [1 / 2, 1, 0] := by
  decide +kernel

/-- The tabulated lookup agrees with the reference recursion at every
state of the branch chain. -/
example (i : Fin 3) :
    lookupTab branchDTMC.P {0, 2} {1} 3 i =
      hitProbC branchDTMC.P {0, 2} {1} 3 i :=
  lookupTab_eq _ _ _ _ _

/-- A chain on `Bool`, a state type other than `Fin m`: from `false`,
move to the target `true` or stay, with probability `1/2` each; `true`
is absorbing. -/
def boolP : Bool → Bool → ℚ :=
  fun s t => if s then (if t then 1 else 0) else 1 / 2

/-- The tabulated horizon-`2` until probability from `false` on the
`Bool` chain is `1 - (1/2)^2`, computed in the kernel. -/
example : hitProbTab boolP {false} {true} 2 false = 3 / 4 := by
  decide +kernel

/-- The guarded bounded-until checker on the `Bool` chain, executed in
the kernel. -/
example : checkBoundedUntilG boolP {false} {true} 2 false .eq (3 / 4) = true := by
  decide +kernel

/- A horizon out of reach of the reference recursion, which would make
about `7^40` recursive calls here: the compiled guarded checker on the
uniform chain on `Fin 8`, where the target `0` is reached from `1`
within `40` steps with probability exactly `1 - (7/8)^40`. -/
#guard checkBoundedUntilG (fun _ _ : Fin 8 => (1 / 8 : ℚ)) (Finset.univ.erase 0) {0} 40 1
  .eq (1 - (7 / 8) ^ 40)

end Cslib.Probability.CheckerTests
