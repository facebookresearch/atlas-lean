/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.StateSpace.Discrete

namespace ControlTheory.StateSpaceCoeffs

private noncomputable def acc : StateSpaceCoeffs ℝ ℝ ℝ ℝ :=
  ⟨1, 1, 1, 0⟩

-- The scalar accumulator with unit input accumulates one unit per step.
example : dtTraj acc (fun _ => (1 : ℝ)) 0 3 = 3 := by
  norm_num [acc, dtTraj]

example : dtTraj acc (fun _ => (1 : ℝ)) 0 0 = 0 :=
  dtTraj_zero acc (fun _ => (1 : ℝ)) 0

-- With `x0 = 10` and input `u j = j + 1`, the first values are
-- `10, 11, 13, 16`; the output agrees because `C = 1` and `D = 0`.
example : dtTraj acc (fun j => (j : ℝ) + 1) 10 3 = 16 := by
  norm_num [acc, dtTraj]

example : dtOutput acc (fun j => (j : ℝ) + 1) 10 3 = 16 := by
  norm_num [acc, dtOutput, dtTraj]

-- Two unrolled steps expose the closed-form index convention: the first
-- input is advanced by one application of `A`, the second is not.
example (S : StateSpaceCoeffs ℝ ℝ ℝ ℝ) (u : ℕ → ℝ) (x0 : ℝ) :
    dtTraj S u x0 2 = S.A (S.A x0 + S.B (u 0)) + S.B (u 1) := by
  rw [dtTraj_succ, dtTraj_succ, dtTraj_zero]

example (S : StateSpaceCoeffs ℝ ℝ ℝ ℝ) (u : ℕ → ℝ) (x0 : ℝ) :
    dtTraj S u x0 2
      = (S.A ^ 2) x0 + ∑ j ∈ Finset.range 2, (S.A ^ (2 - 1 - j)) (S.B (u j)) :=
  dtTraj_closedForm S u x0 2

-- The explicitly given scalar sequence `k ↦ k` is the accumulator
-- trajectory for unit input, by uniqueness.
example : (fun k : ℕ => (k : ℝ)) = dtTraj acc (fun _ => (1 : ℝ)) 0 := by
  apply dtTraj_unique
  · simp
  · intro k
    simp [acc]

-- Zero input from the zero state stays at zero.
example (S : StateSpaceCoeffs ℝ ℝ ℝ ℝ) :
    (fun _ => (0 : ℝ)) = dtTraj S (fun _ => (0 : ℝ)) 0 := by
  apply dtTraj_unique
  · rfl
  · intro k
    simp

-- The output closed form is the state closed form mapped through `C`,
-- plus the feedthrough term.
example (S : StateSpaceCoeffs ℝ ℝ ℝ ℝ) (u : ℕ → ℝ) (x0 : ℝ) (k : ℕ) :
    dtOutput S u x0 k
      = S.C ((S.A ^ k) x0 + ∑ j ∈ Finset.range k, (S.A ^ (k - 1 - j)) (S.B (u j)))
        + S.D (u k) :=
  dtOutput_closedForm S u x0 k

end ControlTheory.StateSpaceCoeffs

#print axioms ControlTheory.StateSpaceCoeffs.dtTraj_zero
#print axioms ControlTheory.StateSpaceCoeffs.dtTraj_succ
#print axioms ControlTheory.StateSpaceCoeffs.dtTraj_closedForm
#print axioms ControlTheory.StateSpaceCoeffs.dtTraj_unique
#print axioms ControlTheory.StateSpaceCoeffs.dtOutput_apply
#print axioms ControlTheory.StateSpaceCoeffs.dtOutput_closedForm
