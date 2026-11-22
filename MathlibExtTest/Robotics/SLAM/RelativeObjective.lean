/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Robotics.SLAM.RelativeObjective
import Mathlib.LinearAlgebra.Matrix.Notation

open Robotics.SLAM

-- Two pose-landmark pairs with distinct poses
-- `![swap 0 1, swap 1 2]`, landmarks `![0, 2]`, and the
-- common transform `swap 0 2`: the objective over the
-- relative observations is invariant.
example :
    (∑ i : Fin 2, (fun l d : Fin 3 => (((l : ℤ) - (d : ℤ)).natAbs : ℝ))
      ((Equiv.swap (0 : Fin 3) 2 * ![Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2] i)⁻¹ •
        (Equiv.swap (0 : Fin 3) 2) • (![(0 : Fin 3), 2] i)) (![1, 0] i))
      = ∑ i : Fin 2, (fun l d : Fin 3 => (((l : ℤ) - (d : ℤ)).natAbs : ℝ))
        ((![Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2] i)⁻¹ • (![(0 : Fin 3), 2] i))
        (![1, 0] i) :=
  objective_invariant_of_relative
    (fun i => ![Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2] i)
    (Equiv.swap (0 : Fin 3) 2)
    (fun i => ![(0 : Fin 3), 2] i) (fun i => ![1, 0] i)
    (fun l d : Fin 3 => (((l : ℤ) - (d : ℤ)).natAbs : ℝ))

-- The two poses are genuinely distinct, so the test does
-- not collapse to a one-pose special case.
example :
    ![Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2] 0
      ≠ ![Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2] 1 := by
  decide

-- A loss that uses the absolute landmark position is not
-- invariant in general: here the two sums are `1` and `0`.
example :
    (∑ _i : Fin 1, (fun l : Fin 3 => ((l : ℕ) : ℝ))
      ((Equiv.swap (0 : Fin 3) 1) • (0 : Fin 3)))
      ≠ ∑ _i : Fin 1, (fun l : Fin 3 => ((l : ℕ) : ℝ)) (0 : Fin 3) := by
  simp [Equiv.swap_apply_left]

#print axioms objective_invariant_of_relative
