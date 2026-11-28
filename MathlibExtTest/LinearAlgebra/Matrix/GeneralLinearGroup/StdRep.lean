/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.StdRep

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

#check @Matrix.GeneralLinearGroup.stdRep
#check @Matrix.GeneralLinearGroup.stdRep_apply

-- `simp` evaluates the standard representation on a concrete matrix and vector: the shear
-- `!![1, 1; 0, 1] ∈ GL₂(ℚ)` sends `(1, 2)` to `(3, 2)`.
example :
    Matrix.GeneralLinearGroup.stdRep (Fin 2) ℚ
        (Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by simp)) ![1, 2] =
      ![3, 2] := by
  ext i
  fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
  norm_num

-- The standard representation in an arbitrary universe.
example {n R : Type 1} [Fintype n] [DecidableEq n] [CommRing R] (g : GL n R) (v : n → R) :
    Matrix.GeneralLinearGroup.stdRep n R g v = (g : Matrix n n R).mulVec v := by
  simp
