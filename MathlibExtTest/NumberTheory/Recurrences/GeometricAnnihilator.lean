/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.Rat
import MathlibExt.NumberTheory.Recurrences.GeometricAnnihilator

namespace MetaMathlibExt

open Polynomial

example : AnnihilatesSeq X (fun s => (0 : ℚ) ^ s) := by
  simpa only [map_zero, sub_zero] using annihilatesSeq_X_sub_C_pow (0 : ℚ)

-- At index zero the zero-ratio sequence starts with `0 ^ 0 = 1`, not zero.
example : (X : ℚ[X]).sum (fun i a => a * (0 : ℚ) ^ (0 + i)) = 0 := by
  simpa only [map_zero, sub_zero] using annihilatesSeq_X_sub_C_pow (0 : ℚ) 0

example : AnnihilatesSeq (X - C (-2 : ℚ)) (fun s => (-2 : ℚ) ^ s) :=
  annihilatesSeq_X_sub_C_pow (-2 : ℚ)

end MetaMathlibExt
