/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.DyckPeakDescents

namespace MetaMathlibExt

open DyckStep

example : dyckPeakDescents [] = [] := by decide

example : dyckPeakDescents [U, D] = [1] := by decide

/-- `U U D D U D`: two peaks with descents `2` and `1`. -/
example : dyckPeakDescents [U, U, D, D, U, D] = [2, 1] := by decide

/-- A trailing `U` is not a peak. -/
example : dyckPeakDescents [U, D, U] = [1] := by decide

example : dyckPeakDescents [U, U, U, U, D, D, D, U, D, D, U, U, D, U, U, D, D, D] =
    [3, 2, 1, 3] := dyckPeakDescents_sample

end MetaMathlibExt
