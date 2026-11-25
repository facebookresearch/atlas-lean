/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.BlockCompatibleSequenceCount
import Mathlib.Data.Fintype.Powerset

open MathlibExt.Combinatorics.BlockCompatibleSequenceCountWanted

-- A triple on four points leaves exactly three pairs to complete.
example : BlockCompatible 4 [3, 2, 2, 2] := by
  refine ⟨by decide, by decide, [{0, 1, 2}, {0, 3}, {1, 3}, {2, 3}], by decide, ?_⟩
  unfold IsPBD
  decide

-- Retaining a pair already covered by a triple violates uniqueness.
example : ¬ IsPBD 3 [{0, 1, 2}, {0, 1}] := by
  unfold IsPBD
  decide

-- A permutation of the same block sizes can violate the descending-order convention.
example : ¬ BlockCompatible 4 [2, 3, 2, 2] := fun h =>
  (by decide : ¬ List.Pairwise (· ≥ ·) [2, 3, 2, 2]) h.1
