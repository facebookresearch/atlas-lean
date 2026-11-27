/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.IncreasingSequenceConsecutiveSumsErdosProblem356

open MathlibExt.Combinatorics.IncreasingSequenceConsecutiveSumsErdosProblem356Wanted

example : consecutiveSums (fun i : Fin 0 => i.val + 1) = ∅ := by decide

-- The singleton 3 and the interval 1 + 2 contribute the same value.
example : consecutiveSums (fun i : Fin 3 => i.val + 1) = {1, 2, 3, 5, 6} := by decide
