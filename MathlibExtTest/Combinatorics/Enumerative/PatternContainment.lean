/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PatternContainment

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

-- The empty pattern occurs even in the empty permutation.
example : HasPattern (Equiv.refl (Fin 0)) (id : Fin 0 → Fin 0) := by
  decide +kernel

-- A strictly increasing pair of positions cannot fit in a singleton.
example : ¬ HasPattern (Equiv.refl (Fin 1)) (id : Fin 2 → Fin 2) := by
  decide +kernel
