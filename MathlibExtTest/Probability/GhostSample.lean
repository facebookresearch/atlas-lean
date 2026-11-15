/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.GhostSample
import Mathlib.Tactic.NormNum

@[expose] public section

/-- For `m = 1` the ghost average is the mean itself. -/
example (f : Fin 2 → ℝ) :
    (∑ S' : Fin 1 → Fin 2, empMean f 1 S') / (Fintype.card (Fin 2)) ^ 1
      = (∑ x, f x) / Fintype.card (Fin 2) :=
  empMean_ghost_average f (by norm_num)

end
