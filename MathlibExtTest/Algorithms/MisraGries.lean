/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.MisraGries

@[expose] public section

/-- On the empty stream the counter for `0` is `0`, matching its frequency. -/
example : (mgRun 3 ([] : List (Fin 2))).1 0 ≤ List.count 0 ([] : List (Fin 2)) :=
  mg_le_freq 3 [] 0

/-- On the empty stream the frequency bound holds trivially. -/
example : List.count 0 ([] : List (Fin 2))
    ≤ (mgRun 3 ([] : List (Fin 2))).1 0 + (mgRun 3 ([] : List (Fin 2))).2 :=
  freq_le_mg_add_rounds 3 [] 0

end
