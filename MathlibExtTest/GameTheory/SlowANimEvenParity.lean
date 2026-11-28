/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.GameTheory.SlowANimEvenParity

namespace MetaMathlibExt.slowANim_one_n_even_isP_iff

-- A zero minimum need not be unique, and the stacks need not be sorted.
example : SpragueGrundy.IsP (slowANimGame 4 {1, 4}) ![3, 0, 1, 0] :=
  (slowANim_one_n_even_isP_iff 4 (by decide) (by decide) _).2 (by decide)

-- An all-stack move sends this even-total position to the all-zero position.
example : ¬ SpragueGrundy.IsP (slowANimGame 2 {1, 2}) ![1, 1] :=
  fun h => (by decide : ¬ ∃ i : Fin 2, (∀ j, (![1, 1] : Fin 2 → ℕ) i ≤ ![1, 1] j) ∧
    Even (![1, 1] i)) ((slowANim_one_n_even_isP_iff 2 (by decide) (by decide) _).1 h).2

-- Playing a single taller stack is legal even when the all-stack move is blocked.
example : ¬ SpragueGrundy.IsP (slowANimGame 2 {1, 2}) ![1, 0] :=
  fun h => (by decide : ¬ Even (∑ i : Fin 2, (![1, 0] : Fin 2 → ℕ) i))
    ((slowANim_one_n_even_isP_iff 2 (by decide) (by decide) _).1 h).1

-- Playing one of several tied odd minima makes it the new even minimum.
example : ¬ SpragueGrundy.IsP (slowANimGame 4 {1, 4}) ![1, 1, 1, 2] :=
  fun h => (by decide : ¬ Even (∑ i : Fin 4, (![1, 1, 1, 2] : Fin 4 → ℕ) i))
    ((slowANim_one_n_even_isP_iff 4 (by decide) (by decide) _).1 h).1

end MetaMathlibExt.slowANim_one_n_even_isP_iff
