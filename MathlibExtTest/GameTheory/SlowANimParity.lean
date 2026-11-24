/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.GameTheory.SlowANimParity

namespace MetaMathlibExt.slowANim_one_odd_isP_iff

-- All stacks are nonempty, so both move sizes are available.
example : SpragueGrundy.IsP (slowANimGame 3 {1, 3}) ![2, 1, 1] :=
  (slowANim_one_odd_isP_iff 3 3 (by decide) (by decide) _).2 (by decide)

-- An odd total still permits a one-stack move when the three-stack move is blocked.
example : ¬ SpragueGrundy.IsP (slowANimGame 3 {1, 3}) ![0, 1, 0] :=
  fun h => (by decide : ¬ Even (∑ i : Fin 3, (![0, 1, 0] : Fin 3 → ℕ) i))
    ((slowANim_one_odd_isP_iff 3 3 (by decide) (by decide) _).1 h)

-- With k = 1 the two allowed sizes coincide.
example : SpragueGrundy.IsP (slowANimGame 1 {1}) ![2] :=
  (slowANim_one_odd_isP_iff 1 1 (by decide) (by decide) _).2 (by decide)

end MetaMathlibExt.slowANim_one_odd_isP_iff
