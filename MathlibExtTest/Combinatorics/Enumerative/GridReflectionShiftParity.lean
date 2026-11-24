/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GridReflectionTilings

/-! # Tests for the parity obstruction to shifted reflection fixed points -/

namespace MetaMathlibExt

-- The smallest positive even modulus, with zero shift.
example : {x : ZMod 2 | x = -1 - x - 0} = ∅ :=
  reflection_shift_solutions_even_even (n := 2) (a := 0) (hn := by decide) (ha := by decide)

-- A composite even modulus, with nonzero even shift.
example : {x : ZMod 6 | x = -1 - x - 2} = ∅ :=
  reflection_shift_solutions_even_even (n := 6) (a := 2) (hn := by decide) (ha := by decide)

-- At the same modulus, an odd shift can have a fixed point.
example : (2 : ZMod 6) ∈ {x : ZMod 6 | x = -1 - x - 1} := by
  change (2 : ZMod 6) = -1 - 2 - 1
  decide

end MetaMathlibExt
