/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.UlamWords

namespace MetaMathlibExt.isUlamWord_three_ones_zeros_iff

-- The two-letter word 10 needs both levels of the fuel-bounded test.
example : ulamWordAux 1 [true, false] = false ∧ ulamWordAux 2 [true, false] = true := by
  decide

-- Direct computation at the lower bound and in each of the next three residue classes.
example :
    ¬IsUlamWord [true, true, true] ∧
      IsUlamWord [true, true, true, false] ∧
      IsUlamWord [true, true, true, false, false] ∧
      ¬IsUlamWord [true, true, true, false, false, false] := by
  decide

-- The criterion also applies to words of symbolic length.
example (k : ℕ) : IsUlamWord (List.replicate 3 true ++ List.replicate (4 * k + 1) false) := by
  apply (isUlamWord_three_ones_zeros_iff (4 * k + 4) (by omega)).2
  omega

end MetaMathlibExt.isUlamWord_three_ones_zeros_iff
