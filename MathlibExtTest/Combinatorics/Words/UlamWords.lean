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

namespace MetaMathlibExt.ulamResidueCount_mod_two_three

-- At the minimum length both parities occur, and the third residue modulo 3 is absent.
example : ulamResidueCount 2 1 0 = 1 ∧ ulamResidueCount 2 1 1 = 1 ∧
    ulamResidueCount 3 1 0 = 1 ∧ ulamResidueCount 3 1 1 = 1 ∧ ulamResidueCount 3 1 2 = 0 := by
  decide

-- Complementation exchanges 1 and 2 modulo 3 at positive even lengths.
example (k : ℕ) (hk : 0 < k) : ulamResidueCount 3 (2 * k) 1 = ulamResidueCount 3 (2 * k) 2 := by
  simpa only [ite_eq_left (even_two_mul k), show -(1 : ZMod 3) = 2 by decide] using
    (ulamResidueCount_mod_two_three (2 * k) (by omega)).2 1

-- At odd lengths it exchanges 0 and 1 instead.
example (k : ℕ) : ulamResidueCount 3 (2 * k + 1) 0 = ulamResidueCount 3 (2 * k + 1) 1 := by
  simpa using (ulamResidueCount_mod_two_three (2 * k + 1) (by omega)).2 0

end MetaMathlibExt.ulamResidueCount_mod_two_three
