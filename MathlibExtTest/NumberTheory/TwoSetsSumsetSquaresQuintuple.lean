/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.TwoSetsSumsetSquaresQuintuple
import Mathlib.Tactic.NormNum

/-! # Tests for square pairwise sums from two semi-magic squares -/

namespace MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

-- The common row sums differ between matrices, and the diagonal roots have opposite signs.
-- The five entries are distinct and both nonzero offsets are negative.
example : PairwiseSumsSquares
    ![940900, 2490084, 1512900, 864900, 1295044] ![0, -856800, (-675675 : ℤ)] := by
  let e : Fin 3 → Fin 3 → ℤ := ![![915, 1278, 970], ![290, 1230, 1347], ![1578, 515, 810]]
  let f : Fin 3 → Fin 3 → ℤ := ![![-915, 662, 930], ![90, -1230, 787], ![1138, 435, -810]]
  have he : IsSemiMagicRoots e := ⟨3411409, by decide⟩
  have hf : IsSemiMagicRoots f := ⟨2140369, by decide⟩
  have h := pairwiseSumsSquares_quintuple_of_isSemiMagicRoots e f
    (he := he) (hf := hf) (hdiag := by decide)
  norm_num [e, f] at h
  exact h

end MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted
