/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.TwoSetsSumsetSquaresQuadruple
import Mathlib.Tactic.NormNum

/-! # Tests for square pairwise sums from three semi-magic squares -/

namespace MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

-- The matrices come from family (5.1) with `(u₁, u₂, v₁, v₂) = (4, 3, 2, 1)`. Some linked roots
-- have opposite signs, and `h` has a different row sum from `e` and `g`.
-- The four entries are distinct, and so are the four offsets.
example : PairwiseSumsSquares
    ![275625, 60025, 3164841, 8003241] ![0, 429975, 5835159, (996759 : ℤ)] := by
  let e : Fin 3 → Fin 3 → ℤ := ![![3000, 700, 525], ![840, 1779, 2428], ![245, 2472, 1896]]
  let g : Fin 3 → Fin 3 → ℤ := ![![3000, -700, 525], ![-840, 2829, 1028], ![245, 1128, 2904]]
  let h : Fin 3 → Fin 3 → ℤ := ![![-3000, 3000, 525], ![1128, -1779, 3720], ![-2829, 2472, 2040]]
  have he : IsSemiMagicRoots e := ⟨9765625, by decide⟩
  have hg : IsSemiMagicRoots g := ⟨9765625, by decide⟩
  have hh : IsSemiMagicRoots h := ⟨18275625, by decide⟩
  have hsums := pairwiseSumsSquares_quadruple_of_isSemiMagicRoots e g h
    (he := he) (hg := hg) (hh := hh) (h25 := by decide) (h26 := by decide) (h27 := by decide)
  norm_num [e, g] at hsums
  exact hsums

end MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted
