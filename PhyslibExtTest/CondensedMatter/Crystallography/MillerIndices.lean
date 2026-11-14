/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.Crystallography.MillerIndices

/-!
# Tests for `PhyslibExt.CondensedMatter.Crystallography.MillerIndices`

* Cubic spacing: `(100)` has spacing `a` and `(110)` has spacing `a / √2` in the simple
  cubic lattice of side `a`.
* Zone law: the direction `[010]` lies in the plane `(100)`, while `[100]` does not
  (pairing `1`).
* Miller-Bravais: the direction `[110]` converts to `[1/3, 1/3, -2/3, 0]`, and the plane
  `(102)` converts to `(10-12)`.
* Reduced vs unreduced: `(200)` has spacing `a / 2`, half the `(100)` spacing `a`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.Crystallography.MillerIndices

open _root_.Crystallography _root_.Crystallography.BravaisLattice
open scoped Matrix RealInnerProductSpace

/-! ### Cubic spacing instances -/

/-- `(100)` in a cubic cell of side `a` has spacing `a`. -/
lemma cubic100_spacing (a : ℝ) (ha : 0 < a) :
    interplanarSpacing (simpleCubic a ha) ![1, 0, 0] = a := by
  rw [spacing_simpleCubic _ _ _ (by decide)]
  norm_num [Real.sqrt_one]

/-- `(110)` in a cubic cell of side `a` has spacing `a / √2`. -/
lemma cubic110_spacing (a : ℝ) (ha : 0 < a) :
    interplanarSpacing (simpleCubic a ha) ![1, 1, 0] = a / Real.sqrt 2 := by
  rw [spacing_simpleCubic _ _ _ (by decide)]
  norm_num [Real.sqrt_one]

/-! ### Zone law instance and non-zone counterexample -/

/-- The direction `[010]` lies in the plane `(100)`. -/
lemma zone_mem_100_010 (a : ℝ) (ha : 0 < a) :
    ⟪reciprocalVector (simpleCubic a ha) ![1, 0, 0],
      latticeDirection (simpleCubic a ha) ![0, 1, 0]⟫ = 0 := by
  rw [inner_reciprocalVector_latticeDirection]
  norm_num

/-- The direction `[100]` does not lie in the plane `(100)`: the pairing is `1`. -/
lemma zone_nonmem_100_100 (a : ℝ) (ha : 0 < a) :
    ⟪reciprocalVector (simpleCubic a ha) ![1, 0, 0],
      latticeDirection (simpleCubic a ha) ![1, 0, 0]⟫ = 1 := by
  rw [inner_reciprocalVector_latticeDirection]
  norm_num

/-! ### Miller-Bravais conversion instances -/

/-- The direction `[110]` converts to `[1/3, 1/3, -2/3, 0]`. -/
lemma millerBravais_dir_110 :
    toMillerBravaisDir ![1, 1, 0] = ![1 / 3, 1 / 3, -2 / 3, 0] := by
  funext i
  fin_cases i <;> simp [toMillerBravaisDir, toMillerBravaisDirQ] <;> norm_num

/-- The plane `(102)` converts to `(10-12)`. -/
lemma millerBravais_plane_102 :
    millerBravaisPlane ![1, 0, 2] = ![1, 0, -1, 2] := by
  funext i
  fin_cases i <;> simp [millerBravaisPlane]

/-! ### Reduced vs unreduced indices -/

/-- `(200)` has spacing `a / 2`: unreduced indices shrink the spacing. -/
lemma spacing_200_unreduced (a : ℝ) (ha : 0 < a) :
    interplanarSpacing (simpleCubic a ha) ![2, 0, 0] = a / 2 := by
  have h2 : (2 : ℤ) • (![1, 0, 0] : Fin 3 → ℤ) = ![2, 0, 0] := by decide
  rw [← h2, interplanarSpacing_smul _ 2 _ (by decide) (by decide),
    cubic100_spacing a ha]
  norm_num

end PhyslibExtTest.CondensedMatter.Crystallography.MillerIndices
