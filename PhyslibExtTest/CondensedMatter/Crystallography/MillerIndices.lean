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
* Zone axis: `(100)` and `(010)` are not parallel and their zone axis is `[001]`; for the
  parallel pair `(100)`, `(100)` the index cross product is `0`, the zero vector.
* Angle: in the simple cubic lattice the angle between `[100]` and `[110]` has cosine `1 / √2`.
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

/-! ### Zone axis: non-parallel and parallel planes -/

/-- The index cross product of `(100)` and `(010)` is `[001]`. -/
lemma zoneAxis_100_010 : zoneAxis ![1, 0, 0] ![0, 1, 0] = ![0, 0, 1] := by
  funext i
  fin_cases i <;> simp [zoneAxis, cross_apply]

/-- `(100)` and `(010)` are not parallel, so `[001]` is their zone axis: every direction lying
in both planes is a multiple of `[001]`. -/
lemma zoneAxis_unique_100_010 (a : ℝ) (ha : 0 < a) (u : Fin 3 → ℤ)
    (hu : ⟪reciprocalVector (simpleCubic a ha) ![1, 0, 0],
      latticeDirection (simpleCubic a ha) u⟫ = 0)
    (hu' : ⟪reciprocalVector (simpleCubic a ha) ![0, 1, 0],
      latticeDirection (simpleCubic a ha) u⟫ = 0) :
    ∃ c : ℝ, latticeDirection (simpleCubic a ha) u
      = c • latticeDirection (simpleCubic a ha) ![0, 0, 1] := by
  rw [← zoneAxis_100_010]
  exact (zoneAxis_unique _ _ _ (by rw [zoneAxis_100_010]; decide)).2.2.2 u hu hu'

/-- **Parallel planes have no zone axis**: for the pair `(100)`, `(100)` the index cross product
is `0`, and its lattice vector is the zero vector, which is not a direction. -/
lemma zoneAxis_parallel_100 (a : ℝ) (ha : 0 < a) :
    zoneAxis ![1, 0, 0] ![1, 0, 0] = 0
      ∧ latticeDirection (simpleCubic a ha) (zoneAxis ![1, 0, 0] ![1, 0, 0]) = 0 := by
  have h0 : zoneAxis ![1, 0, 0] ![1, 0, 0] = 0 := by
    simp [zoneAxis]
  refine ⟨h0, ?_⟩
  rw [h0, latticeDirection_eq_latticeVector, map_zero]

/-! ### Angle from the metric tensor -/

/-- In the simple cubic lattice of side `a`, the angle between `[100]` and `[110]` has cosine
`1 / √2`, computed from `G = a² • 1`. -/
lemma cos_angle_100_110 (a : ℝ) (ha : 0 < a) :
    Real.cos (InnerProductGeometry.angle (latticeDirection (simpleCubic a ha) ![1, 0, 0])
      (latticeDirection (simpleCubic a ha) ![1, 1, 0])) = 1 / Real.sqrt 2 := by
  rw [latticeDirection_eq_sum, latticeDirection_eq_sum, cos_angle_fractional]
  simp only [metricTensor_simpleCubic_apply, Fin.sum_univ_three]
  norm_num
  have h1 : Real.sqrt (a ^ 2) = a := Real.sqrt_sq ha.le
  have h2 : Real.sqrt (a ^ 2 + a ^ 2) = Real.sqrt 2 * a := by
    rw [show a ^ 2 + a ^ 2 = 2 * a ^ 2 by ring, Real.sqrt_mul (by norm_num), h1]
  rw [h1, h2]
  field_simp

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
