/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The real line as one-dimensional Euclidean space

`lineIsometry : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1)` is the bundled linear isometry sending `x` to
the vector whose sole coordinate is `x`. Its `LinearIsometryEquiv` API supplies the inverse,
linearity, norm, distance, continuity, measurability and Lipschitz bounds, so modules that move
between `ℝ` and `EuclideanSpace ℝ (Fin 1)` share one representation.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.LineIsometry

/-- **Identification of the line with one-dimensional Euclidean space.** The linear isometric
isomorphism from $\mathbb{R}$ onto one-dimensional Euclidean space $\mathbb{R}^1$ that sends a
real number $x$ to the vector whose only coordinate is $x$. -/
noncomputable def lineIsometry : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

@[simp] theorem lineIsometry_apply (x : ℝ) (i : Fin 1) : lineIsometry x i = x :=
  OrthonormalBasis.singleton_repr x i

/-- The inverse of `lineIsometry` reads the sole coordinate. -/
theorem lineIsometry_symm_apply (y : EuclideanSpace ℝ (Fin 1)) :
    lineIsometry.symm y = y 0 := by
  have h := lineIsometry_apply (lineIsometry.symm y) 0
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

end MathlibExt.Analysis.InnerProductSpace.LineIsometry
