/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.PositiveDefiniteKernel

open scoped RealInnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.PositiveDefiniteKernel

-- The linear kernel `k(x, y) = x y` on `ℝ` is positive definite, with feature map `id`.
example : IsPosDefKernel (fun x y : ℝ => x * y) :=
  isPosDefKernel_of_eq_inner (H := ℝ) id fun x y => by simp [mul_comm]

-- Hence it has a feature map into some real Hilbert space.
example : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
    (_ : CompleteSpace H) (φ : ℝ → H), ∀ x y : ℝ, x * y = ⟪φ x, φ y⟫ :=
  isPosDefKernel_iff_exists_featureMap.mp
    (isPosDefKernel_of_eq_inner (H := ℝ) id fun x y => by simp [mul_comm])

-- A positive-definite kernel is symmetric, read off the `2 × 2` kernel matrices.
example {X : Type*} {k : X → X → ℝ} (hk : IsPosDefKernel k) (x y : X) : k x y = k y x := by
  obtain ⟨H, _, _, _, φ, hφ⟩ := isPosDefKernel_iff_exists_featureMap.mp hk
  rw [hφ, hφ, real_inner_comm]

end MathlibExt.Analysis.InnerProductSpace.PositiveDefiniteKernel
