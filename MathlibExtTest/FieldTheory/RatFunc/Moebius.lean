/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.RatFunc.Moebius

@[expose] public section

-- Consumer with the original binders.
private theorem exactSource {K : Type*} [Field K] (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    ∃ φ : RatFunc K ≃ₐ[K] RatFunc K,
      φ RatFunc.X = (RatFunc.C a * RatFunc.X + RatFunc.C b) /
        (RatFunc.C c * RatFunc.X + RatFunc.C d) :=
  RatFunc.exists_algEquiv_apply_X_eq_moebius a b c d hdet

-- The inversion `X ↦ -1 / X`.
example {K : Type*} [Field K] : ∃ φ : RatFunc K ≃ₐ[K] RatFunc K,
    φ RatFunc.X = (RatFunc.C 0 * RatFunc.X + RatFunc.C (-1)) /
      (RatFunc.C 1 * RatFunc.X + RatFunc.C 0) :=
  RatFunc.exists_algEquiv_apply_X_eq_moebius 0 (-1) 1 0 (by simp)

-- Boundary: for `a d - b c = 0` the target can be the constant `X / X = 1`, which no
-- automorphism hits since `X` is transcendental.
example {K : Type*} [Field K] (φ : RatFunc K ≃ₐ[K] RatFunc K) :
    φ RatFunc.X ≠ (RatFunc.C 1 * RatFunc.X + RatFunc.C 0) /
      (RatFunc.C 1 * RatFunc.X + RatFunc.C 0) := by
  intro h
  rw [div_self (by simpa using RatFunc.X_ne_zero), ← map_one φ] at h
  have h1 : (RatFunc.X : RatFunc K) = 1 := φ.injective h
  apply RatFunc.transcendental_X (K := K)
  rw [h1]
  exact isAlgebraic_one
