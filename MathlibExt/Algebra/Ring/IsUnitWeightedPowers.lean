/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Tactic.Ring

/-!
# The condition `v³ = v'²` under the weighted action of a unit

Let `R` be a commutative ring and `u ∈ R` a unit. The condition `v³ = v'²` on a pair
`(v, v') ∈ R²` is invariant under the weighted action `(v, v') ↦ (u² v, u³ v')`
(`IsUnit.pow_two_mul_cube_eq_pow_three_mul_sq_iff`).

## References

* B. Conrad, "Minimal models for elliptic curves", notes (version of 21 November 2015),
  <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>: proof of Corollary 2.9, p. 5.
-/

@[expose] public section

variable {R : Type*} [CommRing R]

/-- **The condition `v³ = v'²` under the weighted action of a unit.** Let `R` be a commutative
ring and `u ∈ R` a unit. Then for `v, v' ∈ R`, `(u² v)³ = (u³ v')²` if and only if `v³ = v'²`.

Source: B. Conrad, "Minimal models for elliptic curves", notes (version of 21 November 2015),
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, proof of Corollary 2.9, p. 5, where
the pair `(v, v')` of leading coefficients is well-defined up to `(v, v') ↦ (u² v, u³ v')` with
`u ∈ R^×` and the condition `v³ = v'²` is read off from it. -/
theorem IsUnit.pow_two_mul_cube_eq_pow_three_mul_sq_iff {u : R} (hu : IsUnit u) (v v' : R) :
    (u ^ 2 * v) ^ 3 = (u ^ 3 * v') ^ 2 ↔ v ^ 3 = v' ^ 2 := by
  have h₁ : (u ^ 2 * v) ^ 3 = u ^ 6 * v ^ 3 := by ring
  have h₂ : (u ^ 3 * v') ^ 2 = u ^ 6 * v' ^ 2 := by ring
  rw [h₁, h₂]
  exact (hu.pow 6).mul_right_inj
