/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Tactic.Ring

/-!
# Leading coefficients under a change of local parameter

Let `A` be a ring with a ring map `ε : A → R` (the restriction along a section) and let `K` be an
`A`-algebra (a ring of functions in which `x` and `y` live). If `t² x = a` and `t³ y = b` with
`a, b ∈ A`, so that `x = a / t² + ⋯` and `y = b / t³ + ⋯` have leading coefficients `v = ε a` and
`v' = ε b` along `ε`, then for another parameter `t' = c t` the same functions satisfy
`t'² x = c² a` and `t'³ y = c³ b`, with leading coefficients `ε(c)² v` and `ε(c)³ v'`
(`WeierstrassCurve.LocalParameter.leadingCoeff_mul_parameter`). For a unit `u = ε(c)`, the
condition `v³ = v'²` is unchanged under `(v, v') ↦ (u² v, u³ v')`
(`WeierstrassCurve.LocalParameter.cube_eq_sq_iff_of_isUnit`).

## References

* B. Conrad, "Minimal models for elliptic curves", notes (version of 21 November 2015),
  <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>: proof of Corollary 2.9, p. 5.
-/

@[expose] public section

namespace WeierstrassCurve.LocalParameter

variable {A K R : Type*} [CommRing A] [CommRing K] [Algebra A K] [CommRing R]

/-- **Leading coefficients under a change of local parameter.** Let `A` be a commutative ring,
`K` a commutative `A`-algebra and `ε : A →+* R` a ring map to a commutative ring `R`. Let
`t, c ∈ A` and `x, y ∈ K`, and suppose `t² x = a` and `t³ y = b` in `K` for some `a, b ∈ A`
(so `x = a / t² + ⋯` and `y = b / t³ + ⋯`, with leading coefficients `v = ε a` and `v' = ε b`
along `ε`). Then for the parameter `t' = c t`, `t'² x = c² a` and `t'³ y = c³ b`, and the new
leading coefficients are `ε (c² a) = ε(c)² v` and `ε (c³ b) = ε(c)³ v'`.

This is the computation in Conrad's proof, where `A` is a local ring of the smooth locus of an
abstract integral Weierstrass model along its identity section `ε`, `t` and `t' = c t` generate
the ideal of `ε` with `c` a unit, and `R` is a discrete valuation ring; none of these hypotheses is
needed for the identities, so they are dropped.

Source: B. Conrad, "Minimal models for elliptic curves", notes (version of 21 November 2015),
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, proof of Corollary 2.9, p. 5: "The
pair `(v, v')` is well-defined up to the transformation `(v, v') ↦ (u² v, u³ v')` for
`u ∈ R^×`, due to possible changes in the choice of `t`". -/
theorem leadingCoeff_mul_parameter (ε : A →+* R) {t c a b : A} {x y : K}
    (hx : algebraMap A K t ^ 2 * x = algebraMap A K a)
    (hy : algebraMap A K t ^ 3 * y = algebraMap A K b) :
    algebraMap A K (c * t) ^ 2 * x = algebraMap A K (c ^ 2 * a) ∧
      algebraMap A K (c * t) ^ 3 * y = algebraMap A K (c ^ 3 * b) ∧
      ε (c ^ 2 * a) = ε c ^ 2 * ε a ∧ ε (c ^ 3 * b) = ε c ^ 3 * ε b := by
  refine ⟨?_, ?_, by simp, by simp⟩
  · rw [map_mul, map_mul, map_pow, ← hx]
    ring
  · rw [map_mul, map_mul, map_pow, ← hy]
    ring

/-- **The condition `v³ = v'²` does not depend on the local parameter.** Let `R` be a commutative
ring and `u ∈ R` a unit. Then for `v, v' ∈ R`, `(u² v)³ = (u³ v')²` if and only if `v³ = v'²`.

Source: B. Conrad, "Minimal models for elliptic curves", notes (version of 21 November 2015),
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, proof of Corollary 2.9, p. 5: the
pair `(v, v')` is well-defined up to `(v, v') ↦ (u² v, u³ v')` with `u ∈ R^×`, and the condition
`v³ = v'²` is read off from it. -/
theorem cube_eq_sq_iff_of_isUnit {u : R} (hu : IsUnit u) (v v' : R) :
    (u ^ 2 * v) ^ 3 = (u ^ 3 * v') ^ 2 ↔ v ^ 3 = v' ^ 2 := by
  have h₁ : (u ^ 2 * v) ^ 3 = u ^ 6 * v ^ 3 := by ring
  have h₂ : (u ^ 3 * v') ^ 2 = u ^ 6 * v' ^ 2 := by ring
  rw [h₁, h₂]
  exact (hu.pow 6).mul_right_inj

end WeierstrassCurve.LocalParameter
