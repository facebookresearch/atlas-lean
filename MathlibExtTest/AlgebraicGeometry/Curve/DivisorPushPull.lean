/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.ExistsRestrict
public import MathlibExt.AlgebraicGeometry.Curve.FundamentalIdentity

/-! # Tests for restriction, pushforward and pullback of divisors along an extension -/

@[expose] public section

namespace AlgebraicCurve

section Degree

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

-- The degree of a single place, and the boundary cases of the zero divisor and coefficient.
example (v : Place K F) (n : ℤ) : Divisor.degree (Finsupp.single v n) = n * v.deg :=
  Divisor.degree_single v n

example : Divisor.degree (0 : Divisor K F) = 0 := map_zero _

example (v : Place K F) : Finsupp.single v (0 : ℤ) ∈ Divisor.degZero (K := K) (F := F) := by
  rw [Divisor.mem_degZero, Divisor.degree_single, zero_mul]

-- The principal divisor of `1` is zero.
example : (0 : Divisor K F) ∈ Divisor.principal (K := K) (F := F) :=
  (Divisor.principal (K := K) (F := F)).zero_mem

end Degree

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

section Integral

variable [Algebra.IsIntegral F F']

-- Restriction and pushforward of a single place.
example (w : Place K F') (n : ℤ) :
    Divisor.mapRestrict F (Finsupp.single w n) = Finsupp.single (w.restrict F) n :=
  Divisor.mapRestrict_single w n

example (w : Place K F') (n : ℤ) :
    Divisor.pushforward F (Finsupp.single w n) =
      Finsupp.single (w.restrict F) (n * w.inertiaDeg F) :=
  Divisor.pushforward_single w n

-- The pushforward of a single place has the degree of that place: `deg v * f(w | v) = deg w`.
example (w : Place K F') :
    Divisor.degree (Divisor.pushforward F (Finsupp.single w 1)) = w.deg := by
  rw [Divisor.degree_pushforward, Divisor.degree_single, one_mul]

-- The order of a function of `F` at `w` is `e(w | v)` times its order at `v = w|F`.
example (w : Place K F') (f : F) :
    w.ord (algebraMap F F' f) = w.ramificationIndex F * (w.restrict F).ord f :=
  w.ord_restrict f

example (w : Place K F') : 0 < w.ramificationIndex F := w.ramificationIndex_pos

-- Boundary: an element of the valuation ring of `w` that comes from `F` lies in the valuation
-- ring of the restriction.
example (w : Place K F') {f : F} (hf : algebraMap F F' f ∈ w.toValuationSubring) :
    f ∈ (w.restrict F).toValuationSubring :=
  w.mem_restrict_iff.mpr hf

variable [HasPrincipalDivisors K F']

-- The pullback of a single place is supported on the fiber, weighted by ramification indices.
example [DecidableEq (Place K F)] (v : Place K F) (n : ℤ) (w : Place K F') :
    Divisor.pullback F' (Finsupp.single v n) w =
      if w.restrict F = v then n * w.ramificationIndex F else 0 := by
  split_ifs with hw
  · exact Divisor.pullback_single_apply_of_restrict_eq hw n
  · exact Divisor.pullback_single_apply_of_restrict_ne hw n

example (w : Place K F') : w ∈ (w.restrict F).fiber F' := Place.restrict_mem_fiber w

-- Boundary: the zero coefficient pulls back to the zero divisor.
example (v : Place K F) : Divisor.pullback F' (Finsupp.single v (0 : ℤ)) = 0 := by
  rw [Finsupp.single_zero, map_zero]

-- Pullback of a principal divisor is principal.
example {D : Divisor K F} (hD : D.IsPrincipal) : (Divisor.pullback F' D).IsPrincipal :=
  Divisor.isPrincipal_pullback hD

end Integral

section Separable

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

-- The two descriptions of the places over `v` agree, and the fundamental identity holds for both.
example [HasPrincipalDivisors K F'] (v : Place K F) : v.fiber F' = v.fiberOver F' :=
  v.fiber_eq_fiberOver

example (v : Place K F) {w : Place K F'} : w ∈ v.fiberOver F' ↔ w.restrict F = v :=
  v.mem_fiberOver

-- The places over `v` correspond to the height-one primes of the integral closure.
example (v : Place K F) (w : {w : Place K F' // w.restrict F = v}) :
    (v.fiberEquiv F').symm (v.fiberEquiv F' w) = w :=
  (v.fiberEquiv F').symm_apply_apply w

example (v : Place K F) : (v.fiberOver F').card =
    (IsDedekindDomain.primesOverFinset (IsLocalRing.maximalIdeal v.toValuationSubring)
      (Place.integralClosureAt F' v)).card :=
  v.card_fiberOver_eq

example [HasPrincipalDivisors K F'] (v : Place K F) :
    ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) =
      (Module.finrank F F' : ℤ) :=
  v.sum_ramificationIndex_mul_inertiaDeg

example (v : Place K F) :
    ∑ w ∈ v.fiberOver F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) =
      (Module.finrank F F' : ℤ) :=
  v.sum_ramificationIndex_mul_inertiaDeg_fiberOver

-- Consumer: the fundamental identity gives `deg (pullback D) = [F' : F] deg D`.
example [HasPrincipalDivisors K F'] (D : Divisor K F) :
    Divisor.degree (Divisor.pullback F' D) = (Module.finrank F F' : ℤ) * Divisor.degree D := by
  have : SumRamificationInertia K F F' := ⟨Place.sum_ramificationIndex_mul_inertiaDeg⟩
  exact Divisor.degree_pullback D

-- Every place of `F` has a place of `F'` above it.
example (v : Place K F) : ∃ w : Place K F', w.restrict F = v :=
  Place.exists_restrict_eq (M := F') v

end Separable

end AlgebraicCurve
