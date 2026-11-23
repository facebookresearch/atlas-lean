/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.HahnSeries.CoefficientDerivation
import Mathlib.Algebra.Polynomial.Derivation

open HahnSeries Polynomial

example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (d : Derivation R A A) (a : A) :
    coefficientDerivation d (single (-2 : ℤ) a) = single (-2 : ℤ) (d a) := by
  simp

example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (f : HahnSeries ℤ A) : coefficientDerivation (0 : Derivation R A A) f = 0 := by
  simp

-- A nonzero derivation, tested on a negative exponent and a polynomial coefficient.
example :
    coefficientDerivation (Polynomial.derivative' : Derivation ℚ (Polynomial ℚ) (Polynomial ℚ))
      (single (-2 : ℤ) (X ^ 2)) = single (-2 : ℤ) (2 * X) := by
  simp [Polynomial.derivative', Polynomial.derivative_X]

-- Natural exponents exercise the generalized exponent monoid.
example (d : Derivation ℚ (Polynomial ℚ) (Polynomial ℚ)) (a : Polynomial ℚ) :
    coefficientDerivation (Γ := ℕ) d (HahnSeries.C a) = HahnSeries.C (d a) := by
  simp

-- Leibniz is carried by the actual lifted `Derivation`, without a separate assumption.
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (d : Derivation R A A) (f g : HahnSeries ℤ A) :
    coefficientDerivation d (f * g) =
      f * coefficientDerivation d g + g * coefficientDerivation d f := by
  exact (coefficientDerivation d).leibniz f g

example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (d d' : Derivation R A A) (h : Function.Commute d d') :
    Function.Commute (coefficientDerivation (Γ := ℤ) d) (coefficientDerivation d') :=
  coefficientDerivation_commute h

#print axioms HahnSeries.coefficientDerivation
#print axioms HahnSeries.coefficientDerivation_single
#print axioms HahnSeries.coefficientDerivation_commute
