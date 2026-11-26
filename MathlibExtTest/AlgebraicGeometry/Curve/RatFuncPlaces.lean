/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceClassification
public import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceInftyDeg
public import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceInftyOrd

/-! # Tests for the finite and infinite places of the rational function field -/

@[expose] public section

namespace AlgebraicCurve.RationalFunctionField

open Polynomial

variable (K : Type*) [Field K]

-- Finite places: an irreducible polynomial gives a place of degree its degree.
example {p : K[X]} (hp : Irreducible p) : (finitePlace K hp).deg = p.natDegree :=
  deg_finitePlace K hp

-- Boundary: the place of a point is the finite place of `X - a`, of degree one.
example (a : K) : placeOfPoint K a = finitePlace K (irreducible_X_sub_C a) :=
  placeOfPoint_def K a

example (a : K) : (placeOfPoint K a).deg = 1 := deg_placeOfPoint K a

example {a b : K} (h : placeOfPoint K a = placeOfPoint K b) : a = b :=
  placeOfPoint_injective K h

-- Distinct primes of `K[X]` give distinct places.
example {w w' : IsDedekindDomain.HeightOneSpectrum K[X]}
    (h : Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w =
      Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w') :
    w = w' :=
  Place.ofHeightOneSpectrum_injective h

section Infinity

variable [DecidableEq (RatFunc K)]

-- The place at infinity has degree one and order `-intDegree`.
example : (placeInfty K).deg = 1 := deg_placeInfty K

example {f : RatFunc K} (hf : f ≠ 0) : (placeInfty K).ord f = -f.intDegree :=
  ord_placeInfty hf

-- `X` has a simple pole at infinity, `X⁻¹` a simple zero, and nonzero constants neither.
example : (placeInfty K).ord (RatFunc.X : RatFunc K) = -1 := by
  rw [ord_placeInfty RatFunc.X_ne_zero, RatFunc.intDegree_X]

example : (placeInfty K).ord (RatFunc.X : RatFunc K)⁻¹ = 1 := by
  rw [Place.ord_inv, ord_placeInfty RatFunc.X_ne_zero, RatFunc.intDegree_X, neg_neg]

example {a : K} (ha : a ≠ 0) : (placeInfty K).ord (RatFunc.C a) = 0 := by
  rw [ord_placeInfty (by simpa using ha), RatFunc.intDegree_C, neg_zero]

-- The place at infinity is not finite.
example (w : IsDedekindDomain.HeightOneSpectrum K[X]) :
    placeInfty K ≠ Place.ofHeightOneSpectrum w :=
  placeInfty_ne_ofHeightOneSpectrum K w

example (a : K) : placeOfPoint K a ≠ placeInfty K := placeOfPoint_ne_placeInfty K a

-- Classification: every place is finite or infinite.
example (v : Place K (RatFunc K)) :
    (∃ w : IsDedekindDomain.HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w) ∨
      v = placeInfty K :=
  eq_ofHeightOneSpectrum_or_eq_placeInfty v

-- Over an algebraically closed field the places are the points of `K` and `∞`.
example [IsAlgClosed K] (v : Place K (RatFunc K)) :
    (∃ a : K, v = placeOfPoint K a) ∨ v = placeInfty K :=
  eq_placeOfPoint_or_eq_placeInfty K v

example [IsAlgClosed K] (a : K) : placeEquivOption K (placeOfPoint K a) = some a :=
  placeEquivOption_placeOfPoint K a

example [IsAlgClosed K] : placeEquivOption K (placeInfty K) = none :=
  placeEquivOption_placeInfty K

example [IsAlgClosed K] : (placeEquivOption K).symm none = placeInfty K :=
  placeEquivOption_symm_none K

example [IsAlgClosed K] (v : Place K (RatFunc K)) :
    ofOption K (placeEquivOption K v) = v :=
  (placeEquivOption K).symm_apply_apply v

end Infinity

end AlgebraicCurve.RationalFunctionField
