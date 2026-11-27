/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluationOrd
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaces

open Polynomial

namespace AlgebraicCurve.PlaceEvaluationOrdTest

open AlgebraicCurve RationalFunctionField

-- `exactSource` consumer of `Place.ord_algebraMap` with the original binders.
example {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    v.ord (algebraMap K F c) = 0 :=
  v.ord_algebraMap c

-- Universe check: the base and function fields may live in different universes.
universe u w in
example {K : Type u} {F : Type w} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    v.ord (algebraMap K F c) = 0 :=
  v.ord_algebraMap c

section General

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

-- Constants evaluate to themselves.
example (hv : v.IsRational) (a : K) : v.evalAt hv (algebraMap K F a) = a :=
  v.evalAt_algebraMap hv a

-- The value is the one of the relational API.
example (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasValueAt f (v.evalAt hv f) :=
  v.hasValueAt_evalAt hv hf

-- Boundary: the zero constant has order zero by the convention `ord 0 = 0`.
example : v.ord (algebraMap K F 0) = 0 := v.ord_algebraMap 0

end General

section Concrete

variable {K : Type*} [Field K]

private theorem isRational_placeOfPoint (a : K) : (placeOfPoint K a).IsRational :=
  (Place.isRational_iff_deg_eq_one _).mpr (deg_placeOfPoint K a)

private theorem mem_placeOfPoint (a : K) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ (placeOfPoint K a).toValuationSubring :=
  algebraMap_mem_ofHeightOneSpectrum K _ q

-- At the place of `a`, a polynomial takes its value at `a`.
private theorem evalAt_placeOfPoint (a : K) (q : K[X]) :
    (placeOfPoint K a).evalAt (isRational_placeOfPoint a) (algebraMap K[X] (RatFunc K) q)
      = q.eval a := by
  apply (algebraMap K (placeOfPoint K a).ResidueField).injective
  rw [Place.algebraMap_evalAt _ _ (mem_placeOfPoint a q)]
  have key : residueOfHeightOneSpectrum K
        (heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)) q
      = residueOfHeightOneSpectrum K
        (heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)) (C (q.eval a)) := by
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ker_residueOfHeightOneSpectrum,
      heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton]
    exact X_sub_C_dvd_sub_C_eval
  rw [residueOfHeightOneSpectrum_apply, residueOfHeightOneSpectrum_apply] at key
  exact key.trans (congrArg (IsLocalRing.residue _)
    (Subtype.ext (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) _).symm))

-- Evaluation of `X ^ 2 - 1` at the place of `a`, through `evalAt_sub`, `evalAt_pow` and
-- `evalAt_algebraMap`, and directly.
example (a : K) :
    (placeOfPoint K a).evalAt (isRational_placeOfPoint a)
      (algebraMap K[X] (RatFunc K) X ^ 2 - algebraMap K (RatFunc K) 1) = a ^ 2 - 1 := by
  have hX := mem_placeOfPoint a X
  rw [Place.evalAt_sub _ _ (pow_mem hX 2) (Place.algebraMap_mem _ 1),
    Place.evalAt_pow _ _ hX, Place.evalAt_algebraMap, evalAt_placeOfPoint, eval_X]

example (a : K) :
    (placeOfPoint K a).evalAt (isRational_placeOfPoint a)
      (algebraMap K[X] (RatFunc K) (X ^ 2 - 1)) = a ^ 2 - 1 := by
  rw [evalAt_placeOfPoint]
  simp

-- `evalAt_prod`: the value of `(X - b) (X - c)` at `a` is `(a - b) (a - c)`.
example (a b c : K) :
    (placeOfPoint K a).evalAt (isRational_placeOfPoint a)
      (∏ i ∈ ({0, 1} : Finset (Fin 2)), algebraMap K[X] (RatFunc K) (X - C (![b, c] i)))
      = (a - b) * (a - c) := by
  rw [Place.evalAt_prod _ _ _ _ fun i _ => mem_placeOfPoint a _,
    Finset.prod_pair (by decide : (0 : Fin 2) ≠ 1), evalAt_placeOfPoint, evalAt_placeOfPoint]
  simp

-- `ord_eq_zero_of_evalAt_ne_zero`: `X - b` has order zero at the place of `a ≠ b`.
example (a b : K) (hab : a ≠ b) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C b)) = 0 :=
  Place.ord_eq_zero_of_evalAt_ne_zero _ (isRational_placeOfPoint a) (mem_placeOfPoint a _)
    (by rw [evalAt_placeOfPoint]; simpa [sub_eq_zero] using hab)

-- The nonzero-value hypothesis is needed: `X - a` has value `0` at the place of `a`, and its
-- order there is not zero.
example (a : K) :
    (placeOfPoint K a).evalAt (isRational_placeOfPoint a)
        (algebraMap K[X] (RatFunc K) (X - C a)) = 0 ∧
      (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) ≠ 0 := by
  refine ⟨by rw [evalAt_placeOfPoint]; simp, ?_⟩
  rw [placeOfPoint_eq_ofHeightOneSpectrum,
    Place.ord_ofHeightOneSpectrum_ne_zero_iff _ (X_sub_C_ne_zero a),
    heightOneSpectrumOfIrreducible_asIdeal]
  exact Ideal.mem_span_singleton_self _

end Concrete

end AlgebraicCurve.PlaceEvaluationOrdTest
