/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_RationalFunctionField_algebraMap_polynomial_mem_of_ne_placeInfty.lean`,
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_algebraMap_polynomial_mem_of_ne_placeInfty.lean`,
`P2M/Sol/S_AlgebraicCurve_residueTheorem_ratFunc_of_perfectField.lean`,
`P2M/Sol/S_ModularCurve_CharPModel_place_eq_of_ord_pos_of_derivative_evalEval_ne_zero.lean`,
`Theorems/Thm_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero.lean`,
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span.lean`,
`Theorems/Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.lean`,
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.lean`,
`Theorems/Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord.lean`,
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord.lean`,
`P2M/Sol/S_AlgebraicCurve_isCurveOver_ratFunc.lean`,
`P2M/Sol/S_AlgebraicCurve_instIsCurveOverRatFunc.lean`,
`Theorems/Thm_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors.lean`
and
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaces
import Mathlib.FieldTheory.RatFunc.Degree
import MathlibExt.AlgebraicGeometry.Curve.OrdEqNegLog
import MathlibExt.AlgebraicGeometry.Curve.PlacesOverDVR
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceClassification
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceInftyDeg
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceInftyOrd

/-!
# Principal divisors on the rational function field

Every nonzero `f : RatFunc K` has finitely many places of nonzero order, and its divisor has
degree zero. Every place of `RatFunc K` has a residue field of finite degree over `K`.

## Main statements

* `AlgebraicCurve.RationalFunctionField.finite_setOf_ord_ne_zero`
* `AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors`
* `AlgebraicCurve.RationalFunctionField.finite_residueField`
-/

@[expose] public section

noncomputable section

open Polynomial IsDedekindDomain WithZero

namespace AlgebraicCurve

namespace RationalFunctionField

variable {K : Type*} [Field K]

private theorem ord_algebraMap_const (v : Place K (RatFunc K)) (c : K) :
    v.ord (algebraMap K (RatFunc K) c) = 0 := by
  have h1 := v.ord_nonneg_of_mem (v.algebraMap_mem' c)
  have h2 := v.ord_nonneg_of_mem (v.algebraMap_mem' c⁻¹)
  rw [map_inv₀, v.ord_inv] at h2
  omega

private theorem algebraMap_mem_of_ne_placeInfty [DecidableEq (RatFunc K)]
    {v : Place K (RatFunc K)} (hv : v ≠ placeInfty K) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ v.toValuationSubring := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | h
  · exact algebraMap_mem_ofHeightOneSpectrum K w q
  · exact absurd h hv

private theorem finite_setOf_ord_algebraMap_ne_zero {q : K[X]} (hq : q ≠ 0) :
    {v : Place K (RatFunc K) | v.ord (algebraMap K[X] (RatFunc K) q) ≠ 0}.Finite := by
  classical
  refine ((Place.finite_setOf_forall_mem_and_ord_pos (K := K) (F := RatFunc K) hq).insert
    (placeInfty K)).subset fun v hv => ?_
  rw [Set.mem_insert_iff]
  by_cases hinf : v = placeInfty K
  · exact Or.inl hinf
  have hmem := algebraMap_mem_of_ne_placeInfty hinf
  exact Or.inr ⟨hmem, lt_of_le_of_ne (v.ord_nonneg_of_mem (hmem q)) (Ne.symm hv)⟩

/-- **Finitely many zeros and poles of a rational function.** A nonzero rational function has
nonzero order at only finitely many places. -/
theorem finite_setOf_ord_ne_zero {f : RatFunc K} (hf : f ≠ 0) :
    {v : Place K (RatFunc K) | v.ord f ≠ 0}.Finite := by
  classical
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := f.denom_ne_zero
  have hnum' := RatFunc.algebraMap_ne_zero hnum
  have hden' := RatFunc.algebraMap_ne_zero hden
  refine ((finite_setOf_ord_algebraMap_ne_zero hnum).union
    (finite_setOf_ord_algebraMap_ne_zero hden)).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
  apply hv
  have hfrac := RatFunc.num_div_denom f
  rw [← hfrac, div_eq_mul_inv, v.ord_mul hnum' (inv_ne_zero hden'), v.ord_inv, h.1, h.2,
    neg_zero, add_zero]

private theorem ord_finitePlace_self {p : K[X]} (hp : Irreducible p) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) = 1 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  set w := heightOneSpectrumOfIrreducible K hp
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    rw [w.valuation_of_algebraMap]
    exact w.intValuation_singleton hp0 (heightOneSpectrumOfIrreducible_asIdeal K hp)
  rw [finitePlace_def, (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K)
    w).ord_eq_neg_log_of_valuationSubring_eq (w.valuation (RatFunc K)) rfl hval
    (RatFunc.algebraMap_ne_zero hp0), hval, log_exp, neg_neg]

/-- The divisor of an irreducible polynomial `p`: its zero at the place of `p` and its pole of
order `natDegree p` at infinity. -/
private theorem ord_algebraMap_irreducible [DecidableEq (RatFunc K)] {p : K[X]}
    (hp : Irreducible p) (v : Place K (RatFunc K)) :
    (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single (placeInfty K) (-(p.natDegree : ℤ))) v
      = v.ord (algebraMap K[X] (RatFunc K) p) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [Finsupp.add_apply]
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · rw [Finsupp.single_eq_of_ne (placeInfty_ne_ofHeightOneSpectrum K w).symm, add_zero]
    by_cases hcase :
        Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w = finitePlace K hp
    · rw [hcase, Finsupp.single_eq_same, ord_finitePlace_self]
    · rw [Finsupp.single_eq_of_ne hcase]
      symm
      by_contra hne
      refine hcase ?_
      have hmem : p ∈ w.asIdeal :=
        (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hp0).mp hne
      have hspan : Ideal.span {p} = w.asIdeal :=
        (PrincipalIdealRing.isMaximal_of_irreducible hp).eq_of_le w.isPrime.ne_top
          ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
      have hwp : w = heightOneSpectrumOfIrreducible K hp :=
        HeightOneSpectrum.ext
          (hspan.symm.trans (heightOneSpectrumOfIrreducible_asIdeal K hp).symm)
      rw [hwp, finitePlace_def]
  · have hne : placeInfty K ≠ finitePlace K hp := placeInfty_ne_ofHeightOneSpectrum K _
    rw [Finsupp.single_eq_of_ne hne, zero_add, Finsupp.single_eq_same,
      ord_placeInfty (RatFunc.algebraMap_ne_zero hp0), RatFunc.intDegree_polynomial]

private theorem degree_single_add_single [DecidableEq (RatFunc K)] {p : K[X]}
    (hp : Irreducible p) :
    Divisor.degree (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single (placeInfty K) (-(p.natDegree : ℤ))) = 0 := by
  rw [map_add, Divisor.degree_single, Divisor.degree_single, deg_finitePlace, deg_placeInfty]
  push_cast
  ring

private theorem degree_eq_zero_of_forall_eq_ord_algebraMap (q : K[X]) :
    ∀ D : Divisor K (RatFunc K),
      (∀ v : Place K (RatFunc K), D v = v.ord (algebraMap K[X] (RatFunc K) q)) →
        Divisor.degree D = 0 := by
  classical
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  · intro D hD
    have hzero : D = 0 := by
      ext v
      simp [hD v]
    rw [hzero, map_zero]
  · intro x hx D hD
    obtain ⟨r, -, rfl⟩ := Polynomial.isUnit_iff.mp hx
    have hC : algebraMap K[X] (RatFunc K) (Polynomial.C r) = algebraMap K (RatFunc K) r := by
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    have hzero : D = 0 := by
      ext v
      rw [Finsupp.zero_apply, hD v, hC, ord_algebraMap_const]
    rw [hzero, map_zero]
  · intro a p ha hp ih D hD
    have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 := RatFunc.algebraMap_ne_zero hp.ne_zero
    have ha' : algebraMap K[X] (RatFunc K) a ≠ 0 := RatFunc.algebraMap_ne_zero ha
    set Dp : Divisor K (RatFunc K) :=
      Finsupp.single (finitePlace K hp.irreducible) (1 : ℤ)
        + Finsupp.single (placeInfty K) (-(p.natDegree : ℤ)) with hDp_def
    have hDa : ∀ v : Place K (RatFunc K),
        (D - Dp) v = v.ord (algebraMap K[X] (RatFunc K) a) := by
      intro v
      rw [Finsupp.sub_apply, hD v, hDp_def, ord_algebraMap_irreducible hp.irreducible v,
        map_mul, v.ord_mul hp' ha']
      ring
    have hsplit : D = Dp + (D - Dp) := by abel
    rw [hsplit, map_add, hDp_def, degree_single_add_single hp.irreducible, zero_add]
    exact ih (D - Dp) hDa

private theorem degree_eq_zero_of_forall_eq_ord {f : RatFunc K} (D : Divisor K (RatFunc K))
    (hD : ∀ v : Place K (RatFunc K), D v = v.ord f) : Divisor.degree D = 0 := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · have hzero : D = 0 := by
      ext v
      simp [hD v]
    rw [hzero, map_zero]
  have hdenF : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  set Dden : Divisor K (RatFunc K) :=
    Finsupp.ofSupportFinite
      (fun v : Place K (RatFunc K) => v.ord (algebraMap K[X] (RatFunc K) f.denom))
      (finite_setOf_ord_ne_zero hdenF) with hDden_def
  have hDden : ∀ v : Place K (RatFunc K),
      Dden v = v.ord (algebraMap K[X] (RatFunc K) f.denom) := fun v => rfl
  have hsplit : ∀ v : Place K (RatFunc K),
      (D + Dden) v = v.ord (algebraMap K[X] (RatFunc K) f.num) := by
    intro v
    rw [Finsupp.add_apply, hD v, hDden v]
    have hmul : f * algebraMap K[X] (RatFunc K) f.denom = algebraMap K[X] (RatFunc K) f.num :=
      ((div_eq_iff hdenF).mp f.num_div_denom).symm
    have h2 := v.ord_mul hf hdenF
    rw [hmul] at h2
    exact h2.symm
  have h1 := degree_eq_zero_of_forall_eq_ord_algebraMap f.num (D + Dden) hsplit
  have h2 := degree_eq_zero_of_forall_eq_ord_algebraMap f.denom Dden hDden
  rw [map_add, h2, add_zero] at h1
  exact h1

variable (K) in
/-- **Principal divisors on the rational function field have degree zero.** Every nonzero
rational function has a principal divisor of degree zero. -/
theorem hasPrincipalDivisors : HasPrincipalDivisors K (RatFunc K) :=
  ⟨fun f hf =>
    ⟨Finsupp.ofSupportFinite (fun v : Place K (RatFunc K) => v.ord f)
        (finite_setOf_ord_ne_zero hf),
      fun _ => rfl, degree_eq_zero_of_forall_eq_ord _ fun _ => rfl⟩⟩

/-- **Residue fields of the rational function field have finite degree over `K`.** Every place
of `RatFunc K` has a residue field of finite degree over `K`. -/
theorem finite_residueField (v : Place K (RatFunc K)) : Module.Finite K v.ResidueField := by
  classical
  have hpos : 0 < v.deg := by
    rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    · obtain ⟨p, hp, hw⟩ := exists_irreducible_span K w
      rw [deg_ofHeightOneSpectrum K hw]
      exact Irreducible.natDegree_pos hp
    · rw [deg_placeInfty]
      exact one_pos
  exact Module.finite_of_finrank_pos hpos

end RationalFunctionField

end AlgebraicCurve
