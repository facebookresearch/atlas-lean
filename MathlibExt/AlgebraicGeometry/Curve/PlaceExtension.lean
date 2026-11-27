/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files of the FLT project
(https://github.com/anthropics/fermats-last-theorem):
`Definitions/Def_AlgebraicCurve_DivisorPushPull.lean`;
`Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`;
`Theorems/Thm_AlgebraicCurve_N.lean` and `P2M/Sol/S_AlgebraicCurve_N.lean`
for each `N` in:
`Place_evalAt_algebraMap_eq_evalAt_restrict`;
`Place_inertiaDeg_eq_one_of_isRational`;
`Divisor_support_pushforward_subset`;
`Place_ramificationIndex_eq_ramificationIdx_fiberCenter`;
`Place_inertiaDeg_eq_inertiaDeg_fiberCenter`;
`Place_neg_log_valuation_fiberCenter_eq_ord`;
`Place_le_ord_iff_mem_pow_fiberCenter`;
`Place_count_normalizedFactors_span_singleton`;
`Place_exists_integralClosureAt_of_ord_fiber_nonneg`;
`Place_pairwiseDisjoint_fiber`;
`Divisor_support_pullback_subset`.
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

public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluation
public import MathlibExt.AlgebraicGeometry.Curve.PlacesOverDVR
import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluationLemmas

/-!
# Places above a place, and the pullback of divisors

For a finite separable extension `F' / F` of function fields over `K`, the places of `F'` above
a place `v` of `F` form the finite set `Place.fiberOver F' v` (`Curve/PlacesOverDVR`), and they
correspond to the height-one primes of the integral closure of the valuation ring of `v` in
`F'`. This file defines the pullback of divisors along `F' / F` through these fibres, reads
ramification indices, inertia degrees and orders of functions off the corresponding primes, and
relates evaluation at a place to evaluation at its restriction.
-/

@[expose] public section

noncomputable section

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

namespace Divisor

variable (F') in
/-- The pullback of divisors along a finite separable extension `F' / F`, weighting each place of
`F'` by its ramification index. It sums over `Place.fiberOver`, so unlike `Divisor.pullback`,
which sums over `Place.fiber`, it does not need principal divisors on `F'`; the two agree when
both are defined. -/
def pullbackOver : Divisor K F →+ Divisor K F' :=
  Finsupp.liftAddHom fun v =>
    { toFun n := ∑ w ∈ v.fiberOver F', Finsupp.single w (n * w.ramificationIndex F)
      map_zero' := by simp
      map_add' m n := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun w _ => by rw [add_mul, Finsupp.single_add] }

theorem pullbackOver_single (v : Place K F) (n : ℤ) :
    pullbackOver F' (Finsupp.single v n)
      = ∑ w ∈ v.fiberOver F', Finsupp.single w (n * w.ramificationIndex F) :=
  Finsupp.liftAddHom_apply_single _ _ _

private theorem pullbackOver_single_apply_of_restrict_eq {v : Place K F} {w : Place K F'}
    (hw : w.restrict F = v) (n : ℤ) :
    pullbackOver F' (Finsupp.single v n) w = n * w.ramificationIndex F := by
  rw [pullbackOver_single, Finset.sum_apply']
  trans (Finsupp.single w (n * (w.ramificationIndex F : ℤ))) w
  · refine Finset.sum_eq_single_of_mem w ((Place.mem_fiberOver v).mpr hw) ?_
    intro b _ hb
    exact Finsupp.single_eq_of_ne' hb
  · exact Finsupp.single_eq_same

private theorem pullbackOver_single_apply_of_restrict_ne {v : Place K F} {w : Place K F'}
    (hw : w.restrict F ≠ v) (n : ℤ) :
    pullbackOver F' (Finsupp.single v n) w = 0 := by
  rw [pullbackOver_single, Finset.sum_apply']
  exact Finset.sum_eq_zero fun b hb =>
    Finsupp.single_eq_of_ne fun h => hw (h ▸ (Place.mem_fiberOver v).mp hb)

theorem pullbackOver_apply (D : Divisor K F) (w : Place K F') :
    pullbackOver F' D w = w.ramificationIndex F * D (w.restrict F) := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
    rw [map_add, Finsupp.add_apply, ih, Finsupp.add_apply, mul_add]
    congr 1
    by_cases hw : w.restrict F = v
    · subst hw
      rw [pullbackOver_single_apply_of_restrict_eq rfl, Finsupp.single_eq_same, mul_comm]
    · rw [pullbackOver_single_apply_of_restrict_ne hw,
        Finsupp.single_eq_of_ne hw, mul_zero]

theorem restrict_mem_support_of_mem_support_pullbackOver {D : Divisor K F} {w : Place K F'}
    (hw : w ∈ (pullbackOver F' D).support) : w.restrict F ∈ D.support := by
  rw [Finsupp.mem_support_iff] at hw ⊢
  intro h
  exact hw (by rw [pullbackOver_apply, h, mul_zero])

theorem pullbackOver_apply_eq_ord {f : F} {D : Divisor K F}
    (hD : ∀ v : Place K F, D v = v.ord f) (w : Place K F') :
    pullbackOver F' D w = w.ord (algebraMap F F' f) := by
  rw [pullbackOver_apply, hD, ← Place.ord_restrict]

theorem pullback_eq_pullbackOver [HasPrincipalDivisors K F'] (D : Divisor K F) :
    pullback F' D = pullbackOver F' D :=
  Finsupp.ext fun w => by rw [pullback_apply, pullbackOver_apply]

theorem support_pullbackOver_subset [DecidableEq (Place K F')] (E : Divisor K F) :
    (pullbackOver F' E).support ⊆ E.support.biUnion fun v => v.fiberOver F' := fun w hw =>
  Finset.mem_biUnion.mpr ⟨w.restrict F, restrict_mem_support_of_mem_support_pullbackOver hw,
    Place.restrict_mem_fiberOver w⟩

end Divisor

end AlgebraicCurve

section

open IsLocalRing AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.evalAt_algebraMap_eq_evalAt_restrict {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] (w : Place K F') (hw : w.IsRational)
    (hv : (w.restrict F).IsRational) {g : F} (hg : g ∈ (w.restrict F).toValuationSubring) :
    w.evalAt hw (algebraMap F F' g) = (w.restrict F).evalAt hv g := by
  have hg' : algebraMap F F' g ∈ w.toValuationSubring := ValuationSubring.mem_comap.mp hg
  have h2 : residue w.toValuationSubring (⟨algebraMap F F' g, hg'⟩ : w.toValuationSubring)
      = algebraMap K w.ResidueField ((w.restrict F).evalAt hv g) := by
    have h3 : (⟨algebraMap F F' g, hg'⟩ : w.toValuationSubring)
        = restrictInclusion F w ⟨g, hg⟩ := rfl
    rw [h3, ← restrictResidueMap_residue, ((w.restrict F).algebraMap_evalAt hv hg).symm]
    change restrictResidueMap F w
        (residue _ (algebraMap K (w.restrict F).toValuationSubring ((w.restrict F).evalAt hv g)))
      = residue _ (algebraMap K w.toValuationSubring ((w.restrict F).evalAt hv g))
    rw [restrictResidueMap_residue]
    refine congrArg _ (Subtype.ext ?_)
    change algebraMap F F' (algebraMap K F ((w.restrict F).evalAt hv g))
        = algebraMap K F' ((w.restrict F).evalAt hv g)
    rw [← IsScalarTower.algebraMap_apply]
  rw [w.evalAt_of_mem hw hg', h2, w.residueInv_algebraMap hw]
end

open AlgebraicCurve AlgebraicCurve.Divisor

theorem AlgebraicCurve.Place.inertiaDeg_eq_one_of_isRational {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] (w : Place K F') (hw : w.IsRational) (hv : (w.restrict F).IsRational)
    : w.inertiaDeg F = 1 := by
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [(AlgebraicCurve.Place.isRational_iff_deg_eq_one _).1 hv,
    (AlgebraicCurve.Place.isRational_iff_deg_eq_one _).1 hw, one_mul] at h
  exact h

theorem AlgebraicCurve.Divisor.support_pushforward_subset {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] [DecidableEq (Place K F)] (D : Divisor K F') :
    (Divisor.pushforward F D).support ⊆ D.support.image (fun w => w.restrict F) := by
  classical
  intro v hv
  rw [Finsupp.mem_support_iff, pushforward_apply] at hv
  obtain ⟨w, hw, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  refine Finset.mem_image.mpr ⟨w, hw, ?_⟩
  by_contra h
  exact hne (ite_eq_right h)

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid AlgebraicCurve.Place

theorem AlgebraicCurve.Place.neg_log_valuation_fiberCenter_eq_ord {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} {w : Place K F'}
    (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) : -log ((fiberCenter F' v hw).valuation F' x) =
    w.ord x := by
  refine AlgebraicCurve.Place.eq_ord_of_addHom_of_nonneg_iff w
    (fun y => -log ((fiberCenter F' v hw).valuation F' y)) ?_ ?_ ?_ hx
  · intro a b ha hb
    rw [map_mul, log_mul ((Valuation.ne_zero_iff _).mpr ha) ((Valuation.ne_zero_iff _).mpr hb)]
    ring
  · obtain ⟨t, ht⟩ := (fiberCenter F' v hw).valuation_exists_uniformizer F'
    refine ⟨t, ?_, ?_⟩
    · intro h
      rw [h, map_zero] at ht
      exact exp_ne_zero ht.symm
    · show -log ((fiberCenter F' v hw).valuation F' t) = 1
      rw [ht, log_exp]
      ring
  · intro y hy
    have hy0 : (fiberCenter F' v hw).valuation F' y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    change 0 ≤ -log ((fiberCenter F' v hw).valuation F' y) ↔ y ∈ w.toValuationSubring
    have hmem : y ∈ w.toValuationSubring ↔ (fiberCenter F' v hw).valuation F' y ≤ 1 := by
      rw [toValuationSubring_eq_of_restrict_eq hw,
        HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact Iff.rfl
    rw [hmem]
    constructor
    · intro h
      calc (fiberCenter F' v hw).valuation F' y
          = exp (log ((fiberCenter F' v hw).valuation F' y)) := (exp_log hy0).symm
        _ ≤ exp 0 := by rw [exp_le_exp]; omega
        _ = 1 := exp_zero
    · intro h
      have h1 : exp (log ((fiberCenter F' v hw).valuation F' y)) ≤ exp 0 := by
        rw [exp_log hy0, exp_zero]
        exact h
      rw [exp_le_exp] at h1
      omega

theorem AlgebraicCurve.Place.le_ord_iff_mem_pow_fiberCenter {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} {w : Place K F'}
    (hw : w.restrict F = v) {c : integralClosureAt F' v} (hc : c ≠ 0) (n : ℕ) : (n : ℤ) ≤ w.ord
    (algebraMap (integralClosureAt F' v) F' c) ↔ c ∈ (fiberCenter F' v hw).asIdeal ^ n := by
  have hcF : algebraMap (integralClosureAt F' v) F' c ≠ 0 := by
    simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hc
  rw [← AlgebraicCurve.Place.neg_log_valuation_fiberCenter_eq_ord hw hcF,
    HeightOneSpectrum.valuation_of_algebraMap,
    ← HeightOneSpectrum.intValuation_le_pow_iff_mem]
  have h0 : (fiberCenter F' v hw).intValuation c ≠ 0 :=
    HeightOneSpectrum.intValuation_ne_zero _ c hc
  constructor
  · intro h
    calc (fiberCenter F' v hw).intValuation c
        = exp (log ((fiberCenter F' v hw).intValuation c)) := (exp_log h0).symm
      _ ≤ exp (-(n : ℤ)) := by rw [exp_le_exp]; omega
  · intro h
    have h1 : exp (log ((fiberCenter F' v hw).intValuation c)) ≤ exp (-(n : ℤ)) := by
      rw [exp_log h0]
      exact h
    rw [exp_le_exp] at h1
    omega

theorem AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter {K F F' : Type*}
    [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F)
    {w : Place K F'} (hw : w.restrict F = v) : w.ramificationIndex F =
    (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
    (Place.fiberCenter F' v hw).asIdeal := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπC : algebraMap v.toValuationSubring (integralClosureAt F' v) π ≠ 0 :=
    algebraMap_integralClosureAt_ne_zero hπ0
  have hmap : (IsLocalRing.maximalIdeal v.toValuationSubring).map
      (algebraMap v.toValuationSubring (integralClosureAt F' v))
        = Ideal.span {algebraMap v.toValuationSubring (integralClosureAt F' v) π} := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hord : w.ord (algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) π))
        = w.ramificationIndex F := by
    rw [ord_algebraMap_integralClosureAt hw, ValuationSubring.algebraMap_apply,
      v.ord_coe_irreducible hπ, mul_one]
  refine (Ideal.ramificationIdx'_spec ?_ ?_).symm
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      ← Place.le_ord_iff_mem_pow_fiberCenter hw hπC, hord]
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      ← Place.le_ord_iff_mem_pow_fiberCenter hw hπC, hord]
    have : 0 < w.ramificationIndex F := w.ramificationIndex_pos
    push_cast
    omega

namespace AlgebraicCurve.Place

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

section ResidueDictionary

variable {v : Place K F} {w : Place K F'}

def toValuationSubringOfRestrictEq (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.toValuationSubring :=
  (algebraMap (integralClosureAt F' v) F').codRestrict
    w.toValuationSubring.toSubring (forall_mem_of_restrict_eq hw)

def residueOfCenter (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.ResidueField :=
  (IsLocalRing.residue w.toValuationSubring).comp (toValuationSubringOfRestrictEq hw)

omit [FiniteDimensional F F'] in
theorem residueOfCenter_apply (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    residueOfCenter hw c = IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw c) := rfl

theorem ker_residueOfCenter (hw : w.restrict F = v) :
    RingHom.ker (residueOfCenter hw) = (fiberCenter F' v hw).asIdeal := by
  ext c
  rw [RingHom.mem_ker, residueOfCenter_apply, IsLocalRing.residue_eq_zero_iff]
  exact Iff.rfl

theorem surjective_residueOfCenter (hw : w.restrict F = v) :
    Function.Surjective (residueOfCenter hw) := by
  classical
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hx : (x : F') ∈ HeightOneSpectrum.valuationSubringAtPrime F' (fiberCenter F' v hw) := by
    rw [← toValuationSubring_eq_of_restrict_eq hw]
    exact x.2
  obtain ⟨a, s, hs, hxas⟩ := hx
  have hsP : s ∉ (fiberCenter F' v hw).asIdeal := hs
  have hs0 : s ≠ 0 := fun h => hsP (h ▸ (fiberCenter F' v hw).asIdeal.zero_mem)
  have hsF : algebraMap (integralClosureAt F' v) F' s ≠ 0 := by
    simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hs0
  have hsord : w.ord (algebraMap (integralClosureAt F' v) F' s) = 0 := by
    have h1 : ¬ 0 < w.ord (algebraMap (integralClosureAt F' v) F' s) := by
      rw [← mem_fiberCenter_iff_ord_pos hw hs0]
      exact hsP
    have h2 : 0 ≤ w.ord (algebraMap (integralClosureAt F' v) F' s) :=
      w.ord_nonneg_of_mem (forall_mem_of_restrict_eq hw s)
    omega
  have hmax : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  obtain ⟨t, i, hi, hti⟩ := hmax.exists_inv hsP
  have hst : s * t - 1 ∈ (fiberCenter F' v hw).asIdeal := by
    have h1 : s * t - 1 = -i := by linear_combination hti
    rw [h1]
    exact neg_mem hi
  refine ⟨a * t, ?_⟩
  rw [residueOfCenter_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hcoe : ((toValuationSubringOfRestrictEq hw (a * t) - x : w.toValuationSubring) : F')
      = algebraMap (integralClosureAt F' v) F' (a * t) - (x : F') := rfl
  rcases eq_or_ne (toValuationSubringOfRestrictEq hw (a * t) - x) 0 with hzero | hne
  · rw [hzero]
    exact (IsLocalRing.maximalIdeal w.toValuationSubring).zero_mem
  have hcoene : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F') ≠ 0 := by
    intro h
    exact hne (by rwa [← hcoe, ZeroMemClass.coe_eq_zero] at h)
  have hfactor : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F')
      = algebraMap (integralClosureAt F' v) F' (a * t * s - a)
          * (algebraMap (integralClosureAt F' v) F' s)⁻¹ := by
    rw [hxas, map_sub, map_mul (algebraMap (integralClosureAt F' v) F') (a * t) s,
      sub_mul, mul_assoc, mul_inv_cancel₀ hsF, mul_one]
  have hdiffC : a * t * s - a ≠ 0 := by
    intro h
    apply hcoene
    rw [hfactor, h, map_zero, zero_mul]
  have hdiffP : a * t * s - a ∈ (fiberCenter F' v hw).asIdeal := by
    have h1 : a * t * s - a = a * (s * t - 1) := by ring
    rw [h1]
    exact Ideal.mul_mem_left _ _ hst
  have hmem' : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F')
      ∈ w.toValuationSubring := by
    rw [← hcoe]
    exact Subtype.coe_prop _
  rw [show (toValuationSubringOfRestrictEq hw (a * t) - x)
      = (⟨_, hmem'⟩ : w.toValuationSubring) from Subtype.ext hcoe,
    w.mem_maximalIdeal_iff_ord_pos hcoene hmem']
  rw [hfactor, w.ord_mul (by
      simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hdiffC)
    (inv_ne_zero hsF), w.ord_inv, hsord, neg_zero, add_zero]
  exact (mem_fiberCenter_iff_ord_pos hw hdiffC).mp hdiffP

def residueFieldEquivQuotientCenter (hw : w.restrict F = v) :
    integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal ≃+* w.ResidueField :=
  (Ideal.quotEquivOfEq (ker_residueOfCenter hw).symm).trans
    ((residueOfCenter hw).quotientKerEquivOfSurjective (surjective_residueOfCenter hw))

def placeCongrEquiv {u u' : Place K F} (h : u = u') :
    u.toValuationSubring ≃+* u'.toValuationSubring where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun x := ⟨x.1, h.symm ▸ x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def restrictResidueFieldEquiv (hw : w.restrict F = v) :
    (w.restrict F).ResidueField ≃+* IsLocalRing.ResidueField v.toValuationSubring :=
  IsLocalRing.ResidueField.mapEquiv (placeCongrEquiv hw)

end ResidueDictionary

theorem inertiaDeg_eq_inertiaDeg_fiberCenter (v : Place K F) {w : Place K F'}
    (hw : w.restrict F = v) :
    w.inertiaDeg F = (fiberCenter F' v hw).asIdeal.inertiaDeg v.toValuationSubring := by
  have := fiberCenter_liesOver hw
  have : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal v.toValuationSubring)]
  change Module.finrank (w.restrict F).ResidueField w.ResidueField = _
  refine Algebra.finrank_eq_of_equiv_equiv (restrictResidueFieldEquiv hw)
    (residueFieldEquivQuotientCenter hw).symm ?_
  ext a
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]
  apply (residueFieldEquivQuotientCenter hw).injective
  rw [RingEquiv.apply_symm_apply]
  change IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw
        (algebraMap v.toValuationSubring (integralClosureAt F' v) (placeCongrEquiv hw a)))
    = IsLocalRing.residue w.toValuationSubring (restrictInclusion F w a)
  refine congrArg _ (Subtype.ext ?_)
  change algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) (placeCongrEquiv hw a))
    = algebraMap F F' (a : F)
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply v.toValuationSubring F F']
  rfl

end AlgebraicCurve.Place

theorem AlgebraicCurve.Place.count_normalizedFactors_span_singleton {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} {w : Place K F'}
    (hw : w.restrict F = v) {c : integralClosureAt F' v} (hc : c ≠ 0) :
    (normalizedFactors (Ideal.span {c})).count (fiberCenter F' v hw).asIdeal =
    (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat := by
  have : (fiberCenter F' v hw).asIdeal.IsPrime := (fiberCenter F' v hw).isPrime
  have hord0 : 0 ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) :=
    w.ord_nonneg_of_mem (forall_mem_of_restrict_eq hw c)
  refine Ideal.count_normalizedFactors_eq (p := (fiberCenter F' v hw).asIdeal)
    (x := Ideal.span {c})
    (n := (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) ?_ ?_
  · rw [Ideal.span_singleton_le_iff_mem, ← AlgebraicCurve.Place.le_ord_iff_mem_pow_fiberCenter hw
    hc]
    omega
  · rw [Ideal.span_singleton_le_iff_mem, ← AlgebraicCurve.Place.le_ord_iff_mem_pow_fiberCenter hw
    hc]
    push_cast
    omega

theorem AlgebraicCurve.Place.exists_integralClosureAt_of_ord_fiber_nonneg {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F}
    {f : F'} (hf : f ≠ 0) (hord : ∀ w ∈ v.fiberOver F', 0 ≤ w.ord f) : ∃ c : integralClosureAt F' v,
    algebraMap (integralClosureAt F' v) F' c = f := by
  classical
  obtain ⟨⟨c₀, s₀⟩, hcs⟩ := IsLocalization.surj
    (nonZeroDivisors (integralClosureAt F' v)) f
  have hs0 : (s₀ : integralClosureAt F' v) ≠ 0 := nonZeroDivisors.coe_ne_zero s₀
  have hsF : algebraMap (integralClosureAt F' v) F' (s₀ : integralClosureAt F' v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mpr hs0
  have hcF : algebraMap (integralClosureAt F' v) F' c₀ ≠ 0 := by
    rw [← hcs]; exact mul_ne_zero hf hsF
  have hc0 : c₀ ≠ 0 := fun h => hcF (by rw [h, map_zero])
  have hdom : ∀ (w : Place K F') (hw : w.restrict F = v),
      w.ord (algebraMap (integralClosureAt F' v) F' (s₀ : integralClosureAt F' v))
        ≤ w.ord (algebraMap (integralClosureAt F' v) F' c₀) := by
    intro w hw
    have h1 : w.ord (algebraMap (integralClosureAt F' v) F' c₀)
        = w.ord f + w.ord (algebraMap (integralClosureAt F' v) F' (s₀ :
            integralClosureAt F' v)) := by
      rw [← hcs]; exact w.ord_mul hf hsF
    have h2 := hord w ((mem_fiberOver v).mpr hw)
    omega
  have hle : Ideal.span {c₀} ≤ Ideal.span {(s₀ : integralClosureAt F' v)} := by
    have hspan_c : (Ideal.span {c₀} : Ideal (integralClosureAt F' v)) ≠ ⊥ := fun h =>
      hc0 (Ideal.span_singleton_eq_bot.mp h)
    have hspan_s : (Ideal.span {(s₀ : integralClosureAt F' v)} :
        Ideal (integralClosureAt F' v)) ≠ ⊥ := fun h => hs0 (Ideal.span_singleton_eq_bot.mp h)
    rw [← Ideal.dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors hspan_s hspan_c,
      Multiset.le_iff_count]
    intro P
    by_cases hP : P ∈ normalizedFactors
      (Ideal.span {(s₀ : integralClosureAt F' v)} : Ideal (integralClosureAt F' v))
    · have hPprime : Prime P := prime_of_normalized_factor P hP
      have : P.IsPrime := Ideal.isPrime_of_prime hPprime
      have hres := restrict_placeOfPrime
        (⟨P, inferInstance, hPprime.ne_zero⟩ : HeightOneSpectrum (integralClosureAt F' v))
      have hPeq : (fiberCenter F' v hres).asIdeal = P := congrArg HeightOneSpectrum.asIdeal
        (fiberCenter_placeOfPrime
          (⟨P, inferInstance, hPprime.ne_zero⟩ : HeightOneSpectrum (integralClosureAt F' v)))
      rw [← hPeq, AlgebraicCurve.Place.count_normalizedFactors_span_singleton hres hs0,
        AlgebraicCurve.Place.count_normalizedFactors_span_singleton hres hc0]
      exact Int.toNat_le_toNat (hdom _ hres)
    · rw [Multiset.count_eq_zero_of_notMem hP]
      exact Nat.zero_le _
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (hle (Ideal.mem_span_singleton_self c₀))
  refine ⟨d, ?_⟩
  have hmapped := congrArg (algebraMap (integralClosureAt F' v) F') hd
  rw [map_mul] at hmapped
  refine mul_left_cancel₀ hsF ?_
  rw [← hmapped, ← hcs]
  ring

theorem AlgebraicCurve.Place.pairwiseDisjoint_fiber {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] (s : Finset (Place K F)) : Set.PairwiseDisjoint
    (s : Set (Place K F)) (fun v : Place K F => v.fiberOver F') := by
  intro v₁ _ v₂ _ hne
  refine Finset.disjoint_left.mpr fun w hw₁ hw₂ => ?_
  exact hne (((mem_fiberOver v₁).mp hw₁).symm.trans ((mem_fiberOver v₂).mp hw₂))
