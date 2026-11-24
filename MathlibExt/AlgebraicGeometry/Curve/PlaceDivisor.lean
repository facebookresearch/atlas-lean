/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files of the FLT project
(https://github.com/anthropics/fermats-last-theorem):
`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`;
`Definitions/Def_AlgebraicCurve_PlaceEvaluation.lean`;
`Definitions/Def_AlgebraicCurve_RatFuncPlaceInfty.lean`;
`Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean`;
`Theorems/Thm_AlgebraicCurve_N.lean` and `P2M/Sol/S_AlgebraicCurve_N.lean`
for each `N` in:
`Divisor_evalFun_add`;
`Place_evalAt_ne_zero`;
`Place_isRational_iff_deg_eq_one`;
`Place_evalAt_mul`;
`Divisor_evalFun_mul`;
`Place_eq_ord_of_addHom_of_nonneg_iff`;
`Divisor_evalFun_single_sub_single`;
`Place_evalAt_inv`;
`Place_evalAt_zpow`;
`Divisor_evalFun_zpow_left`;
`Divisor_evalFun_zsmul`;
`Place_adicValuation_isRankOneDiscrete`;
`Place_adicValuation_isTrivialOn`;
`Place_evalAt_algebraMap`;
`Place_evalAt_congr`;
`Place_ord_algebraMap`;
`Place_ord_eq_neg_log_of_valuationSubring_eq`;
`Theorems/Thm_N.lean` and `P2M/Sol/S_N.lean` for each `N` in:
`Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap`;
`Algebra_norm_of_subsingleton`;
`Algebra_norm_prod`.
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

public import Mathlib.FieldTheory.RatFunc.Valuation
public import MathlibExt.AlgebraicGeometry.Curve.Place
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Divisors, residue fields and evaluation at places of a function field

For a field extension `F / K`, this file extends `AlgebraicCurve.Place` with the residue field
and degree of a place, divisors (finitely supported `ℤ`-valued functions on places) and their
degree, the class `AlgebraicCurve.HasPrincipalDivisors` saying that principal divisors exist
and have degree zero, evaluation `Place.evalAt` of functions at rational places, the
multiplicative evaluation `Divisor.evalFun f D = ∏ v, f(v) ^ D v`, and the statement
`AlgebraicCurve.WeilReciprocity K F`. It also constructs the places of the rational function
field `RatFunc K`: the finite places attached to irreducible polynomials and the place at
infinity.
-/

@[expose] public section

noncomputable section

section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F} (v : Place K F)

/-- The residue field of a place. -/
abbrev ResidueField : Type _ := IsLocalRing.ResidueField v.toValuationSubring

/-- The degree of a place: the dimension of its residue field over `K`. -/
def deg : ℕ := Module.finrank K v.ResidueField

end Place

/-- A divisor on `F / K`: a finitely supported integer-valued function on places. -/
abbrev Divisor : Type _ := Place K F →₀ ℤ

namespace Divisor

variable {K F}

/-- The degree of a divisor, `∑ v, D v * deg v`. -/
def degree : Divisor K F →+ ℤ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulRight (v.deg : ℤ)

@[simp]
theorem degree_single (v : Place K F) (n : ℤ) :
    degree (Finsupp.single v n) = n * v.deg := by
  simp [degree]

end Divisor

/-- Every nonzero element of `F` has a principal divisor, and it has degree zero. -/
class HasPrincipalDivisors : Prop where
  exists_divisor : ∀ f : F, f ≠ 0 → ∃ D : Divisor K F,
    (∀ v : Place K F, D v = v.ord f) ∧ Divisor.degree D = 0

namespace Place

variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

open IsDedekindDomain.HeightOneSpectrum in
/-- The valuation ring of a height-one prime of a Dedekind domain is a PID. -/
theorem isPrincipalIdealRing_valuationSubring (w : HeightOneSpectrum R) :
    IsPrincipalIdealRing ((w.valuation F).valuationSubring) := by
  rw [show (w.valuation F).valuationSubring = valuationSubringAtPrime F w from
    (valuationSubringAtPrime_eq_valuationSubring (K := F) w).symm]
  infer_instance

open IsDedekindDomain.HeightOneSpectrum in
/-- The place of `F` attached to a height-one prime of a Dedekind domain with fraction
field `F`. -/
def ofHeightOneSpectrum [Algebra K R] [IsScalarTower K R F] (w : HeightOneSpectrum R) :
    Place K F where
  toValuationSubring := (w.valuation F).valuationSubring
  algebraMap_mem' := fun a => by
    rw [Valuation.mem_valuationSubring_iff, IsScalarTower.algebraMap_apply K R F]
    exact w.valuation_le_one (algebraMap K R a)
  ne_top' := by
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' := isPrincipalIdealRing_valuationSubring w

@[simp]
theorem ofHeightOneSpectrum_toValuationSubring [Algebra K R] [IsScalarTower K R F]
    (w : HeightOneSpectrum R) :
    (ofHeightOneSpectrum (K := K) w).toValuationSubring = (w.valuation F).valuationSubring :=
  rfl

end Place

end AlgebraicCurve

end

section

section

open IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

/-- A place is rational if its residue field is `K`. -/
def IsRational : Prop := Function.Surjective (algebraMap K v.ResidueField)

theorem algebraMap_residueField_injective :
    Function.Injective (algebraMap K v.ResidueField) :=
  (algebraMap K v.ResidueField).injective

/-- A left inverse of `K → v.ResidueField`; an inverse when `v` is rational. -/
def residueInv : v.ResidueField → K :=
  Function.invFun (algebraMap K v.ResidueField)

theorem algebraMap_residueInv (hv : v.IsRational) (x : v.ResidueField) :
    algebraMap K v.ResidueField (v.residueInv x) = x :=
  Function.invFun_eq (hv x)

theorem residueInv_algebraMap (a : K) : v.residueInv (algebraMap K v.ResidueField a) = a :=
  Function.leftInverse_invFun v.algebraMap_residueField_injective a

open Classical in

/-- The value in `K` of `f` at a place: its residue when `f` is integral at `v`, read back
in `K`, and `0` otherwise. -/
def evalAt (f : F) : K :=
  if hf : f ∈ v.toValuationSubring then
    v.residueInv (residue v.toValuationSubring ⟨f, hf⟩)
  else 0

theorem evalAt_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = v.residueInv (residue v.toValuationSubring ⟨f, hf⟩) :=
  dif_pos hf

theorem algebraMap_evalAt (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    algebraMap K v.ResidueField (v.evalAt f)
      = residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [v.evalAt_of_mem hf]
  exact v.algebraMap_residueInv hv _

@[simp]
theorem evalAt_one : v.evalAt (1 : F) = 1 := by
  rw [v.evalAt_of_mem (one_mem _)]
  have h1 : (⟨(1 : F), one_mem _⟩ : v.toValuationSubring) = 1 := rfl
  rw [h1, map_one, ← map_one (algebraMap K v.ResidueField), v.residueInv_algebraMap]

end Place

namespace Divisor

/-- Evaluation of `f` on a divisor: `∏ v, f(v) ^ D v`. -/
def evalFun (f : F) (D : Divisor K F) : K :=
  D.prod fun v n => v.evalAt f ^ n

theorem evalFun_def (f : F) (D : Divisor K F) :
    evalFun f D = ∏ v ∈ D.support, v.evalAt f ^ D v := rfl

@[simp]
theorem evalFun_zero (f : F) : evalFun f (0 : Divisor K F) = 1 :=
  Finsupp.prod_zero_index

theorem evalFun_single (f : F) (v : Place K F) (n : ℤ) :
    evalFun f (Finsupp.single v n) = v.evalAt f ^ n :=
  Finsupp.prod_single_index (zpow_zero _)

end Divisor

variable (K F) in

/-- Weil reciprocity for `F / K`: for nonzero `f, g` whose divisors have disjoint
supports and are supported on rational places, `f(div g) = g(div f)`. -/
def WeilReciprocity : Prop :=
  ∀ (f g : F) (Df Dg : Divisor K F), f ≠ 0 → g ≠ 0 →
    (∀ v : Place K F, Df v = v.ord f) → (∀ v : Place K F, Dg v = v.ord g) →
    (∀ v : Place K F, v.ord f = 0 ∨ v.ord g = 0) →
    (∀ v ∈ Df.support, Place.IsRational v) → (∀ v ∈ Dg.support, Place.IsRational v) →
    Divisor.evalFun f Dg = Divisor.evalFun g Df

end AlgebraicCurve

end

section

section

open IsDedekindDomain WithZero

namespace AlgebraicCurve

namespace RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

/-- The place at infinity of `RatFunc K`. -/
def placeInfty : Place K (RatFunc K) :=
  { toValuationSubring := (RatFunc.inftyValuation K).valuationSubring
    algebraMap_mem' := fun a => by
      rw [Valuation.mem_valuationSubring_iff]
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one (v := RatFunc.inftyValuation K) a
    ne_top' := by
      simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
      infer_instance
    isPrincipalIdealRing' :=
      (Valuation.valuationSubring_isDiscreteValuationRing
        (RatFunc.inftyValuation K)).toIsPrincipalIdealRing }

@[simp]
theorem placeInfty_toValuationSubring :
    (placeInfty K).toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := rfl

end RationalFunctionField

end AlgebraicCurve

end

section

section

open Polynomial IsDedekindDomain WithZero IsLocalRing

open scoped Polynomial

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem adicValuation_valuationSubring :
    v.adicValuation.valuationSubring = v.toValuationSubring := by
  ext x
  rw [Valuation.mem_valuationSubring_iff]
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    exact a.2
  · intro hx
    exact v.heightOneSpectrum.valuation_le_one (⟨x, hx⟩ : v.toValuationSubring)

theorem mem_iff_adicValuation_le_one {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by
  rw [← v.adicValuation_valuationSubring]
  exact Valuation.mem_valuationSubring_iff _ _

instance instIsRankOneDiscreteAdicValuation : v.adicValuation.IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F

instance instIsTrivialOnAdicValuation : v.adicValuation.IsTrivialOn K :=
  Valuation.IsTrivialOn.of_le_one v.adicValuation fun a =>
    v.mem_iff_adicValuation_le_one.mp (v.algebraMap_mem' a)

theorem isEquiv_adicValuation_of_valuationSubring_eq {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) : w.IsEquiv v.adicValuation :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mpr
    (h.trans v.adicValuation_valuationSubring.symm)

theorem mem_maximalIdeal_iff_adicValuation_lt_one (a : v.toValuationSubring) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ v.adicValuation (a : F) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← v.adicValuation_coe_eq_one_iff,
    lt_iff_le_and_ne]
  have hle : v.adicValuation (a : F) ≤ 1 := v.mem_iff_adicValuation_le_one.mp a.2
  tauto

theorem ord_eq_zero_iff_adicValuation_eq_one {f : F} (hf : f ≠ 0) :
    v.ord f = 0 ↔ v.adicValuation f = 1 := by
  simp only [ord, neg_eq_zero]
  constructor
  · intro h
    have h2 := exp_log (v.adicValuation_ne_zero hf)
    rw [h, exp_zero] at h2
    exact h2.symm
  · intro h
    rw [h, log_one]

section OfHeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
  [Algebra K R] [IsScalarTower K R F]

theorem isEquiv_adicValuation_ofHeightOneSpectrum (w : HeightOneSpectrum R) :
    (w.valuation F).IsEquiv (ofHeightOneSpectrum (K := K) w).adicValuation :=
  (ofHeightOneSpectrum (K := K) w).isEquiv_adicValuation_of_valuationSubring_eq rfl

theorem ofHeightOneSpectrum_injective :
    Function.Injective (ofHeightOneSpectrum (K := K) (F := F) (R := R)) := by
  intro w w' h
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F) ?_
  refine (isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := F) w).trans ?_
  rw [h]
  exact (isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := F) w').symm

theorem ord_ofHeightOneSpectrum_ne_zero_iff (w : HeightOneSpectrum R) {q : R} (hq : q ≠ 0) :
    (ofHeightOneSpectrum (K := K) (F := F) w).ord (algebraMap R F q) ≠ 0 ↔ q ∈ w.asIdeal := by
  have hq' : algebraMap R F q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hq
  rw [ne_eq, (ofHeightOneSpectrum (K := K) w).ord_eq_zero_iff_adicValuation_eq_one hq',
    ← (isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := F) w).eq_one_iff_eq_one,
    HeightOneSpectrum.valuation_eq_one_iff_notMem, not_not]

end OfHeightOneSpectrum

end Place

namespace RationalFunctionField

variable (K : Type*) [Field K]

def heightOneSpectrumOfIrreducible {p : K[X]} (hp : Irreducible p) :
    HeightOneSpectrum K[X] where
  asIdeal := Ideal.span {p}
  isPrime := (PrincipalIdealRing.isMaximal_of_irreducible hp).isPrime
  ne_bot := by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero

@[simp]
theorem heightOneSpectrumOfIrreducible_asIdeal {p : K[X]} (hp : Irreducible p) :
    (heightOneSpectrumOfIrreducible K hp).asIdeal = Ideal.span {p} := rfl

theorem exists_irreducible_span (w : HeightOneSpectrum K[X]) :
    ∃ p : K[X], Irreducible p ∧ w.asIdeal = Ideal.span {p} := by
  obtain ⟨p, hp⟩ := (IsPrincipalIdealRing.principal w.asIdeal).principal
  rw [Ideal.submodule_span_eq] at hp
  refine ⟨p, ?_, hp⟩
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact w.ne_bot (hp.trans (by simp))
  have hpr := w.isPrime
  rw [hp] at hpr
  exact ((Ideal.span_singleton_prime hp0).mp hpr).irreducible

/-- The finite place of `RatFunc K` attached to an irreducible polynomial. -/
def finitePlace {p : K[X]} (hp : Irreducible p) : Place K (RatFunc K) :=
  Place.ofHeightOneSpectrum (heightOneSpectrumOfIrreducible K hp)

theorem finitePlace_def {p : K[X]} (hp : Irreducible p) :
    finitePlace K hp = Place.ofHeightOneSpectrum (heightOneSpectrumOfIrreducible K hp) := rfl

section ResidueDegree

theorem algebraMap_mem_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring :=
  (Place.mem_iff_adicValuation_le_one _).mpr
    ((Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).le_one_iff_le_one.mp (w.valuation_le_one q))

def residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    K[X] →+* (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ResidueField :=
  (IsLocalRing.residue _).comp
    ((algebraMap K[X] (RatFunc K)).codRestrict
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring.toSubring
      (algebraMap_mem_ofHeightOneSpectrum K w))

theorem residueOfHeightOneSpectrum_apply (w : HeightOneSpectrum K[X]) (q : K[X]) :
    residueOfHeightOneSpectrum K w q = IsLocalRing.residue _
      ⟨algebraMap K[X] (RatFunc K) q, algebraMap_mem_ofHeightOneSpectrum K w q⟩ := rfl

theorem ker_residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    RingHom.ker (residueOfHeightOneSpectrum K w) = w.asIdeal := by
  ext q
  rw [RingHom.mem_ker, residueOfHeightOneSpectrum_apply, IsLocalRing.residue_eq_zero_iff,
    Place.mem_maximalIdeal_iff_adicValuation_lt_one,
    ← (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).lt_one_iff_lt_one]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem w q

theorem surjective_residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    Function.Surjective (residueOfHeightOneSpectrum K w) := by
  intro y
  obtain ⟨⟨x, hx⟩, rfl⟩ := IsLocalRing.residue_surjective y
  have hxval : w.valuation (RatFunc K) x ≤ 1 :=
    (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).le_one_iff_le_one.mpr ((Place.mem_iff_adicValuation_le_one _).mp hx)

  have hden_ne : algebraMap K[X] (RatFunc K) x.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr x.denom_ne_zero
  have hmul : x * algebraMap K[X] (RatFunc K) x.denom = algebraMap K[X] (RatFunc K) x.num :=
    ((div_eq_iff hden_ne).mp x.num_div_denom).symm

  have hden : x.denom ∉ w.asIdeal := by
    intro hd
    have hnum : x.num ∉ w.asIdeal := by
      intro hn
      refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
      obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom x
      exact hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hd)
    have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.num) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hnum
    refine absurd h1 (ne_of_lt ?_)
    calc w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.num)
        = w.valuation (RatFunc K) x
            * w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.denom) := by
          rw [← map_mul, hmul]
      _ ≤ w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.denom) :=
          mul_le_of_le_one_left' hxval
      _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w x.denom).mpr hd

  have hmax : w.asIdeal.IsMaximal := IsPrime.to_maximal_ideal w.ne_bot
  obtain ⟨t, ht⟩ : ∃ t : K[X], x.denom * t - 1 ∈ w.asIdeal := by
    obtain ⟨b, c, hc, hbc⟩ := hmax.exists_inv hden
    refine ⟨b, ?_⟩
    rw [show x.denom * b - 1 = -c by linear_combination hbc]
    exact neg_mem hc

  refine ⟨x.num * t, ?_⟩
  rw [residueOfHeightOneSpectrum_apply, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, Place.mem_maximalIdeal_iff_adicValuation_lt_one]
  show (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).adicValuation
    (algebraMap K[X] (RatFunc K) (x.num * t) - x) < 1
  rw [← (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).lt_one_iff_lt_one]
  have key : algebraMap K[X] (RatFunc K) (x.num * t) - x
      = x * algebraMap K[X] (RatFunc K) (x.denom * t - 1) := by
    rw [map_sub, map_mul, map_mul, map_one, mul_sub, mul_one, ← mul_assoc, hmul]
  rw [key, map_mul]
  calc w.valuation (RatFunc K) x
        * w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) (x.denom * t - 1))
      ≤ w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) (x.denom * t - 1)) :=
        mul_le_of_le_one_left' hxval
    _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr ht

def residueFieldEquivOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    (K[X] ⧸ w.asIdeal) ≃ₐ[K]
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ResidueField := by
  refine AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq
    (ker_residueOfHeightOneSpectrum K w).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_residueOfHeightOneSpectrum K w))) ?_
  intro a
  rw [show (algebraMap K (K[X] ⧸ w.asIdeal)) a
      = Ideal.Quotient.mk w.asIdeal (algebraMap K K[X] a) from rfl]
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, residueOfHeightOneSpectrum_apply]
  exact congrArg (IsLocalRing.residue _)
    (Subtype.ext (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) a).symm)

theorem deg_ofHeightOneSpectrum {w : HeightOneSpectrum K[X]} {p : K[X]}
    (hw : w.asIdeal = Ideal.span {p}) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).deg = p.natDegree := by
  rw [Place.deg, ← (residueFieldEquivOfHeightOneSpectrum K w).toLinearEquiv.finrank_eq, hw]
  exact finrank_quotient_span_eq_natDegree

theorem deg_finitePlace {p : K[X]} (hp : Irreducible p) :
    (finitePlace K hp).deg = p.natDegree :=
  deg_ofHeightOneSpectrum K (heightOneSpectrumOfIrreducible_asIdeal K hp)

end ResidueDegree

/-- The finite place of `RatFunc K` at the point `a`, attached to `X - C a`. -/
def placeOfPoint (a : K) : Place K (RatFunc K) :=
  finitePlace K (irreducible_X_sub_C a)

theorem placeOfPoint_eq_ofHeightOneSpectrum (a : K) :
    placeOfPoint K a
      = Place.ofHeightOneSpectrum (heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)) :=
  rfl

theorem placeOfPoint_injective : Function.Injective (placeOfPoint K) := by
  intro a b h
  have h2 : heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)
      = heightOneSpectrumOfIrreducible K (irreducible_X_sub_C b) :=
    Place.ofHeightOneSpectrum_injective (K := K) (F := RatFunc K) h
  have h3 : Ideal.span {(X : K[X]) - C a} = Ideal.span {(X : K[X]) - C b} := by
    have := congrArg HeightOneSpectrum.asIdeal h2
    simpa using this
  have h4 : ((X : K[X]) - C a) ∣ (X - C b) :=
    (Ideal.span_singleton_eq_span_singleton.mp h3).dvd
  have h5 : (X - C b).IsRoot a := dvd_iff_isRoot.mp h4
  have h6 : a - b = 0 := by simpa [IsRoot] using h5
  exact sub_eq_zero.mp h6

@[simp]
theorem deg_placeOfPoint (a : K) : (placeOfPoint K a).deg = 1 := by
  rw [placeOfPoint, deg_finitePlace, natDegree_X_sub_C]

end RationalFunctionField

namespace Place

section Congr

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F')

variable (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
include he

end Congr

end Place

end AlgebraicCurve

end

end

section

theorem Algebra.norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap {R A : Type*} [CommRing R]
  [IsDomain R] [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A] {a : A} {μ : R} (h :
    IsNilpotent (a - algebraMap R A μ)) : Algebra.norm R a = μ ^ Module.finrank R A := by
  have hN : IsNilpotent (Algebra.lmul R A (a - algebraMap R A μ)) := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← map_pow, hk, map_zero]⟩
  have hN' : IsNilpotent (-(Algebra.lmul R A (a - algebraMap R A μ))) := hN.neg
  have hsplit : (Algebra.lmul R A) a
      = algebraMap R (Module.End R A) μ - (-(Algebra.lmul R A (a - algebraMap R A μ))) := by
    rw [sub_neg_eq_add, ← (Algebra.lmul R A).commutes μ, ← map_add]
    congr 1
    abel
  rw [Algebra.norm_apply, hsplit, ← LinearMap.eval_charpoly,
    IsNilpotent.charpoly_eq_X_pow_finrank hN', Polynomial.eval_pow, Polynomial.eval_X]

end

section

theorem Algebra.norm_of_subsingleton {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Subsingleton A] (a : A) : Algebra.norm R a = 1 :=
  LinearMap.det_eq_one_of_subsingleton _

end

section

theorem Algebra.norm_prod {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R
  B] [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B] (x : A × B) :
    Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  have lmul_prod : Algebra.lmul R (A × B) x
      = ((Algebra.lmul R A x.1).prodMap (Algebra.lmul R B x.2) : A × B →ₗ[R] A × B) := by
    ext y <;> rfl
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, lmul_prod,
    LinearMap.det_prodMap]

end

section

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.evalFun_add {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F)
    {D E : Divisor K F} (hD : ∀ v ∈ D.support, Place.evalAt v f ≠ 0)
    (hE : ∀ v ∈ E.support, Place.evalAt v f ≠ 0) : Divisor.evalFun f (D + E) = Divisor.evalFun f D *
    Divisor.evalFun f E :=
    by
  classical
  refine Finsupp.prod_add_index (fun v _ => zpow_zero _) (fun v hv b₁ b₂ => ?_)
  refine zpow_add₀ ?_ b₁ b₂
  rcases Finset.mem_union.mp hv with h | h
  · exact hD v h
  · exact hE v h

end

section

open IsLocalRing AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) : v.evalAt f ≠ 0 :=
    by
  have hmem : f ∈ v.toValuationSubring := v.mem_of_ord_nonneg hf h.ge

  have hunit : IsUnit (⟨f, hmem⟩ : v.toValuationSubring) := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
    rw [h, zpow_zero, mul_one] at hu
    have huf : (⟨f, hmem⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
    rw [huf]
    exact u.isUnit
  have hres : residue v.toValuationSubring (⟨f, hmem⟩ : v.toValuationSubring) ≠ 0 :=
    (residue_ne_zero_iff_isUnit _).mpr hunit
  intro h0
  have key := v.algebraMap_evalAt hv hmem
  rw [h0, map_zero] at key
  exact hres key.symm

end

section

open AlgebraicCurve

theorem AlgebraicCurve.Place.isRational_iff_deg_eq_one {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) : v.IsRational ↔ v.deg = 1 := by
  constructor
  · intro hv
    have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
      ⟨v.algebraMap_residueField_injective, hv⟩
    show Module.finrank K v.ResidueField = 1
    rw [← Module.finrank_self K]
    exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField)
      hbij).toLinearEquiv.finrank_eq).symm
  · intro h x
    have hbot : (⊥ : Subalgebra K v.ResidueField) = ⊤ :=
      Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr h
    have hx : x ∈ (⊥ : Subalgebra K v.ResidueField) := by
      rw [hbot]
      exact Algebra.mem_top
    exact Algebra.mem_bot.mp hx

end

section

open IsLocalRing AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_mul {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv (mul_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

end

section

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.evalFun_mul {K F : Type*} [Field K] [Field F] [Algebra K F] {f g : F}
    {D : Divisor K F} (hrat : ∀ v ∈ D.support, Place.IsRational v)
    (hf : ∀ v ∈ D.support, f ∈ v.toValuationSubring)
    (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring) : Divisor.evalFun (f * g) D = Divisor.evalFun f
    D * Divisor.evalFun g D := by
  rw [show Divisor.evalFun (f * g) D = D.prod fun v n => v.evalAt f ^ n * v.evalAt g ^ n from
    Finsupp.prod_congr fun v hv => by
      rw [AlgebraicCurve.Place.evalAt_mul v (hrat v hv) (hf v hv) (hg v hv), mul_zpow]]
  exact Finsupp.prod_mul

end

section

open AlgebraicCurve

theorem AlgebraicCurve.Place.eq_ord_of_addHom_of_nonneg_iff {K F : Type*} [Field K] [Field F]
    [Algebra K F] (w : Place K F) (φ : F → ℤ) (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1) (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring)) {x : F}
    (hx : x ≠ 0) : φ x = w.ord x := by
  obtain ⟨t, ht0, ht1⟩ := hone

  have hφ1 : φ 1 = 0 := by
    have := hmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega

  have hinv : ∀ y, y ≠ 0 → φ y⁻¹ = -φ y := by
    intro y hy
    have h1 : φ (y * y⁻¹) = φ y + φ y⁻¹ := hmul y y⁻¹ hy (inv_ne_zero hy)
    rw [mul_inv_cancel₀ hy, hφ1] at h1
    omega

  have hpow : ∀ (y : F), y ≠ 0 → ∀ m : ℕ, φ (y ^ m) = m * φ y := by
    intro y hy m
    induction m with
    | zero => simpa using hφ1
    | succ m ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ hy) hy, ih]
      push_cast
      ring
  have hzpow : ∀ (y : F) (n : ℤ), y ≠ 0 → φ (y ^ n) = n * φ y := by
    intro y n hy
    rcases n with m | m
    · simpa using hpow y hy m
    · rw [zpow_negSucc, hinv _ (pow_ne_zero _ hy), hpow y hy, Int.negSucc_eq]
      push_cast
      ring

  have hsign : ∀ y, y ≠ 0 → (0 ≤ φ y ↔ 0 ≤ w.ord y) := by
    intro y hy
    rw [hiff y hy, w.mem_iff_ord_nonneg hy]
  have hzero : ∀ y, y ≠ 0 → (φ y = 0 ↔ w.ord y = 0) := by
    intro y hy
    have h1 := hsign y hy
    have h2 := hsign y⁻¹ (inv_ne_zero hy)
    rw [hinv y hy, w.ord_inv] at h2
    omega

  have htord : 0 < w.ord t := by
    have h1 := (hsign t ht0).mp (by omega)
    have h2 := (hzero t ht0).not.mp (by omega)
    omega

  have hcancel : ∀ y, y ≠ 0 → w.ord y = φ y * w.ord t := by
    intro y hy
    have hyt : y * t ^ (-(φ y)) ≠ 0 := mul_ne_zero hy (zpow_ne_zero _ ht0)
    have h1 : φ (y * t ^ (-(φ y))) = 0 := by
      rw [hmul _ _ hy (zpow_ne_zero _ ht0), hzpow t _ ht0, ht1]
      ring
    have h2 : w.ord (y * t ^ (-(φ y))) = 0 := (hzero _ hyt).mp h1
    rw [w.ord_mul hy (zpow_ne_zero _ ht0), w.ord_zpow] at h2
    linarith

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hπcancel := hcancel (π : F) hπ0
  rw [w.ord_coe_irreducible hπ] at hπcancel

  have htord1 : w.ord t = 1 := by
    have hdvd : w.ord t ∣ 1 := ⟨φ (π : F), by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    omega
  have := hcancel x hx
  rw [htord1, mul_one] at this
  exact this.symm

end

section

open AlgebraicCurve AlgebraicCurve.Divisor

theorem AlgebraicCurve.Divisor.evalFun_single_sub_single {K F : Type*} [Field K] [Field F]
    [Algebra K F] (f : F) {v₁ v₂ : Place K F} (h₁ : v₁.evalAt f ≠ 0) (h₂ : v₂.evalAt f ≠ 0) :
    Divisor.evalFun f (Finsupp.single v₁ 1 + Finsupp.single v₂ (-1)) = v₁.evalAt f / v₂.evalAt f :=
    by
  have hsupp : ∀ (w : Place K F) (n : ℤ), w.evalAt f ≠ 0 →
      ∀ v ∈ (Finsupp.single w n).support, Place.evalAt v f ≠ 0 := by
    intro w n hw v hv
    have := Finsupp.support_single_subset hv
    rw [Finset.mem_singleton] at this
    rw [this]
    exact hw
  rw [AlgebraicCurve.Divisor.evalFun_add f (hsupp v₁ 1 h₁) (hsupp v₂ (-1) h₂), evalFun_single,
    evalFun_single,
    zpow_one, zpow_neg_one, div_eq_mul_inv]

end

section

open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_inv {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) : v.evalAt f⁻¹ =
    (v.evalAt f)⁻¹ :=
    by
  have hfi : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hi : v.ord f⁻¹ = 0 := by rw [v.ord_inv, h, neg_zero]
  have hmul := v.evalAt_mul hv (v.mem_of_ord_nonneg hf h.ge) (v.mem_of_ord_nonneg hfi hi.ge)
  rw [mul_inv_cancel₀ hf, v.evalAt_one] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

end

section

open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_zpow {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) (n : ℤ) : v.evalAt
    (f ^ n) = v.evalAt f ^ n := by
  have hpow : ∀ m : ℕ, v.evalAt (f ^ m) = v.evalAt f ^ m := by
    intro m
    induction m with
    | zero => simp [v.evalAt_one]
    | succ m ih =>
      have hm : v.ord (f ^ (m : ℤ)) = 0 := by rw [v.ord_zpow, h, mul_zero]
      rw [pow_succ, v.evalAt_mul hv ?_ (v.mem_of_ord_nonneg hf h.ge), ih, pow_succ]
      have : (f ^ m : F) = f ^ (m : ℤ) := by rw [zpow_natCast]
      rw [this]
      exact v.mem_of_ord_nonneg (zpow_ne_zero _ hf) hm.ge
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]
    exact hpow m
  · rw [zpow_negSucc, zpow_negSucc, ← hpow (m + 1)]
    refine v.evalAt_inv hv (pow_ne_zero _ hf) ?_
    have : (f ^ (m + 1) : F) = f ^ ((m + 1 : ℕ) : ℤ) := by rw [zpow_natCast]
    rw [this, v.ord_zpow, h, mul_zero]

end

section

open AlgebraicCurve AlgebraicCurve.Divisor

theorem AlgebraicCurve.Divisor.evalFun_zpow_left {K F : Type*} [Field K] [Field F] [Algebra K F]
    {f : F} (hf : f ≠ 0) {D : Divisor K F} (n : ℤ) (hrat : ∀ v ∈ D.support, Place.IsRational v)
    (hord : ∀ v ∈ D.support, Place.ord v f = 0) : Divisor.evalFun (f ^ n) D = Divisor.evalFun f D ^
    n := by
  rw [evalFun_def, evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [AlgebraicCurve.Place.evalAt_zpow v (hrat v hv) hf (hord v hv) n, ← zpow_mul, ← zpow_mul,
    mul_comm]

end

section

open AlgebraicCurve AlgebraicCurve.Divisor

theorem AlgebraicCurve.Divisor.evalFun_zsmul {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F)
    (D : Divisor K F) (n : ℤ) : Divisor.evalFun f (n • D) = Divisor.evalFun f D ^ n := by
  rw [show evalFun f (n • D) = ∏ v ∈ D.support, v.evalAt f ^ ((n • D) v) from
      Finsupp.prod_of_support_subset _ Finsupp.support_smul _ fun v _ => zpow_zero _,
    evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm n (D v), zpow_mul]

end

section

open IsDedekindDomain WithZero IsLocalRing

section

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem rowMain : v.adicValuation.IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F

end Place

end AlgebraicCurve

end

open AlgebraicCurve in
theorem AlgebraicCurve.Place.adicValuation_isRankOneDiscrete {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) : v.adicValuation.IsRankOneDiscrete :=
  AlgebraicCurve.Place.rowMain v

end

section

open IsDedekindDomain WithZero IsLocalRing

section

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.adicValuation_valuationSubring_loc :
    v.adicValuation.valuationSubring = v.toValuationSubring := by
  ext x
  rw [Valuation.mem_valuationSubring_iff]
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    exact a.2
  · intro hx
    exact v.heightOneSpectrum.valuation_le_one (⟨x, hx⟩ : v.toValuationSubring)

private theorem _root_.AlgebraicCurve.Place.mem_iff_adicValuation_le_one_loc {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by
  rw [← v.adicValuation_valuationSubring_loc]
  exact Valuation.mem_valuationSubring_iff _ _

private theorem rowMain_838 : v.adicValuation.IsTrivialOn K :=
  Valuation.IsTrivialOn.of_le_one v.adicValuation fun a =>
    v.mem_iff_adicValuation_le_one_loc.mp (v.algebraMap_mem' a)

end Place

end AlgebraicCurve

end

open AlgebraicCurve in
theorem AlgebraicCurve.Place.adicValuation_isTrivialOn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) : v.adicValuation.IsTrivialOn K :=
  AlgebraicCurve.Place.rowMain_838 v

end

section

open IsLocalRing AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have ha : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [ha, ← ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
    v.residueInv_algebraMap]

end

section

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnAdicValuation
attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open IsDedekindDomain WithZero IsLocalRing AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_congr {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring)
    (h : f - g = 0 ∨ 0 < v.ord (f - g)) : v.evalAt f = v.evalAt g := by
  rcases h with h | h
  · rw [sub_eq_zero] at h
    rw [h]
  have hsub : f - g ∈ v.toValuationSubring := sub_mem hf hg

  have hmax : ∀ {x : F} (hx : x ∈ v.toValuationSubring), 0 < v.ord x →
      (⟨x, hx⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    intro x hx hpos
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Submodule.zero_mem _
    rw [v.mem_maximalIdeal_iff_adicValuation_lt_one]
    have hne : v.adicValuation x ≠ 0 := v.adicValuation_ne_zero hx0
    rw [← exp_log hne, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp]
    have : v.ord x = -log (v.adicValuation x) := rfl
    omega
  have hmem : (⟨f, hf⟩ : v.toValuationSubring) - ⟨g, hg⟩ ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    have : (⟨f, hf⟩ : v.toValuationSubring) - ⟨g, hg⟩ = ⟨f - g, hsub⟩ := rfl
    rw [this]
    exact hmax hsub h
  have hres : residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring)
      = residue v.toValuationSubring (⟨g, hg⟩ : v.toValuationSubring) := by
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  rw [v.evalAt_of_mem hf, v.evalAt_of_mem hg, hres]

end

section

open IsDedekindDomain WithZero IsLocalRing

section

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.isUnit_algebraMap {c : K} (hc : c ≠ 0) :
    IsUnit (algebraMap K v.toValuationSubring c) :=
  (isUnit_iff_ne_zero.mpr hc).map _

private theorem _root_.AlgebraicCurve.Place.adicValuation_algebraMap {c : K} (hc : c ≠ 0) :
    v.adicValuation (algebraMap K F c) = 1 := by
  rw [← v.coe_algebraMap]
  exact (v.adicValuation_coe_eq_one_iff _).mpr (v.isUnit_algebraMap hc)

private theorem rowMain_932 (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, v.ord_zero]
  · simp only [ord, v.adicValuation_algebraMap hc, log_one, neg_zero]

end Place

end AlgebraicCurve

end

open AlgebraicCurve in
theorem AlgebraicCurve.Place.ord_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 :=
  AlgebraicCurve.Place.rowMain_932 v c

end

section

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnAdicValuation
attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

namespace AlgebraicCurve
namespace WFa
open AlgebraicCurve

theorem le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx : x < 1) : x ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_le'
  · rw [← exp_log hx0] at hx ⊢
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp] at hx
    rw [exp_le_exp]
    omega

end AlgebraicCurve.WFa

open AlgebraicCurve.WFa in
theorem AlgebraicCurve.Place.ord_eq_neg_log_of_valuationSubring_eq {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) (w : Valuation F (WithZero (Multiplicative ℤ)))
    (hw : w.valuationSubring = v.toValuationSubring) {π : F} (hπ : w π = WithZero.exp (-1 : ℤ))
    {f : F} (hf : f ≠ 0) : v.ord f = -WithZero.log (w f) := by
  have hequiv : w.IsEquiv v.adicValuation :=
    v.isEquiv_adicValuation_of_valuationSubring_eq hw
  have hexp_lt : (exp (-1 : ℤ) : ℤᵐ⁰) < 1 := by
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl]
    exact exp_lt_exp.mpr (by omega)
  obtain ⟨π₀, hπ₀⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hadic_π₀ : v.adicValuation (π₀ : F) = exp (-1 : ℤ) := v.adicValuation_coe_irreducible hπ₀

  have hwπ₀ : w (π₀ : F) = exp (-1 : ℤ) := by
    refine le_antisymm (le_exp_neg_one_of_lt_one (hequiv.lt_one_iff_lt_one.mpr ?_)) ?_
    · rw [hadic_π₀]
      exact hexp_lt
    · rw [← hπ]
      refine (hequiv π π₀).mpr ?_
      rw [hadic_π₀]
      refine le_exp_neg_one_of_lt_one (hequiv.lt_one_iff_lt_one.mp ?_)
      rw [hπ]
      exact hexp_lt
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ₀
  have hwu : w ((u : v.toValuationSubring) : F) = 1 :=
    hequiv.eq_one_iff_eq_one.mpr ((v.adicValuation_coe_eq_one_iff _).mpr u.isUnit)
  set n := v.ord f with hn
  rw [hu, map_mul, map_zpow₀, hwu, hwπ₀, one_mul, log_zpow, log_exp, smul_eq_mul]
  ring

end

end

