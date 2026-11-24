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
public import MathlibExt.AlgebraicGeometry.Curve.PlaceDivisor
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Restriction of places along a field extension

For a tower `K ⊆ F ⊆ F'`, a place of `F'` restricts to a place of `F`. This file defines
restriction, ramification index and inertia degree, the pushforward and pullback of divisors,
the fibre of a place, and identifies the places above a place `v` of `F` with the height-one
primes of the integral closure of the valuation ring of `v` in `F'`.
-/

@[expose] public section

noncomputable section

section

section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

namespace Place

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem exists_ord_pos : ∃ f : F, f ≠ 0 ∧ 0 < v.ord f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  refine ⟨(π : F), ?_, ?_⟩
  · simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  · rw [v.ord_coe_irreducible hπ]
    exact one_pos

end SinglePlace

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

theorem algebraMap_ne_zero {f : F} (hf : f ≠ 0) : algebraMap F F' f ≠ 0 := by
  simpa using hf

variable (w : Place K F')

theorem comap_algebraMap_ne_top [Algebra.IsIntegral F F'] :
    w.toValuationSubring.comap (algebraMap F F') ≠ ⊤ := by
  intro htop
  apply w.ne_top'

  have hF : ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring := fun f =>
    ValuationSubring.mem_comap.mp (htop ▸ ValuationSubring.mem_top f)

  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  letI : Algebra F w.toValuationSubring :=
    ((algebraMap F F').codRestrict w.toValuationSubring.toSubring hF).toAlgebra
  letI : IsScalarTower F w.toValuationSubring F' :=
    IsScalarTower.of_algebraMap_eq fun f => rfl
  have hx : IsIntegral w.toValuationSubring x :=
    (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  exact hy ▸ y.2

variable {w} in

theorem mem_comap_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.comap (algebraMap F F') ↔
      0 ≤ w.ord (algebraMap F F' f) := by
  rw [ValuationSubring.mem_comap]
  exact w.mem_iff_ord_nonneg (algebraMap_ne_zero hf)

variable {w} in

theorem isUnit_mk_comap_iff {f : F} (hf : f ≠ 0)
    (hmem : f ∈ w.toValuationSubring.comap (algebraMap F F')) :
    IsUnit (⟨f, hmem⟩ : w.toValuationSubring.comap (algebraMap F F')) ↔
      w.ord (algebraMap F F' f) = 0 := by
  constructor
  · rintro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp h
    have hb' : f * (b : F) = 1 := by
      simpa [Subtype.ext_iff] using hb
    have hbne : (b : F) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hb'
      exact zero_ne_one hb'
    have hsum : w.ord (algebraMap F F' f) + w.ord (algebraMap F F' (b : F)) = 0 := by
      rw [← w.ord_mul (algebraMap_ne_zero hf) (algebraMap_ne_zero hbne), ← map_mul, hb',
        map_one, w.ord_one]
    have h1 : 0 ≤ w.ord (algebraMap F F' f) := (mem_comap_iff_ord_nonneg hf).mp hmem
    have h2 : 0 ≤ w.ord (algebraMap F F' (b : F)) := (mem_comap_iff_ord_nonneg hbne).mp b.2
    omega
  · intro h0
    have hinv : f⁻¹ ∈ w.toValuationSubring.comap (algebraMap F F') :=
      (mem_comap_iff_ord_nonneg (inv_ne_zero hf)).mpr (by rw [map_inv₀, w.ord_inv]; omega)
    exact ⟨⟨⟨f, hmem⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf),
      Subtype.ext (inv_mul_cancel₀ hf)⟩, rfl⟩

theorem exists_ord_algebraMap_pos [Algebra.IsIntegral F F'] :
    ∃ f : F, f ≠ 0 ∧ 0 < w.ord (algebraMap F F' f) := by
  have h := w.comap_algebraMap_ne_top (F := F)
  rw [ne_eq, SetLike.ext_iff, not_forall] at h
  obtain ⟨g, hg⟩ := h
  simp only [ValuationSubring.mem_top, iff_true] at hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hg (zero_mem _)
  refine ⟨g⁻¹, inv_ne_zero hg0, ?_⟩
  rw [map_inv₀, w.ord_inv]
  have := (mem_comap_iff_ord_nonneg hg0).not.mp hg
  omega

/-- The ramification index of `w` over its restriction to `F`. -/
def ramificationIndex (F : Type*) [Field F] [Algebra F F'] : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F' f) = n}

theorem ramificationIndex_le_ord {f : F} (hf : f ≠ 0)
    (hpos : 0 < w.ord (algebraMap F F' f)) :
    (ramificationIndex (F := F) w : ℤ) ≤ w.ord (algebraMap F F' f) := by
  have h := Nat.sInf_le
    (s := {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F' f) = n})
    (m := (w.ord (algebraMap F F' f)).toNat) ⟨by omega, f, hf, by omega⟩
  rw [ramificationIndex]
  omega

variable [Algebra.IsIntegral F F']

theorem ramificationIndex_set_nonempty :
    {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F' f) = n}.Nonempty := by
  obtain ⟨f, hf0, hf⟩ := w.exists_ord_algebraMap_pos (F := F)
  exact ⟨(w.ord (algebraMap F F' f)).toNat, by omega, f, hf0, by omega⟩

theorem ramificationIndex_pos : 0 < ramificationIndex (F := F) w :=
  (Nat.sInf_mem (w.ramificationIndex_set_nonempty (F := F))).1

theorem exists_ord_eq_ramificationIndex :
    ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F' f) = ramificationIndex (F := F) w :=
  (Nat.sInf_mem (w.ramificationIndex_set_nonempty (F := F))).2

theorem ramificationIndex_dvd_ord {f : F} (hf : f ≠ 0) :
    (ramificationIndex (F := F) w : ℤ) ∣ w.ord (algebraMap F F' f) := by
  obtain ⟨g, hg0, hge⟩ := w.exists_ord_eq_ramificationIndex (F := F)
  set e : ℤ := (ramificationIndex (F := F) w : ℤ) with he
  have hepos : 0 < e := by
    have := w.ramificationIndex_pos (F := F)
    omega
  set m : ℤ := w.ord (algebraMap F F' f) with hm
  set q : ℤ := m / e with hq

  have hgq : algebraMap F F' (g ^ (-q)) = (algebraMap F F' g) ^ (-q) := map_zpow₀ _ _ _
  have hr : w.ord (algebraMap F F' (f * g ^ (-q))) = m - e * q := by
    rw [map_mul, w.ord_mul (algebraMap_ne_zero hf)
      (by rw [hgq]; exact zpow_ne_zero _ (algebraMap_ne_zero hg0)), hgq, w.ord_zpow, hge,
      ← hm]
    ring
  have hmod := Int.emod_nonneg m (by omega : e ≠ 0)
  have hmod' := Int.emod_lt_of_pos m hepos
  have hbridge : m % e = m - e * q := by
    rw [hq]
    exact Int.emod_def m e

  rcases eq_or_lt_of_le (show (0 : ℤ) ≤ m - e * q by omega) with heq | hlt
  · exact ⟨q, by omega⟩
  · exfalso
    have hfg : f * g ^ (-q) ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ hg0)
    have hle := w.ramificationIndex_le_ord (F := F) hfg (by omega)
    rw [hr, ← he] at hle
    omega

theorem irreducible_mk_comap {g : F} (hg0 : g ≠ 0)
    (hmem : g ∈ w.toValuationSubring.comap (algebraMap F F'))
    (hge : w.ord (algebraMap F F' g) = ramificationIndex (F := F) w) :
    Irreducible (⟨g, hmem⟩ : w.toValuationSubring.comap (algebraMap F F')) := by
  have hepos : 0 < ramificationIndex (F := F) w := w.ramificationIndex_pos (F := F)
  constructor
  ·
    rw [isUnit_mk_comap_iff hg0 hmem, hge]
    omega
  ·

    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : g = a * b := by simpa [Subtype.ext_iff] using hab
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hg0 (by simpa using hab')
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hg0 (by simpa using hab')
    have hsum : w.ord (algebraMap F F' a) + w.ord (algebraMap F F' b)
        = ramificationIndex (F := F) w := by
      rw [← w.ord_mul (algebraMap_ne_zero ha0) (algebraMap_ne_zero hb0), ← map_mul, ← hab',
        hge]
    have ha' : 0 ≤ w.ord (algebraMap F F' a) := (mem_comap_iff_ord_nonneg ha0).mp ha
    have hb' : 0 ≤ w.ord (algebraMap F F' b) := (mem_comap_iff_ord_nonneg hb0).mp hb

    rcases eq_or_lt_of_le ha' with ha0' | hapos
    · exact Or.inl ((isUnit_mk_comap_iff ha0 ha).mpr ha0'.symm)
    rcases eq_or_lt_of_le hb' with hb0' | hbpos
    · exact Or.inr ((isUnit_mk_comap_iff hb0 hb).mpr hb0'.symm)
    exfalso
    have h1 := w.ramificationIndex_le_ord (F := F) ha0 hapos
    have h2 := w.ramificationIndex_le_ord (F := F) hb0 hbpos
    omega

theorem isPrincipalIdealRing_comap :
    IsPrincipalIdealRing (w.toValuationSubring.comap (algebraMap F F')) := by
  obtain ⟨g, hg0, hge⟩ := w.exists_ord_eq_ramificationIndex (F := F)
  have hepos : 0 < ramificationIndex (F := F) w := w.ramificationIndex_pos (F := F)
  have hgmem : g ∈ w.toValuationSubring.comap (algebraMap F F') :=
    (mem_comap_iff_ord_nonneg hg0).mpr (by omega)
  refine (IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨⟨g, hgmem⟩, irreducible_mk_comap w hg0 hgmem hge, ?_⟩).toIsPrincipalIdealRing
  rintro ⟨f, hmem⟩ hx
  have hf : f ≠ 0 := by simpa [Subtype.ext_iff] using hx

  obtain ⟨c, hc⟩ := w.ramificationIndex_dvd_ord (F := F) hf
  have hnonneg : 0 ≤ w.ord (algebraMap F F' f) := (mem_comap_iff_ord_nonneg hf).mp hmem
  have hcnonneg : 0 ≤ c := by
    by_contra hneg
    have hcle : c ≤ -1 := by omega
    have : (ramificationIndex (F := F) w : ℤ) * c ≤ (ramificationIndex (F := F) w : ℤ) * -1 :=
      mul_le_mul_of_nonneg_left hcle (by omega)
    omega
  set n : ℕ := c.toNat with hn
  have hcn : (n : ℤ) = c := Int.toNat_of_nonneg hcnonneg
  refine ⟨n, ?_⟩

  have hgn : g ^ n ≠ 0 := pow_ne_zero _ hg0
  have hdiv0 : f / g ^ n ≠ 0 := div_ne_zero hf hgn
  have hu0 : w.ord (algebraMap F F' (f / g ^ n)) = 0 := by
    have hkey : algebraMap F F' (f / g ^ n)
        = algebraMap F F' f * (algebraMap F F' g) ^ (-(n : ℤ)) := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, ← zpow_natCast (algebraMap F F' g) n,
        ← zpow_neg]
    rw [hkey, w.ord_mul (algebraMap_ne_zero hf) (zpow_ne_zero _ (algebraMap_ne_zero hg0)),
      w.ord_zpow, hge, hc, ← hcn]
    ring
  have humem : f / g ^ n ∈ w.toValuationSubring.comap (algebraMap F F') :=
    (mem_comap_iff_ord_nonneg hdiv0).mpr (le_of_eq hu0.symm)
  have hu : IsUnit (⟨f / g ^ n, humem⟩ : w.toValuationSubring.comap (algebraMap F F')) :=
    (isUnit_mk_comap_iff hdiv0 humem).mpr hu0
  refine ⟨hu.unit, ?_⟩
  refine Subtype.ext ?_
  have hcoe : ((hu.unit : w.toValuationSubring.comap (algebraMap F F')) : F) = f / g ^ n := by
    rw [IsUnit.unit_spec]
  push_cast
  rw [hcoe, mul_comm, div_mul_cancel₀]
  exact hgn

section RestrictDef

variable [Algebra K F] [IsScalarTower K F F']

variable (F) in

/-- The restriction of a place of `F'` to `F`. -/
def restrict : Place K F where
  toValuationSubring := w.toValuationSubring.comap (algebraMap F F')
  algebraMap_mem' a := by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact w.algebraMap_mem' a
  ne_top' := w.comap_algebraMap_ne_top
  isPrincipalIdealRing' := w.isPrincipalIdealRing_comap

@[simp]
theorem restrict_toValuationSubring :
    (w.restrict F).toValuationSubring = w.toValuationSubring.comap (algebraMap F F') := rfl

theorem ord_restrict (f : F) :
    w.ord (algebraMap F F' f) = ramificationIndex (F := F) w * (w.restrict F).ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨g, hg0, hge⟩ := w.exists_ord_eq_ramificationIndex (F := F)
  have hepos : 0 < ramificationIndex (F := F) w := w.ramificationIndex_pos (F := F)
  have hgmem : g ∈ w.toValuationSubring.comap (algebraMap F F') :=
    (mem_comap_iff_ord_nonneg hg0).mpr (by omega)

  obtain ⟨u, hu⟩ := (w.restrict F).exists_unit_mul_zpow hf
    (π := ⟨g, hgmem⟩) (irreducible_mk_comap w hg0 hgmem hge)
  set n : ℤ := (w.restrict F).ord f with hn

  have hune : ((u : (w.restrict F).toValuationSubring) : F) ≠ 0 := by
    intro h0
    have := u.mul_inv
    rw [Subtype.ext_iff] at this
    push_cast at this
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have huord : w.ord (algebraMap F F' ((u : (w.restrict F).toValuationSubring) : F)) = 0 :=
    (isUnit_mk_comap_iff hune (u : (w.restrict F).toValuationSubring).2).mp u.isUnit

  have hgz : (algebraMap F F' g) ^ n ≠ 0 := zpow_ne_zero _ (algebraMap_ne_zero hg0)
  calc w.ord (algebraMap F F' f)
      = w.ord (algebraMap F F' (((u : (w.restrict F).toValuationSubring) : F) * g ^ n)) := by
        rw [← hu]
    _ = w.ord (algebraMap F F' ((u : (w.restrict F).toValuationSubring) : F))
          + w.ord ((algebraMap F F' g) ^ n) := by
        rw [map_mul, map_zpow₀]
        exact w.ord_mul (algebraMap_ne_zero hune) hgz
    _ = ramificationIndex (F := F) w * n := by
        rw [huord, w.ord_zpow, hge, zero_add, mul_comm]

theorem ord_algebraMap_ne_zero_of_restrict_eq {v : Place K F} {f : F}
    (hford : v.ord f ≠ 0) (hw : w.restrict F = v) :
    w.ord (algebraMap F F' f) ≠ 0 := by
  rw [w.ord_restrict f, hw]
  have hepos : 0 < ramificationIndex (F := F) w := w.ramificationIndex_pos (F := F)
  exact mul_ne_zero (by omega) hford

theorem restrict_fiber_finite [HasPrincipalDivisors K F'] (v : Place K F) :
    {w : Place K F' | w.restrict F = v}.Finite := by
  obtain ⟨f, hf0, hford⟩ := v.exists_ord_pos
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K)
    (algebraMap F F' f) (algebraMap_ne_zero hf0)
  apply Set.Finite.subset D.support.finite_toSet
  intro w hw
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, hD w]
  exact w.ord_algebraMap_ne_zero_of_restrict_eq (by omega) hw

end RestrictDef

end Restrict

end Place

end AlgebraicCurve

section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

namespace Place

variable (w : Place K F')

variable (F) in

def restrictInclusion : (w.restrict F).toValuationSubring →+* w.toValuationSubring where
  toFun a := ⟨algebraMap F F' (a : F), ValuationSubring.mem_comap.mp a.2⟩
  map_one' := Subtype.ext (map_one (algebraMap F F'))
  map_mul' a b := Subtype.ext (map_mul (algebraMap F F') (a : F) (b : F))
  map_zero' := Subtype.ext (map_zero (algebraMap F F'))
  map_add' a b := Subtype.ext (map_add (algebraMap F F') (a : F) (b : F))

@[simp]
theorem coe_restrictInclusion (a : (w.restrict F).toValuationSubring) :
    ((restrictInclusion F w a : w.toValuationSubring) : F') = algebraMap F F' (a : F) := rfl

instance instIsLocalHomRestrictInclusion : IsLocalHom (restrictInclusion F w) where
  map_nonunit a ha := by

    have hord : w.ord (algebraMap F F' (a : F)) = 0 := by
      have h := w.ord_coe_unit ha.unit
      rwa [IsUnit.unit_spec, coe_restrictInclusion] at h

    have ha0 : (a : F) ≠ 0 := by
      rintro h0
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
      have hb' : algebraMap F F' (a : F) * (b : F') = 1 := congrArg Subtype.val hb
      rw [h0, map_zero, zero_mul] at hb'
      exact zero_ne_one hb'
    exact (isUnit_mk_comap_iff ha0 a.2).mpr hord

variable (F) in

def restrictResidueMap : (w.restrict F).ResidueField →+* w.ResidueField :=
  IsLocalRing.ResidueField.map (restrictInclusion F w)

@[simp]
theorem restrictResidueMap_residue (a : (w.restrict F).toValuationSubring) :
    restrictResidueMap F w (IsLocalRing.residue _ a) =
      IsLocalRing.residue _ (restrictInclusion F w a) :=
  IsLocalRing.ResidueField.map_residue _ _

instance instAlgebraResidueFieldRestrictPushforward :
    Algebra (w.restrict F).ResidueField w.ResidueField :=
  (restrictResidueMap F w).toAlgebra

theorem algebraMap_residueField_eq :
    algebraMap (w.restrict F).ResidueField w.ResidueField = restrictResidueMap F w := rfl

instance instIsScalarTowerResidueFieldRestrictPushforward :
    IsScalarTower K (w.restrict F).ResidueField w.ResidueField := by
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show IsLocalRing.residue _ (algebraMap K w.toValuationSubring a) =
    restrictResidueMap F w
      (IsLocalRing.residue _ (algebraMap K (w.restrict F).toValuationSubring a))
  rw [restrictResidueMap_residue]
  refine congrArg _ (Subtype.ext ?_)
  show algebraMap K F' a = algebraMap F F' (algebraMap K F a)
  rw [← IsScalarTower.algebraMap_apply]

variable (F) in

/-- The inertia degree of `w` over its restriction to `F`. -/
def inertiaDeg : ℕ := Module.finrank (w.restrict F).ResidueField w.ResidueField

theorem deg_restrict_mul_inertiaDeg : (w.restrict F).deg * w.inertiaDeg F = w.deg :=
  Module.finrank_mul_finrank K (w.restrict F).ResidueField w.ResidueField

end Place

namespace Divisor

variable (F) in

/-- The pushforward of divisors, weighting each place by its inertia degree. -/
def pushforward : Divisor K F' →+ Divisor K F :=
  Finsupp.liftAddHom fun w =>
    (Finsupp.singleAddHom (w.restrict F)).comp (AddMonoidHom.mulRight (w.inertiaDeg F : ℤ))

theorem pushforward_apply [DecidableEq (Place K F)] (D : Divisor K F') (v : Place K F) :
    pushforward F D v =
      ∑ w ∈ D.support, if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0 := by
  classical
  rw [pushforward, Finsupp.liftAddHom_apply, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : w.restrict F = v <;> simp [Finsupp.single_apply, h]

variable (K F F') in

/-- The pushforward of the divisor of `f` is the divisor of its norm. -/
def PushforwardNormFormula [Module.Finite F F'] : Prop :=
  ∀ (f : F'), f ≠ 0 → ∀ D : Divisor K F', (∀ w, D w = w.ord f) →
    ∀ v : Place K F, pushforward F D v = v.ord (Algebra.norm F f)

theorem pushforward_eq_of_normFormula [Module.Finite F F']
    (H : PushforwardNormFormula K F F') {f : F'} (hf : f ≠ 0)
    {D : Divisor K F'} (hD : ∀ w, D w = w.ord f)
    {E : Divisor K F} (hE : ∀ v, E v = v.ord (Algebra.norm F f)) :
    pushforward F D = E :=
  Finsupp.ext fun v => (H f hf D hD v).trans (hE v).symm

end Divisor

end AlgebraicCurve

section

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

namespace Place

variable (F') in

/-- The places of `F'` lying over a place of `F`. -/
def fiber (v : Place K F) : Finset (Place K F') :=
  (restrict_fiber_finite v).toFinset

@[simp]
theorem mem_fiber {v : Place K F} {w : Place K F'} :
    w ∈ v.fiber F' ↔ w.restrict F = v := by
  simp only [fiber, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem restrict_mem_fiber (w : Place K F') : w ∈ (w.restrict F).fiber F' :=
  mem_fiber.mpr rfl

end Place

namespace Divisor

variable (F') in

def pullbackSingleHom (v : Place K F) : ℤ →+ Divisor K F' where
  toFun n := ∑ w ∈ v.fiber F', Finsupp.single w (n * w.ramificationIndex F)
  map_zero' := by simp
  map_add' m n := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by rw [add_mul, Finsupp.single_add]

variable (F') in

/-- The pullback of divisors, weighting each place by its ramification index. -/
def pullback : Divisor K F →+ Divisor K F' :=
  Finsupp.liftAddHom (pullbackSingleHom F')

theorem pullback_single (v : Place K F) (n : ℤ) :
    pullback F' (Finsupp.single v n)
      = ∑ w ∈ v.fiber F', Finsupp.single w (n * w.ramificationIndex F) :=
  Finsupp.liftAddHom_apply_single _ _ _

theorem pullback_single_apply_of_restrict_eq {v : Place K F} {w : Place K F'}
    (hw : w.restrict F = v) (n : ℤ) :
    pullback F' (Finsupp.single v n) w = n * w.ramificationIndex F := by
  rw [pullback_single, Finset.sum_apply']
  trans (Finsupp.single w (n * (w.ramificationIndex F : ℤ))) w
  · refine Finset.sum_eq_single_of_mem w (Place.mem_fiber.mpr hw) ?_
    intro b _ hb
    exact Finsupp.single_eq_of_ne' hb
  · exact Finsupp.single_eq_same

theorem pullback_single_apply_of_restrict_ne {v : Place K F} {w : Place K F'}
    (hw : w.restrict F ≠ v) (n : ℤ) :
    pullback F' (Finsupp.single v n) w = 0 := by
  rw [pullback_single, Finset.sum_apply']
  exact Finset.sum_eq_zero fun b hb =>
    Finsupp.single_eq_of_ne fun h => hw (h ▸ Place.mem_fiber.mp hb)

theorem pullback_apply (D : Divisor K F) (w : Place K F') :
    pullback F' D w = w.ramificationIndex F * D (w.restrict F) := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
    rw [map_add, Finsupp.add_apply, ih, Finsupp.add_apply, mul_add]
    congr 1
    by_cases hw : w.restrict F = v
    · subst hw
      rw [pullback_single_apply_of_restrict_eq rfl, Finsupp.single_eq_same, mul_comm]
    · rw [pullback_single_apply_of_restrict_ne hw,
        Finsupp.single_eq_of_ne hw, mul_zero]

theorem restrict_mem_support_of_mem_support_pullback {D : Divisor K F} {w : Place K F'}
    (hw : w ∈ (pullback F' D).support) : w.restrict F ∈ D.support := by
  rw [Finsupp.mem_support_iff] at hw ⊢
  intro h
  exact hw (by rw [pullback_apply, h, mul_zero])

theorem pullback_apply_eq_ord {f : F} {D : Divisor K F}
    (hD : ∀ v : Place K F, D v = v.ord f) (w : Place K F') :
    pullback F' D w = w.ord (algebraMap F F' f) := by
  rw [pullback_apply, hD, ← Place.ord_restrict]

end Divisor

namespace Divisor

end Divisor

end AlgebraicCurve

section

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

namespace Pic0

end Pic0

end AlgebraicCurve

end

section

section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

namespace Place

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem_593 {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

end SinglePlace

section IntegrallyClosed

open Polynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

theorem mem_of_eval_monic_eq_zero {P : Polynomial F} (hP : P.Monic)
    (hcoeff : ∀ i, P.coeff i ∈ w.toValuationSubring) {x : F} (hx : P.eval x = 0) :
    x ∈ w.toValuationSubring := by

  have hlift : P ∈ lifts (algebraMap w.toValuationSubring F) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨P.coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨Q, hQmap, -, hQmonic⟩ := lifts_and_degree_eq_and_monic hlift hP

  have hint : IsIntegral w.toValuationSubring x := by
    refine ⟨Q, hQmonic, ?_⟩
    rw [show eval₂ (algebraMap w.toValuationSubring F) x Q = (Q.map _).eval x from
      (eval_map _ x).symm, hQmap, hx]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact hy ▸ y.2

theorem mem_maximalIdeal_iff_ord_pos {x : F} (hx : x ≠ 0)
    (hmem : x ∈ w.toValuationSubring) :
    (⟨x, hmem⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring ↔
      0 < w.ord x := by
  have hnonneg : 0 ≤ w.ord x := w.ord_nonneg_of_mem_593 hmem
  have hcoe : ((⟨x, hmem⟩ : w.toValuationSubring) : F) = x := rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← w.adicValuation_coe_eq_one_iff,
    hcoe, ← w.ord_eq_zero_iff_adicValuation_eq_one hx]
  omega

end IntegrallyClosed

section Chart

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (w : Place K F)

def chartHom (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    R →+* w.toValuationSubring :=
  (algebraMap R F).codRestrict w.toValuationSubring.toSubring hw

variable (R) in

def center (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) : Ideal R :=
  (IsLocalRing.maximalIdeal w.toValuationSubring).comap (chartHom w hw)

instance (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    (center R w hw).IsPrime :=
  Ideal.comap_isPrime _ _

omit [IsDedekindDomain R] [IsFractionRing R F] in
theorem mem_center_iff (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) {r : R} :
    r ∈ center R w hw ↔
      (⟨algebraMap R F r, hw r⟩ : w.toValuationSubring) ∈
        IsLocalRing.maximalIdeal w.toValuationSubring :=
  Iff.rfl

theorem mem_center_iff_ord_pos (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring)
    {r : R} (hr : r ≠ 0) :
    r ∈ center R w hw ↔ 0 < w.ord (algebraMap R F r) := by
  have hr' : algebraMap R F r ≠ 0 := by
    simpa using (IsFractionRing.injective R F).ne_iff.mpr hr
  rw [mem_center_iff, w.mem_maximalIdeal_iff_ord_pos hr']

omit [IsDedekindDomain R] [IsFractionRing R F] in

theorem inv_algebraMap_mem (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring)
    {s : R} (hs : IsUnit (chartHom w hw s)) :
    (algebraMap R F s)⁻¹ ∈ w.toValuationSubring := by
  obtain ⟨u, hu⟩ := hs
  have hcoe : ((u : w.toValuationSubring) : F) = algebraMap R F s := by rw [hu]; rfl
  have h1 : (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F)
      * algebraMap R F s = 1 := by
    have hmul := congrArg (fun a : w.toValuationSubring => (a : F)) u.inv_mul
    push_cast at hmul
    rwa [hcoe] at hmul
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact SetLike.coe_mem _

theorem center_ne_bot (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    center R w hw ≠ ⊥ := by
  intro hbot
  apply w.ne_top'

  have hunit : ∀ r : R, r ≠ 0 → IsUnit (chartHom w hw r) := by
    intro r hr
    by_contra hu
    have : r ∈ center R w hw :=
      (mem_center_iff w hw).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu)
    rw [hbot] at this
    exact hr (by simpa using this)

  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := R) x
  rw [← hx, div_eq_mul_inv]
  exact mul_mem (hw a) (inv_algebraMap_mem w hw (hunit b (nonZeroDivisors.ne_zero hb)))

variable (R) in

def centerHeightOneSpectrum (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    HeightOneSpectrum R :=
  ⟨center R w hw, inferInstance, center_ne_bot w hw⟩

theorem valuationSubringAtPrime_centerHeightOneSpectrum_le
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    HeightOneSpectrum.valuationSubringAtPrime F (centerHeightOneSpectrum R w hw) ≤
      w.toValuationSubring := by
  rintro x ⟨a, s, hs, rfl⟩
  refine mul_mem (hw a) (inv_algebraMap_mem w hw ?_)
  rw [← IsLocalRing.notMem_maximalIdeal]
  exact fun hmem => hs ((mem_center_iff w hw).mpr hmem)

theorem toValuationSubring_eq_of_forall_mem
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    w.toValuationSubring =
      HeightOneSpectrum.valuationSubringAtPrime F (centerHeightOneSpectrum R w hw) :=
  (ValuationSubring.eq_of_le_of_ne_top _
    (valuationSubringAtPrime_centerHeightOneSpectrum_le w hw) w.ne_top').symm

end Chart

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

variable (F') in

@[reducible] def valuationSubringAlgebra (v : Place K F) : Algebra v.toValuationSubring F' :=
  ((algebraMap F F').comp (algebraMap v.toValuationSubring F)).toAlgebra

section Setup

variable (v : Place K F)

variable (F') in

/-- The integral closure in `F'` of the valuation ring of a place of `F`. -/
abbrev integralClosureAt : Type _ := integralClosure v.toValuationSubring F'

instance : IsDedekindDomain (integralClosureAt F' v) :=
  integralClosure.isDedekindDomain v.toValuationSubring F F'

instance : IsFractionRing (integralClosureAt F' v) F' :=
  integralClosure.isFractionRing_of_finite_extension (A := v.toValuationSubring) F F'

instance instFiniteIntegralClosureAt :
    Module.Finite v.toValuationSubring (integralClosureAt F' v) :=
  IsIntegralClosure.finite v.toValuationSubring F F' _

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] in

theorem algebraMap_integralClosureAt_injective :
    Function.Injective
      (algebraMap v.toValuationSubring (integralClosureAt F' v)) := by
  intro a b hab
  have h1 : algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) a)
        = algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) b) := by rw [hab]
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
  exact ((algebraMap F F').injective.comp
    (IsFractionRing.injective v.toValuationSubring F)) h1

instance instIsTorsionFreeIntegralClosureAt :
    Module.IsTorsionFree v.toValuationSubring (integralClosureAt F' v) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r c hrc
  rw [Algebra.smul_def] at hrc
  rcases mul_eq_zero.mp hrc with h | h
  · exact Or.inl (algebraMap_integralClosureAt_injective v (by rw [h, map_zero]))
  · exact Or.inr h

theorem maximalIdeal_ne_bot :
    IsLocalRing.maximalIdeal v.toValuationSubring ≠ ⊥ := by
  intro h
  exact ValuationSubring.not_isField_of_ne_top F v.ne_top'
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)

end Setup

section Center

variable {v : Place K F} {w : Place K F'}

omit [FiniteDimensional F F'] in

theorem forall_mem_of_restrict_eq (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    algebraMap (integralClosureAt F' v) F' c ∈ w.toValuationSubring := by
  obtain ⟨Q, hQmonic, hQeval⟩ := c.2
  have hOv : ∀ g : F, g ∈ v.toValuationSubring →
      algebraMap F F' g ∈ w.toValuationSubring := by
    intro g hg
    rw [← hw] at hg
    exact hg
  refine w.mem_of_eval_monic_eq_zero (P := Q.map (algebraMap v.toValuationSubring F'))
    (hQmonic.map _) (fun i => ?_) (by rw [Polynomial.eval_map]; exact hQeval)
  rw [Polynomial.coeff_map,
    IsScalarTower.algebraMap_apply v.toValuationSubring F F']
  exact hOv _ (Q.coeff i).2

variable (F' v) in

/-- The height-one prime of `integralClosureAt F' v` below a place `w` over `v`. -/
def fiberCenter (hw : w.restrict F = v) : HeightOneSpectrum (integralClosureAt F' v) :=
  centerHeightOneSpectrum (integralClosureAt F' v) w (forall_mem_of_restrict_eq hw)

theorem mem_fiberCenter_iff_ord_pos (hw : w.restrict F = v) {c : integralClosureAt F' v}
    (hc : c ≠ 0) :
    c ∈ (fiberCenter F' v hw).asIdeal ↔
      0 < w.ord (algebraMap (integralClosureAt F' v) F' c) :=
  mem_center_iff_ord_pos w (forall_mem_of_restrict_eq hw) hc

theorem toValuationSubring_eq_of_restrict_eq (hw : w.restrict F = v) :
    w.toValuationSubring =
      HeightOneSpectrum.valuationSubringAtPrime F' (fiberCenter F' v hw) :=
  toValuationSubring_eq_of_forall_mem w (forall_mem_of_restrict_eq hw)

theorem mem_maximalIdeal_iff_ord_pos' {r : v.toValuationSubring} (hr : r ≠ 0) :
    r ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔
      0 < v.ord (algebraMap v.toValuationSubring F r) := by
  have hrF : (algebraMap v.toValuationSubring F r : F) ≠ 0 := by
    simpa using (IsFractionRing.injective v.toValuationSubring F).ne_iff.mpr hr
  have := v.mem_maximalIdeal_iff_ord_pos hrF (Subtype.coe_prop r)
  simpa using this

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] in

theorem algebraMap_integralClosureAt_ne_zero {r : v.toValuationSubring} (hr : r ≠ 0) :
    algebraMap v.toValuationSubring (integralClosureAt F' v) r ≠ 0 := fun h =>
  hr (algebraMap_integralClosureAt_injective v (by rw [h, map_zero]))

omit [FiniteDimensional F F'] in

theorem ord_algebraMap_integralClosureAt (hw : w.restrict F = v) (r : v.toValuationSubring) :
    w.ord (algebraMap (integralClosureAt F' v) F'
        (algebraMap v.toValuationSubring (integralClosureAt F' v) r))
      = w.ramificationIndex F * v.ord (algebraMap v.toValuationSubring F r) := by
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply v.toValuationSubring F F', w.ord_restrict, hw]

theorem fiberCenter_liesOver (hw : w.restrict F = v) :
    (fiberCenter F' v hw).asIdeal.LiesOver
      (IsLocalRing.maximalIdeal v.toValuationSubring) := by
  refine ⟨?_⟩
  rw [Ideal.under_def]
  ext r
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  rw [Ideal.mem_comap,
    mem_fiberCenter_iff_ord_pos hw (algebraMap_integralClosureAt_ne_zero hr),
    ord_algebraMap_integralClosureAt hw, mem_maximalIdeal_iff_ord_pos' hr]
  have hepos : 0 < ramificationIndex (F := F) w := w.ramificationIndex_pos
  constructor
  · intro h
    positivity
  · intro h
    rcases mul_pos_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · omega

end Center

section Bijection

variable {v : Place K F}

def placeOfPrime (P : HeightOneSpectrum (integralClosureAt F' v)) : Place K F' where
  toValuationSubring := HeightOneSpectrum.valuationSubringAtPrime F' P
  algebraMap_mem' := fun a => by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
    have h1 : algebraMap K F' a = algebraMap (integralClosureAt F' v) F'
        (algebraMap v.toValuationSubring (integralClosureAt F' v)
          (algebraMap K v.toValuationSubring a)) := by
      rw [← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply v.toValuationSubring F F',
        ← IsScalarTower.algebraMap_apply K v.toValuationSubring F,
        ← IsScalarTower.algebraMap_apply K F F']
    rw [h1]
    exact P.valuation_le_one _
  ne_top' := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact isPrincipalIdealRing_valuationSubring P

@[simp]
theorem placeOfPrime_toValuationSubring (P : HeightOneSpectrum (integralClosureAt F' v)) :
    (placeOfPrime P).toValuationSubring = HeightOneSpectrum.valuationSubringAtPrime F' P :=
  rfl

theorem restrict_placeOfPrime (P : HeightOneSpectrum (integralClosureAt F' v)) :
    (placeOfPrime P).restrict F = v := by

  have hle : v.toValuationSubring ≤ ((placeOfPrime P).restrict F).toValuationSubring := by
    intro g hg
    rw [restrict_toValuationSubring, ValuationSubring.mem_comap,
      placeOfPrime_toValuationSubring,
      HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
    have h1 : algebraMap F F' g = algebraMap (integralClosureAt F' v) F'
        (algebraMap v.toValuationSubring (integralClosureAt F' v) ⟨g, hg⟩) := by
      rw [← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply v.toValuationSubring F F']
      rfl
    rw [h1]
    exact P.valuation_le_one _

  exact (Place.ext (ValuationSubring.eq_of_le_of_ne_top _ hle
    ((placeOfPrime P).restrict F).ne_top')).symm

theorem fiberCenter_placeOfPrime (P : HeightOneSpectrum (integralClosureAt F' v)) :
    fiberCenter F' v (restrict_placeOfPrime P) = P := by

  have h1 : HeightOneSpectrum.valuationSubringAtPrime F'
      (fiberCenter F' v (restrict_placeOfPrime P))
        = HeightOneSpectrum.valuationSubringAtPrime F' P := by
    rw [← toValuationSubring_eq_of_restrict_eq (restrict_placeOfPrime P),
      placeOfPrime_toValuationSubring]
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F') ?_
  rw [Valuation.isEquiv_iff_valuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring, h1]

theorem eq_of_fiberCenter_eq {w w' : Place K F'} (hw : w.restrict F = v)
    (hw' : w'.restrict F = v)
    (h : fiberCenter F' v hw = fiberCenter F' v hw') : w = w' := by
  refine Place.ext ?_
  rw [toValuationSubring_eq_of_restrict_eq hw, toValuationSubring_eq_of_restrict_eq hw', h]

end Bijection

section Fiber

variable (v : Place K F)

theorem finite_setOf_restrict_eq : {w : Place K F' | w.restrict F = v}.Finite := by
  classical
  let c : {w : Place K F' | w.restrict F = v} →
      (IsDedekindDomain.primesOverFinset (IsLocalRing.maximalIdeal v.toValuationSubring)
        (integralClosureAt F' v) : Set (Ideal (integralClosureAt F' v))) :=
    fun w => ⟨(fiberCenter F' v w.2).asIdeal, by
      rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)]
      exact ⟨(fiberCenter F' v w.2).isPrime, fiberCenter_liesOver w.2⟩⟩
  have hc : Function.Injective c := fun w w' h =>
    Subtype.ext (eq_of_fiberCenter_eq w.2 w'.2 (HeightOneSpectrum.ext (congrArg Subtype.val h)))
  haveI : Finite {w : Place K F' | w.restrict F = v} := Finite.of_injective c hc
  exact Set.toFinite _

variable (F') in

def fiberOver : Finset (Place K F') :=
  (finite_setOf_restrict_eq (F' := F') v).toFinset

@[simp]
theorem mem_fiberOver {w : Place K F'} : w ∈ v.fiberOver F' ↔ w.restrict F = v := by
  rw [fiberOver, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem fiber_eq_fiberOver [HasPrincipalDivisors K F'] : v.fiber F' = v.fiberOver F' :=
  Finset.ext fun w => by rw [mem_fiber, mem_fiberOver]

end Fiber

end Place

end AlgebraicCurve

end

end

section

open IsLocalRing AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.evalAt_algebraMap_eq_evalAt_restrict {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] (w : Place K F') (hv : (w.restrict F).IsRational) {g : F}
    (hg : g ∈ (w.restrict F).toValuationSubring) : w.evalAt (algebraMap F F' g) =
    (w.restrict F).evalAt g :=
    by
  have hg' : algebraMap F F' g ∈ w.toValuationSubring := ValuationSubring.mem_comap.mp hg
  have h2 : residue w.toValuationSubring (⟨algebraMap F F' g, hg'⟩ : w.toValuationSubring)
      = algebraMap K w.ResidueField ((w.restrict F).evalAt g) := by
    have h3 : (⟨algebraMap F F' g, hg'⟩ : w.toValuationSubring)
        = restrictInclusion F w ⟨g, hg⟩ := rfl
    rw [h3, ← restrictResidueMap_residue, ((w.restrict F).algebraMap_evalAt hv hg).symm]
    show restrictResidueMap F w
        (residue _ (algebraMap K (w.restrict F).toValuationSubring ((w.restrict F).evalAt g)))
      = residue _ (algebraMap K w.toValuationSubring ((w.restrict F).evalAt g))
    rw [restrictResidueMap_residue]
    refine congrArg _ (Subtype.ext ?_)
    show algebraMap F F' (algebraMap K F ((w.restrict F).evalAt g))
        = algebraMap K F' ((w.restrict F).evalAt g)
    rw [← IsScalarTower.algebraMap_apply]
  rw [w.evalAt_of_mem hg', h2, w.residueInv_algebraMap]

end

section

open AlgebraicCurve

theorem AlgebraicCurve.Place.inertiaDeg_eq_one_of_isRational {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] (w : Place K F') (hw : w.IsRational) (hv : (w.restrict F).IsRational)
    : w.inertiaDeg F = 1 := by
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [(AlgebraicCurve.Place.isRational_iff_deg_eq_one _).1 hv,
    (AlgebraicCurve.Place.isRational_iff_deg_eq_one _).1 hw, one_mul] at h
  exact h

end

section

open AlgebraicCurve AlgebraicCurve.Divisor

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
  exact hne (if_neg h)

end

section

section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

namespace Place

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem eq_ord_of_addHom_of_nonneg_iff_loc (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring))
    {x : F} (hx : x ≠ 0) : φ x = w.ord x := by
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

end Uniqueness

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

section ValuationDictionary

variable {v : Place K F} {w : Place K F'}

private theorem neg_log_valuation_fiberCenter_eq_ord_ram (hw : w.restrict F = v) {x : F'}
    (hx : x ≠ 0) :
    -log ((fiberCenter F' v hw).valuation F' x) = w.ord x := by
  refine eq_ord_of_addHom_of_nonneg_iff_loc w
    (fun y => -log ((fiberCenter F' v hw).valuation F' y)) ?_ ?_ ?_ hx
  ·
    intro a b ha hb
    show -log ((fiberCenter F' v hw).valuation F' (a * b)) =
      -log ((fiberCenter F' v hw).valuation F' a) +
        -log ((fiberCenter F' v hw).valuation F' b)
    rw [map_mul, log_mul ((Valuation.ne_zero_iff _).mpr ha) ((Valuation.ne_zero_iff _).mpr hb)]
    ring
  ·
    obtain ⟨t, ht⟩ := (fiberCenter F' v hw).valuation_exists_uniformizer F'
    refine ⟨t, ?_, ?_⟩
    · intro h
      rw [h, map_zero] at ht
      exact exp_ne_zero ht.symm
    · show -log ((fiberCenter F' v hw).valuation F' t) = 1
      rw [ht, log_exp]
      ring
  ·
    intro y hy
    have hy0 : (fiberCenter F' v hw).valuation F' y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    show 0 ≤ -log ((fiberCenter F' v hw).valuation F' y) ↔ y ∈ w.toValuationSubring
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

private theorem le_ord_iff_mem_pow_fiberCenter_ram (hw : w.restrict F = v)
    {c : integralClosureAt F' v} (hc : c ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) ↔
      c ∈ (fiberCenter F' v hw).asIdeal ^ n := by
  have hcF : algebraMap (integralClosureAt F' v) F' c ≠ 0 := by
    simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hc
  rw [← neg_log_valuation_fiberCenter_eq_ord_ram hw hcF,
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

private theorem ramificationIndex_eq_ramificationIdx_fiberCenter_aux (hw : w.restrict F = v) :
    w.ramificationIndex F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal := by

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

  refine (Ideal.ramificationIdx_spec ?_ ?_).symm
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      ← le_ord_iff_mem_pow_fiberCenter_ram hw hπC, hord]
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      ← le_ord_iff_mem_pow_fiberCenter_ram hw hπC, hord]
    have : 0 < w.ramificationIndex F := w.ramificationIndex_pos
    push_cast
    omega

end ValuationDictionary

end Place

end AlgebraicCurve

end

open AlgebraicCurve

theorem AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter {K F F' : Type*}
    [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F)
    {w : Place K F'} (hw : w.restrict F = v) : w.ramificationIndex F =
    (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
    (Place.fiberCenter F' v hw).asIdeal :=
  Place.ramificationIndex_eq_ramificationIdx_fiberCenter_aux hw

end

section

section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

namespace Place

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
private theorem residueOfCenter_apply (hw : w.restrict F = v) (c : integralClosureAt F' v) :
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

  haveI hmax : (fiberCenter F' v hw).asIdeal.IsMaximal :=
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

private theorem inertiaDeg_eq_inertiaDeg_fiberCenter_aux (hw : w.restrict F = v) :
    w.inertiaDeg F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg'
        (fiberCenter F' v hw).asIdeal := by
  haveI := fiberCenter_liesOver hw
  rw [Ideal.inertiaDeg_algebraMap]
  show Module.finrank (w.restrict F).ResidueField w.ResidueField = _
  refine Algebra.finrank_eq_of_equiv_equiv (restrictResidueFieldEquiv hw)
    (residueFieldEquivQuotientCenter hw).symm ?_

  ext a
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]

  apply (residueFieldEquivQuotientCenter hw).injective
  rw [RingEquiv.apply_symm_apply]

  show IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw
        (algebraMap v.toValuationSubring (integralClosureAt F' v) (placeCongrEquiv hw a)))
    = IsLocalRing.residue w.toValuationSubring (restrictInclusion F w a)

  refine congrArg _ (Subtype.ext ?_)
  show algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) (placeCongrEquiv hw a))
    = algebraMap F F' (a : F)
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply v.toValuationSubring F F']
  rfl

end ResidueDictionary

end Place

end AlgebraicCurve

end

open AlgebraicCurve

theorem AlgebraicCurve.Place.inertiaDeg_eq_inertiaDeg_fiberCenter {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F) {w : Place K F'}
    (hw : w.restrict F = v) : w.inertiaDeg F =
    (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg' (Place.fiberCenter F' v hw).asIdeal
    :=
  Place.inertiaDeg_eq_inertiaDeg_fiberCenter_aux hw

end

section

open IsDedekindDomain WithZero IsLocalRing AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.neg_log_valuation_fiberCenter_eq_ord {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} {w : Place K F'}
    (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) : -log ((fiberCenter F' v hw).valuation F' x) =
    w.ord x := by
  refine AlgebraicCurve.Place.eq_ord_of_addHom_of_nonneg_iff w
    (fun y => -log ((fiberCenter F' v hw).valuation F' y)) ?_ ?_ ?_ hx
  ·
    intro a b ha hb
    show -log ((fiberCenter F' v hw).valuation F' (a * b)) =
      -log ((fiberCenter F' v hw).valuation F' a) +
        -log ((fiberCenter F' v hw).valuation F' b)
    rw [map_mul, log_mul ((Valuation.ne_zero_iff _).mpr ha) ((Valuation.ne_zero_iff _).mpr hb)]
    ring
  ·
    obtain ⟨t, ht⟩ := (fiberCenter F' v hw).valuation_exists_uniformizer F'
    refine ⟨t, ?_, ?_⟩
    · intro h
      rw [h, map_zero] at ht
      exact exp_ne_zero ht.symm
    · show -log ((fiberCenter F' v hw).valuation F' t) = 1
      rw [ht, log_exp]
      ring
  ·
    intro y hy
    have hy0 : (fiberCenter F' v hw).valuation F' y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    show 0 ≤ -log ((fiberCenter F' v hw).valuation F' y) ↔ y ∈ w.toValuationSubring
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

end

section

open IsDedekindDomain WithZero IsLocalRing AlgebraicCurve AlgebraicCurve.Place

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

end

section

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid AlgebraicCurve
  AlgebraicCurve.Place

theorem AlgebraicCurve.Place.count_normalizedFactors_span_singleton {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} {w : Place K F'}
    (hw : w.restrict F = v) {c : integralClosureAt F' v} (hc : c ≠ 0) :
    (normalizedFactors (Ideal.span {c})).count (fiberCenter F' v hw).asIdeal =
    (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat := by
  haveI : (fiberCenter F' v hw).asIdeal.IsPrime := (fiberCenter F' v hw).isPrime

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

end

section

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid AlgebraicCurve
  AlgebraicCurve.Place

theorem AlgebraicCurve.Place.exists_integralClosureAt_of_ord_fiber_nonneg {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} [HasPrincipalDivisors K F']
    {f : F'} (hf : f ≠ 0) (hord : ∀ w ∈ v.fiber F', 0 ≤ w.ord f) : ∃ c : integralClosureAt F' v,
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
    have h2 := hord w (mem_fiber.mpr hw)
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
    ·
      have hPprime : Prime P := prime_of_normalized_factor P hP
      haveI : P.IsPrime := Ideal.isPrime_of_prime hPprime
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

end

section

open AlgebraicCurve

theorem AlgebraicCurve.Place.pairwiseDisjoint_fiber {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
    [HasPrincipalDivisors K F'] (s : Finset (Place K F)) : Set.PairwiseDisjoint
    (s : Set (Place K F)) (fun v : Place K F => v.fiber F') := by
  intro v₁ _ v₂ _ hne
  refine Finset.disjoint_left.mpr fun w hw₁ hw₂ => ?_
  exact hne ((Place.mem_fiber.mp hw₁).symm.trans (Place.mem_fiber.mp hw₂))

end

section

open AlgebraicCurve AlgebraicCurve.Divisor

theorem AlgebraicCurve.Divisor.support_pullback_subset {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] [DecidableEq (Place K F')]
    (E : Divisor K F) : (Divisor.pullback F' E).support ⊆ E.support.biUnion (fun v => v.fiber F') :=
    by
  classical
  intro w hw
  exact Finset.mem_biUnion.mpr ⟨w.restrict F,
    restrict_mem_support_of_mem_support_pullback hw, w.restrict_mem_fiber⟩

end

end

