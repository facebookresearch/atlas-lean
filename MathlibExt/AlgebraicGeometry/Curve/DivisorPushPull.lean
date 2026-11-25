/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_DivisorPushPull.lean`
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

public import MathlibExt.AlgebraicGeometry.Curve.DivisorClassGroup
import MathlibExt.AlgebraicGeometry.Curve.ExistsOrdPos
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Restriction of places and pushforward of divisors

This file defines the restriction of places along a field extension, ramification indices and
inertia degrees, and the pushforward of divisors.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

namespace Place

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

private theorem algebraMap_ne_zero {f : F} (hf : f ≠ 0) : algebraMap F F' f ≠ 0 := by
  simpa using hf

variable (w : Place K F')

theorem comap_algebraMap_ne_top [Algebra.IsIntegral F F'] :
    w.toValuationSubring.comap (algebraMap F F') ≠ ⊤ := by
  intro htop
  apply w.ne_top'
  have hF : ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring := fun f =>
    ValuationSubring.mem_comap.mp (htop ▸ ValuationSubring.mem_top f)
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  let : Algebra F w.toValuationSubring :=
    ((algebraMap F F').codRestrict w.toValuationSubring.toSubring hF).toAlgebra
  let : IsScalarTower F w.toValuationSubring F' :=
    IsScalarTower.of_algebraMap_eq fun f => rfl
  have hx : IsIntegral w.toValuationSubring x :=
    (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  exact hy ▸ y.2

variable {w} in
private theorem mem_comap_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.comap (algebraMap F F') ↔
      0 ≤ w.ord (algebraMap F F' f) := by
  rw [ValuationSubring.mem_comap]
  exact w.mem_iff_ord_nonneg (algebraMap_ne_zero hf)

variable {w} in
private theorem isUnit_mk_comap_iff {f : F} (hf : f ≠ 0)
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

private theorem exists_ord_algebraMap_pos [Algebra.IsIntegral F F'] :
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

private theorem ramificationIndex_set_nonempty :
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
  · rw [isUnit_mk_comap_iff hg0 hmem, hge]
    omega
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
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

theorem mem_restrict_iff {f : F} :
    f ∈ (w.restrict F).toValuationSubring ↔ algebraMap F F' f ∈ w.toValuationSubring :=
  Iff.rfl

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

noncomputable section

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
  change IsLocalRing.residue _ (algebraMap K w.toValuationSubring a) =
    restrictResidueMap F w
      (IsLocalRing.residue _ (algebraMap K (w.restrict F).toValuationSubring a))
  rw [restrictResidueMap_residue]
  refine congrArg _ (Subtype.ext ?_)
  change algebraMap K F' a = algebraMap F F' (algebraMap K F a)
  rw [← IsScalarTower.algebraMap_apply]

variable (F) in
def inertiaDeg : ℕ := Module.finrank (w.restrict F).ResidueField w.ResidueField

theorem deg_restrict_mul_inertiaDeg : (w.restrict F).deg * w.inertiaDeg F = w.deg :=
  Module.finrank_mul_finrank K (w.restrict F).ResidueField w.ResidueField

end Place

namespace Divisor

variable (F) in
def mapRestrict : Divisor K F' →+ Divisor K F :=
  Finsupp.liftAddHom fun w => Finsupp.singleAddHom (w.restrict F)

@[simp]
theorem mapRestrict_single (w : Place K F') (n : ℤ) :
    mapRestrict F (Finsupp.single w n) = Finsupp.single (w.restrict F) n := by
  simp [mapRestrict]

variable (F) in
def pushforward : Divisor K F' →+ Divisor K F :=
  Finsupp.liftAddHom fun w =>
    (Finsupp.singleAddHom (w.restrict F)).comp (AddMonoidHom.mulRight (w.inertiaDeg F : ℤ))

@[simp]
theorem pushforward_single (w : Place K F') (n : ℤ) :
    pushforward F (Finsupp.single w n) =
      Finsupp.single (w.restrict F) (n * w.inertiaDeg F) := by
  simp [pushforward]

@[simp]
theorem degree_pushforward (D : Divisor K F') :
    degree (pushforward F D) = degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add w n D hw hn ih =>
    simp only [map_add, pushforward_single, degree_single, ih]
    have h := w.deg_restrict_mul_inertiaDeg (F := F)
    push_cast [← h]
    ring

theorem pushforward_mem_degZero {D : Divisor K F'} (hD : D ∈ degZero (K := K) (F := F')) :
    pushforward F D ∈ degZero (K := K) (F := F) := by
  rwa [mem_degZero, degree_pushforward]

theorem pushforward_apply [DecidableEq (Place K F)] (D : Divisor K F') (v : Place K F) :
    pushforward F D v =
      ∑ w ∈ D.support, if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0 := by
  classical
  rw [pushforward, Finsupp.liftAddHom_apply, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : w.restrict F = v <;> simp [h]

variable (K F F') in
def PushforwardNormFormula [Module.Finite F F'] : Prop :=
  ∀ (f : F'), f ≠ 0 → ∀ D : Divisor K F', (∀ w, D w = w.ord f) →
    ∀ v : Place K F, pushforward F D v = v.ord (Algebra.norm F f)

theorem pushforward_eq_of_normFormula [Module.Finite F F']
    (H : PushforwardNormFormula K F F') {f : F'} (hf : f ≠ 0)
    {D : Divisor K F'} (hD : ∀ w, D w = w.ord f)
    {E : Divisor K F} (hE : ∀ v, E v = v.ord (Algebra.norm F f)) :
    pushforward F D = E :=
  Finsupp.ext fun v => (H f hf D hD v).trans (hE v).symm

theorem isPrincipal_pushforward_of_normFormula [Module.Finite F F']
    (H : PushforwardNormFormula K F F') {D : Divisor K F'} (hD : IsPrincipal D) :
    IsPrincipal (pushforward F D) := by
  obtain ⟨f, hf, hDf⟩ := hD
  exact ⟨Algebra.norm F f, Algebra.norm_ne_zero_iff.mpr hf, fun v => H f hf D hDf v⟩

end Divisor

end AlgebraicCurve

noncomputable section

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

namespace Place

variable (F') in
def fiber (v : Place K F) : Finset (Place K F') :=
  (restrict_fiber_finite v).toFinset

@[simp]
theorem mem_fiber {v : Place K F} {w : Place K F'} :
    w ∈ v.fiber F' ↔ w.restrict F = v := by
  simp only [fiber, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

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

theorem pullbackSingleHom_apply (v : Place K F) (n : ℤ) :
    pullbackSingleHom F' v n
      = ∑ w ∈ v.fiber F', Finsupp.single w (n * w.ramificationIndex F) :=
  rfl

variable (F') in
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

theorem isPrincipal_pullback {D : Divisor K F} (hD : D.IsPrincipal) :
    (pullback F' D).IsPrincipal := by
  obtain ⟨f, hf, hDf⟩ := hD
  exact ⟨algebraMap F F' f, by simpa using hf, fun w => pullback_apply_eq_ord hDf w⟩

theorem pullback_mem_principal {D : Divisor K F} (hD : D ∈ principal (K := K) (F := F)) :
    pullback F' D ∈ principal (K := K) (F := F') :=
  isPrincipal_pullback hD

end Divisor

variable (K F F') in
class FundamentalIdentity : Prop where
  sum_ramificationIndex_mul_deg : ∀ v : Place K F,
    ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = (Module.finrank F F' : ℤ) * (v.deg : ℤ)

namespace Divisor

theorem degree_pullback_single [FundamentalIdentity K F F'] (v : Place K F) (n : ℤ) :
    degree (pullback F' (Finsupp.single v n))
      = (Module.finrank F F' : ℤ) * degree (Finsupp.single v n) := by
  rw [pullback_single, map_sum, degree_single]
  simp_rw [degree_single, mul_assoc]
  rw [← Finset.mul_sum,
    FundamentalIdentity.sum_ramificationIndex_mul_deg (K := K) (F := F) (F' := F') v]
  ring

theorem degree_pullback [FundamentalIdentity K F F'] (D : Divisor K F) :
    degree (pullback F' D) = (Module.finrank F F' : ℤ) * degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
    rw [map_add, map_add, map_add, mul_add, ih, degree_pullback_single]

theorem pullback_mem_degZero [FundamentalIdentity K F F'] {D : Divisor K F}
    (hD : D ∈ degZero (K := K) (F := F)) :
    pullback F' D ∈ degZero (K := K) (F := F') := by
  rw [mem_degZero] at hD ⊢
  rw [degree_pullback, hD, mul_zero]

end Divisor

end AlgebraicCurve

noncomputable section

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

variable (K F F') in
class SumRamificationInertia : Prop where
  sum_ramificationIndex_mul_inertiaDeg : ∀ v : Place K F,
    ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)
      = (Module.finrank F F' : ℤ)

instance (priority := 100) instFundamentalIdentityOfSumRamificationInertia
    [SumRamificationInertia K F F'] : FundamentalIdentity K F F' where
  sum_ramificationIndex_mul_deg v := by
    have key := SumRamificationInertia.sum_ramificationIndex_mul_inertiaDeg
      (K := K) (F := F) (F' := F') v
    calc
      ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
          = ∑ w ∈ v.fiber F',
              (v.deg : ℤ) * ((w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)) := by
            refine Finset.sum_congr rfl fun w hw => ?_
            have htower : ((w.restrict F).deg : ℤ) * (w.inertiaDeg F : ℤ) = (w.deg : ℤ) := by
              exact_mod_cast congrArg (Nat.cast (R := ℤ))
                (w.deg_restrict_mul_inertiaDeg (F := F))
            rw [Place.mem_fiber.mp hw] at htower
            rw [← htower]; ring
      _ = (v.deg : ℤ) * ∑ w ∈ v.fiber F',
              (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) := by
            rw [Finset.mul_sum]
      _ = (Module.finrank F F' : ℤ) * (v.deg : ℤ) := by rw [key]; ring

namespace Pic0

variable (F') in
def pullbackDegZeroHom [FundamentalIdentity K F F'] :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F') :=
  ((Divisor.pullback F').domRestrict (Divisor.degZero (K := K) (F := F))).codRestrict _
    fun D => Divisor.pullback_mem_degZero D.2

@[simp]
theorem coe_pullbackDegZeroHom [FundamentalIdentity K F F']
    (D : Divisor.degZero (K := K) (F := F)) :
    (pullbackDegZeroHom F' D : Divisor K F') = Divisor.pullback F' (D : Divisor K F) := rfl

variable (F') in
def pullbackHom [FundamentalIdentity K F F'] : Pic0 K F →+ Pic0 K F' :=
  QuotientAddGroup.map _ _ (pullbackDegZeroHom F') (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.pullback_mem_principal hD)

theorem pullbackHom_mk [FundamentalIdentity K F F']
    (D : Divisor.degZero (K := K) (F := F)) :
    pullbackHom F' (mk D) = mk (pullbackDegZeroHom F' D) := rfl

variable (F) in
def pushforwardDegZeroHom :
    Divisor.degZero (K := K) (F := F') →+ Divisor.degZero (K := K) (F := F) :=
  ((Divisor.pushforward F).domRestrict (Divisor.degZero (K := K) (F := F'))).codRestrict _
    fun D => Divisor.pushforward_mem_degZero D.2

omit [HasPrincipalDivisors K F'] in
@[simp]
theorem coe_pushforwardDegZeroHom (D : Divisor.degZero (K := K) (F := F')) :
    (pushforwardDegZeroHom F D : Divisor K F) = Divisor.pushforward F (D : Divisor K F') := rfl

variable (K F F') in
def pushforwardHom [Module.Finite F F'] (H : Divisor.PushforwardNormFormula K F F') :
    Pic0 K F' →+ Pic0 K F :=
  QuotientAddGroup.map _ _ (pushforwardDegZeroHom F) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pushforward_of_normFormula H hD)

omit [HasPrincipalDivisors K F'] in
theorem pushforwardHom_mk [Module.Finite F F'] (H : Divisor.PushforwardNormFormula K F F')
    (D : Divisor.degZero (K := K) (F := F')) :
    pushforwardHom K F F' H (mk D) = mk (pushforwardDegZeroHom F D) := rfl

end Pic0

end AlgebraicCurve
