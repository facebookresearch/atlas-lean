/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean`
and
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean`
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

public import MathlibExt.AlgebraicGeometry.Curve.IsCurveOver
public import MathlibExt.AlgebraicGeometry.Curve.PoleDivisorPackage
public import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceInftyOrd
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Order.Int.LeastGreatest
import Mathlib.RingTheory.PicardGroup
import MathlibExt.AlgebraicGeometry.Curve.ExistsRestrict
import MathlibExt.AlgebraicGeometry.Curve.FundamentalIdentity
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceInftyDeg

/-!
# Existence of the genus for finite separable extensions of `K(x)`

This file proves that a finite separable extension `F` of the rational function field `RatFunc K`,
which is the function field of a curve over `K` with field of constants `K`, has a genus: `deg D -
ℓ(D)` is bounded above and attains its maximum. The proof bounds `deg D - ℓ(D)` through the pole
divisor of `x`, using the fundamental identity and the description of the places of `RatFunc K`.

## Main statement

* `AlgebraicCurve.RationalFunctionField.stichtenothGenusExists`
-/

namespace CurveGenus.RatFuncGenusExists

open Polynomial

namespace AlgebraicCurve
open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {D : Divisor K F}
private theorem lSpace_eq_bot_of_degree_neg [IsCurveOver K F]
    (hD : Divisor.degree D < 0) : LSpace D = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hf0
  obtain ⟨P, hPord, hPdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have heff : ∀ v : Place K F, 0 ≤ (P + D) v := by
    intro v
    rw [Finsupp.add_apply, hPord]
    rcases mem_lSpace_iff_ord.mp hf with rfl | h
    · exact absurd rfl hf0
    · linarith [h v]
  have hdegPD : 0 ≤ Divisor.degree (P + D) := Divisor.degree_nonneg_of_nonneg heff
  rw [map_add, hPdeg, zero_add] at hdegPD
  exact absurd hdegPD (not_le.mpr hD)
private theorem ell_eq_zero_of_degree_neg [IsCurveOver K F] (hD : Divisor.degree D < 0) :
    ell D = 0 := by
  rw [ell, lSpace_eq_bot_of_degree_neg hD, finrank_bot]
end AlgebraicCurve

noncomputable section

open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.IsDedekindDomain
open _root_.WithZero

namespace AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
open _root_.AlgebraicCurve.Place

variable (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.mk_mem_maximalIdeal_iff {f : F} (hf : f ∈
    v.toValuationSubring) :
    (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring
      ↔ f = 0 ∨ 0 < v.ord f := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hu
    rcases eq_or_ne f 0 with rfl | hf0
    · exact Or.inl rfl
    · refine Or.inr ?_
      rcases lt_or_eq_of_le (v.ord_nonneg_of_mem hf) with h | h
      · exact h
      · exfalso
        apply hu
        rw [← v.adicValuation_coe_eq_one_iff ⟨f, hf⟩]
        change v.adicValuation f = 1
        rw [v.adicValuation_eq_exp_neg_ord hf0, ← h, neg_zero, WithZero.exp_zero]
  · intro h hu
    have hne : f ≠ 0 := fun h0 => hu.ne_zero (Subtype.ext h0)
    have h0 : v.ord f = 0 := by
      obtain ⟨u, hu'⟩ := hu
      have hcoe : f = ((u : v.toValuationSubring) : F) := by rw [hu']
      rw [hcoe]; exact v.ord_coe_unit u
    rcases h with rfl | hpos
    · exact hne rfl
    · omega

end Place

private theorem ell_le_ell_sub_single_add_deg [IsCurveOver K F] (D : Divisor K F) (P : Place K F) :
    ell D ≤ ell (D - Finsupp.single P 1) + P.deg := by
  classical
  have : Module.Finite K P.ResidueField := IsCurveOver.finiteResidueField P
  set E : Divisor K F := D - Finsupp.single P 1 with hE
  have hEP : E P = D P - 1 := by rw [hE, Finsupp.sub_apply, Finsupp.single_eq_same]
  have hEv : ∀ v, v ≠ P → E v = D v := by
    intro v hv; rw [hE, Finsupp.sub_apply, Finsupp.single_eq_of_ne hv, sub_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  set t : F := (π : F) with ht
  have ht0 : t ≠ 0 := by
    simpa [ht, ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have ht1 : P.ord t = 1 := P.ord_coe_irreducible hπ
  have htn0 : t ^ (D P) ≠ 0 := zpow_ne_zero _ ht0
  have hordmul : ∀ {g : F}, g ≠ 0 → P.ord (t ^ (D P) * g) = D P + P.ord g := by
    intro g hg
    rw [P.ord_mul htn0 hg, P.ord_zpow, ht1, mul_one]
  have hmem : ∀ g : F, g ∈ LSpace D → t ^ (D P) * g ∈ P.toValuationSubring := by
    intro g hg
    rcases eq_or_ne g 0 with rfl | hg0
    · simp
    · refine P.mem_of_ord_nonneg (mul_ne_zero htn0 hg0) ?_
      rw [hordmul hg0]
      have := (mem_lSpace_iff_ord.mp hg).resolve_left hg0 P
      linarith
  let ψ : LSpace D →ₗ[K] P.toValuationSubring :=
    { toFun := fun f => ⟨t ^ (D P) * (f : F), hmem _ f.2⟩
      map_add' := by intro f g; apply Subtype.ext; push_cast; ring
      map_smul' := by
        intro c f; apply Subtype.ext
        simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def, MulMemClass.coe_mul,
          Place.coe_algebraMap]
        ring }
  let res : P.toValuationSubring →ₗ[K] P.ResidueField :=
    (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K
  have hres : ∀ x : P.toValuationSubring, res x = IsLocalRing.residue _ x := by
    intro x
    change (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K x = _
    rw [LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      IsLocalRing.ResidueField.algebraMap_eq]
  let φ : LSpace D →ₗ[K] P.ResidueField := res ∘ₗ ψ
  have hphi : ∀ f : LSpace D, φ f = 0 ↔
      (⟨t ^ (D P) * (f : F), hmem _ f.2⟩ : P.toValuationSubring)
        ∈ IsLocalRing.maximalIdeal P.toValuationSubring := by
    intro f
    rw [show φ f = IsLocalRing.residue P.toValuationSubring ⟨t ^ (D P) * (f : F), hmem _ f.2⟩
          from hres (ψ f),
      IsLocalRing.residue_eq_zero_iff]
  have hED : E ≤ D := by
    rw [Finsupp.le_def]; intro v; rw [hE, Finsupp.sub_apply]
    have : (0 : ℤ) ≤ Finsupp.single P 1 v := by
      rcases eq_or_ne v P with rfl | hv
      · simp
      · simp [Finsupp.single_eq_of_ne hv]
    linarith
  have hsub : LSpace E ≤ LSpace D := lSpace_mono hED
  have hker : LinearMap.ker φ = (LSpace E).comap (LSpace D).subtype := by
    ext f
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
    rw [hphi f, P.mk_mem_maximalIdeal_iff]
    rcases eq_or_ne (f : F) 0 with hf0 | hf0
    · simp only [hf0, mul_zero, true_or, true_iff]
      exact (LSpace E).zero_mem
    · rw [mem_lSpace_iff_ord]
      have hfD := (mem_lSpace_iff_ord.mp f.2).resolve_left hf0
      constructor
      · rintro (h | h)
        · exact absurd h (mul_ne_zero htn0 hf0)
        · refine Or.inr (fun v => ?_)
          rcases eq_or_ne v P with rfl | hv
          · rw [hEP]; rw [hordmul hf0] at h; omega
          · rw [hEv v hv]; exact hfD v
      · rintro (h | h)
        · exact absurd h hf0
        · refine Or.inr ?_
          have hP := h P
          rw [hEP] at hP
          rw [hordmul hf0]; omega
  have hkerfin : finrank K (LinearMap.ker φ) = ell E := by
    rw [hker, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hsub)]
    rfl
  have hquot : finrank K (LSpace D ⧸ LinearMap.ker φ) ≤ P.deg := by
    rw [LinearEquiv.finrank_eq φ.quotKerEquivRange]
    exact Submodule.finrank_le (LinearMap.range φ)
  by_cases hfin : FiniteDimensional K (LSpace D)
  · have := hfin
    have hrn := Submodule.finrank_quotient_add_finrank (LinearMap.ker φ)
    rw [hkerfin] at hrn
    have hb : ell D = finrank K (LSpace D) := rfl
    omega
  · have h0 : ell D = 0 := by rw [ell]; exact finrank_of_infinite_dimensional hfin
    omega

private theorem ell_le_degree_add_ellZero [IsCurveOver K F] {D : Divisor K F}
    (hD : ∀ v, 0 ≤ D v) :
    (ell D : ℤ) ≤ Divisor.degree D + ell (0 : Divisor K F) := by
  classical
  suffices H : ∀ m : ℕ, ∀ D : Divisor K F, (∀ v, 0 ≤ D v) →
      (Divisor.degree D).toNat = m →
      (ell D : ℤ) ≤ Divisor.degree D + ell (0 : Divisor K F) by
    exact H (Divisor.degree D).toNat D hD rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro D hD hm
    by_cases hD0 : D = 0
    · subst hD0; simp
    · obtain ⟨P, hP⟩ := Finsupp.support_nonempty_iff.mpr hD0
      have hPpos : 1 ≤ D P := by
        have hne : D P ≠ 0 := Finsupp.mem_support_iff.mp hP
        have := hD P; omega
      set E : Divisor K F := D - Finsupp.single P 1 with hE
      have hEeff : ∀ v, 0 ≤ E v := by
        intro v; rw [hE, Finsupp.sub_apply]
        rcases eq_or_ne v P with rfl | hv
        · rw [Finsupp.single_eq_same]; omega
        · rw [Finsupp.single_eq_of_ne hv, sub_zero]; exact hD v
      have hdegE : Divisor.degree E = Divisor.degree D - P.deg := by
        rw [hE, map_sub, Divisor.degree_single, one_mul]
      have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast IsCurveOver.one_le_deg P
      have hDnn : 0 ≤ Divisor.degree D := Divisor.degree_nonneg_of_nonneg hD
      have hEnn : 0 ≤ Divisor.degree E := Divisor.degree_nonneg_of_nonneg hEeff
      have hmlt : (Divisor.degree E).toNat < m := by rw [← hm]; omega
      have hIH := IH _ hmlt E hEeff rfl
      have hstep := ell_le_ell_sub_single_add_deg D P
      rw [← hE] at hstep
      have hstep' : (ell D : ℤ) ≤ (ell E : ℤ) + P.deg := by exact_mod_cast hstep
      rw [hdegE] at hIH
      linarith

private theorem ell_le_degree_add_one_of_effective [IsCurveOver K F]
    (hC : ConstantsAreBase K F) {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) :
    (ell D : ℤ) ≤ Divisor.degree D + 1 := by
  have h := ell_le_degree_add_ellZero hD
  rw [ell_zero_eq_one_of_constantsAreBase hC] at h
  exact_mod_cast h

private def lSpaceShiftEquiv (D : Divisor K F) {g : F} (hg : g ≠ 0)
    {Dg : Divisor K F} (hDg : ∀ v, Dg v = v.ord g) :
    LSpace D ≃ₗ[K] LSpace (D + Dg) where
  toFun h := ⟨(h : F) * g⁻¹, by
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (h : F) 0 with hh0 | hh0
    · left; rw [hh0, zero_mul]
    · right; intro v
      rw [Finsupp.add_apply, hDg, v.ord_mul hh0 (inv_ne_zero hg), v.ord_inv]
      have := (mem_lSpace_iff_ord.mp h.2).resolve_left hh0 v
      linarith⟩
  invFun k := ⟨(k : F) * g, by
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (k : F) 0 with hk0 | hk0
    · left; rw [hk0, zero_mul]
    · right; intro v
      have := (mem_lSpace_iff_ord.mp k.2).resolve_left hk0 v
      rw [Finsupp.add_apply, hDg] at this
      rw [v.ord_mul hk0 hg]
      linarith⟩
  map_add' h₁ h₂ := by apply Subtype.ext; push_cast; ring
  map_smul' c h := by
    apply Subtype.ext
    simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def]
    ring
  left_inv h := by
    apply Subtype.ext
    change (h : F) * g⁻¹ * g = (h : F)
    rw [mul_assoc, inv_mul_cancel₀ hg, mul_one]
  right_inv k := by
    apply Subtype.ext
    change (k : F) * g * g⁻¹ = (k : F)
    rw [mul_assoc, mul_inv_cancel₀ hg, mul_one]

private theorem ell_le_degree_add_one [IsCurveOver K F] (hC : ConstantsAreBase K F)
    {D : Divisor K F} (hD : 0 ≤ Divisor.degree D) :
    (ell D : ℤ) ≤ Divisor.degree D + 1 := by
  rcases eq_or_ne (ell D) 0 with h0 | h0
  · rw [h0]; push_cast; linarith
  · have hbot : LSpace D ≠ ⊥ := fun h => h0 (by rw [ell, h, finrank_bot])
    obtain ⟨g, hgL, hg0⟩ := (Submodule.ne_bot_iff _).mp hbot
    obtain ⟨Dg, hDgord, hDgdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg0
    have heff : ∀ v, 0 ≤ (D + Dg) v := by
      intro v; rw [Finsupp.add_apply, hDgord]
      have := (mem_lSpace_iff_ord.mp hgL).resolve_left hg0 v
      linarith
    have hdeg : Divisor.degree (D + Dg) = Divisor.degree D := by
      rw [map_add, hDgdeg, add_zero]
    have hell : ell D = ell (D + Dg) :=
      LinearEquiv.finrank_eq (lSpaceShiftEquiv D hg0 hDgord)
    have hfin := ell_le_degree_add_one_of_effective hC heff
    rw [hdeg] at hfin
    rw [hell]; exact hfin

end AlgebraicCurve

end

noncomputable section

open _root_.Module
open _root_.IsLocalRing
open _root_.Module.IsLocalRing
open _root_.IsDedekindDomain
open _root_.WithZero

namespace Submodule
open _root_.Submodule

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

private def nestedComapMapMkQEquiv {A B C : Submodule K X} (_hAB : A ≤ B) (hBC : B ≤ C) :
    ((B.comap C.subtype).map (A.comap C.subtype).mkQ : Submodule K _)
      ≃ₗ[K] B ⧸ A.comap B.subtype := by
  set S := A.comap C.subtype with hS
  set T := B.comap C.subtype with hT
  let ψ : (T : Type _) →ₗ[K] (C ⧸ S) := S.mkQ ∘ₗ T.subtype
  have hker : LinearMap.ker ψ = S.comap T.subtype := by
    simp only [ψ, LinearMap.ker_comp, ker_mkQ]
  have hran : LinearMap.range ψ = T.map S.mkQ := by
    simp only [ψ, LinearMap.range_comp, range_subtype]
  let e1 : (T ⧸ S.comap T.subtype) ≃ₗ[K] (T.map S.mkQ : Submodule K _) :=
    (Submodule.Quotient.equiv _ (LinearMap.ker ψ) (LinearEquiv.refl K T)
        (by rw [hker]; simp)).trans
      (ψ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hran))
  have hmap : (S.comap T.subtype).map
      (Submodule.comapSubtypeEquivOfLe hBC : (T : Type _) →ₗ[K] B) = A.comap B.subtype := by
    ext ⟨b, hb⟩
    simp only [mem_map, mem_comap, Submodule.coe_subtype, hS]
    constructor
    · rintro ⟨⟨⟨x, hxC⟩, hxB⟩, hxA, hxeq⟩
      have hx : x = b := congrArg Subtype.val hxeq
      subst hx; exact hxA
    · intro hbA
      exact ⟨⟨⟨b, hBC hb⟩, hb⟩, hbA, rfl⟩
  let e2 : (T ⧸ S.comap T.subtype) ≃ₗ[K] (B ⧸ A.comap B.subtype) :=
    Submodule.Quotient.equiv _ _ (Submodule.comapSubtypeEquivOfLe hBC) hmap
  exact e1.symm.trans e2

private theorem finrank_quotient_chain {A B C : Submodule K X} (hAB : A ≤ B) (hBC : B ≤ C)
    [hCB : Module.Finite K (C ⧸ B.comap C.subtype)]
    [hBA : Module.Finite K (B ⧸ A.comap B.subtype)] :
    Module.Finite K (C ⧸ A.comap C.subtype) ∧
      finrank K (C ⧸ A.comap C.subtype)
        = finrank K (C ⧸ B.comap C.subtype) + finrank K (B ⧸ A.comap B.subtype) := by
  set S := A.comap C.subtype
  set T := B.comap C.subtype
  have hST : S ≤ T := comap_mono hAB
  have e3 := Submodule.quotientQuotientEquivQuotient S T hST
  have eK := nestedComapMapMkQEquiv (K := K) hAB hBC
  have : Module.Finite K (T.map S.mkQ : Submodule K _) := Module.Finite.equiv eK.symm
  have : Module.Finite K ((C ⧸ S) ⧸ T.map S.mkQ) := Module.Finite.equiv e3.symm
  have hfin : Module.Finite K (C ⧸ S) := Module.Finite.of_submodule_quotient (T.map S.mkQ)
  refine ⟨hfin, ?_⟩
  have h := Submodule.finrank_quotient_add_finrank (R := K) (T.map S.mkQ)
  rw [LinearEquiv.finrank_eq e3, LinearEquiv.finrank_eq eK] at h
  omega

private theorem finrank_quotient_chain' {A B C : Submodule K X} (hAB : A ≤ B) (hBC : B ≤ C)
    [hCA : Module.Finite K (C ⧸ A.comap C.subtype)] :
    Module.Finite K (C ⧸ B.comap C.subtype) ∧
      finrank K (C ⧸ B.comap C.subtype)
        = finrank K (C ⧸ A.comap C.subtype) - finrank K (B ⧸ A.comap B.subtype) := by
  set S := A.comap C.subtype
  set T := B.comap C.subtype
  have hST : S ≤ T := comap_mono hAB
  have e3 := Submodule.quotientQuotientEquivQuotient S T hST
  have eK := nestedComapMapMkQEquiv (K := K) hAB hBC
  have : Module.Finite K (C ⧸ T) := Module.Finite.equiv e3
  refine ⟨this, ?_⟩
  have h := Submodule.finrank_quotient_add_finrank (R := K) (T.map S.mkQ)
  rw [LinearEquiv.finrank_eq e3, LinearEquiv.finrank_eq eK] at h
  omega

end Submodule

namespace AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private def adeleBddQuotSingleEquivResidueField (D : Divisor K F) (P : Place K F) :
    (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype)
      ≃ₗ[K] P.ResidueField := by
  classical
  set E : Divisor K F := D - Finsupp.single P 1 with hE
  have hEP : E P = D P - 1 := by rw [hE, Finsupp.sub_apply, Finsupp.single_eq_same]
  have hEv : ∀ v, v ≠ P → E v = D v := by
    intro v hv; rw [hE, Finsupp.sub_apply, Finsupp.single_eq_of_ne hv, sub_zero]
  let π : P.toValuationSubring :=
    (IsDiscreteValuationRing.exists_irreducible P.toValuationSubring).choose
  have hπ : Irreducible π :=
    (IsDiscreteValuationRing.exists_irreducible P.toValuationSubring).choose_spec
  set t : F := (π : F) with ht
  have ht0 : t ≠ 0 := by simpa [ht, ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have ht1 : P.ord t = 1 := P.ord_coe_irreducible hπ
  have htn0 : t ^ (D P) ≠ 0 := zpow_ne_zero _ ht0
  have hordmul : ∀ {g : F}, g ≠ 0 → P.ord (t ^ (D P) * g) = D P + P.ord g := fun {g} hg => by
    rw [P.ord_mul htn0 hg, P.ord_zpow, ht1, mul_one]
  have hmem : ∀ α : Place K F → F, α ∈ adeleBdd D → t ^ (D P) * α P ∈ P.toValuationSubring := by
    intro α hα
    rcases eq_or_ne (α P) 0 with hg0 | hg0
    · simp [hg0]
    · refine P.mem_of_ord_nonneg (mul_ne_zero htn0 hg0) ?_
      rw [hordmul hg0]
      have h := hα P
      rw [P.adicValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp] at h
      linarith
  let ψ : adeleBdd D →ₗ[K] P.toValuationSubring :=
    { toFun := fun α => ⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩
      map_add' := by
        intro α β; apply Subtype.ext
        simp only [Submodule.coe_add, Pi.add_apply]
        push_cast; ring
      map_smul' := by
        intro c α; apply Subtype.ext
        simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def, MulMemClass.coe_mul,
          Place.coe_algebraMap, Pi.smul_apply]
        ring }
  have hψ_apply : ∀ α : adeleBdd D,
      (ψ α : F) = t ^ (D P) * (α : Place K F → F) P := fun α => rfl
  let res : P.toValuationSubring →ₗ[K] P.ResidueField :=
    (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K
  have hres : ∀ x : P.toValuationSubring, res x = IsLocalRing.residue _ x := by
    intro x
    change (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K x = _
    rw [LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      IsLocalRing.ResidueField.algebraMap_eq]
  let φ : adeleBdd D →ₗ[K] P.ResidueField := res ∘ₗ ψ
  have hphi : ∀ α : adeleBdd D, φ α = 0 ↔
      (⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩ : P.toValuationSubring)
        ∈ IsLocalRing.maximalIdeal P.toValuationSubring := fun α => by
    rw [show φ α = IsLocalRing.residue P.toValuationSubring
            ⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩ from hres (ψ α),
      IsLocalRing.residue_eq_zero_iff]
  have hker : LinearMap.ker φ = (adeleBdd E).comap (adeleBdd D).subtype := by
    ext α
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
    rw [hphi α, P.mk_mem_maximalIdeal_iff, mem_adeleBdd]
    have hαD := α.2
    constructor
    · rintro (h | h) v
      · have hα0 : (α : Place K F → F) P = 0 := by
          rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' htn0
          · exact h'
        by_cases hv : v = P
        · subst v; rw [hα0, Valuation.map_zero]; exact zero_le
        · rw [hEv v hv]; exact hαD v
      · by_cases hv : v = P
        · subst v
          rcases eq_or_ne ((α : Place K F → F) P) 0 with hα0 | hα0
          · rw [hα0, Valuation.map_zero]; exact zero_le
          · rw [P.adicValuation_eq_exp_neg_ord hα0, WithZero.exp_le_exp, hEP]
            rw [hordmul hα0] at h; omega
        · rw [hEv v hv]; exact hαD v
    · intro h
      rcases eq_or_ne ((α : Place K F → F) P) 0 with hα0 | hα0
      · left; rw [hα0, mul_zero]
      · right
        have hP := h P
        rw [P.adicValuation_eq_exp_neg_ord hα0, WithZero.exp_le_exp, hEP] at hP
        rw [hordmul hα0]; omega
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨cl, hcl⟩ := IsLocalRing.residue_surjective (R := P.toValuationSubring) c
    set f : F := (cl : F) * t ^ (-(D P)) with hf
    have hαD : Pi.single P f ∈ adeleBdd D := by
      intro v
      by_cases hv : v = P
      · subst v
        simp only [Pi.single_eq_same]
        rcases eq_or_ne (cl : F) 0 with hc0 | hc0
        · rw [hf, hc0, zero_mul, Valuation.map_zero]; exact zero_le
        · have hf0 : f ≠ 0 := by rw [hf]; exact mul_ne_zero hc0 (zpow_ne_zero _ ht0)
          rw [P.adicValuation_eq_exp_neg_ord hf0, WithZero.exp_le_exp]
          rw [hf, P.ord_mul hc0 (zpow_ne_zero _ ht0), P.ord_zpow, ht1, mul_one]
          have hclnn := P.ord_nonneg_of_mem cl.2
          linarith
      · rw [Pi.single_eq_of_ne hv, Valuation.map_zero]; exact zero_le
    refine ⟨⟨Pi.single P f, hαD⟩, ?_⟩
    change res (ψ ⟨Pi.single P f, hαD⟩) = c
    rw [hres]
    rw [show (ψ ⟨Pi.single P f, hαD⟩ : P.toValuationSubring) = cl from ?_, hcl]
    apply Subtype.ext
    rw [hψ_apply]
    change t ^ (D P) * (Pi.single P f : Place K F → F) P = (cl : F)
    rw [show (Pi.single P f : Place K F → F) P = f from Pi.single_eq_same _ _, hf,
      mul_comm (cl : F), ← mul_assoc, ← zpow_add₀ ht0, add_neg_cancel, zpow_zero, one_mul]
  exact (Submodule.Quotient.equiv _ _ (LinearEquiv.refl K _) (by rw [← hker]; simp)).trans
    (φ.quotKerEquivOfSurjective hsurj)

private theorem finrank_adeleBdd_quotient_single [IsCurveOver K F] (D : Divisor K F) (P : Place K
    F) :
    Module.Finite K
        (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype) ∧
      finrank K
          (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype)
        = P.deg := by
  have := IsCurveOver.finiteResidueField (K := K) P
  exact ⟨Module.Finite.equiv (adeleBddQuotSingleEquivResidueField D P).symm,
    (adeleBddQuotSingleEquivResidueField D P).finrank_eq⟩

private theorem finrank_adeleBdd_quotient [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    Module.Finite K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) ∧
      (finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ)
        = Divisor.degree D₂ - Divisor.degree D₁ := by
  classical
  suffices H : ∀ m : ℕ, ∀ D₁ D₂ : Divisor K F, D₁ ≤ D₂ →
      (Divisor.degree (D₂ - D₁)).toNat = m →
      Module.Finite K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) ∧
        (finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ)
          = Divisor.degree D₂ - Divisor.degree D₁ from
    H _ D₁ D₂ hD rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro D₁ D₂ hD hm
    have hEeff : ∀ v, 0 ≤ (D₂ - D₁) v := fun v => by
      rw [Finsupp.sub_apply]; have := hD v; omega
    by_cases hD0 : D₂ - D₁ = 0
    · have hD12 : D₁ = D₂ := (sub_eq_zero.mp hD0).symm
      subst hD12
      rw [Submodule.comap_subtype_self]
      have : Subsingleton (adeleBdd D₁ ⧸ (⊤ : Submodule K (adeleBdd D₁))) :=
        Submodule.Quotient.subsingleton_iff.mpr rfl
      exact ⟨Module.Finite.of_finite, by simp [Module.finrank_zero_of_subsingleton]⟩
    · obtain ⟨P, hP⟩ := Finsupp.support_nonempty_iff.mpr hD0
      have hPpos : 1 ≤ (D₂ - D₁) P := by
        have hne : (D₂ - D₁) P ≠ 0 := Finsupp.mem_support_iff.mp hP
        have := hEeff P; omega
      set D₂' : Divisor K F := D₂ - Finsupp.single P 1 with hD₂'
      have h12' : D₁ ≤ D₂' := by
        intro v; rw [hD₂', Finsupp.sub_apply]
        by_cases hv : v = P
        · subst v; rw [Finsupp.single_eq_same]
          have := hPpos; rw [Finsupp.sub_apply] at this; omega
        · rw [Finsupp.single_eq_of_ne hv, sub_zero]; exact hD v
      have h2'2 : D₂' ≤ D₂ := by
        intro v; rw [hD₂', Finsupp.sub_apply]
        by_cases hv : v = P
        · subst v; rw [Finsupp.single_eq_same]; omega
        · rw [Finsupp.single_eq_of_ne hv, sub_zero]
      have hdegD₂' : Divisor.degree D₂' = Divisor.degree D₂ - P.deg := by
        rw [hD₂', map_sub, Divisor.degree_single, one_mul]
      have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast IsCurveOver.one_le_deg P
      have hEnn : 0 ≤ Divisor.degree (D₂ - D₁) := Divisor.degree_nonneg_of_nonneg hEeff
      have hE'nn : 0 ≤ Divisor.degree (D₂' - D₁) := Divisor.degree_nonneg_of_nonneg
        (fun v => by rw [Finsupp.sub_apply]; have := h12' v; omega)
      have hdegdiff : Divisor.degree (D₂' - D₁) = Divisor.degree (D₂ - D₁) - P.deg := by
        simp only [hD₂', map_sub, Divisor.degree_single, one_mul]; ring
      have hmlt : (Divisor.degree (D₂' - D₁)).toNat < m := by rw [← hm]; omega
      obtain ⟨hfin', hrank'⟩ := IH _ hmlt D₁ D₂' h12' rfl
      obtain ⟨hfinS, hrankS⟩ := finrank_adeleBdd_quotient_single (K := K) D₂ P
      rw [← hD₂'] at hfinS hrankS
      have := hfin'; have := hfinS
      obtain ⟨hfin, hrank⟩ := Submodule.finrank_quotient_chain
        (A := adeleBdd D₁) (B := adeleBdd D₂') (C := adeleBdd D₂)
        (adeleBdd_mono h12') (adeleBdd_mono h2'2)
      refine ⟨hfin, ?_⟩
      rw [hrank, hrankS]
      push_cast
      linarith [hrank', hdegD₂']

private theorem module_finite_adeleBdd_quotient [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁
    ≤ D₂) :
    Module.Finite K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) :=
  (finrank_adeleBdd_quotient hD).1

private theorem finrank_adeleBdd_quotient_eq [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁
    ≤ D₂) :
    (finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ)
      = Divisor.degree D₂ - Divisor.degree D₁ :=
  (finrank_adeleBdd_quotient hD).2

private def lSpaceQuotientToAdeleBddQuotient {D₁ D₂ : Divisor K F} (_hD : D₁ ≤ D₂) :
    (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype)
      →ₗ[K] (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) :=
  Submodule.mapQ _ _
    ((diagonalHom K F).restrict
      (p := (LSpace D₂ : Submodule K F)) (q := (adeleBdd D₂ : Submodule K _))
      (fun f hf => diagonal_mem_adeleBdd_iff.mpr hf))
    (fun f hf => by
      simp only [Submodule.mem_comap, Submodule.coe_subtype] at hf ⊢
      exact diagonal_mem_adeleBdd_iff.mpr hf)

private theorem lSpaceQuotientToAdeleBddQuotient_injective {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    Function.Injective (lSpaceQuotientToAdeleBddQuotient hD) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]
  rw [show (lSpaceQuotientToAdeleBddQuotient hD) (Submodule.Quotient.mk f)
        = Submodule.Quotient.mk ((diagonalHom K F).restrict
            (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) f) from rfl,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype] at hx
  exact diagonal_mem_adeleBdd_iff.mp hx

private theorem ell_sub_ell_le_degree_sub_degree [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁
    ≤ D₂)
    [FiniteDimensional K (LSpace D₂)] :
    (ell D₂ : ℤ) - (ell D₁ : ℤ) ≤ Divisor.degree D₂ - Divisor.degree D₁ := by
  have := module_finite_adeleBdd_quotient hD
  have hℓ₁ : ell D₁ = finrank K ((LSpace D₁).comap (LSpace D₂).subtype) :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (lSpace_mono hD))).symm
  have hL : ell D₂
      = finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) + ell D₁ := by
    rw [hℓ₁]; exact (Submodule.finrank_quotient_add_finrank _).symm
  have hemb : finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype)
      ≤ finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) :=
    LinearMap.finrank_le_finrank_of_injective (lSpaceQuotientToAdeleBddQuotient_injective hD)
  have hloc := finrank_adeleBdd_quotient_eq hD
  have : (ell D₂ : ℤ) - (ell D₁ : ℤ)
      = (finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) : ℤ) := by
    rw [hL]; push_cast; ring
  rw [this, ← hloc]
  exact_mod_cast hemb

private theorem adeleBdd_inf_sup_globalSub {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    adeleBdd D₂ ⊓ (adeleBdd D₁ ⊔ globalSub K F)
      = adeleBdd D₁ ⊔ adeleBdd D₂ ⊓ globalSub K F := by
  rw [inf_comm, sup_inf_assoc_of_le _ (adeleBdd_mono hD), inf_comm]

private theorem map_diagonal_lSpace_inf_adeleBdd {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    (LSpace D₂).map (diagonalHom K F) ⊓ adeleBdd D₁ = (LSpace D₁).map (diagonalHom K F) := by
  rw [map_diagonal_lSpace, map_diagonal_lSpace, inf_right_comm,
    inf_eq_right.mpr (adeleBdd_mono hD)]

private theorem gate_finrank_adeleBdd_quotient_single_point [IsCurveOver K F] (P : Place K F) :
    (finrank K (adeleBdd (Finsupp.single P 1 : Divisor K F)
        ⧸ (adeleBdd (0 : Divisor K F)).comap (adeleBdd (Finsupp.single P 1)).subtype) : ℤ)
      = (P.deg : ℤ) := by
  classical
  have h01 : (0 : Divisor K F) ≤ Finsupp.single P 1 := by
    intro v; rw [Finsupp.zero_apply, Finsupp.single_apply]; split_ifs <;> omega
  have h := finrank_adeleBdd_quotient_eq (K := K) h01
  rw [h, map_zero, sub_zero, Divisor.degree_single, one_mul]

end AlgebraicCurve

end

noncomputable section

open Module IsDedekindDomain WithZero

namespace Submodule
open _root_.Submodule

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

private theorem comap_subtype_sup_of_le_of_le {S T C : Submodule K X} (hS : S ≤ C) (hT : T ≤ C) :
    S.comap C.subtype ⊔ T.comap C.subtype = (S ⊔ T).comap C.subtype := by
  apply Submodule.map_injective_of_injective (f := C.subtype) C.subtype_injective
  rw [Submodule.map_sup, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
    Submodule.map_comap_subtype, inf_eq_right.mpr hS, inf_eq_right.mpr hT,
    inf_eq_right.mpr (sup_le hS hT)]

private theorem finrank_quotient_chain_top {M : Type*} [AddCommGroup M] [Module K M]
    {A B : Submodule K M} (hAB : A ≤ B)
    [hMB : Module.Finite K (M ⧸ B)] [hBA : Module.Finite K (B ⧸ A.comap B.subtype)] :
    Module.Finite K (M ⧸ A) ∧
      finrank K (M ⧸ A) = finrank K (M ⧸ B) + finrank K (B ⧸ A.comap B.subtype) := by
  have e3 := Submodule.quotientQuotientEquivQuotient A B hAB
  let ψ : (B : Type _) →ₗ[K] (M ⧸ A) := A.mkQ ∘ₗ B.subtype
  have hker : LinearMap.ker ψ = A.comap B.subtype := by
    simp only [ψ, LinearMap.ker_comp, ker_mkQ]
  have hran : LinearMap.range ψ = B.map A.mkQ := by
    simp only [ψ, LinearMap.range_comp, range_subtype]
  let eK : (B ⧸ A.comap B.subtype) ≃ₗ[K] (B.map A.mkQ : Submodule K (M ⧸ A)) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (ψ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hran))
  have : Module.Finite K (B.map A.mkQ : Submodule K (M ⧸ A)) := Module.Finite.equiv eK
  have : Module.Finite K ((M ⧸ A) ⧸ B.map A.mkQ) := Module.Finite.equiv e3.symm
  have hfin : Module.Finite K (M ⧸ A) := Module.Finite.of_submodule_quotient (B.map A.mkQ)
  refine ⟨hfin, ?_⟩
  have h := Submodule.finrank_quotient_add_finrank (R := K) (B.map A.mkQ)
  rw [LinearEquiv.finrank_eq e3, ← LinearEquiv.finrank_eq eK] at h
  omega

end Submodule

namespace AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem globalSub_le_adeleSpace [HasPrincipalDivisors K F] :
    globalSub K F ≤ adeleSpace K F := by
  rintro _ ⟨f, rfl⟩
  exact diagonal_mem_adeleSpace f

private theorem adeleBdd_sup_globalSub_le_adeleSpace [HasPrincipalDivisors K F] (D : Divisor K F) :
    adeleBdd D ⊔ globalSub K F ≤ adeleSpace K F :=
  sup_le adeleBdd_le_adeleSpace globalSub_le_adeleSpace

private theorem adeleBddPrincipal_eq_comap [HasPrincipalDivisors K F] (D : Divisor K F) :
    adeleBddPrincipal K F D = (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype :=
  Submodule.comap_subtype_sup_of_le_of_le adeleBdd_le_adeleSpace globalSub_le_adeleSpace

private theorem adeleBddPrincipal_mono {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    adeleBddPrincipal K F D₁ ≤ adeleBddPrincipal K F D₂ :=
  sup_le_sup_right (Submodule.comap_mono (adeleBdd_mono hD)) _

section FiniteLSpace

variable [IsCurveOver K F] [Nonempty (Place K F)]

omit [Nonempty (Place K F)] in
private theorem finiteDimensional_lSpace [hL0 : FiniteDimensional K (LSpace (0 : Divisor K F))]
    (D : Divisor K F) : FiniteDimensional K (LSpace D) := by
  have h0D : (0 : Divisor K F) ≤ D ⊔ 0 := le_sup_right
  have hDD : D ≤ D ⊔ 0 := le_sup_left
  suffices h : FiniteDimensional K (LSpace (D ⊔ 0)) by
    exact Module.Finite.of_injective (Submodule.inclusion (lSpace_mono hDD))
      (Submodule.inclusion_injective _)
  have := module_finite_adeleBdd_quotient (K := K) h0D
  have hfinQ : FiniteDimensional K
      (LSpace (D ⊔ 0) ⧸ (LSpace (0 : Divisor K F)).comap (LSpace (D ⊔ 0)).subtype) :=
    Module.Finite.of_injective _ (lSpaceQuotientToAdeleBddQuotient_injective h0D)
  have : FiniteDimensional K
      ((LSpace (0 : Divisor K F)).comap (LSpace (D ⊔ 0)).subtype : Submodule K _) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (lSpace_mono h0D)).symm
  exact Module.Finite.of_submodule_quotient
    ((LSpace (0 : Divisor K F)).comap (LSpace (D ⊔ 0)).subtype)

end FiniteLSpace

private theorem range_lSpaceQuotientToAdeleBddQuotient {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    LinearMap.range (lSpaceQuotientToAdeleBddQuotient hD)
      = ((adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype).map
          ((adeleBdd D₁).comap (adeleBdd D₂).subtype).mkQ := by
  classical
  ext z
  obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  simp only [LinearMap.mem_range, Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype,
    Submodule.mkQ_apply]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hxeq : Submodule.Quotient.mk
        ((diagonalHom K F).restrict (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) f)
        = (Submodule.Quotient.mk α :
            adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) := hx
    refine ⟨α, ?_, rfl⟩
    have hdiag2 : (diagonalHom K F (f : F)) ∈ adeleBdd D₂ := diagonal_mem_adeleBdd_iff.mpr f.2
    have hsub : (α : Place K F → F) - diagonalHom K F (f : F) ∈ adeleBdd D₁ := by
      have hq := (Submodule.Quotient.eq _).mp hxeq.symm
      simpa using hq
    refine Submodule.mem_sup.mpr ⟨(α : Place K F → F) - diagonalHom K F (f : F), hsub,
      diagonalHom K F (f : F), diagonal_mem_globalSub _, ?_⟩
    abel
  · rintro ⟨β, hβ, hβeq⟩
    have hβ' : (β : Place K F → F) ∈ adeleBdd D₂ ⊓ (adeleBdd D₁ ⊔ globalSub K F) :=
      Submodule.mem_inf.mpr ⟨β.2, hβ⟩
    rw [adeleBdd_inf_sup_globalSub hD, ← map_diagonal_lSpace] at hβ'
    obtain ⟨γ, hγ, δ, ⟨f, hf, hfδ⟩, hsum⟩ := Submodule.mem_sup.mp hβ'
    refine ⟨Submodule.Quotient.mk ⟨f, hf⟩, ?_⟩
    rw [show (lSpaceQuotientToAdeleBddQuotient hD) (Submodule.Quotient.mk ⟨f, hf⟩)
          = Submodule.Quotient.mk ((diagonalHom K F).restrict
              (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) ⟨f, hf⟩) from rfl,
      ← hβeq, Submodule.Quotient.eq]
    refine Submodule.mem_comap.mpr ?_
    change diagonalHom K F f - (β : Place K F → F) ∈ adeleBdd D₁
    have hβsub : diagonalHom K F f - (β : Place K F → F) = -γ := by
      rw [← hsum, hfδ]; ring
    rw [hβsub]; exact (adeleBdd D₁).neg_mem hγ

private theorem finrank_adeleBddSup_quotient [IsCurveOver K F] [Nonempty (Place K F)]
    {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) [hL : FiniteDimensional K (LSpace D₂)] :
    Module.Finite K (↥(adeleBdd D₂ ⊔ globalSub K F)
        ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) ∧
      (finrank K (↥(adeleBdd D₂ ⊔ globalSub K F)
          ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) : ℤ)
        = (Divisor.degree D₂ - ell D₂) - (Divisor.degree D₁ - ell D₁) := by
  classical
  let A : Submodule K (adeleBdd D₂) := (adeleBdd D₁).comap (adeleBdd D₂).subtype
  let B : Submodule K (adeleBdd D₂) :=
    (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype
  have hAB : A ≤ B := Submodule.comap_mono le_sup_left
  have hfinA : Module.Finite K (adeleBdd D₂ ⧸ A) := module_finite_adeleBdd_quotient hD
  have hdimA : (finrank K (adeleBdd D₂ ⧸ A) : ℤ) = Divisor.degree D₂ - Divisor.degree D₁ :=
    finrank_adeleBdd_quotient_eq hD
  have hran : LinearMap.range (lSpaceQuotientToAdeleBddQuotient hD) = B.map A.mkQ :=
    range_lSpaceQuotientToAdeleBddQuotient hD
  have hℓ₁ : ell D₁ = finrank K ((LSpace D₁).comap (LSpace D₂).subtype) :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (lSpace_mono hD))).symm
  have hdimL : ell D₂
      = finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) + ell D₁ := by
    have h := Submodule.finrank_quotient_add_finrank (R := K)
      ((LSpace D₁).comap (LSpace D₂).subtype)
    rw [← hℓ₁] at h; exact h.symm
  have hdimB : ell D₂ = finrank K (B.map A.mkQ : Submodule K (adeleBdd D₂ ⧸ A)) + ell D₁ := by
    rw [← hran, LinearMap.finrank_range_of_inj
      (lSpaceQuotientToAdeleBddQuotient_injective hD)]
    exact hdimL
  have e3 := Submodule.quotientQuotientEquivQuotient A B hAB
  have hfinB : Module.Finite K (adeleBdd D₂ ⧸ B) := Module.Finite.equiv e3
  have hdim2 : finrank K (adeleBdd D₂ ⧸ A)
      = finrank K (adeleBdd D₂ ⧸ B) + finrank K (B.map A.mkQ : Submodule K _) := by
    have h := Submodule.finrank_quotient_add_finrank (R := K) (M := adeleBdd D₂ ⧸ A)
      (B.map A.mkQ)
    rw [LinearEquiv.finrank_eq e3] at h; omega
  have e2 := LinearMap.quotientInfEquivSupQuotient (R := K)
    (adeleBdd D₂) (adeleBdd D₁ ⊔ globalSub K F)
  have hsup : adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F) = adeleBdd D₂ ⊔ globalSub K F := by
    rw [← sup_assoc, sup_eq_left.mpr (adeleBdd_mono hD)]
  have hB' : (adeleBdd D₂).comap (adeleBdd D₂).subtype ⊓
      (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype = B := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
  let eL : (adeleBdd D₂ ⧸ B) ≃ₗ[K]
      (adeleBdd D₂ ⧸ ((adeleBdd D₂).comap (adeleBdd D₂).subtype ⊓
        (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype)) :=
    Submodule.quotEquivOfEq _ _ hB'.symm
  have hfin_iso : Module.Finite K (↥(adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)) ⧸
        (adeleBdd D₁ ⊔ globalSub K F).comap
          (adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)).subtype) :=
    Module.Finite.equiv (eL.trans e2)
  have hdim_iso : finrank K (↥(adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)) ⧸
        (adeleBdd D₁ ⊔ globalSub K F).comap
          (adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)).subtype)
      = finrank K (adeleBdd D₂ ⧸ B) :=
    (LinearEquiv.finrank_eq (eL.trans e2)).symm
  have hcast : (finrank K (adeleBdd D₂ ⧸ A) : ℤ)
      = (finrank K (adeleBdd D₂ ⧸ B) : ℤ) + ((ell D₂ : ℤ) - (ell D₁ : ℤ)) := by
    have hb : (ell D₂ : ℤ)
        = (finrank K (B.map A.mkQ : Submodule K (adeleBdd D₂ ⧸ A)) : ℤ) + (ell D₁ : ℤ) := by
      exact_mod_cast hdimB
    push_cast [hdim2]; linarith
  have hgoal : (finrank K (adeleBdd D₂ ⧸ B) : ℤ)
      = Divisor.degree D₂ - ↑(ell D₂) - (Divisor.degree D₁ - ↑(ell D₁)) := by
    linarith [hdimA, hcast]
  clear_value eL
  exact hsup ▸ ⟨hfin_iso, by rw [hdim_iso]; exact hgoal⟩

section Index

variable [IsCurveOver K F] [Nonempty (Place K F)]

private theorem adeleBddSup_eq_of_degree_sub_ell_eq {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂)
    [FiniteDimensional K (LSpace D₂)]
    (heq : Divisor.degree D₂ - ell D₂ = Divisor.degree D₁ - ell D₁) :
    adeleBdd D₂ ⊔ globalSub K F = adeleBdd D₁ ⊔ globalSub K F := by
  obtain ⟨hfin, hdim⟩ := finrank_adeleBddSup_quotient hD
  rw [heq, sub_self] at hdim
  refine le_antisymm ?_ (sup_le_sup_right (adeleBdd_mono hD) _)
  have := hfin
  have hd0 : finrank K (↥(adeleBdd D₂ ⊔ globalSub K F)
      ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) = 0 := by
    exact_mod_cast hdim
  have hsub : Subsingleton (↥(adeleBdd D₂ ⊔ globalSub K F)
      ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) :=
    Module.finrank_zero_iff.mp hd0
  have htop := Submodule.Quotient.subsingleton_iff.mp hsub
  intro x hx
  have hxc : (⟨x, hx⟩ : ↥(adeleBdd D₂ ⊔ globalSub K F)) ∈
      (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype := by
    rw [htop]; exact Submodule.mem_top
  exact hxc

end Index

namespace RiemannGenusReachedAt
open scoped _root_.AlgebraicCurve.RiemannGenusReachedAt in
private theorem _root_.AlgebraicCurve.RiemannGenusReachedAt.eq_of_ge [IsCurveOver K F] [Nonempty
    (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {D : Divisor K F} (hD : D₀ ≤ D) :
    Divisor.degree D - ell D = γ - 1 := by
  have := finiteDimensional_lSpace (K := K) D
  have hge : Divisor.degree D₀ - (ell D₀ : ℤ) ≤ Divisor.degree D - ell D := by
    have := ell_sub_ell_le_degree_sub_degree (K := K) hD
    linarith
  exact le_antisymm (h.isMax D) (h.eq ▸ hge)

end RiemannGenusReachedAt
private theorem adeleSpace_eq_of_genusReached [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    adeleSpace K F = adeleBdd D₀ ⊔ globalSub K F := by
  refine le_antisymm ?_ (adeleBdd_sup_globalSub_le_adeleSpace D₀)
  intro α hα
  obtain ⟨D, hαD⟩ := mem_adeleSpace_iff.mp hα
  refine (le_trans (adeleBdd_mono (le_sup_left : D ≤ D ⊔ D₀)) ?_) hαD
  have := finiteDimensional_lSpace (K := K) (D ⊔ D₀)
  have heq : Divisor.degree (D ⊔ D₀) - ell (D ⊔ D₀) = Divisor.degree D₀ - ell D₀ :=
    (h.eq_of_ge le_sup_right).trans h.eq.symm
  have hsup := adeleBddSup_eq_of_degree_sub_ell_eq (K := K)
    (le_sup_right : D₀ ≤ D ⊔ D₀) heq
  rw [← hsup]
  exact le_sup_left

private theorem indexOfSpecialty_eq_zero_of_genusReached [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    indexOfSpecialty D₀ = 0 := by
  rw [indexOfSpecialty_eq, adeleBddPrincipal_eq_comap, ← adeleSpace_eq_of_genusReached h,
    Submodule.comap_subtype_self]
  have : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

private theorem indexOfSpecialty_eq_of_genusReached [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D) ∧
      (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) := by
  classical
  have hDD' : D ≤ D ⊔ D₀ := le_sup_left
  have hD0D' : D₀ ≤ D ⊔ D₀ := le_sup_right
  have := finiteDimensional_lSpace (K := K) (D ⊔ D₀)
  have heqD' : Divisor.degree (D ⊔ D₀) - ell (D ⊔ D₀) = γ - 1 := h.eq_of_ge hD0D'
  have hsa : adeleSpace K F = adeleBdd (D ⊔ D₀) ⊔ globalSub K F := by
    refine le_antisymm ?_ (adeleBdd_sup_globalSub_le_adeleSpace _)
    rw [adeleSpace_eq_of_genusReached h]
    exact sup_le_sup_right (adeleBdd_mono hD0D') _
  have hABsub : adeleBdd D ⊔ globalSub K F ≤ adeleBdd (D ⊔ D₀) ⊔ globalSub K F :=
    sup_le_sup_right (adeleBdd_mono hDD') _
  have hBCsub : adeleBdd (D ⊔ D₀) ⊔ globalSub K F ≤ adeleSpace K F :=
    adeleBdd_sup_globalSub_le_adeleSpace _
  have hCB : (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype = ⊤ := by
    rw [← hsa, Submodule.comap_subtype_self]
  have hfinCB : Module.Finite K (adeleSpace K F ⧸
      (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [hCB]
    have : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Module.Finite.of_finite
  have hdimCB : finrank K (adeleSpace K F ⧸
      (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype) = 0 := by
    rw [hCB]
    have : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton
  obtain ⟨hfinBA, hdimBA⟩ := finrank_adeleBddSup_quotient (K := K) hDD'
  have := hfinBA
  obtain ⟨hfinCA, hdimCA⟩ := Submodule.finrank_quotient_chain
    (A := adeleBdd D ⊔ globalSub K F) (B := adeleBdd (D ⊔ D₀) ⊔ globalSub K F)
    (C := adeleSpace K F) hABsub hBCsub
  have hieq : indexOfSpecialty D
      = finrank K (adeleSpace K F ⧸
        (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [indexOfSpecialty_eq, adeleBddPrincipal_eq_comap]
  rw [adeleBddPrincipal_eq_comap]
  refine ⟨hfinCA, ?_⟩
  rw [hieq]
  push_cast [hdimCA, hdimCB]
  linarith [hdimBA, heqD']

private theorem gate_indexOfSpecialty_at_witness [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    (indexOfSpecialty D₀ : ℤ) = 0 := by
  have h1 := (indexOfSpecialty_eq_of_genusReached h D₀).2
  have h2 := h.eq
  have h3 := indexOfSpecialty_eq_zero_of_genusReached h
  exact_mod_cast h3

private theorem gate_riemannInequality_of_genusReached [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Divisor.degree D + 1 - γ ≤ (ell D : ℤ) := by
  have heq := (indexOfSpecialty_eq_of_genusReached h D).2
  have hnn : (0 : ℤ) ≤ indexOfSpecialty D := Int.natCast_nonneg _
  linarith

end AlgebraicCurve

end

noncomputable section

open Module IsDedekindDomain WithZero

namespace AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem adeleSpaceMul_add [HasPrincipalDivisors K F] (f g : F) :
    adeleSpaceMul K F (f + g) = adeleSpaceMul K F f + adeleSpaceMul K F g := by
  refine LinearMap.ext fun α => Subtype.ext (funext fun v => ?_)
  simp only [adeleSpaceMul_coe, mulAdele_apply, LinearMap.add_apply, Submodule.coe_add,
    Pi.add_apply, add_mul]

private theorem adeleSpaceMul_zero [HasPrincipalDivisors K F] :
    adeleSpaceMul K F (0 : F) = 0 := by
  refine LinearMap.ext fun α => Subtype.ext (funext fun v => ?_)
  simp only [adeleSpaceMul_coe, mulAdele_apply, zero_mul, LinearMap.zero_apply,
    Submodule.coe_zero, Pi.zero_apply]

private theorem weilSmul_add_left [HasPrincipalDivisors K F] (f g : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (f + g) φ = weilSmul K F f φ + weilSmul K F g φ := by
  ext α
  simp only [weilSmul_apply, adeleSpaceMul_add, LinearMap.add_apply, map_add]

private theorem weilSmul_zero_left [HasPrincipalDivisors K F]
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (0 : F) φ = 0 := by
  ext α
  simp only [weilSmul_apply, adeleSpaceMul_zero, LinearMap.zero_apply, map_zero]

private theorem weilSmul_neg_left [HasPrincipalDivisors K F] (f : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (-f) φ = -weilSmul K F f φ := by
  have h := weilSmul_add_left (K := K) (F := F) f (-f) φ
  rw [add_neg_cancel, weilSmul_zero_left] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

private theorem weilSmul_sub_left [HasPrincipalDivisors K F] (f g : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (f - g) φ = weilSmul K F f φ - weilSmul K F g φ := by
  rw [sub_eq_add_neg, weilSmul_add_left, weilSmul_neg_left, sub_eq_add_neg]

private theorem weilSmul_eq_zero_iff_left [HasPrincipalDivisors K F]
    {f : F} {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ≠ 0) :
    weilSmul K F f φ = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ weilSmul_zero_left φ⟩
  by_contra hf
  exact hφ (weilSmul_injective hf (h.trans (map_zero (weilSmul K F f)).symm))

private theorem weilSmul_left_injective [HasPrincipalDivisors K F]
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ≠ 0) :
    Function.Injective (fun f : F => weilSmul K F f φ) := by
  intro f g hfg
  have hsub : weilSmul K F (f - g) φ = 0 := by
    rw [weilSmul_sub_left, sub_eq_zero]; exact hfg
  exact sub_eq_zero.mp ((weilSmul_eq_zero_iff_left hφ).mp hsub)

variable (K F) in
private def doubleResiduePairing [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) :
    LSpace (W - D) × LSpace (W - D) →ₗ[K] omegaSpace D :=
  (residuePairing K F W D hφ).coprod (residuePairing K F W D hμ)

private theorem doubleResiduePairing_apply_coe [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (g h : LSpace (W - D)) :
    (doubleResiduePairing K F W D hφ hμ (g, h) : Module.Dual K (adeleSpace K F))
      = weilSmul K F (g : F) φ + weilSmul K F (h : F) μ := by
  simp only [doubleResiduePairing, LinearMap.coprod_apply, Submodule.coe_add,
    residuePairing_apply_coe]

private theorem doubleResiduePairing_injective [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W)
    (hφ0 : φ ≠ 0) (hindep : ∀ f : F, μ ≠ weilSmul K F f φ) :
    Function.Injective (doubleResiduePairing K F W D hφ hμ) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨g, h⟩ heq
  have heq' : weilSmul K F (g : F) φ + weilSmul K F (h : F) μ = 0 := by
    have hcoe := congrArg Subtype.val heq
    rwa [doubleResiduePairing_apply_coe, Submodule.coe_zero] at hcoe
  rcases eq_or_ne (h : F) 0 with hh0 | hh0
  · rw [hh0, weilSmul_zero_left, add_zero] at heq'
    have hg0 : (g : F) = 0 := (weilSmul_eq_zero_iff_left hφ0).mp heq'
    exact Prod.ext (Subtype.ext hg0) (Subtype.ext hh0)
  · exfalso
    have hμeq : weilSmul K F (h : F) μ = -weilSmul K F (g : F) φ := by
      have h2 : weilSmul K F (h : F) μ + weilSmul K F (g : F) φ = 0 := by
        rw [add_comm]; exact heq'
      exact eq_neg_of_add_eq_zero_left h2
    have hLHS : weilSmul K F (h : F)⁻¹ (weilSmul K F (h : F) μ) = μ := by
      rw [← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hh0, weilSmul_one,
        LinearMap.id_apply]
    have hRHS : weilSmul K F (h : F)⁻¹ (-weilSmul K F (g : F) φ)
        = weilSmul K F (-(g : F) * (h : F)⁻¹) φ := by
      rw [map_neg, ← LinearMap.comp_apply, ← weilSmul_mul, neg_mul, weilSmul_neg_left]
    exact hindep (-(g : F) * (h : F)⁻¹) (by rw [← hLHS, hμeq, hRHS])

private theorem two_mul_ell_le_indexOfSpecialty [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W)
    (hφ0 : φ ≠ 0) (hindep : ∀ f : F, μ ≠ weilSmul K F f φ)
    [Module.Finite K (omegaSpace (K := K) (F := F) D)]
    [Module.Finite K (LSpace (K := K) (F := F) (W - D))] :
    2 * ell (W - D) ≤ indexOfSpecialty D := by
  have hinj := doubleResiduePairing_injective W D hφ hμ hφ0 hindep
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hle
  rw [← finrank_omegaSpace_eq_indexOfSpecialty, two_mul]
  exact hle

end AlgebraicCurve

end

noncomputable section

open Module IsDedekindDomain WithZero

namespace AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section Finiteness

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

private theorem omegaSpace_finite_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (omegaSpace (K := K) (F := F) D) := by
  have := (indexOfSpecialty_eq_of_genusReached h D).1
  exact Module.Finite.equiv (omegaSpaceEquivIndexDual D).symm

end Finiteness

section ParametricRankOne

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

private theorem exists_weilSmul_eq_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {φ μ : Module.Dual K (adeleSpace K F)} {W : Divisor K F}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (hφ0 : φ ≠ 0) :
    ∃ f : F, μ = weilSmul K F f φ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨P⟩ := ‹Nonempty (Place K F)›
  set n : ℕ := 3 * γ.natAbs + 2 * (Divisor.degree W).natAbs + 4 with hn
  set D : Divisor K F := -Finsupp.single P (n : ℤ) with hD
  have hdegD : Divisor.degree D = -(n : ℤ) * (P.deg : ℤ) := by
    rw [hD, map_neg, Divisor.degree_single]; ring
  have hdegWD : Divisor.degree (W - D) = Divisor.degree W + (n : ℤ) * (P.deg : ℤ) := by
    rw [map_sub, hdegD]; ring
  have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast IsCurveOver.one_le_deg P
  have habsγ : -(|γ|) ≤ γ ∧ γ ≤ |γ| := ⟨neg_abs_le _, le_abs_self _⟩
  have habsW : -|Divisor.degree W| ≤ Divisor.degree W ∧
      Divisor.degree W ≤ |Divisor.degree W| := ⟨neg_abs_le _, le_abs_self _⟩
  have hn_ge : 3 * |γ| + 2 * |Divisor.degree W| + 4 ≤ (n : ℤ) := by
    rw [hn]; push_cast [Int.natCast_natAbs]; ring_nf; omega
  have hndegP : (n : ℤ) ≤ (n : ℤ) * (P.deg : ℤ) := by nlinarith [Int.natCast_nonneg n]
  have hellD : ell D = 0 := ell_eq_zero_of_degree_neg (by rw [hdegD]; nlinarith)
  have hiD : (indexOfSpecialty D : ℤ) = (n : ℤ) * (P.deg : ℤ) - 1 + γ := by
    have hidx := (indexOfSpecialty_eq_of_genusReached h D).2
    rw [hellD, hdegD] at hidx; push_cast at hidx; linarith
  have hlowerWD : Divisor.degree W + (n : ℤ) * (P.deg : ℤ) + 1 - γ
      ≤ (ell (W - D) : ℤ) := by
    have hlow := gate_riemannInequality_of_genusReached h (W - D)
    rw [hdegWD] at hlow; exact hlow
  have := omegaSpace_finite_of_genusReached h D
  have := finiteDimensional_lSpace (K := K) (W - D)
  have hdbl : (2 * ell (W - D) : ℤ) ≤ (indexOfSpecialty D : ℤ) := by
    exact_mod_cast two_mul_ell_le_indexOfSpecialty W D hφ hμ hφ0 hcon
  rw [hiD] at hdbl
  nlinarith [habsγ.1, habsγ.2, habsW.1, habsW.2]

private theorem weilDifferentialRankOne_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    WeilDifferentialRankOne K F := by
  intro φ hφmem hφ0 μ hμmem
  obtain ⟨W₁, hφW₁⟩ := mem_weilDifferentialModule_iff.mp hφmem
  obtain ⟨W₂, hμW₂⟩ := mem_weilDifferentialModule_iff.mp hμmem
  have hφW : φ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_left hφW₁
  have hμW : μ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_right hμW₂
  obtain ⟨f, hf⟩ := exists_weilSmul_eq_of_genusReached h hφW hμW hφ0
  exact ⟨f, hf, fun f' hf' => weilSmul_left_injective hφ0 (hf'.symm.trans hf)⟩

end ParametricRankOne

private theorem residuePairing_surjective_of_rankOne_max [HasPrincipalDivisors K F]
    (hRankOne : WeilDifferentialRankOne K F)
    {W : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)
    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W) (D : Divisor K F) :
    Function.Surjective (residuePairing K F W D hφ) := by
  rintro ⟨μ, hμD⟩
  have hφmem : φ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule W hφ
  have hμmem : μ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule D hμD
  obtain ⟨f, hf, -⟩ := hRankOne hφmem hφ0 hμmem
  rcases eq_or_ne f 0 with rfl | hf0
  · have hμ0 : (⟨μ, hμD⟩ : omegaSpace D) = 0 :=
      Subtype.ext (hf.trans (weilSmul_zero_left φ))
    exact ⟨0, (map_zero _).trans hμ0.symm⟩
  · obtain ⟨P, hPord, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
    have hPinv : ∀ v, (-P) v = v.ord f⁻¹ := fun v => by
      rw [Finsupp.neg_apply, hPord v, v.ord_inv]
    have hinv : weilSmul K F f⁻¹ μ = φ := by
      rw [hf, ← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hf0, weilSmul_one,
        LinearMap.id_apply]
    have hφD : φ ∈ omegaSpace (D + -P) := by
      rw [← hinv]; exact weilSmul_mem_omegaSpace_add (inv_ne_zero hf0) hPinv hμD
    have hDP : D + -P ≤ W := hWmax _ hφD
    have hfL : f ∈ LSpace (W - D) := by
      rw [mem_lSpace_iff_ord]; refine Or.inr fun v => ?_
      have hv := hDP v
      rw [Finsupp.add_apply, Finsupp.neg_apply, hPord v] at hv
      rw [Finsupp.sub_apply]; linarith
    exact ⟨⟨f, hfL⟩, Subtype.ext hf.symm⟩

end AlgebraicCurve

end

noncomputable section

open Module IsDedekindDomain WithZero

namespace AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem exists_riemannGenusReachedAt_of_bounded
    [IsCurveOver K F] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hbdd : RiemannGenusBounded K F) :
    ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀ := by
  obtain ⟨γ, hγ⟩ := hbdd
  obtain ⟨M, ⟨D₀, hD₀⟩, hMmax⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun n => ∃ D : Divisor K F, Divisor.degree D - ell D = n)
      ⟨γ, fun n ⟨D, hD⟩ => hD ▸ hγ D⟩
      ⟨Divisor.degree (0 : Divisor K F) - ell (0 : Divisor K F), 0, rfl⟩
  refine ⟨M + 1, D₀, ?_, ?_, ?_⟩
  · exact finiteDimensional_lSpace D₀
  · rw [hD₀]; ring
  · intro D
    have := hMmax (Divisor.degree D - ell D) ⟨D, rfl⟩
    linarith

private theorem stichtenothGenusExists_of_bounded
    [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hbdd : RiemannGenusBounded K F) :
    StichtenothGenusExists K F :=
  ⟨‹_›, ‹_›, exists_riemannGenusReachedAt_of_bounded hbdd⟩

private theorem indexOfSpecialty_sub_of_ge [IsCurveOver K F] [Nonempty (Place K F)]
    {D₀ D : Divisor K F} (hD : D₀ ≤ D)
    [FiniteDimensional K (LSpace D)]
    [hfin : Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D₀)] :
    Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D) ∧
      (Divisor.degree D - ell D) - (Divisor.degree D₀ - ell D₀)
        = (indexOfSpecialty D₀ : ℤ) - (indexOfSpecialty D : ℤ) := by
  have hABsub : adeleBdd D₀ ⊔ globalSub K F ≤ adeleBdd D ⊔ globalSub K F :=
    sup_le_sup_right (adeleBdd_mono hD) _
  have hBCsub : adeleBdd D ⊔ globalSub K F ≤ adeleSpace K F :=
    adeleBdd_sup_globalSub_le_adeleSpace _
  obtain ⟨hfinBA, hdimBA⟩ := finrank_adeleBddSup_quotient (K := K) hD
  have := hfinBA
  have hfinCA : Module.Finite K (adeleSpace K F ⧸
      (adeleBdd D₀ ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [← adeleBddPrincipal_eq_comap]; exact hfin
  obtain ⟨hfinCB, hdimCB⟩ := Submodule.finrank_quotient_chain'
    (A := adeleBdd D₀ ⊔ globalSub K F) (B := adeleBdd D ⊔ globalSub K F)
    (C := adeleSpace K F) hABsub hBCsub
  have hi0 : indexOfSpecialty D₀
      = finrank K (adeleSpace K F ⧸
        (adeleBdd D₀ ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [indexOfSpecialty_eq, adeleBddPrincipal_eq_comap]
  have hiD : indexOfSpecialty D
      = finrank K (adeleSpace K F ⧸
        (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [indexOfSpecialty_eq, adeleBddPrincipal_eq_comap]
  have := hfinCB
  obtain ⟨_, hdimCA⟩ := Submodule.finrank_quotient_chain
    (A := adeleBdd D₀ ⊔ globalSub K F) (B := adeleBdd D ⊔ globalSub K F)
    (C := adeleSpace K F) hABsub hBCsub
  refine ⟨?_, ?_⟩
  · rw [show adeleBddPrincipal K F D
        = (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype
      from adeleBddPrincipal_eq_comap D]
    exact hfinCB
  · have hcast : (indexOfSpecialty D₀ : ℤ)
        = (indexOfSpecialty D : ℤ)
          + (finrank K (↥(adeleBdd D ⊔ globalSub K F)
              ⧸ (adeleBdd D₀ ⊔ globalSub K F).comap
                (adeleBdd D ⊔ globalSub K F).subtype) : ℤ) := by
      rw [hiD, hi0]; exact_mod_cast hdimCA
    linarith [hdimBA, hcast]

private theorem degreeSub_ell_le_of_indexFinite [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {D₀ : Divisor K F}
    (hfin : Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D₀))
    (D : Divisor K F) :
    Divisor.degree D - ell D ≤ (Divisor.degree D₀ - ell D₀) + indexOfSpecialty D₀ := by
  have := hfin
  have := finiteDimensional_lSpace (K := K) (D ⊔ D₀)
  have hmono : Divisor.degree D - (ell D : ℤ)
      ≤ Divisor.degree (D ⊔ D₀) - ell (D ⊔ D₀) := by
    have h := ell_sub_ell_le_degree_sub_degree (K := K) (le_sup_left : D ≤ D ⊔ D₀)
    linarith
  obtain ⟨_, heq⟩ :=
    indexOfSpecialty_sub_of_ge (K := K) (le_sup_right : D₀ ≤ D ⊔ D₀)
  have hi0 : (0 : ℤ) ≤ indexOfSpecialty (D ⊔ D₀) := Int.natCast_nonneg _
  linarith

private theorem riemannGenusBounded_of_indexFinite [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hfin : IndexOfSpecialtyFinite K F) :
    RiemannGenusBounded K F := by
  obtain ⟨D₀, hD₀⟩ := hfin
  exact ⟨(Divisor.degree D₀ - ell D₀) + indexOfSpecialty D₀,
    degreeSub_ell_le_of_indexFinite hD₀⟩

private theorem stichtenothGenusExists_of_indexFinite
    [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hfin : IndexOfSpecialtyFinite K F) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_bounded (riemannGenusBounded_of_indexFinite hfin)

private theorem indexOfSpecialtyFinite_of_stichtenothGenusExists
    [IsCurveOver K F] (hSG : StichtenothGenusExists K F) :
    IndexOfSpecialtyFinite K F := by
  obtain ⟨hne, hL0, γ, D₀, hD₀⟩ := hSG
  have := hne; have := hL0
  refine ⟨D₀, ?_⟩
  rw [show adeleBddPrincipal K F D₀
      = (adeleBdd D₀ ⊔ globalSub K F).comap (adeleSpace K F).subtype
    from adeleBddPrincipal_eq_comap D₀, ← adeleSpace_eq_of_genusReached hD₀,
    Submodule.comap_subtype_self]
  have : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.Finite.of_finite

private theorem stichtenothGenusExists_iff_indexFinite
    [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] :
    StichtenothGenusExists K F ↔ IndexOfSpecialtyFinite K F :=
  ⟨indexOfSpecialtyFinite_of_stichtenothGenusExists,
    stichtenothGenusExists_of_indexFinite⟩

private theorem gate_indexOfSpecialty_engine_at_witness [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    (indexOfSpecialty D₀ : ℤ) = 0 := by
  exact_mod_cast indexOfSpecialty_eq_zero_of_genusReached h

private theorem gate_stichtenothGenus_le_of_indexFinite [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {D₀ : Divisor K F}
    (hfin : Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D₀))
    {γ : ℤ} {D₁ : Divisor K F} (h : RiemannGenusReachedAt γ D₁) :
    γ - 1 ≤ (Divisor.degree D₀ - ell D₀) + indexOfSpecialty D₀ := by
  have := degreeSub_ell_le_of_indexFinite hfin D₁
  rw [h.eq] at this; exact this

private theorem gate_riemannGenusBounded_of_reachedAt
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    RiemannGenusBounded K F :=
  ⟨γ - 1, h.isMax⟩

private theorem gate_indexOfSpecialtyFinite_at_zero [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F (0 : Divisor K F)) :=
  (indexOfSpecialty_eq_of_genusReached h 0).1

end AlgebraicCurve

end

noncomputable section

open Module IsDedekindDomain WithZero

namespace AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem pow_mem_lSpace_nsmul {B : Divisor K F} {f : F} (hf : f ∈ LSpace B) (j : ℕ) :
    f ^ j ∈ LSpace (j • B) := by
  induction j with
  | zero => simpa using one_mem_lSpace_zero (K := K) (F := F)
  | succ j ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_lSpace_add ih hf

namespace PoleDivisorPackage
open _root_.AlgebraicCurve.PoleDivisorPackage

variable (P : PoleDivisorPackage K F)

private theorem _root_.AlgebraicCurve.PoleDivisorPackage.pow_mul_u_mem_lSpace (j : ℕ) (i : Fin P.n)
    :
    P.x ^ j * P.u i ∈ LSpace ((j + P.c) • P.B) := by
  rw [add_nsmul]
  exact mul_mem_lSpace_add (pow_mem_lSpace_nsmul P.hx_mem j) (P.hu_mem i)

private theorem _root_.AlgebraicCurve.PoleDivisorPackage.pow_mul_u_mem_lSpace_of_le {j m : ℕ} (hjm
    : j + P.c ≤ m) (i : Fin P.n) :
    P.x ^ j * P.u i ∈ LSpace (m • P.B) := by
  refine lSpace_mono ?_ (P.pow_mul_u_mem_lSpace j i)
  intro v
  have hBv : (0 : ℤ) ≤ P.B v := P.hB_eff v
  change ((j + P.c) • P.B) v ≤ (m • P.B) v
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjm) hBv

private theorem _root_.AlgebraicCurve.PoleDivisorPackage.ell_nsmul_poleDivisor_ge [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] {m : ℕ} (hm : P.c ≤ m) :
    (P.n : ℤ) * (m - P.c + 1) ≤ ell (m • P.B) := by
  have := finiteDimensional_lSpace (K := K) (m • P.B)
  set g : Fin (m - P.c + 1) × Fin P.n → LSpace (m • P.B) :=
    fun p => ⟨P.x ^ (p.1 : ℕ) * P.u p.2,
      P.pow_mul_u_mem_lSpace_of_le (by have := p.1.isLt; omega) p.2⟩
    with hgdef
  have hsub : LinearIndependent K (fun p => (g p : F)) := by
    have heq : (fun p => (g p : F))
        = (fun p : ℕ × Fin P.n => P.x ^ p.1 * P.u p.2)
            ∘ (fun p : Fin (m - P.c + 1) × Fin P.n => ((p.1 : ℕ), p.2)) := by
      funext p; rfl
    rw [heq]
    refine P.lin_indep.comp _ ?_
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext (Fin.val_injective hpq.1) hpq.2
  have hg : LinearIndependent K g := hsub.of_comp (LSpace (m • P.B)).subtype
  have hcard := hg.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  have hZ : ((m - P.c + 1) * P.n : ℤ) ≤ (ell (m • P.B) : ℤ) := by exact_mod_cast hcard
  have heq : (((m - P.c + 1 : ℕ) : ℤ) * P.n : ℤ) = (P.n : ℤ) * ((m : ℤ) - P.c + 1) := by
    rw [Nat.cast_add, Nat.cast_sub hm, Nat.cast_one]; ring
  linarith

private theorem _root_.AlgebraicCurve.PoleDivisorPackage.degree_nsmul_sub_ell_le [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] {m : ℕ} (hm : P.c ≤ m) :
    Divisor.degree (m • P.B) - ell (m • P.B) ≤ (P.n : ℤ) * (P.c - 1) := by
  have hge := P.ell_nsmul_poleDivisor_ge hm
  have hdeg : Divisor.degree (m • P.B) = (m : ℤ) * P.n := by
    rw [show m • P.B = (m : ℤ) • P.B from (natCast_zsmul _ _).symm,
      Divisor.degree.map_zsmul, smul_eq_mul, P.degB_eq]
  linarith

end PoleDivisorPackage

namespace PoleDivisorPackage
open scoped _root_.AlgebraicCurve.PoleDivisorPackage in
private theorem _root_.AlgebraicCurve.PoleDivisorPackage.ell_nsmul_sub_pos [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) {A : Divisor K F} (hA : 0 ≤ A) {m : ℕ} (hm : P.c ≤ m)
    (hbig : Divisor.degree A < (P.n : ℤ) * (m - P.c + 1)) :
    0 < ell (m • P.B - A) := by
  have := finiteDimensional_lSpace (K := K) (m • P.B)
  have hle : m • P.B - A ≤ m • P.B := by
    intro v
    have hAv : (0 : ℤ) ≤ A v := hA v
    rw [Finsupp.sub_apply]
    linarith
  have h48 := ell_sub_ell_le_degree_sub_degree (K := K) hle
  rw [map_sub, sub_sub_cancel] at h48
  have h412 := P.ell_nsmul_poleDivisor_ge hm
  have : (0 : ℤ) < (ell (m • P.B - A) : ℤ) := by linarith
  exact_mod_cast this

end PoleDivisorPackage
namespace PoleDivisorPackage
open scoped _root_.AlgebraicCurve.PoleDivisorPackage in
private theorem _root_.AlgebraicCurve.PoleDivisorPackage.degree_sub_ell_le [IsCurveOver K F]
    [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) (D : Divisor K F) :
    Divisor.degree D - ell D ≤ (P.n : ℤ) * (P.c - 1) := by
  classical
  set D' : Divisor K F := D ⊔ 0 with hD'def
  have hD'eff : 0 ≤ D' := le_sup_right
  have hDD' : D ≤ D' := le_sup_left
  have := finiteDimensional_lSpace (K := K) D'
  have hmono : Divisor.degree D - (ell D : ℤ) ≤ Divisor.degree D' - ell D' := by
    have h := ell_sub_ell_le_degree_sub_degree (K := K) hDD'
    linarith
  set m : ℕ := P.c + (Divisor.degree D').toNat with hmdef
  have hcm : P.c ≤ m := Nat.le_add_right _ _
  have hdegD' : 0 ≤ Divisor.degree D' := Divisor.degree_nonneg_of_nonneg hD'eff
  have hbig : Divisor.degree D' < (P.n : ℤ) * (m - P.c + 1) := by
    have hcast : ((m : ℤ) - P.c) = Divisor.degree D' := by
      simp only [hmdef, Nat.cast_add, add_sub_cancel_left, Int.toNat_of_nonneg hdegD']
    rw [hcast]
    have hn1 : (1 : ℤ) ≤ P.n := by exact_mod_cast P.hn_pos
    nlinarith
  have hellpos := P.ell_nsmul_sub_pos hD'eff hcm hbig
  have hnebot : LSpace (m • P.B - D') ≠ ⊥ :=
    fun h => by rw [ell, h, finrank_bot] at hellpos; exact lt_irrefl 0 hellpos
  obtain ⟨z, hzL, hz0⟩ := (Submodule.ne_bot_iff _).mp hnebot
  obtain ⟨Dz, hDzord, hDzdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) z hz0
  have hzmem := (mem_lSpace_iff_ord.mp hzL).resolve_left hz0
  have hD'le : D' ≤ m • P.B + Dz := by
    intro v
    have := hzmem v
    simp only [Finsupp.add_apply, Finsupp.sub_apply, neg_sub] at this ⊢
    rw [hDzord]; linarith
  have hellshift : ell (m • P.B + Dz) = ell (m • P.B) :=
    (LinearEquiv.finrank_eq (lSpaceShiftEquiv (m • P.B) hz0 hDzord)).symm
  have hdegshift : Divisor.degree (m • P.B + Dz) = Divisor.degree (m • P.B) := by
    rw [map_add, hDzdeg, add_zero]
  have := finiteDimensional_lSpace (K := K) (m • P.B + Dz)
  have hmono' : Divisor.degree D' - (ell D' : ℤ)
      ≤ Divisor.degree (m • P.B + Dz) - ell (m • P.B + Dz) := by
    have h := ell_sub_ell_le_degree_sub_degree (K := K) hD'le
    linarith
  rw [hellshift, hdegshift] at hmono'
  have h412 := P.degree_nsmul_sub_ell_le hcm
  linarith

end PoleDivisorPackage

private theorem riemannGenusBounded_of_poleDivisorPackage [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) :
    RiemannGenusBounded K F :=
  ⟨(P.n : ℤ) * (P.c - 1), P.degree_sub_ell_le⟩

private theorem stichtenothGenusExists_of_poleDivisorPackage [IsCurveOver K F] [Nonempty (Place K
    F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_bounded (riemannGenusBounded_of_poleDivisorPackage P)

private theorem indexOfSpecialtyFinite_of_poleDivisorPackage [IsCurveOver K F] [Nonempty (Place K
    F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) :
    IndexOfSpecialtyFinite K F :=
  indexOfSpecialtyFinite_of_stichtenothGenusExists
    (stichtenothGenusExists_of_poleDivisorPackage P)

private theorem indexOfSpecialtyFinite_of_hasPoleDivisorPackage [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (h : HasPoleDivisorPackage K F) :
    IndexOfSpecialtyFinite K F :=
  indexOfSpecialtyFinite_of_poleDivisorPackage h.some

private theorem stichtenothGenusExists_of_hasPoleDivisorPackage [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (h : HasPoleDivisorPackage K F) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_poleDivisorPackage h.some

private theorem gate_stichtenothGenus_le_of_poleDivisorPackage [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F)
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    γ ≤ (P.n : ℤ) * (P.c - 1) + 1 := by
  have := P.degree_sub_ell_le D₀
  rw [h.eq] at this; linarith

private theorem gate_ell_c_nsmul_ge [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) :
    (P.n : ℤ) ≤ ell (P.c • P.B) := by
  have h := P.ell_nsmul_poleDivisor_ge (le_refl P.c)
  simp only [sub_self, zero_add, mul_one] at h
  exact h

private theorem gate_x_transcendental_of_poleDivisorPackage (P : PoleDivisorPackage K F) :
    LinearIndependent K (fun j : ℕ => P.x ^ j * P.u ⟨0, P.hn_pos⟩) := by
  refine P.lin_indep.comp (fun j => (j, ⟨0, P.hn_pos⟩)) ?_
  intro a b hab
  exact (Prod.mk.injEq .. ▸ hab).1

private theorem gate_u_linearIndependent_of_poleDivisorPackage (P : PoleDivisorPackage K F) :
    LinearIndependent K P.u := by
  have h : LinearIndependent K (fun i : Fin P.n => P.x ^ (0 : ℕ) * P.u i) := by
    refine P.lin_indep.comp (fun i => (0, i)) ?_
    intro a b hab
    exact (Prod.mk.injEq .. ▸ hab).2
  simpa using h

end AlgebraicCurve

end

namespace AlgebraicCurve
open _root_.AlgebraicCurve

private scoped instance instSumRamificationInertia_port {K F F' : Type*} [Field K] [Field F] [Field
    F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    [HasPrincipalDivisors K F'] : SumRamificationInertia K F F' :=
  ⟨fun v => Place.sum_ramificationIndex_mul_inertiaDeg v⟩
end AlgebraicCurve
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve

noncomputable section

open Module IsDedekindDomain WithZero

namespace AlgebraicCurve
open _root_.AlgebraicCurve

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

namespace TranscendenceTower
open _root_.AlgebraicCurve.TranscendenceTower

variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
variable (T : TranscendenceTower K E F)

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in
private theorem _root_.AlgebraicCurve.TranscendenceTower.x_ne_zero : T.x ≠ 0 := fun h => by
  have := T.hxv; rw [h, Place.ord_zero] at this; exact absurd this (by decide)

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in
private theorem xF_ne_zero : T.xF ≠ 0 :=
  fun h => T.x_ne_zero ((algebraMap E F).injective (by rwa [map_zero]))

omit [FiniteDimensional E F] in
private theorem _root_.AlgebraicCurve.TranscendenceTower.poleDivisor_apply (w : Place K F) :
    T.poleDivisor w = (w.ramificationIndex E : ℤ) * (Finsupp.single T.v 1) (w.restrict E) :=
  Divisor.pullback_apply (Finsupp.single T.v 1) w

omit [FiniteDimensional E F] in
private theorem _root_.AlgebraicCurve.TranscendenceTower.poleDivisor_nonneg : 0 ≤ T.poleDivisor :=
    by
  classical
  intro w
  rw [Finsupp.coe_zero, Pi.zero_apply, T.poleDivisor_apply, Finsupp.single_apply]
  refine mul_nonneg (Int.natCast_nonneg _) ?_
  split_ifs <;> simp

omit [FiniteDimensional E F] in
private theorem _root_.AlgebraicCurve.TranscendenceTower.xF_mem_lSpace_poleDivisor : T.xF ∈ LSpace
    T.poleDivisor := by
  classical
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun w => ?_
  rw [T.poleDivisor_apply, Place.ord_restrict, Finsupp.single_apply]
  rcases eq_or_ne (w.restrict E) T.v with hw | hw
  · simp only [hw, T.hxv, ite_true, mul_one, mul_neg_one, le_refl]
  · simp only [ite_eq_right (Ne.symm hw), mul_zero, neg_zero]
    exact mul_nonneg (Int.natCast_nonneg _) (T.hxreg _ hw)

private theorem _root_.AlgebraicCurve.TranscendenceTower.degree_poleDivisor_eq_finrank :
    Divisor.degree T.poleDivisor = (Module.finrank E F : ℤ) := by
  rw [poleDivisor, Divisor.degree_pullback, Divisor.degree_single, T.hvdeg]
  push_cast; ring

omit [FiniteDimensional E F] in
private theorem
    _root_.AlgebraicCurve.TranscendenceTower.mem_lSpace_nsmul_poleDivisor_of_regular_outside {f : F}
    (hreg : ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord f)
    {c : ℕ} (hc : ∀ w ∈ T.v.fiber F, -(c : ℤ) ≤ w.ord f) :
    f ∈ LSpace (c • T.poleDivisor) := by
  classical
  rcases eq_or_ne f 0 with rfl | hf0
  · exact (LSpace _).zero_mem
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun w => ?_
  rw [Finsupp.smul_apply, T.poleDivisor_apply, Finsupp.single_apply, nsmul_eq_mul]
  rcases eq_or_ne (w.restrict E) T.v with hw | hw
  · simp only [hw, ite_true, mul_one]
    have he : (1 : ℤ) ≤ w.ramificationIndex E := by
      exact_mod_cast w.ramificationIndex_pos (F := E)
    have hbdd := hc w (Place.mem_fiber.mpr hw)
    nlinarith [Int.natCast_nonneg c]
  · simp only [ite_eq_right (Ne.symm hw), mul_zero, neg_zero]
    exact hreg w hw

omit [FiniteDimensional E F] in
private theorem _root_.AlgebraicCurve.TranscendenceTower.exists_forall_mem_lSpace_nsmul_poleDivisor
    {n : ℕ} (u : Fin n → F)
    (hreg : ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)) :
    ∃ c : ℕ, ∀ i, u i ∈ LSpace (c • T.poleDivisor) := by
  classical
  refine ⟨(Finset.univ : Finset (Fin n)).sup fun i =>
    (T.v.fiber F).sup fun w => (-(w.ord (u i))).toNat,
    fun i => T.mem_lSpace_nsmul_poleDivisor_of_regular_outside (hreg i) ?_⟩
  intro w hw
  have h1 : (-(w.ord (u i))).toNat
      ≤ (T.v.fiber F).sup fun w' => (-(w'.ord (u i))).toNat :=
    Finset.le_sup (f := fun w' => (-(w'.ord (u i))).toNat) hw
  have h2 : ((T.v.fiber F).sup fun w' => (-(w'.ord (u i))).toNat)
      ≤ (Finset.univ : Finset (Fin n)).sup fun i' =>
          (T.v.fiber F).sup fun w' => (-(w'.ord (u i'))).toNat :=
    Finset.le_sup (f := fun i' => (T.v.fiber F).sup fun w' => (-(w'.ord (u i'))).toNat)
      (Finset.mem_univ i)
  have htnat : -(w.ord (u i)) ≤ ((-(w.ord (u i))).toNat : ℤ) := Int.self_le_toNat _
  omega

end TranscendenceTower
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve

variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]

open scoped _root_.AlgebraicCurve.IntegralBasisInLSpace in
private def IntegralBasisInLSpace.ofRegularOutside (T : TranscendenceTower K E F)
    (u : Fin (Module.finrank E F) → F) (hu_indep : LinearIndependent E u)
    (hreg : ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)) :
    IntegralBasisInLSpace T where
  c := (T.exists_forall_mem_lSpace_nsmul_poleDivisor u hreg).choose
  u := u
  hu_indep := hu_indep
  hu_mem := (T.exists_forall_mem_lSpace_nsmul_poleDivisor u hreg).choose_spec

omit [FiniteDimensional E F] in
private theorem hasIntegralBasisInLSpace_of_regularOutside (T : TranscendenceTower K E F)
    (h : HasIntegralBasisRegularOutside K E F T) :
    HasIntegralBasisInLSpace K E F T := by
  obtain ⟨u, hu_indep, hreg⟩ := h
  exact ⟨IntegralBasisInLSpace.ofRegularOutside T u hu_indep hreg⟩

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in
private theorem linearIndependent_pow_mul {x : E} {n : ℕ} {u : Fin n → F}
    (hx : LinearIndependent K (fun j : ℕ => x ^ j)) (hu : LinearIndependent E u) :
    LinearIndependent K (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2) := by
  have heq : (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2)
      = (fun p : ℕ × Fin n => (x ^ p.1) • u p.2) := by
    funext p
    rw [Algebra.smul_def, map_pow]
  rw [heq]
  exact linearIndependent_smul (R := K) (S := E) (A := F) hx hu

open scoped _root_.AlgebraicCurve.PoleDivisorPackage in
private def PoleDivisorPackage.ofTranscendenceTower (T : TranscendenceTower K E F)
    (IB : IntegralBasisInLSpace T) :
    PoleDivisorPackage K F where
  x := T.xF
  B := T.poleDivisor
  hB_eff := T.poleDivisor_nonneg
  hx_mem := T.xF_mem_lSpace_poleDivisor
  n := Module.finrank E F
  hn_pos := Module.finrank_pos
  degB_eq := T.degree_poleDivisor_eq_finrank
  c := IB.c
  u := IB.u
  hu_mem := IB.hu_mem
  lin_indep := linearIndependent_pow_mul T.hx_indep IB.hu_indep

private theorem hasPoleDivisorPackage_of_transcendenceTower
    (T : TranscendenceTower K E F) (IB : IntegralBasisInLSpace T) :
    HasPoleDivisorPackage K F :=
  ⟨PoleDivisorPackage.ofTranscendenceTower T IB⟩

private theorem hasPoleDivisorPackage_of_hasIntegralBasisInLSpace
    (T : TranscendenceTower K E F) (h : HasIntegralBasisInLSpace K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_transcendenceTower T h.some

private theorem hasPoleDivisorPackage_of_hasIntegralBasisRegularOutside
    (T : TranscendenceTower K E F) (h : HasIntegralBasisRegularOutside K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasIntegralBasisInLSpace T
    (hasIntegralBasisInLSpace_of_regularOutside T h)

private theorem indexOfSpecialtyFinite_of_transcendenceTower [IsCurveOver K F] [Nonempty (Place K
    F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F) (IB : IntegralBasisInLSpace T) :
    IndexOfSpecialtyFinite K F :=
  indexOfSpecialtyFinite_of_poleDivisorPackage
    (PoleDivisorPackage.ofTranscendenceTower T IB)

private theorem stichtenothGenusExists_of_transcendenceTower [IsCurveOver K F] [Nonempty (Place K
    F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F) (IB : IntegralBasisInLSpace T) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_poleDivisorPackage
    (PoleDivisorPackage.ofTranscendenceTower T IB)

private theorem gate_ofTranscendenceTower_n_eq (T : TranscendenceTower K E F)
    (IB : IntegralBasisInLSpace T) :
    (PoleDivisorPackage.ofTranscendenceTower T IB).n = Module.finrank E F := rfl

private theorem gate_ofTranscendenceTower_B_eq (T : TranscendenceTower K E F)
    (IB : IntegralBasisInLSpace T) :
    (PoleDivisorPackage.ofTranscendenceTower T IB).B = T.poleDivisor := rfl

private theorem gate_ofTranscendenceTower_x_transcendental (T : TranscendenceTower K E F)
    (IB : IntegralBasisInLSpace T) :
    LinearIndependent K
      (fun j : ℕ => T.xF ^ j *
        (PoleDivisorPackage.ofTranscendenceTower T IB).u ⟨0, Module.finrank_pos⟩) :=
  gate_x_transcendental_of_poleDivisorPackage
    (PoleDivisorPackage.ofTranscendenceTower T IB)

private theorem gate_degree_pullback_single_of_deg_eq (v : Place K E) (d : ℕ) (hd : v.deg = d) :
    Divisor.degree (Divisor.pullback F (Finsupp.single v (1 : ℤ)))
      = (Module.finrank E F : ℤ) * d := by
  rw [Divisor.degree_pullback, Divisor.degree_single, hd]; ring

private theorem gate_stichtenothGenus_le_of_transcendenceTower [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F) (IB : IntegralBasisInLSpace T)
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    γ ≤ (Module.finrank E F : ℤ) * (IB.c - 1) + 1 :=
  gate_stichtenothGenus_le_of_poleDivisorPackage
    (PoleDivisorPackage.ofTranscendenceTower T IB) h

end AlgebraicCurve
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve

end
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve

noncomputable section

open Module

namespace AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem _root_.AlgebraicCurve.Place.mem_of_isIntegral {f : F} (hf : IsIntegral
    w.toValuationSubring f) :
    f ∈ w.toValuationSubring := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hf
  exact hy ▸ y.2

private theorem ord_nonneg_of_isIntegral {f : F} (hf : IsIntegral w.toValuationSubring f) :
    0 ≤ w.ord f :=
  w.ord_nonneg_of_mem (w.mem_of_isIntegral hf)

private theorem _root_.AlgebraicCurve.Place.mem_of_isIntegral_of_algebraMap_mem {A : Type*}
    [CommRing A] [Algebra A F]
    (hA : ∀ a : A, algebraMap A F a ∈ w.toValuationSubring)
    {f : F} (hf : IsIntegral A f) : f ∈ w.toValuationSubring := by
  let : Algebra A w.toValuationSubring :=
    ((algebraMap A F).codRestrict w.toValuationSubring.toSubring hA).toAlgebra
  have : IsScalarTower A w.toValuationSubring F :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  exact w.mem_of_isIntegral hf.tower_top

private theorem ord_nonneg_of_isIntegral_of_algebraMap_mem {A : Type*} [CommRing A] [Algebra A F]
    (hA : ∀ a : A, algebraMap A F a ∈ w.toValuationSubring)
    {f : F} (hf : IsIntegral A f) : 0 ≤ w.ord f :=
  w.ord_nonneg_of_mem (w.mem_of_isIntegral_of_algebraMap_mem hA hf)

end Place
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve

section Bridge

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
variable {A : Type*} [CommRing A] [Algebra A E] [Algebra A F] [IsScalarTower A E F]

namespace Place
open scoped _root_.AlgebraicCurve.Place in
private theorem _root_.AlgebraicCurve.Place.mem_of_isIntegral_of_restrict [Algebra.IsIntegral E F]
    (w : Place K F)
    {u : Place K E} (hw : w.restrict E = u)
    (hA : ∀ a : A, algebraMap A E a ∈ u.toValuationSubring)
    {f : F} (hf : IsIntegral A f) : f ∈ w.toValuationSubring := by
  refine w.mem_of_isIntegral_of_algebraMap_mem (fun a => ?_) hf
  rw [IsScalarTower.algebraMap_apply A E F, ← w.mem_restrict_iff, hw]
  exact hA a

end Place
namespace Place
open scoped _root_.AlgebraicCurve.Place in
private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_isIntegral_of_restrict
    [Algebra.IsIntegral E F] (w : Place K F)
    {u : Place K E} (hw : w.restrict E = u)
    (hA : ∀ a : A, algebraMap A E a ∈ u.toValuationSubring)
    {f : F} (hf : IsIntegral A f) : 0 ≤ w.ord f :=
  w.ord_nonneg_of_mem (w.mem_of_isIntegral_of_restrict hw hA hf)

end Place
namespace TranscendenceTower
open scoped _root_.AlgebraicCurve.TranscendenceTower in
private theorem _root_.AlgebraicCurve.TranscendenceTower.ord_nonneg_of_isIntegral_of_regularOutside
    [Algebra.IsIntegral E F] (T : TranscendenceTower K E F) (hA : T.RegularOutside A)
    {f : F} (hf : IsIntegral A f) :
    ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord f := fun w hw =>
  w.ord_nonneg_of_isIntegral_of_restrict rfl (hA _ hw) hf

end TranscendenceTower
end Bridge
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve

section Headline

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] in
private theorem linearIndependent_reindex_basis {s : Finset F} (b : Basis s E F) :
    LinearIndependent E (fun i : Fin (Module.finrank E F) =>
      b ((Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm).symm i)) :=
  b.linearIndependent.comp _ (Equiv.injective _)

omit [HasPrincipalDivisors K F] in
private theorem hasIntegralBasisRegularOutside_of_isFractionRing
    {A : Type*} [CommRing A] [IsDomain A] [Algebra A E] [IsFractionRing A E]
    [Algebra A F] [IsScalarTower A E F]
    (T : TranscendenceTower K E F) (hA : T.RegularOutside A) :
    HasIntegralBasisRegularOutside K E F T := by
  obtain ⟨s, b, hint⟩ := FiniteDimensional.exists_is_basis_integral A E F
  set e : Fin (Module.finrank E F) ≃ s :=
    (Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm).symm
  refine ⟨fun i => b (e i), linearIndependent_reindex_basis b, fun i w hw => ?_⟩
  exact T.ord_nonneg_of_isIntegral_of_regularOutside hA (hint (e i)) w hw

omit [HasPrincipalDivisors K F] in
private theorem hasIntegralBasisRegularOutside_of_hasRegularFractionSubring
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    HasIntegralBasisRegularOutside K E F T := by
  obtain ⟨A, hfrac, hreg⟩ := h
  have : IsFractionRing A E := hfrac
  exact hasIntegralBasisRegularOutside_of_isFractionRing (A := A) T
    (fun u hu a => hreg u hu (a : E) a.property)

private theorem hasPoleDivisorPackage_of_isFractionRing
    {A : Type*} [CommRing A] [IsDomain A] [Algebra A E] [IsFractionRing A E]
    [Algebra A F] [IsScalarTower A E F]
    (T : TranscendenceTower K E F) (hA : T.RegularOutside A) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasIntegralBasisRegularOutside T
    (hasIntegralBasisRegularOutside_of_isFractionRing T hA)

private theorem stichtenothGenusExists_of_isFractionRing [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {A : Type*} [CommRing A] [IsDomain A] [Algebra A E] [IsFractionRing A E]
    [Algebra A F] [IsScalarTower A E F]
    (T : TranscendenceTower K E F) (hA : T.RegularOutside A) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_hasPoleDivisorPackage
    (hasPoleDivisorPackage_of_isFractionRing T hA)

private theorem hasPoleDivisorPackage_of_hasRegularFractionSubring
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasIntegralBasisRegularOutside T
    (hasIntegralBasisRegularOutside_of_hasRegularFractionSubring T h)

private theorem stichtenothGenusExists_of_hasRegularFractionSubring [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_hasPoleDivisorPackage
    (hasPoleDivisorPackage_of_hasRegularFractionSubring T h)

namespace TranscendenceTower
open scoped _root_.AlgebraicCurve.TranscendenceTower in
omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in
private theorem _root_.AlgebraicCurve.TranscendenceTower.adjoin_x_regularOutside (T :
    TranscendenceTower K E F) :
    ∀ u : Place K E, u ≠ T.v →
      ∀ a ∈ Algebra.adjoin K {T.x}, a ∈ u.toValuationSubring := by
  intro u hu a ha
  let S : Subalgebra K E :=
    { u.toValuationSubring.toSubsemiring with
      algebraMap_mem' := u.algebraMap_mem' }
  suffices h : a ∈ S from h
  refine Algebra.adjoin_le ?_ ha
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  change T.x ∈ u.toValuationSubring
  exact u.mem_of_ord_nonneg T.x_ne_zero (T.hxreg u hu)

end TranscendenceTower
omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in
private theorem hasRegularFractionSubring_of_adjoin_x_isFractionRing
    (T : TranscendenceTower K E F)
    (hfrac : IsFractionRing (Algebra.adjoin K {T.x}) E) :
    HasRegularFractionSubring K E F T :=
  ⟨Algebra.adjoin K {T.x}, hfrac, T.adjoin_x_regularOutside⟩

omit [HasPrincipalDivisors K F] in
private theorem hasIntegralBasisRegularOutside_of_adjoin_x_isFractionRing
    (T : TranscendenceTower K E F)
    (hfrac : IsFractionRing (Algebra.adjoin K {T.x}) E) :
    HasIntegralBasisRegularOutside K E F T :=
  hasIntegralBasisRegularOutside_of_hasRegularFractionSubring T
    (hasRegularFractionSubring_of_adjoin_x_isFractionRing T hfrac)

private theorem stichtenothGenusExists_of_adjoin_x_isFractionRing [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F)
    (hfrac : IsFractionRing (Algebra.adjoin K {T.x}) E) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_hasRegularFractionSubring T
    (hasRegularFractionSubring_of_adjoin_x_isFractionRing T hfrac)

end Headline
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve

section Gates

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem gate_mem_of_isIntegral_recovers_comap (w : Place K F) (E : Type*) [Field E]
    [Algebra E F] [Algebra.IsIntegral E F]
    (hE : ∀ a : E, algebraMap E F a ∈ w.toValuationSubring) (f : F) :
    f ∈ w.toValuationSubring := by
  let : Algebra E w.toValuationSubring :=
    ((algebraMap E F).codRestrict w.toValuationSubring.toSubring hE).toAlgebra
  have : IsScalarTower E w.toValuationSubring F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact w.mem_of_isIntegral (Algebra.IsIntegral.isIntegral (R := E) f).tower_top

variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

private theorem gate_bridge_recovers_hxreg [Algebra.IsIntegral E F]
    (T : TranscendenceTower K E F) (w : Place K F) (hw : w.restrict E ≠ T.v) :
    0 ≤ w.ord T.xF := by
  rw [TranscendenceTower.xF, Place.ord_restrict]
  exact mul_nonneg (Int.natCast_nonneg _) (T.hxreg _ hw)

private theorem gate_regularOutside_mono (T : TranscendenceTower K E F) {A A' : Subalgebra K E}
    (hle : A ≤ A')
    (hA' : ∀ u : Place K E, u ≠ T.v → ∀ a ∈ A', a ∈ u.toValuationSubring) :
    ∀ u : Place K E, u ≠ T.v → ∀ a ∈ A, a ∈ u.toValuationSubring :=
  fun u hu a ha => hA' u hu a (hle ha)

private theorem gate_bot_regularOutside (T : TranscendenceTower K E F) :
    ∀ u : Place K E, u ≠ T.v → ∀ a ∈ (⊥ : Subalgebra K E), a ∈ u.toValuationSubring := by
  intro u _ a ha
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.mp ha
  exact u.algebraMap_mem' c

private theorem gate_adjoin_x_not_regular_at_v (T : TranscendenceTower K E F) :
    ¬ ∀ a ∈ Algebra.adjoin K {T.x}, a ∈ T.v.toValuationSubring := by
  intro h
  have hx := T.v.ord_nonneg_of_mem (h T.x (Algebra.subset_adjoin rfl))
  rw [T.hxv] at hx
  exact absurd hx (by decide)

end Gates
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve

end AlgebraicCurve
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve

end
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve

noncomputable section

open Module Polynomial

namespace AlgebraicCurve
open _root_.AlgebraicCurve

section Transcendental

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

private theorem linearIndependent_pow_of_transcendental {x : A} (hx : Transcendental K x) :
    LinearIndependent K (fun j : ℕ => x ^ j) := by
  have hinj : Function.Injective (Polynomial.aeval x : K[X] →ₐ[K] A) :=
    transcendental_iff_injective.mp hx
  have hXj : LinearIndependent K (fun j : ℕ => (X : K[X]) ^ j) := by
    have hb := (Polynomial.basisMonomials K).linearIndependent
    simp only [Polynomial.coe_basisMonomials] at hb
    convert hb using 2 with j
    exact (Polynomial.monomial_one_right_eq_X_pow j).symm
  have heq : (fun j : ℕ => x ^ j)
      = (fun j : ℕ => (Polynomial.aeval x : K[X] →ₐ[K] A) (X ^ j)) := by
    funext j; simp
  rw [heq]
  exact hXj.map' (Polynomial.aeval x).toLinearMap
    (LinearMap.ker_eq_bot_of_injective hinj)

private theorem transcendental_of_linearIndependent_pow {x : A}
    (hx : LinearIndependent K (fun j : ℕ => x ^ j)) :
    Transcendental K x := by
  rw [transcendental_iff]
  intro p hp
  rw [Polynomial.aeval_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at hp
  ext j
  rcases lt_or_ge j (p.natDegree + 1) with hj | hj
  · exact (Fintype.linearIndependent_iff.mp
      (hx.comp (Fin.val : Fin (p.natDegree + 1) → ℕ) Fin.val_injective))
      (fun i => p.coeff i) hp ⟨j, hj⟩
  · exact p.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le hj)

end Transcendental
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve

namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

private theorem ord_placeInfty_X : (placeInfty K).ord (RatFunc.X : RatFunc K) = -1 := by
  rw [ord_placeInfty (K := K) RatFunc.X_ne_zero, RatFunc.intDegree_X]

private theorem algebraMap_polynomial_mem_of_ne_placeInfty
    {u : Place K (RatFunc K)} (hu : u ≠ placeInfty K) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ u.toValuationSubring := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty u with ⟨w, hw⟩ | hw
  · subst hw; exact algebraMap_mem_ofHeightOneSpectrum K w q
  · exact absurd hw hu

private theorem ord_X_nonneg_of_ne_placeInfty
    {u : Place K (RatFunc K)} (hu : u ≠ placeInfty K) :
    0 ≤ u.ord (RatFunc.X : RatFunc K) := by
  rw [← RatFunc.algebraMap_X]
  exact u.ord_nonneg_of_mem (algebraMap_polynomial_mem_of_ne_placeInfty K hu Polynomial.X)

variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]

private def transcendenceTower : TranscendenceTower K (RatFunc K) F where
  x := RatFunc.X
  hx_indep := linearIndependent_pow_of_transcendental RatFunc.transcendental_X
  v := placeInfty K
  hvdeg := deg_placeInfty K
  hxv := ord_placeInfty_X K
  hxreg := fun _ hu => ord_X_nonneg_of_ne_placeInfty K hu

@[scoped simp]
private theorem transcendenceTower_x : (transcendenceTower K F).x = RatFunc.X := rfl

@[scoped simp]
private theorem transcendenceTower_v : (transcendenceTower K F).v = placeInfty K := rfl

omit [DecidableEq (RatFunc K)] in
private theorem aeval_X_eq_algebraMap (q : K[X]) :
    (Polynomial.aeval (R := K) (RatFunc.X : RatFunc K)) q
      = algebraMap K[X] (RatFunc K) q := by
  have hext : (Polynomial.aeval (R := K) (RatFunc.X : RatFunc K))
      = IsScalarTower.toAlgHom K K[X] (RatFunc K) :=
    Polynomial.algHom_ext (by simp [RatFunc.algebraMap_X])
  rw [hext]; rfl

omit [DecidableEq (RatFunc K)] in
private theorem algebraMap_polynomial_mem_adjoin_X (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Algebra.adjoin K {(RatFunc.X : RatFunc K)} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨q, aeval_X_eq_algebraMap K q⟩

omit [DecidableEq (RatFunc K)] in
private theorem isFractionRing_adjoin_X :
    IsFractionRing (Algebra.adjoin K {(RatFunc.X : RatFunc K)}) (RatFunc K) := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  refine ⟨⟨algebraMap K[X] (RatFunc K) z.num, algebraMap_polynomial_mem_adjoin_X K z.num⟩,
    ⟨algebraMap K[X] (RatFunc K) z.denom, algebraMap_polynomial_mem_adjoin_X K z.denom⟩, ?_⟩
  change z = algebraMap K[X] (RatFunc K) z.num / algebraMap K[X] (RatFunc K) z.denom
  exact z.num_div_denom.symm

private theorem hasRegularFractionSubring :
    HasRegularFractionSubring K (RatFunc K) F (transcendenceTower K F) :=
  hasRegularFractionSubring_of_adjoin_x_isFractionRing
    (transcendenceTower K F) (isFractionRing_adjoin_X K)

variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]

private theorem hasIntegralBasisRegularOutside :
    HasIntegralBasisRegularOutside K (RatFunc K) F (transcendenceTower K F) :=
  hasIntegralBasisRegularOutside_of_adjoin_x_isFractionRing
    (transcendenceTower K F) (isFractionRing_adjoin_X K)

variable [HasPrincipalDivisors K F]

private theorem hasPoleDivisorPackage_of_ratFunc_tower :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasRegularFractionSubring
    (transcendenceTower K F) (hasRegularFractionSubring K F)

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

private theorem stichtenothGenusExists_of_ratFunc_tower :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_adjoin_x_isFractionRing
    (transcendenceTower K F) (isFractionRing_adjoin_X K)

private theorem indexOfSpecialtyFinite_of_ratFunc_tower :
    IndexOfSpecialtyFinite K F :=
  indexOfSpecialtyFinite_of_stichtenothGenusExists
    (stichtenothGenusExists_of_ratFunc_tower K F)

end RationalFunctionField
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve
    _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve.RationalFunctionField

section Gates

variable (K : Type*) [Field K]

variable [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]

variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
  [HasPrincipalDivisors K F]

end Gates
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve
    _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve.RationalFunctionField

end AlgebraicCurve
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve
    _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve.RationalFunctionField

end
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve
    _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve.RationalFunctionField

noncomputable section

open Module Polynomial IsDedekindDomain

namespace AlgebraicCurve
open _root_.AlgebraicCurve

namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]

section LyingOver

variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]

private theorem nonempty_place_of_ratFunc_tower : Nonempty (Place K F) :=
  (Place.exists_restrict_eq (M := F) (placeInfty K)).nonempty

end LyingOver
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve
    _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve.RationalFunctionField

omit [DecidableEq (RatFunc K)] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] in
private theorem finiteDimensional_lSpace_zero_of_constantsAreBase (hC : ConstantsAreBase K F) :
    FiniteDimensional K (LSpace (0 : Divisor K F)) := by
  rw [show LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) from hC]
  exact LinearMap.finiteDimensional_range _

variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
variable [IsCurveOver K F]

private theorem stichtenothGenusExists_port (hC : ConstantsAreBase K F) :
    StichtenothGenusExists K F :=
  haveI := nonempty_place_of_ratFunc_tower K F
  haveI := finiteDimensional_lSpace_zero_of_constantsAreBase K F hC
  stichtenothGenusExists_of_ratFunc_tower K F

private theorem indexOfSpecialtyFinite (hC : ConstantsAreBase K F) :
    IndexOfSpecialtyFinite K F :=
  indexOfSpecialtyFinite_of_stichtenothGenusExists (stichtenothGenusExists_port K F hC)

private theorem riemannGenusBounded (hC : ConstantsAreBase K F) : RiemannGenusBounded K F :=
  haveI := nonempty_place_of_ratFunc_tower K F
  haveI := finiteDimensional_lSpace_zero_of_constantsAreBase K F hC
  riemannGenusBounded_of_poleDivisorPackage (hasPoleDivisorPackage_of_ratFunc_tower K F).some

end RationalFunctionField
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve
    _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve.RationalFunctionField

section Gates

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]

omit [DecidableEq (RatFunc K)] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F] in
variable [IsCurveOver K F]

end Gates
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve
    _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve.RationalFunctionField

end AlgebraicCurve
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve
    _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve.RationalFunctionField

end
open scoped _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve
    _root_.CurveGenus.RatFuncGenusExists.AlgebraicCurve.RationalFunctionField

/-- A finite separable extension of `RatFunc K` that is the function field of a curve with field of
constants `K` has a genus. -/
public theorem _root_.AlgebraicCurve.RationalFunctionField.stichtenothGenusExists (K : Type*)
    [Field K] (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
    [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] [AlgebraicCurve.IsCurveOver K F]
    (hC : AlgebraicCurve.ConstantsAreBase K F) :
    AlgebraicCurve.StichtenothGenusExists K F := by
  classical
  exact AlgebraicCurve.RationalFunctionField.stichtenothGenusExists_port
    (K := K) (F := F) (hC := hC)

end RatFuncGenusExists

end CurveGenus
