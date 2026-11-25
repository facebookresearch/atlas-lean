/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_associated_discr_norm_jacobianDet_of_square_presentation.lean`,
`P2M/Sol/S_Algebra_associated_discr_norm_jacobianDet_of_square_presentation.lean`,
`Theorems/Thm_Algebra_isUnit_det_dual_mul_of_bijective.lean`,
`P2M/Sol/S_Algebra_isUnit_det_dual_mul_of_bijective.lean`,
`Theorems/Thm_Algebra_det_dual_mul_mul_eq_norm_mul_det.lean`,
`P2M/Sol/S_Algebra_det_dual_mul_mul_eq_norm_mul_det.lean`,
`Theorems/Thm_Algebra_exists_dual_bijective_mul_and_trace_eq_jacobianDet_mul_of_square_
presentation.lean`,
`P2M/Sol/S_Algebra_exists_dual_bijective_mul_and_trace_eq_jacobianDet_mul_of_square_
presentation.lean`,
`Theorems/Thm_Algebra_trace_eq_dual_lmul_of_bijective_rTensor.lean`,
`P2M/Sol/S_Algebra_trace_eq_dual_lmul_of_bijective_rTensor.lean`,
`Theorems/Thm_Algebra_lmul_bezoutian_eq_jacobianDet.lean`,
`P2M/Sol/S_Algebra_lmul_bezoutian_eq_jacobianDet.lean`,
`Theorems/Thm_MvPolynomial_lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul.lean`,
`P2M/Sol/S_MvPolynomial_lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul.lean`,
`Theorems/Thm_MvPolynomial_exists_tmul_one_sub_one_tmul_eq_sum_mul.lean`,
`P2M/Sol/S_MvPolynomial_exists_tmul_one_sub_one_tmul_eq_sum_mul.lean`,
`Theorems/Thm_Algebra_bijective_rTensor_dual_bezoutian_of_square_presentation.lean`,
`P2M/Sol/S_Algebra_bijective_rTensor_dual_bezoutian_of_square_presentation.lean`,
`Theorems/Thm_Algebra_bijective_rTensor_dual_bezoutian_of_isAlgClosed.lean`,
`P2M/Sol/S_Algebra_bijective_rTensor_dual_bezoutian_of_isAlgClosed.lean`,
`Theorems/Thm_Algebra_tmul_one_mul_bezoutian_eq_one_tmul_mul.lean`,
`P2M/Sol/S_Algebra_tmul_one_mul_bezoutian_eq_one_tmul_mul.lean`,
`Theorems/Thm_Algebra_bijective_rTensor_dual_bezoutian_of_forall_field.lean`,
`P2M/Sol/S_Algebra_bijective_rTensor_dual_bezoutian_of_forall_field.lean`,
`Theorems/Thm_LinearMap_bijective_of_forall_bijective_baseChange_quotient_maximal.lean`,
`P2M/Sol/S_LinearMap_bijective_of_forall_bijective_baseChange_quotient_maximal.lean`,
`Theorems/Thm_IsArtinianRing_nonempty_quotient_pow_algEquiv_localization_atPrime.lean`,
`P2M/Sol/S_IsArtinianRing_nonempty_quotient_pow_algEquiv_localization_atPrime.lean`,
`Theorems/Thm_MvPowerSeries_exists_bijective_compr2_mul_of_finite.lean`,
`P2M/Sol/S_MvPowerSeries_exists_bijective_compr2_mul_of_finite.lean`,
`Theorems/Thm_MvPowerSeries_quotient_mk_det_mem_of_ne_bot.lean`,
`P2M/Sol/S_MvPowerSeries_quotient_mk_det_mem_of_ne_bot.lean`,
`Theorems/Thm_Ideal_colon_span_eq_sup_span_det_of_isWeaklyRegular.lean`,
`P2M/Sol/S_Ideal_colon_span_eq_sup_span_det_of_isWeaklyRegular.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style. The localization step reuses
`MvPolynomial.exists_algEquiv_localization_atPrime_mvPowerSeries_quotient_apply_mk`.
-/

module

import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic.Continuity
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import MathlibExt.LinearAlgebra.ExteriorPower.Contraction
import MathlibExt.RingTheory.MvPowerSeries.ArtinianLocalization
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Discriminant and Jacobian determinant for a square presentation

Let `R` be a Noetherian domain and `A` a finite free `R`-algebra presented as
`R[X₁, …, Xₘ] ⧸ (f₁, …, fₘ)`. Then the discriminant of any basis of `A` is
associated to the norm of the image of the Jacobian determinant
`det (∂fᵢ/∂Xⱼ)` of the presenting equations.
-/

namespace JacobianSquarePresentation.KoszulColon

open Finset

namespace Koszul

universe u v

section Sign

variable (P : Type u) [CommRing P] {I : Type} [LinearOrder I]

def sgn (i : I) (T : Finset I) : P := (-1) ^ (T.filter (· < i)).card

private theorem sgn_mul_self (i : I) (T : Finset I) : sgn P i T * sgn P i T = 1 := by
  rw [sgn, ← pow_add, ← two_mul, pow_mul]; simp

private theorem sgn_insert_of_lt {i j : I} {T : Finset I} (hj : j ∉ T) (h : j < i) :
    sgn P i (insert j T) = -sgn P i T := by
  rw [sgn, sgn, filter_insert, ite_eq_left h, card_insert_of_notMem (by simp [hj]), pow_succ]
  ring

private theorem sgn_insert_of_not_lt {i j : I} {T : Finset I} (h : ¬j < i) :
    sgn P i (insert j T) = sgn P i T := by
  rw [sgn, sgn, filter_insert, ite_eq_right h]

end Sign

section Chains

variable {P : Type u} [CommRing P] {I : Type} (M : Type v) [AddCommGroup M] [Module P M]

def C (p : ℕ) : Submodule P (Finset I → M) where
  carrier := {m | ∀ T, T.card ≠ p → m T = 0}
  add_mem' ha hb T hT := by simp [ha T hT, hb T hT]
  zero_mem' _ _ := rfl
  smul_mem' c m hm T hT := by simp [hm T hT]

private theorem mem_C {p : ℕ} {m : Finset I → M} : m ∈ C (P := P) M p ↔ ∀ T, T.card ≠ p → m T = 0 :=
  Iff.rfl

end Chains

section Differential

variable {P : Type u} [CommRing P] {I : Type} [LinearOrder I] [Fintype I]
variable (x : I → P) (M : Type v) [AddCommGroup M] [Module P M]

def coef (i : I) (T : Finset I) : P := if i ∈ T then 0 else sgn P i T * x i

omit [Fintype I] in
private theorem coef_of_mem {i : I} {T : Finset I} (h : i ∈ T) : coef x i T = 0 := ite_eq_left h

omit [Fintype I] in
private theorem coef_of_not_mem {i : I} {T : Finset I} (h : i ∉ T) : coef x i T = sgn P i T * x i :=
    ite_eq_right h

def d : (Finset I → M) →ₗ[P] (Finset I → M) :=
  ∑ i : I, LinearMap.pi fun T => coef x i T • LinearMap.proj (insert i T)

private theorem d_apply (m : Finset I → M) (T : Finset I) :
    d x M m T = ∑ i, coef x i T • m (insert i T) := by
  simp [d, LinearMap.sum_apply]

private theorem d_d (m : Finset I → M) : d x M (d x M m) = 0 := by
  classical
  funext U
  simp only [d_apply, Pi.zero_apply, smul_sum, smul_smul]
  rw [← sum_product' univ univ (fun j i => (coef x j U * coef x i (insert j U)) • m
      (insert i (insert j U)))]
  refine sum_involution (fun ji _ => (ji.2, ji.1)) ?_ ?_ (fun _ _ => by simp) (fun _ _ => rfl)
  · rintro ⟨j, i⟩ -
    dsimp only
    rcases eq_or_ne j i with rfl | hne
    · rw [coef_of_mem x (mem_insert_self j U)]; simp
    rw [insert_comm i j U]
    by_cases hj : j ∈ U
    · rw [coef_of_mem x hj, coef_of_mem x (mem_insert_of_mem hj)]; simp
    by_cases hi : i ∈ U
    · rw [coef_of_mem x hi, coef_of_mem x (mem_insert_of_mem hi)]; simp
    have hij : i ∉ insert j U := by simp [hi, hne.symm]
    have hji : j ∉ insert i U := by simp [hj, hne]
    rw [coef_of_not_mem x hj, coef_of_not_mem x hij, coef_of_not_mem x hi, coef_of_not_mem x hji,
      ← add_smul]
    rcases hne.lt_or_gt with h | h
    · rw [sgn_insert_of_lt P hj h, sgn_insert_of_not_lt P (not_lt.mpr h.le)]
      convert zero_smul P (m (insert j (insert i U))) using 2; ring
    · rw [sgn_insert_of_not_lt P (not_lt.mpr h.le), sgn_insert_of_lt P hi h]
      convert zero_smul P (m (insert j (insert i U))) using 2; ring
  · rintro ⟨j, i⟩ - hne
    simp only [ne_eq, Prod.mk.injEq, not_and]
    rintro rfl
    exfalso; apply hne; dsimp only
    rw [coef_of_mem x (mem_insert_self _ U)]; simp

theorem d_mem_C {p : ℕ} {m : Finset I → M} (hm : m ∈ C (P := P) M (p + 1)) :
    d x M m ∈ C (P := P) M p := by
  intro T hT
  rw [d_apply]
  refine sum_eq_zero fun i _ => ?_
  by_cases hi : i ∈ T
  · rw [coef_of_mem x hi, zero_smul]
  · rw [hm _ (by rw [card_insert_of_notMem hi]; omega), smul_zero]

def Z (p : ℕ) : Submodule P (Finset I → M) := C M p ⊓ LinearMap.ker (d x M)

def B (p : ℕ) : Submodule P (Finset I → M) := (C M (p + 1)).map (d x M)

abbrev H (p : ℕ) : Type (max v 0) := Z x M p ⧸ (B x M p).comap (Z x M p).subtype

example (p : ℕ) : Module P (H x M p) := inferInstance

end Differential

end Koszul

namespace Koszul

open CategoryTheory

universe u' v'

section Complex

variable {P : Type u'} [CommRing P] {I : Type} [LinearOrder I] [Fintype I]
variable (x : I → P) (M : Type v') [AddCommGroup M] [Module P M]

def dC (p : ℕ) : C (P := P) (I := I) M (p + 1) →ₗ[P] C (P := P) (I := I) M p :=
  (d x M).restrict fun _ hm => d_mem_C x M hm

@[scoped simp] private theorem coe_dC_apply (p : ℕ) (m : C (P := P) (I := I) M (p + 1)) :
    (dC x M p m : Finset I → M) = d x M m := rfl

private theorem dC_dC (p : ℕ) (m : C (P := P) (I := I) M (p + 2)) :
    dC x M p (dC x M (p + 1) m) = 0 := by
  ext1; simp [d_d]

theorem d_eq_zero_of_mem_C_zero {m : Finset I → M} (hm : m ∈ C (P := P) (I := I) M 0) :
    d x M m = 0 := by
  funext T
  rw [d_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i ∈ T
  · rw [coef_of_mem x hi, zero_smul]
  · rw [hm _ (by rw [Finset.card_insert_of_notMem hi]; omega), smul_zero]

noncomputable def complex : ChainComplex (ModuleCat.{v'} P) ℕ :=
  ChainComplex.of (fun p => ModuleCat.of P (C (P := P) (I := I) M p))
      (fun p => ModuleCat.ofHom (dC x M p))
    fun p => by ext m : 2; exact dC_dC x M p m

private theorem complex_d (p : ℕ) : (complex x M).d (p + 1) p = ModuleCat.ofHom (dC x M p) := by
  simp [complex]

noncomputable def scZ (p : ℕ) : ShortComplex (ModuleCat.{v'} P) :=
  ShortComplex.mk (ModuleCat.ofHom (dC x M p) : ModuleCat.of P (C (P := P) (I := I) M (p + 1))
      ⟶ ModuleCat.of P (C (P := P) (I := I) M p))
    (ModuleCat.ofHom ((d x M).domRestrict (C (P := P) (I := I) M p)) :
      ModuleCat.of P (C (P := P) (I := I) M p) ⟶ ModuleCat.of P (Finset I → M))
    (by ext m : 2; simp [d_d])

noncomputable def scToScZ (p : ℕ) :
    (complex x M).sc' (p + 1) p ((ComplexShape.down ℕ).next p) ⟶ scZ x M p where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := ModuleCat.ofHom (C (P := P) (I := I) M ((ComplexShape.down ℕ).next p)).subtype
  comm₁₂ := by
    change 𝟙 _ ≫ ModuleCat.ofHom (dC x M p) = (complex x M).d (p + 1) p ≫ 𝟙 _
    rw [Category.comp_id, Category.id_comp, complex_d]
  comm₂₃ := by
    change 𝟙 _ ≫ ModuleCat.ofHom ((d x M).domRestrict (C (P := P) (I := I) M p)) =
      (complex x M).d p ((ComplexShape.down ℕ).next p) ≫ _
    rw [Category.id_comp]
    cases p with
    | zero =>
      rw [ChainComplex.next_nat_zero]
      have h0 : (complex x M).d 0 0 = 0 := (complex x M).shape _ _ (by simp)
      rw [h0]
      ext m : 2
      change d x M m = 0
      exact d_eq_zero_of_mem_C_zero x M m.2
    | succ q =>
      rw [show (ComplexShape.down ℕ).next (q + 1) = q from ChainComplex.next_nat_succ q, complex_d]
      rfl

scoped instance (p : ℕ) : Epi (scToScZ x M p).τ₁ := IsIso.epi_of_iso (𝟙 _)
scoped instance (p : ℕ) : IsIso (scToScZ x M p).τ₂ := IsIso.id _
scoped instance (p : ℕ) : Mono (scToScZ x M p).τ₃ :=
  (ModuleCat.mono_iff_injective _).mpr (Submodule.injective_subtype _)

abbrev X₂toC {p : ℕ} (k : (scZ x M p).X₂) : C (P := P) (I := I) M p := k

abbrev X₁toC {p : ℕ} (k : (scZ x M p).X₁) : C (P := P) (I := I) M (p + 1) := k

def kerEquivZ (p : ℕ) : LinearMap.ker (scZ x M p).g.hom ≃ₗ[P] Z x M p where
  toFun k := ⟨(X₂toC x M k.1).1, (X₂toC x M k.1).2, k.2⟩
  invFun z := ⟨(⟨z.1, z.2.1⟩ : C (P := P) (I := I) M p), z.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem map_kerEquivZ_range (p : ℕ) :
    (LinearMap.range (scZ x M p).moduleCatToCycles).map (kerEquivZ x M p : _ →ₗ[P] Z x M p) =
      (B x M p).comap (Z x M p).subtype := by
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_comap, Submodule.subtype_apply,
    B, exists_exists_eq_and]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨(X₁toC x M m).1, (X₁toC x M m).2, rfl⟩
  · rintro ⟨m, hm, hz⟩
    exact ⟨(⟨m, hm⟩ : C (P := P) (I := I) M (p + 1)), Subtype.ext hz⟩

noncomputable def scZHomologyEquiv (p : ℕ) :
    (LinearMap.ker (scZ x M p).g.hom ⧸ LinearMap.range (scZ x M p).moduleCatToCycles) ≃ₗ[P]
        H x M p :=
  Submodule.Quotient.equiv _ _ (kerEquivZ x M p) (map_kerEquivZ_range x M p)

noncomputable def bridge (p : ℕ) : (complex x M).homology p ≅ ModuleCat.of P (H x M p) :=
  (complex x M).homologyIsoSc' (p + 1) p _ (ChainComplex.prev ℕ p) rfl ≪≫
    asIso (ShortComplex.homologyMap (scToScZ x M p)) ≪≫ (scZ x M p).moduleCatHomologyIso ≪≫
      (scZHomologyEquiv x M p).toModuleIso

noncomputable def ZToCycles (p : ℕ) : ModuleCat.of P (Z x M p) ⟶ (complex x M).cycles p :=
  (complex x M).liftCycles (ModuleCat.ofHom (Submodule.inclusion inf_le_left :
    Z x M p →ₗ[P] C (P := P) (I := I) M p)) _ rfl (by
      cases p with
      | zero =>
        have h0 : (complex x M).d 0 ((ComplexShape.down ℕ).next 0) = 0 :=
          (complex x M).shape _ _ (by simp)
        rw [h0]
        exact Limits.comp_zero
      | succ q =>
        rw [show (ComplexShape.down ℕ).next (q + 1) = q from ChainComplex.next_nat_succ q,
            complex_d]
        ext z : 2
        exact Subtype.ext (LinearMap.mem_ker.mp z.2.2))

private theorem ZToCycles_comp (p : ℕ) :
    ZToCycles x M p ≫ ((complex x M).cyclesIsoSc' (p + 1) p _ (ChainComplex.prev ℕ p) rfl).hom ≫
      ShortComplex.cyclesMap (scToScZ x M p) ≫ (scZ x M p).moduleCatCyclesIso.hom =
        (kerEquivZ x M p).symm.toModuleIso.hom := by
  rw [← cancel_mono (scZ x M p).moduleCatLeftHomologyData.i, Category.assoc, Category.assoc,
    Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i, ShortComplex.cyclesMap_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles_assoc, ZToCycles]
  erw [HomologicalComplex.liftCycles_i_assoc]
  rfl

scoped instance isIso_ZToCycles (p : ℕ) : IsIso (ZToCycles x M p) :=
  IsIso.of_isIso_fac_right (ZToCycles_comp x M p)

private theorem ZToCycles_π_bridge (p : ℕ) :
    ZToCycles x M p ≫ (complex x M).homologyπ p ≫ (bridge x M p).hom =
      ModuleCat.ofHom ((B x M p).comap (Z x M p).subtype).mkQ := by
  rw [bridge, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, asIso_hom,
    HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.homologyπ_naturality_assoc,
    ShortComplex.π_moduleCatCyclesIso_hom_assoc, reassoc_of% (ZToCycles_comp x M p)]
  ext z : 2
  change scZHomologyEquiv x M p (Submodule.Quotient.mk ((kerEquivZ x M p).symm z)) = _
  rw [scZHomologyEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rfl

end Complex

section Functoriality

variable {P : Type u'} [CommRing P]
variable {I : Type} [LinearOrder I] [Fintype I] {J : Type} [LinearOrder J] [Fintype J]
variable {L : Type} [LinearOrder L] [Fintype L]
variable {x : I → P} {M : Type v'} [AddCommGroup M] [Module P M]
variable {y : J → P} {N : Type v'} [AddCommGroup N] [Module P N]
variable {w : L → P} {O : Type v'} [AddCommGroup O] [Module P O]

variable (x M y N) in
structure HMap where
  toLinearMap : (Finset I → M) →ₗ[P] (Finset J → N)
  map_Z : ∀ p, Z x M p ≤ (Z y N p).comap toLinearMap
  map_B : ∀ p, B x M p ≤ (B y N p).comap toLinearMap

namespace HMap

def mapZ (f : HMap x M y N) (p : ℕ) : Z x M p →ₗ[P] Z y N p :=
  f.toLinearMap.restrict fun _ hz => f.map_Z p hz

@[scoped simp] private theorem coe_mapZ (f : HMap x M y N) (p : ℕ) (z : Z x M p) :
    (f.mapZ p z : Finset J → N) = f.toLinearMap z := rfl

def mapH (f : HMap x M y N) (p : ℕ) : H x M p →ₗ[P] H y N p :=
  Submodule.mapQ _ _ (f.mapZ p) fun _ hz => f.map_B p hz

@[scoped simp] private theorem mapH_mk (f : HMap x M y N) (p : ℕ) (z : Z x M p) :
    f.mapH p (Submodule.Quotient.mk z) = Submodule.Quotient.mk (f.mapZ p z) := rfl

variable (x M) in
protected def id : HMap x M x M where
  toLinearMap := LinearMap.id
  map_Z _ _ hz := hz
  map_B _ _ hz := hz

def comp (g : HMap y N w O) (f : HMap x M y N) : HMap x M w O where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  map_Z p _ hz := g.map_Z p (f.map_Z p hz)
  map_B p _ hz := g.map_B p (f.map_B p hz)

@[scoped simp] private theorem comp_toLinearMap (g : HMap y N w O) (f : HMap x M y N) :
    (g.comp f).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap := rfl

private theorem mapH_id (p : ℕ) : (HMap.id x M).mapH p = LinearMap.id := by
  ext; rfl

private theorem mapH_comp (g : HMap y N w O) (f : HMap x M y N) (p : ℕ) :
    (g.comp f).mapH p = g.mapH p ∘ₗ f.mapH p := by
  ext; rfl

private theorem mapH_congr {f g : HMap x M y N} (h : f.toLinearMap = g.toLinearMap) (p : ℕ) :
    f.mapH p = g.mapH p := by
  ext z
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, mapH_mk]
  congr 1; ext1; simp [h]

def mapHEquiv (f : HMap x M y N) (g : HMap y N x M)
    (hfg : g.toLinearMap ∘ₗ f.toLinearMap = LinearMap.id)
    (hgf : f.toLinearMap ∘ₗ g.toLinearMap = LinearMap.id) (p : ℕ) : H x M p ≃ₗ[P] H y N p :=
  LinearEquiv.ofLinearMap (f.mapH p) (g.mapH p)
    (by rw [← mapH_comp, mapH_congr (f := f.comp g) (g := HMap.id y N) hgf, mapH_id])
    (by rw [← mapH_comp, mapH_congr (f := g.comp f) (g := HMap.id x M) hfg, mapH_id])

end HMap
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap

variable (x M y N) in
structure ChainMap where
  toLinearMap : (Finset I → M) →ₗ[P] (Finset J → N)
  comm : toLinearMap ∘ₗ d x M = d y N ∘ₗ toLinearMap
  map_C : ∀ p, C (P := P) (I := I) M p ≤ (C (P := P) (I := J) N p).comap toLinearMap

namespace ChainMap

private theorem comm_apply (f : ChainMap x M y N) (m : Finset I → M) :
    f.toLinearMap (d x M m) = d y N (f.toLinearMap m) :=
  congr($f.comm m)

def toHMap (f : ChainMap x M y N) : HMap x M y N where
  toLinearMap := f.toLinearMap
  map_Z p m hm := ⟨f.map_C p hm.1, by
    change d y N (f.toLinearMap m) = 0
    rw [← f.comm_apply, LinearMap.mem_ker.mp hm.2, map_zero]⟩
  map_B p m hm := by
    obtain ⟨m', hm', rfl⟩ := hm
    exact ⟨f.toLinearMap m', f.map_C _ hm', (f.comm_apply m').symm⟩

@[scoped simp] private theorem toHMap_toLinearMap (f : ChainMap x M y N) :
    f.toHMap.toLinearMap = f.toLinearMap := rfl

abbrev mapH (f : ChainMap x M y N) (p : ℕ) : H x M p →ₗ[P] H y N p := f.toHMap.mapH p

def mapC (f : ChainMap x M y N) (p : ℕ) :
    C (P := P) (I := I) M p →ₗ[P] C (P := P) (I := J) N p :=
  f.toLinearMap.restrict fun _ hm => f.map_C p hm

noncomputable def toHom (f : ChainMap x M y N) : complex x M ⟶ complex y N where
  f p := ModuleCat.ofHom (f.mapC p)
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [complex_d, complex_d]
    ext m : 2
    exact Subtype.ext (f.comm_apply _).symm

private theorem ZToCycles_cyclesMap (f : ChainMap x M y N) (p : ℕ) :
    ZToCycles x M p ≫ HomologicalComplex.cyclesMap f.toHom p =
      ModuleCat.ofHom (f.toHMap.mapZ p) ≫ ZToCycles y N p := by
  rw [← cancel_mono ((complex y N).iCycles p), Category.assoc, Category.assoc,
    HomologicalComplex.cyclesMap_i, ZToCycles, ZToCycles]
  erw [HomologicalComplex.liftCycles_i_assoc, HomologicalComplex.liftCycles_i]
  rfl

private theorem homologyMap_bridge (f : ChainMap x M y N) (p : ℕ) :
    HomologicalComplex.homologyMap f.toHom p ≫ (bridge y N p).hom =
      (bridge x M p).hom ≫ ModuleCat.ofHom (f.mapH p) := by
  have : Epi (ZToCycles x M p ≫ (complex x M).homologyπ p) := epi_comp _ _
  rw [← cancel_epi (ZToCycles x M p ≫ (complex x M).homologyπ p), Category.assoc, Category.assoc,
    HomologicalComplex.homologyπ_naturality_assoc, reassoc_of% (ZToCycles_cyclesMap f p),
    ZToCycles_π_bridge, reassoc_of% (ZToCycles_π_bridge x M p)]
  rfl

variable (x) in
def ofLinearMap {M' : Type v'} [AddCommGroup M'] [Module P M'] (φ : M →ₗ[P] M') :
    ChainMap x M x M' where
  toLinearMap := φ.compLeft (Finset I)
  comm := by
    ext m T S
    change φ (d x M (Pi.single m T) S) = d x M' (φ.compLeft _ (Pi.single m T)) S
    rw [d_apply, d_apply, map_sum]
    simp only [map_smul]
    rfl
  map_C p m hm T hT := by
    change φ (m T) = 0
    rw [hm T hT, map_zero]

end ChainMap
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap

end Functoriality
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap

end Koszul
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

namespace Koszul

universe u' v'

section Reindex

variable {P : Type u'} [CommRing P]
variable {I : Type} [LinearOrder I] [Fintype I] {J : Type} [LinearOrder J] [Fintype J]
variable (M : Type v') [AddCommGroup M] [Module P M]

variable (P) in
def reindexLin (e : I ≃ J) : (Finset J → M) ≃ₗ[P] (Finset I → M) where
  toFun m S := m (S.map e.toEmbedding)
  invFun m T := m (T.map e.symm.toEmbedding)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv m := by funext T; simp [Finset.map_map]
  right_inv m := by funext S; simp [Finset.map_map]

omit [LinearOrder I] [Fintype I] [LinearOrder J] [Fintype J] in
@[scoped simp] private theorem reindexLin_apply (e : I ≃ J) (m : Finset J → M) (S : Finset I) :
    reindexLin P M e m S = m (S.map e.toEmbedding) := rfl

omit [LinearOrder I] [Fintype I] [LinearOrder J] [Fintype J] in
private theorem reindexLin_mem_C_iff (e : I ≃ J) {p : ℕ} {m : Finset J → M} :
    reindexLin P M e m ∈ C (P := P) (I := I) M p ↔ m ∈ C (P := P) (I := J) M p := by
  simp only [mem_C, reindexLin_apply]
  constructor
  · intro h T hT
    have h' := h (T.map e.symm.toEmbedding) (by rwa [Finset.card_map])
    rwa [Finset.map_map, Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding,
      Finset.map_refl] at h'
  · intro h S hS
    exact h _ (by rwa [Finset.card_map])

omit [Fintype I] [Fintype J] in
private theorem sgn_map_orderIso (e : I ≃o J) (i : I) (T : Finset I) :
    sgn P (e i) (T.map e.toEquiv.toEmbedding) = sgn P i T := by
  rw [sgn, sgn, Finset.filter_map, Finset.card_map]
  congr 2
  exact Finset.filter_congr fun j _ => by simp

theorem d_reindexLin_orderIso (e : I ≃o J) (x : J → P) (m : Finset J → M) :
    d (x ∘ e) M (reindexLin P M e.toEquiv m) = reindexLin P M e.toEquiv (d x M m) := by
  funext T
  rw [d_apply, reindexLin_apply, d_apply]
  refine Fintype.sum_equiv e.toEquiv _ _ fun i => ?_
  rw [reindexLin_apply, Finset.map_insert, Equiv.coe_toEmbedding, OrderIso.coe_toEquiv]
  have hi' : e i ∈ T.map e.toEquiv.toEmbedding ↔ i ∈ T := Finset.mem_map' _
  by_cases hi : i ∈ T
  · rw [coef_of_mem _ hi, coef_of_mem _ (hi'.mpr hi)]
  · rw [coef_of_not_mem _ hi, coef_of_not_mem _ (mt hi'.mp hi), sgn_map_orderIso,
      Function.comp_apply]

def reindex (e : I ≃o J) (x : J → P) : ChainMap x M (x ∘ e) M where
  toLinearMap := reindexLin P M e.toEquiv
  comm := LinearMap.ext fun m => (d_reindexLin_orderIso M e x m).symm
  map_C p m hm := by
    change reindexLin P M e.toEquiv m ∈ C (P := P) (I := I) M p
    exact (reindexLin_mem_C_iff M e.toEquiv).mpr hm

def reindexInv (e : I ≃o J) (x : J → P) : ChainMap (x ∘ e) M x M where
  toLinearMap := reindexLin P M e.symm.toEquiv
  comm := by
    refine LinearMap.ext fun m => ?_
    have h := d_reindexLin_orderIso M e.symm (x ∘ e) m
    rw [show (x ∘ e) ∘ e.symm = x from funext fun j => congrArg x (e.apply_symm_apply j)] at h
    exact h.symm
  map_C p m hm := by
    change reindexLin P M e.symm.toEquiv m ∈ C (P := P) (I := J) M p
    exact (reindexLin_mem_C_iff M e.symm.toEquiv).mpr hm

def reindexH (e : I ≃o J) (x : J → P) (p : ℕ) : H (x ∘ e) M p ≃ₗ[P] H x M p :=
  ((reindexInv M e x).toHMap.mapHEquiv (reindex M e x).toHMap
    (LinearMap.ext fun m => (reindexLin P M e.toEquiv).apply_symm_apply m)
    (LinearMap.ext fun m => (reindexLin P M e.toEquiv).symm_apply_apply m) p)

private theorem neg_one_pow_mul_self (n : ℕ) : ((-1 : P) ^ n) * (-1) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

omit [LinearOrder I] [Fintype I] in
private theorem map_toDual_map_ofDual (S : Finset I) :
    (S.map OrderDual.toDual.toEmbedding).map OrderDual.ofDual.toEmbedding = S := by
  rw [Finset.map_map, ← OrderDual.toDual_symm_eq,
    Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding, Finset.map_refl]

omit [Fintype I] in
private theorem sgn_dual (i : I) (T : Finset I) (hi : i ∉ T) :
    sgn P (OrderDual.toDual i) (T.map OrderDual.toDual.toEmbedding) = (-1) ^ T.card * sgn P i T :=
        by
  have hgt : (T.filter fun j => ¬j < i) = T.filter fun j => i < j :=
    Finset.filter_congr fun j hj =>
      ⟨fun h => lt_of_le_of_ne (not_lt.mp h) (ne_of_mem_of_not_mem hj hi).symm,
        fun h => not_lt.mpr h.le⟩
  have hcard : (T.filter (· < i)).card + (T.filter fun j => i < j).card = T.card := by
    rw [← hgt]; exact Finset.card_filter_add_card_filter_not _
  rw [sgn, sgn, Finset.filter_map, Finset.card_map,
    Finset.filter_congr (q := fun j => i < j) fun j _ => by simp, ← hcard, pow_add,
    mul_right_comm, neg_one_pow_mul_self, one_mul]

omit [Fintype I] in
private theorem sgn_ofDual {i : Iᵒᵈ} {T : Finset Iᵒᵈ} (hi : i ∉ T) :
    sgn P i T = (-1) ^ T.card * sgn P (OrderDual.ofDual i) (T.map OrderDual.ofDual.toEmbedding) :=
        by
  have h := sgn_dual (P := P) (OrderDual.ofDual i) (T.map OrderDual.ofDual.toEmbedding)
    fun h => hi ((Finset.mem_map' _).mp h)
  rw [Finset.card_map, ← OrderDual.ofDual_symm_eq, Equiv.symm_apply_apply, Finset.map_map,
    Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding, Finset.map_refl] at h
  exact h

private theorem d_reindexLin_dual (x : I → P) (m : Finset I → M) (T : Finset Iᵒᵈ) :
    d (x ∘ OrderDual.ofDual) M (reindexLin P M OrderDual.ofDual m) T =
      ((-1 : P) ^ T.card) • reindexLin P M OrderDual.ofDual (d x M m) T := by
  rw [d_apply, reindexLin_apply, d_apply, Finset.smul_sum]
  refine Fintype.sum_equiv OrderDual.ofDual _ _ fun i => ?_
  rw [reindexLin_apply, Finset.map_insert, Equiv.coe_toEmbedding, smul_smul]
  have hi' : OrderDual.ofDual i ∈ T.map OrderDual.ofDual.toEmbedding ↔ i ∈ T :=
    Finset.mem_map' _
  by_cases hi : i ∈ T
  · rw [coef_of_mem _ hi, coef_of_mem _ (hi'.mpr hi), mul_zero]
  · rw [coef_of_not_mem _ hi, coef_of_not_mem _ (mt hi'.mp hi), sgn_ofDual hi, mul_assoc,
      Function.comp_apply]

private theorem d_reindexLin_toDual (x : I → P) (n : Finset Iᵒᵈ → M) (S : Finset I) :
    d x M (reindexLin P M OrderDual.toDual n) S =
      ((-1 : P) ^ S.card) • reindexLin P M OrderDual.toDual (d (x ∘ OrderDual.ofDual) M n) S := by
  have h := d_reindexLin_dual M x (reindexLin P M OrderDual.toDual n)
    (S.map OrderDual.toDual.toEmbedding)
  rw [Finset.card_map, reindexLin_apply, map_toDual_map_ofDual,
    show reindexLin P M OrderDual.ofDual (reindexLin P M OrderDual.toDual n) = n from
      (reindexLin P M OrderDual.ofDual).apply_symm_apply n] at h
  rw [reindexLin_apply, h, smul_smul, neg_one_pow_mul_self, one_smul]

def reverse (x : I → P) : HMap x M (x ∘ OrderDual.ofDual) M where
  toLinearMap := reindexLin P M (OrderDual.ofDual : Iᵒᵈ ≃ I)
  map_Z p m hm := by
    refine ⟨(reindexLin_mem_C_iff M OrderDual.ofDual).mpr hm.1, ?_⟩
    change d (x ∘ OrderDual.ofDual) M (reindexLin P M OrderDual.ofDual m) = 0
    funext T
    rw [Pi.zero_apply, d_reindexLin_dual, reindexLin_apply, LinearMap.mem_ker.mp hm.2,
      Pi.zero_apply, smul_zero]
  map_B p m hm := by
    obtain ⟨m', hm', rfl⟩ := hm
    refine ⟨((-1 : P) ^ p) • reindexLin P M OrderDual.ofDual m',
      Submodule.smul_mem _ _ ((reindexLin_mem_C_iff M OrderDual.ofDual).mpr hm'), ?_⟩
    change d (x ∘ OrderDual.ofDual) M (((-1 : P) ^ p) • reindexLin P M OrderDual.ofDual m') =
      reindexLin P M OrderDual.ofDual (d x M m')
    funext T
    rw [LinearMap.map_smul, Pi.smul_apply, d_reindexLin_dual, smul_smul, reindexLin_apply]
    by_cases hT : T.card = p
    · rw [hT, neg_one_pow_mul_self, one_smul]
    · rw [d_mem_C x M hm' (T.map OrderDual.ofDual.toEmbedding)
        (by rwa [Finset.card_map]), smul_zero]

def reverseInv (x : I → P) : HMap (x ∘ OrderDual.ofDual) M x M where
  toLinearMap := reindexLin P M (OrderDual.toDual : I ≃ Iᵒᵈ)
  map_Z p m hm := by
    refine ⟨(reindexLin_mem_C_iff M OrderDual.toDual).mpr hm.1, ?_⟩
    change d x M (reindexLin P M OrderDual.toDual m) = 0
    funext S
    rw [Pi.zero_apply, d_reindexLin_toDual, reindexLin_apply, LinearMap.mem_ker.mp hm.2,
      Pi.zero_apply, smul_zero]
  map_B p m hm := by
    obtain ⟨m', hm', rfl⟩ := hm
    refine ⟨((-1 : P) ^ p) • reindexLin P M OrderDual.toDual m',
      Submodule.smul_mem _ _ ((reindexLin_mem_C_iff M OrderDual.toDual).mpr hm'), ?_⟩
    change d x M (((-1 : P) ^ p) • reindexLin P M OrderDual.toDual m') =
      reindexLin P M OrderDual.toDual (d (x ∘ OrderDual.ofDual) M m')
    funext S
    rw [LinearMap.map_smul, Pi.smul_apply, d_reindexLin_toDual, smul_smul, reindexLin_apply]
    by_cases hS : S.card = p
    · rw [hS, neg_one_pow_mul_self, one_smul]
    · rw [d_mem_C (x ∘ OrderDual.ofDual) M hm' (S.map OrderDual.toDual.toEmbedding)
        (by rwa [Finset.card_map]), smul_zero]

def reverseH (x : I → P) (p : ℕ) : H (x ∘ OrderDual.ofDual) M p ≃ₗ[P] H x M p :=
  (reverseInv M x).mapHEquiv (reverse M x)
    (LinearMap.ext fun m => (reindexLin P M (OrderDual.ofDual : Iᵒᵈ ≃ I)).apply_symm_apply m)
    (LinearMap.ext fun m => (reindexLin P M (OrderDual.ofDual : Iᵒᵈ ≃ I)).symm_apply_apply m) p

end Reindex
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section Ends

variable {P : Type u'} [CommRing P] {I : Type} [LinearOrder I] [Fintype I]
variable (x : I → P) (M : Type v') [AddCommGroup M] [Module P M]

def annihilatedBy : Submodule P M where
  carrier := {m | ∀ i, x i • m = 0}
  add_mem' ha hb i := by simp [smul_add, ha i, hb i]
  zero_mem' i := smul_zero _
  smul_mem' c m hm i := by rw [smul_comm, hm i, smul_zero]

omit [LinearOrder I] in
private theorem C_eq_bot_of_card_lt {p : ℕ} (hp : Fintype.card I < p) : C (P := P)
    (I := I) M p = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun m hm => funext fun T => hm T ?_
  have := Finset.card_le_univ T
  omega

private theorem subsingleton_H_of_card_lt {p : ℕ} (hp : Fintype.card I < p) :
    Subsingleton (H x M p) := by
  have hZ : ∀ z : Z x M p, z = 0 := fun z => by
    have h : (z : Finset I → M) ∈ C (P := P) (I := I) M p := z.2.1
    rw [C_eq_bot_of_card_lt M hp, Submodule.mem_bot] at h
    exact Subtype.ext h
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [hZ a, hZ b]

omit [Fintype I] in
private theorem coef_smul_of_forall_smul_eq_zero {m : M} (hm : ∀ i, x i • m = 0) (i : I)
    (T : Finset I) : coef x i T • m = 0 := by
  by_cases hi : i ∈ T
  · rw [coef_of_mem x hi, zero_smul]
  · rw [coef_of_not_mem x hi, mul_smul, hm i, smul_zero]

private theorem d_apply_univ_erase (m : Finset I → M) (i : I) :
    d x M m (univ.erase i) = (sgn P i (univ.erase i) * x i) • m univ := by
  rw [d_apply, Finset.sum_eq_single i, coef_of_not_mem x (Finset.notMem_erase i univ),
    Finset.insert_erase (Finset.mem_univ i)]
  · intro j _ hji
    rw [coef_of_mem x (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩), zero_smul]
  · exact fun h => absurd (Finset.mem_univ i) h

theorem smul_apply_univ_eq_zero {m : Finset I → M} (hm : d x M m = 0) (i : I) :
    x i • m univ = 0 := by
  have h : (sgn P i (univ.erase i) * x i) • m univ = 0 := by
    rw [← d_apply_univ_erase, hm, Pi.zero_apply]
  calc x i • m univ = sgn P i (univ.erase i) • ((sgn P i (univ.erase i) * x i) • m univ) := by
        rw [smul_smul, ← mul_assoc, sgn_mul_self, one_mul]
    _ = 0 := by rw [h, smul_zero]

def evalTop : Z x M (Fintype.card I) →ₗ[P] annihilatedBy x M where
  toFun z := ⟨(z : Finset I → M) univ, fun i =>
    smul_apply_univ_eq_zero x M (LinearMap.mem_ker.mp z.2.2) i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem single_univ_mem_C (m : M) :
    Pi.single (univ : Finset I) m ∈ C (P := P) (I := I) M (Fintype.card I) :=
  fun _ hT => Pi.single_eq_of_ne (fun h => hT (by rw [h, Finset.card_univ])) _

theorem d_single_univ (m : annihilatedBy x M) :
    d x M (Pi.single (univ : Finset I) (m : M)) = 0 := by
  funext T
  rw [d_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : insert i T = univ
  · rw [h, Pi.single_eq_same]
    exact coef_smul_of_forall_smul_eq_zero x M m.2 i T
  · rw [Pi.single_eq_of_ne h, smul_zero]

def topCycle : annihilatedBy x M →ₗ[P] Z x M (Fintype.card I) where
  toFun m := ⟨Pi.single (univ : Finset I) (m : M), single_univ_mem_C M (m : M),
    LinearMap.mem_ker.mpr (d_single_univ x M m)⟩
  map_add' a b := Subtype.ext (Pi.single_add (f := fun _ : Finset I => M) univ (a : M) (b : M))
  map_smul' c a := Subtype.ext (Pi.single_smul' (univ : Finset I) c (a : M))

theorem topCycle_evalTop (z : Z x M (Fintype.card I)) :
    topCycle x M (evalTop x M z) = z := by
  refine Subtype.ext (funext fun T => ?_)
  change (Pi.single univ ((z : Finset I → M) univ) : Finset I → M) T = (z : Finset I → M) T
  by_cases hT : T = univ
  · rw [hT, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hT]
    exact (z.2.1 T fun h => hT (Finset.eq_univ_of_card T h)).symm

theorem evalTop_topCycle (m : annihilatedBy x M) : evalTop x M (topCycle x M m) = m :=
  Subtype.ext (Pi.single_eq_same (M := fun _ : Finset I => M) univ (m : M))

theorem comap_B_top_eq_bot :
    (B x M (Fintype.card I)).comap (Z x M (Fintype.card I)).subtype = ⊥ := by
  rw [B, C_eq_bot_of_card_lt M (p := Fintype.card I + 1) (Nat.lt_succ_self _), Submodule.map_bot,
    Submodule.comap_bot, Submodule.ker_subtype]

def HTopEquiv : H x M (Fintype.card I) ≃ₗ[P] annihilatedBy x M := by
  exact LinearEquiv.ofLinearMap
    (((B x M (Fintype.card I)).comap (Z x M (Fintype.card I)).subtype).liftQ (evalTop x M)
      ((comap_B_top_eq_bot x M).le.trans bot_le))
    (((B x M (Fintype.card I)).comap (Z x M (Fintype.card I)).subtype).mkQ ∘ₗ topCycle x M)
    (LinearMap.ext (evalTop_topCycle x M))
    (Submodule.linearMap_qext _ (LinearMap.ext fun z =>
      congr_arg Submodule.Quotient.mk (topCycle_evalTop x M z)))

private theorem HTopEquiv_mk (z : Z x M (Fintype.card I)) :
    (HTopEquiv x M (Submodule.Quotient.mk z) : M) = (z : Finset I → M) Finset.univ := by
  rfl

omit [Fintype I] in
private theorem sgn_emptyset (i : I) : sgn P i ∅ = 1 := by
  simp [sgn]

omit [Fintype I] in
theorem single_empty_mem_C (m : M) :
    Pi.single (∅ : Finset I) m ∈ C (P := P) (I := I) M 0 :=
  fun _ hT => Pi.single_eq_of_ne (fun h => hT (Finset.card_eq_zero.mpr h)) _

omit [Fintype I] in
private theorem single_singleton_mem_C (i : I) (n : M) :
    Pi.single ({i} : Finset I) n ∈ C (P := P) (I := I) M 1 :=
  fun _ hT => Pi.single_eq_of_ne (fun h => hT (by rw [h, Finset.card_singleton])) _

def zeroCycleEquiv : Z x M 0 ≃ₗ[P] M where
  toFun z := (z : Finset I → M) ∅
  invFun m := ⟨Pi.single (∅ : Finset I) m, single_empty_mem_C M m,
    LinearMap.mem_ker.mpr (d_eq_zero_of_mem_C_zero x M (single_empty_mem_C M m))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by
    refine Subtype.ext (funext fun T => ?_)
    change (Pi.single ∅ ((z : Finset I → M) ∅) : Finset I → M) T = (z : Finset I → M) T
    by_cases hT : T = ∅
    · rw [hT, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hT]
      exact (z.2.1 T fun h => hT (Finset.card_eq_zero.mp h)).symm
  right_inv m := Pi.single_eq_same (M := fun _ : Finset I => M) ∅ m

private theorem zeroCycleEquiv_apply (z : Z x M 0) :
    zeroCycleEquiv x M z = (z : Finset I → M) ∅ := rfl

private theorem coe_zeroCycleEquiv_symm (m : M) :
    (((zeroCycleEquiv x M).symm m : Z x M 0) : Finset I → M) = Pi.single (∅ : Finset I) m := rfl

private theorem single_empty_smul_mem_B (i : I) (n : M) :
    Pi.single (∅ : Finset I) (x i • n) ∈ B x M 0 := by
  refine ⟨Pi.single ({i} : Finset I) n, single_singleton_mem_C M i n, ?_⟩
  funext T
  by_cases hT : T = ∅
  · rw [hT, Pi.single_eq_same, d_apply, Finset.sum_eq_single i]
    · rw [Finset.insert_empty, Pi.single_eq_same, coef_of_not_mem x (Finset.notMem_empty i),
        sgn_emptyset, one_mul]
    · intro j _ hji
      rw [Finset.insert_empty, Pi.single_eq_of_ne (Finset.singleton_injective.ne hji), smul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  · rw [Pi.single_eq_of_ne hT]
    exact d_mem_C x M (p := 0) (single_singleton_mem_C M i n) T
      fun h => hT (Finset.card_eq_zero.mp h)

theorem map_zeroCycleEquiv_comap_B :
    ((B x M 0).comap (Z x M 0).subtype).map (zeroCycleEquiv x M : Z x M 0 →ₗ[P] M) =
      Ideal.span (Set.range x) • ⊤ := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.mpr fun z hz => ?_)
    (Submodule.smul_le.mpr fun r hr n _ => ?_)
  · obtain ⟨m, -, hmz⟩ := hz
    have hz0 : d x M m ∅ = (z : Finset I → M) ∅ := congr_fun hmz ∅
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, zeroCycleEquiv_apply, ← hz0, d_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [coef_of_not_mem x (Finset.notMem_empty i)]
    exact Submodule.smul_mem_smul
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))) Submodule.mem_top
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hr
    rw [Finset.sum_smul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mul_smul]
    refine Submodule.smul_mem _ _ ⟨(zeroCycleEquiv x M).symm (x i • n), ?_,
      (zeroCycleEquiv x M).apply_symm_apply _⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Submodule.subtype_apply,
      coe_zeroCycleEquiv_symm]
    exact single_empty_smul_mem_B x M i n

def HZeroEquiv : H x M 0 ≃ₗ[P] M ⧸ (Ideal.span (Set.range x) • ⊤ : Submodule P M) := by
  exact Submodule.Quotient.equiv _ _ (zeroCycleEquiv x M) (map_zeroCycleEquiv_comap_B x M)

private theorem HZeroEquiv_mk (z : Z x M 0) :
    HZeroEquiv x M (Submodule.Quotient.mk z) = Submodule.Quotient.mk ((z : Finset I → M) ∅) := by
  rfl

end Ends
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section Htpy

variable (P : Type u') [CommRing P] {I : Type} [LinearOrder I] [Fintype I]
variable (M : Type v') [AddCommGroup M] [Module P M]

def contract (i : I) : (Finset I → M) →ₗ[P] (Finset I → M) where
  toFun m T := if i ∈ T then sgn P i (T.erase i) • m (T.erase i) else 0
  map_add' m m' := by funext T; by_cases h : i ∈ T <;> simp [h]
  map_smul' c m := by funext T; by_cases h : i ∈ T <;> simp [h, smul_comm c]

omit [Fintype I] in
private theorem contract_apply (i : I) (m : Finset I → M) (T : Finset I) :
    contract P M i m T = if i ∈ T then sgn P i (T.erase i) • m (T.erase i) else 0 := rfl

variable {P M} (x : I → P)

private theorem d_contract_add_contract_d (i : I) (m : Finset I → M) :
    d x M (contract P M i m) + contract P M i (d x M m) = x i • m := by
  funext T
  simp only [Pi.add_apply, Pi.smul_apply, contract_apply, d_apply]
  by_cases hi : i ∈ T
  · obtain ⟨S, hiS, rfl⟩ : ∃ S, i ∉ S ∧ T = insert i S :=
      ⟨T.erase i, Finset.notMem_erase i T, (Finset.insert_erase hi).symm⟩
    rw [ite_eq_left hi, Finset.erase_insert hiS, Finset.smul_sum, ← Finset.sum_add_distrib,
      Finset.sum_eq_single i]
    · rw [coef_of_mem x hi, zero_smul, zero_add, coef_of_not_mem x hiS, smul_smul, ← mul_assoc,
        sgn_mul_self, one_mul]
    · intro j _ hji
      by_cases hjS : j ∈ S
      · rw [coef_of_mem x (Finset.mem_insert_of_mem hjS), coef_of_mem x hjS, zero_smul, zero_add,
          zero_smul, smul_zero]
      have hjT : j ∉ insert i S := by simp [hji, hjS]
      rw [ite_eq_left (Finset.mem_insert_of_mem (Finset.mem_insert_self i S) :
          i ∈ insert j (insert i S)),
        (Finset.erase_insert_of_ne hji).trans (congrArg _ (Finset.erase_insert hiS)),
        coef_of_not_mem x hjT, coef_of_not_mem x hjS, smul_smul, smul_smul, ← add_smul]
      suffices h0 : sgn P j (insert i S) * x j * sgn P i (insert j S) + sgn P i S *
          (sgn P j S * x j) = 0 by
        rw [h0, zero_smul]
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · rw [sgn_insert_of_lt P hjS hlt, sgn_insert_of_not_lt P (not_lt.mpr hlt.le)]; ring
      · rw [sgn_insert_of_not_lt P (not_lt.mpr hgt.le), sgn_insert_of_lt P hiS hgt]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [ite_eq_right hi, add_zero, Finset.sum_eq_single i]
    · rw [ite_eq_left (Finset.mem_insert_self i T), Finset.erase_insert hi, coef_of_not_mem x hi,
        smul_smul, mul_right_comm, sgn_mul_self, one_mul]
    · intro j _ hji
      rw [ite_eq_right, smul_zero]
      simp [Ne.symm hji, hi]
    · intro h; exact absurd (Finset.mem_univ i) h

omit [Fintype I] in
private theorem contract_mem_C (i : I) {p : ℕ} {m : Finset I → M}
    (hm : m ∈ C (P := P) (I := I) M p) : contract P M i m ∈ C (P := P) (I := I) M (p + 1) := by
  intro T hT
  rw [contract_apply]
  split_ifs with hiT
  · rw [hm _ (fun h => hT (by rw [← Finset.card_erase_add_one hiT, h])), smul_zero]
  · rfl

variable {x}

private theorem smul_H_eq_zero (i : I) {p : ℕ} (h : H x M p) : x i • h = 0 := by
  induction h using Submodule.Quotient.induction_on with
  | H z =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_smul]
    refine ⟨contract P M i z, contract_mem_C i z.2.1, ?_⟩
    have h := d_contract_add_contract_d x i (z : Finset I → M)
    rwa [LinearMap.mem_ker.mp z.2.2, map_zero, add_zero] at h

private theorem smul_H_eq_zero_of_mem_span {p : ℕ} (a : P) (ha : a ∈ Ideal.span (Set.range x))
    (h : H x M p) : a • h = 0 := by
  induction ha using Submodule.span_induction with
  | mem r hr => obtain ⟨i, rfl⟩ := hr; exact smul_H_eq_zero i h
  | zero => exact zero_smul P h
  | add r s _ _ hr hs => rw [add_smul, hr, hs, add_zero]
  | smul r s _ hs => rw [smul_eq_mul, mul_smul, hs, smul_zero]

end Htpy
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section ClassLemmas

variable {P : Type u'} [CommRing P] {I : Type} [LinearOrder I] [Fintype I]
variable {x : I → P} {M : Type v'} [AddCommGroup M] [Module P M]

private theorem H_mk_eq_zero_iff {p : ℕ} (z : Z x M p) :
    (Submodule.Quotient.mk z : H x M p) = 0 ↔ (z : Finset I → M) ∈ B x M p := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]

private theorem H_mk_eq_mk_iff {p : ℕ} (z z' : Z x M p) :
    (Submodule.Quotient.mk z : H x M p) = Submodule.Quotient.mk z' ↔ (z : Finset I → M) - z' ∈
        B x M p := by
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub]

end ClassLemmas
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section Cone

variable {P : Type u'} [CommRing P] {I : Type} [LinearOrder I] [Fintype I]
variable {U : Type} [LinearOrder U] [Fintype U] [Unique U]
variable {J : Type} [LinearOrder J] [Fintype J]

variable (U) in
def snoc (x : I → P) (t : P) : I ⊕ₗ U → P := fun k => Sum.elim x (fun _ => t) (ofLex k)

variable (I U) in
def top : I ⊕ₗ U := toLex (Sum.inr default)

variable (U) in
def inlₗ : I ↪ I ⊕ₗ U := ⟨fun i => toLex (Sum.inl i), fun _ _ h => Sum.inl_injective
    (toLex.injective h)⟩

omit [CommRing P] [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] [Unique U] in
@[scoped simp] private theorem snoc_inl (x : I → P) (t : P) (i : I) : snoc U x t (inlₗ U i) = x
    i := rfl
omit [CommRing P] [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] in
@[scoped simp] private theorem snoc_top (x : I → P) (t : P) : snoc U x t (top I U) = t := rfl

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] in
private theorem lex_cases (k : I ⊕ₗ U) : (∃ i, k = inlₗ U i) ∨ k = top I U := by
  obtain ⟨k, rfl⟩ := toLex.surjective k
  rcases k with i | u
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr (by rw [Subsingleton.elim u default]; rfl)

omit [Fintype I] [Fintype U] in
private theorem inlₗ_lt_top (i : I) : inlₗ U i < top I U := Sum.Lex.inl_lt_inr _ _

omit [Fintype I] [Fintype U] in
private theorem not_top_lt_inlₗ (i : I) : ¬top I U < inlₗ U i := Sum.Lex.not_inr_lt_inl

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] in
private theorem inlₗ_ne_top (i : I) : inlₗ U i ≠ top I U :=
    fun h => Sum.inl_ne_inr (toLex.injective h)

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] in
private theorem top_notMem_map (T : Finset I) : top I U ∉ T.map (inlₗ U) := by
  simp only [Finset.mem_map, not_exists, not_and]
  exact fun i _ h => inlₗ_ne_top i h

variable (U) in
noncomputable def down (S : Finset (I ⊕ₗ U)) : Finset I := S.preimage (inlₗ U)
    (inlₗ U).injective.injOn

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] [Unique U] in
@[scoped simp] private theorem mem_down {S : Finset (I ⊕ₗ U)} {i : I} : i ∈ down U S ↔ inlₗ U i ∈
    S :=
  Finset.mem_preimage

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] [Unique U] in
@[scoped simp] private theorem down_map (T : Finset I) : down U (T.map (inlₗ U)) = T := by
  ext i; simp

omit [Fintype I] [Fintype U] in
@[scoped simp] private theorem down_insert_top (S : Finset (I ⊕ₗ U)) : down U (insert (top I U) S)
    = down U
    S := by
  ext i; simp [inlₗ_ne_top]

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] in
private theorem eq_map_down {S : Finset (I ⊕ₗ U)} (h : top I U ∉ S) :
    S = (down U S).map (inlₗ U) := by
  ext k
  rcases lex_cases k with ⟨i, rfl⟩ | rfl
  · simp
  · simp only [top_notMem_map, iff_false]; exact h

omit [Fintype I] [Fintype U] in
private theorem eq_insert_map_down {S : Finset (I ⊕ₗ U)} (h : top I U ∈ S) :
    S = insert (top I U) ((down U S).map (inlₗ U)) := by
  ext k
  rcases lex_cases k with ⟨i, rfl⟩ | rfl
  · simp [inlₗ_ne_top]
  · simp only [Finset.mem_insert, true_or, iff_true]; exact h

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] in
private theorem card_down_of_notMem {S : Finset (I ⊕ₗ U)}
    (h : top I U ∉ S) : (down U S).card = S.card := by
  rw [← Finset.card_map (inlₗ U), ← eq_map_down h]

omit [Fintype I] [Fintype U] in
private theorem card_insert_top_map (T : Finset I) : (insert (top I U) (T.map (inlₗ U))).card =
    T.card + 1 := by
  rw [Finset.card_insert_of_notMem (top_notMem_map T), Finset.card_map]

omit [Fintype I] [Fintype U] in
private theorem card_down_of_mem {S : Finset (I ⊕ₗ U)} (h : top I U ∈ S) :
    (down U S).card + 1 = S.card :=
    by
  rw [← card_insert_top_map (U := U) (down U S), ← eq_insert_map_down h]

omit [Fintype I] [Fintype U] [Unique U] in
private theorem map_insert_inlₗ (i : I) (T : Finset I) :
    (insert i T).map (inlₗ U) = insert (inlₗ U i) (T.map (inlₗ U)) := Finset.map_insert _ _ _

omit [LinearOrder I] [LinearOrder U] in
private theorem sum_lex {A : Type*} [AddCommMonoid A] (f : I ⊕ₗ U → A) :
    ∑ k, f k = ∑ i, f (inlₗ U i) + f (top I U) := by
  rw [← Fintype.sum_equiv toLex (fun k => f (toLex k)) f (fun _ => rfl), Fintype.sum_sum_type]
  congr 1
  exact Fintype.sum_unique (fun u : U => f (toLex (Sum.inr u)))

omit [Fintype I] [Fintype U] [Unique U] in
private theorem sgn_inlₗ_map (i : I) (T : Finset I) : sgn P (inlₗ U i)
    (T.map (inlₗ U)) = sgn P i T := by
  rw [sgn, sgn, Finset.filter_map, Finset.card_map]
  congr 2

omit [Fintype I] [Fintype U] in
private theorem sgn_inlₗ_insert_top (i : I) (T : Finset I) :
    sgn P (inlₗ U i) (insert (top I U) (T.map (inlₗ U))) = sgn P i T := by
  erw [sgn_insert_of_not_lt P (not_top_lt_inlₗ i)]
  rw [sgn_inlₗ_map]

omit [Fintype I] [Fintype U] in
private theorem sgn_top_map (T : Finset I) : sgn P (top I U) (T.map (inlₗ U)) = (-1) ^ T.card := by
  rw [sgn, Finset.filter_true_of_mem, Finset.card_map]
  simp only [Finset.mem_map, forall_exists_index, and_imp]
  rintro _ i _ rfl; exact inlₗ_lt_top i

omit [Fintype I] [Fintype U] [Unique U] in
private theorem coef_snoc_inlₗ_map (x : I → P) (t : P) (i : I) (T : Finset I) :
    coef (snoc U x t) (inlₗ U i) (T.map (inlₗ U)) = coef x i T := by
  by_cases hi : i ∈ T
  · rw [coef_of_mem _ ((Finset.mem_map' _).mpr hi), coef_of_mem _ hi]
  · rw [coef_of_not_mem _ (fun h => hi ((Finset.mem_map' _).mp h)), coef_of_not_mem _ hi,
      sgn_inlₗ_map, snoc_inl]

omit [Fintype I] [Fintype U] in
private theorem coef_snoc_inlₗ_insert_top (x : I → P) (t : P) (i : I) (T : Finset I) :
    coef (snoc U x t) (inlₗ U i) (insert (top I U) (T.map (inlₗ U))) = coef x i T := by
  have hmem : inlₗ U i ∈ insert (top I U) (T.map (inlₗ U)) ↔ i ∈ T := by
    simp [inlₗ_ne_top]
  by_cases hi : i ∈ T
  · rw [coef_of_mem _ (hmem.mpr hi), coef_of_mem _ hi]
  · rw [coef_of_not_mem _ (fun h => hi (hmem.mp h)), coef_of_not_mem _ hi, sgn_inlₗ_insert_top,
      snoc_inl]

omit [Fintype I] [Fintype U] in
private theorem coef_snoc_top_map (x : I → P) (t : P) (T : Finset I) :
    coef (snoc U x t) (top I U) (T.map (inlₗ U)) = (-1) ^ T.card * t := by
  rw [coef_of_not_mem _ (top_notMem_map T), sgn_top_map, snoc_top]

private theorem d_snoc_apply_map (x : I → P) (t : P) {M : Type v'} [AddCommGroup M] [Module P M]
    (m : Finset (I ⊕ₗ U) → M) (T : Finset I) : d (snoc U x t) M m (T.map (inlₗ U)) =
      ∑ i, coef x i T • m ((insert i T).map (inlₗ U)) + ((-1) ^ T.card * t) •
          m (insert (top I U) (T.map (inlₗ U))) := by
  rw [d_apply, sum_lex]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by rw [coef_snoc_inlₗ_map, map_insert_inlₗ]; rfl
  · rw [coef_snoc_top_map]; rfl

private theorem d_snoc_apply_insert_top (x : I → P) (t : P) {M : Type v'} [AddCommGroup M]
    [Module P M] (m : Finset (I ⊕ₗ U) → M) (T : Finset I) :
    d (snoc U x t) M m (insert (top I U) (T.map (inlₗ U))) =
      ∑ i, coef x i T • m (insert (top I U) ((insert i T).map (inlₗ U))) := by
  rw [d_apply, sum_lex, coef_of_mem _ (Finset.mem_insert_self _ _), zero_smul, add_zero]
  exact Finset.sum_congr rfl fun i _ =>
      by rw [coef_snoc_inlₗ_insert_top, map_insert_inlₗ, Finset.insert_comm]; rfl

variable (x : I → P) (t : P) (M : Type v') [AddCommGroup M] [Module P M]
variable {y : J → P} {N : Type v'} [AddCommGroup N] [Module P N]

variable (P U) in
def coneRes : (Finset (I ⊕ₗ U) → M) →ₗ[P] (Finset I → M) where
  toFun m T := m (T.map (inlₗ U))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (P U) in
def coneProj : (Finset (I ⊕ₗ U) → M) →ₗ[P] (Finset I → M) where
  toFun m T := m (insert (top I U) (T.map (inlₗ U)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (P U) in
noncomputable def coneInclLin : (Finset I → M) →ₗ[P] (Finset (I ⊕ₗ U) → M) where
  toFun m S := if top I U ∈ S then 0 else m (S.preimage (inlₗ U) (inlₗ U).injective.injOn)
  map_add' m m' := by funext S; by_cases h : top I U ∈ S <;> simp [h]
  map_smul' c m := by funext S; by_cases h : top I U ∈ S <;> simp [h]

variable (P U) in
noncomputable def coneCoprojLin : (Finset I → M) →ₗ[P] (Finset (I ⊕ₗ U) → M) where
  toFun m S := if top I U ∈ S then m (S.preimage (inlₗ U) (inlₗ U).injective.injOn) else 0
  map_add' m m' := by funext S; by_cases h : top I U ∈ S <;> simp [h]
  map_smul' c m := by funext S; by_cases h : top I U ∈ S <;> simp [h]

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] [Unique U] in
@[scoped simp] private theorem coneRes_apply (m : Finset (I ⊕ₗ U) → M) (T : Finset I) :
    coneRes P U M m T = m (T.map (inlₗ U)) := rfl

omit [Fintype I] [Fintype U] in
@[scoped simp] private theorem coneProj_apply (m : Finset (I ⊕ₗ U) → M) (T : Finset I) :
    coneProj P U M m T = m (insert (top I U) (T.map (inlₗ U))) := rfl

omit [Fintype I] [Fintype U] in
private theorem coneInclLin_apply_of_mem (m : Finset I → M) {S : Finset (I ⊕ₗ U)}
    (h : top I U ∈ S) : coneInclLin P U M m S = 0 := ite_eq_left h

omit [Fintype I] [Fintype U] in
private theorem coneInclLin_apply_of_notMem (m : Finset I → M) {S : Finset (I ⊕ₗ U)}
    (h : top I U ∉ S) : coneInclLin P U M m S = m (down U S) := ite_eq_right h

omit [Fintype I] [Fintype U] in
@[scoped simp] private theorem coneInclLin_apply_map (m : Finset I → M) (T : Finset I) :
    coneInclLin P U M m (T.map (inlₗ U)) = m T := by
  rw [coneInclLin_apply_of_notMem _ _ (top_notMem_map T), down_map]

omit [Fintype I] [Fintype U] in
@[scoped simp] private theorem coneInclLin_apply_insert_top (m : Finset I → M) (S : Finset (I ⊕ₗ
    U)) :
    coneInclLin P U M m (insert (top I U) S) = 0 :=
  coneInclLin_apply_of_mem _ _ (Finset.mem_insert_self _ _)

omit [Fintype I] [Fintype U] in
private theorem coneCoprojLin_apply_of_mem (m : Finset I → M) {S : Finset (I ⊕ₗ U)}
    (h : top I U ∈ S) : coneCoprojLin P U M m S = m (down U S) := ite_eq_left h

omit [Fintype I] [Fintype U] in
private theorem coneCoprojLin_apply_of_notMem (m : Finset I → M) {S : Finset (I ⊕ₗ U)}
    (h : top I U ∉ S) : coneCoprojLin P U M m S = 0 := ite_eq_right h

omit [Fintype I] [Fintype U] in
@[scoped simp] private theorem coneCoprojLin_apply_map (m : Finset I → M) (T : Finset I) :
    coneCoprojLin P U M m (T.map (inlₗ U)) = 0 :=
  coneCoprojLin_apply_of_notMem _ _ (top_notMem_map T)

omit [Fintype I] [Fintype U] in
@[scoped simp] private theorem coneCoprojLin_apply_insert_top_map (m : Finset I → M) (T : Finset I)
    :
    coneCoprojLin P U M m (insert (top I U) (T.map (inlₗ U))) = m T := by
  rw [coneCoprojLin_apply_of_mem _ _ (Finset.mem_insert_self _ _), down_insert_top, down_map]

omit [Fintype I] [Fintype U] in
private theorem coneInclLin_coneRes_add (m : Finset (I ⊕ₗ U) → M) :
    coneInclLin P U M (coneRes P U M m) + coneCoprojLin P U M (coneProj P U M m) = m := by
  funext S
  rw [Pi.add_apply]
  by_cases h : top I U ∈ S
  · rw [coneInclLin_apply_of_mem _ _ h, coneCoprojLin_apply_of_mem _ _ h, zero_add, coneProj_apply,
      ← eq_insert_map_down h]
  · rw [coneInclLin_apply_of_notMem _ _ h, coneCoprojLin_apply_of_notMem _ _ h, add_zero,
      coneRes_apply, ← eq_map_down h]

omit [Fintype I] [Fintype U] in
@[scoped simp] private theorem coneRes_coneInclLin (m : Finset I → M) : coneRes P U M (coneInclLin
    P U M m)
    = m := by
  funext T; simp
omit [Fintype I] [Fintype U] in
@[scoped simp] private theorem coneProj_coneInclLin (m : Finset I → M) : coneProj P U M
    (coneInclLin P U M
    m) = 0 := by
  funext T; simp
omit [Fintype I] [Fintype U] in
@[scoped simp] private theorem coneRes_coneCoprojLin (m : Finset I → M) : coneRes P U M
    (coneCoprojLin P U
    M m) = 0 := by
  funext T; simp
omit [Fintype I] [Fintype U] in
@[scoped simp] private theorem coneProj_coneCoprojLin (m : Finset I → M) : coneProj P U M
    (coneCoprojLin P
    U M m) = m := by
  funext T; simp

omit [Fintype I] [Fintype U] in
private theorem cone_ext {m m' : Finset (I ⊕ₗ U) → M} (h₁ : coneRes P U M m = coneRes P U M m')
    (h₂ : coneProj P U M m = coneProj P U M m') : m = m' := by
  rw [← coneInclLin_coneRes_add (P := P) M m, ← coneInclLin_coneRes_add (P := P) M m', h₁, h₂]

def coneTw : (Finset I → M) →ₗ[P] (Finset I → M) where
  toFun m T := ((-1 : P) ^ T.card * t) • m T
  map_add' m m' := by funext T; simp [smul_add]
  map_smul' c m := by funext T; simp [smul_comm c]

omit [LinearOrder I] [Fintype I] in
@[scoped simp] private theorem coneTw_apply (m : Finset I → M) (T : Finset I) :
    coneTw t M m T = ((-1 : P) ^ T.card * t) • m T := rfl

omit [LinearOrder I] [Fintype I] in
private theorem coneTw_of_mem_C {p : ℕ} {m : Finset I → M}
    (hm : m ∈ C (P := P) (I := I) M p) : coneTw t M m = ((-1 : P) ^ p * t) • m := by
  funext T
  rw [coneTw_apply, Pi.smul_apply]
  by_cases hT : T.card = p
  · rw [hT]
  · rw [hm T hT, smul_zero, smul_zero]

private theorem coneProj_d (m : Finset (I ⊕ₗ U) → M) :
    coneProj P U M (d (snoc U x t) M m) = d x M (coneProj P U M m) := by
  funext T
  rw [coneProj_apply, d_snoc_apply_insert_top, d_apply]
  rfl

private theorem coneRes_d (m : Finset (I ⊕ₗ U) → M) (T : Finset I) :
    coneRes P U M (d (snoc U x t) M m) T =
      d x M (coneRes P U M m) T + ((-1 : P) ^ T.card * t) • coneProj P U M m T := by
  rw [coneRes_apply, d_snoc_apply_map, d_apply]
  rfl

private theorem coneRes_d' (m : Finset (I ⊕ₗ U) → M) :
    coneRes P U M (d (snoc U x t) M m) = d x M (coneRes P U M m) + coneTw t M (coneProj P U M m) :=
        by
  funext T; rw [coneRes_d]; rfl

theorem d_coneInclLin (a : Finset I → M) :
    d (snoc U x t) M (coneInclLin P U M a) = coneInclLin P U M (d x M a) := by
  apply cone_ext (P := P) M
  · rw [coneRes_d', coneRes_coneInclLin, coneProj_coneInclLin, map_zero, add_zero,
      coneRes_coneInclLin]
  · rw [coneProj_d, coneProj_coneInclLin, coneProj_coneInclLin, map_zero]

private theorem d_coneCoprojLin (b : Finset I → M) :
    d (snoc U x t) M (coneCoprojLin P U M b) =
      coneInclLin P U M (coneTw t M b) + coneCoprojLin P U M (d x M b) := by
  apply cone_ext (P := P) M
  · rw [coneRes_d', coneRes_coneCoprojLin, coneProj_coneCoprojLin, map_zero, zero_add, map_add,
      coneRes_coneInclLin, coneRes_coneCoprojLin, add_zero]
  · rw [coneProj_d, coneProj_coneCoprojLin, map_add, coneProj_coneInclLin, coneProj_coneCoprojLin,
      zero_add]

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] [Unique U] in
private theorem coneRes_mem_C {p : ℕ} {m : Finset (I ⊕ₗ U) → M}
    (hm : m ∈ C (P := P) (I := I ⊕ₗ U) M p) : coneRes P U M m ∈ C (P := P)
    (I := I) M p := fun T hT =>
  hm _ (by rwa [Finset.card_map])

omit [Fintype I] [Fintype U] in
private theorem coneProj_mem_C {p : ℕ} {m : Finset (I ⊕ₗ U) → M}
    (hm : m ∈ C (P := P) (I := I ⊕ₗ U) M (p + 1)) : coneProj P U M m ∈ C (P := P)
    (I := I) M p := fun T hT =>
  hm _ (by rw [card_insert_top_map]; omega)

omit [Fintype I] [Fintype U] in
private theorem coneProj_eq_zero_of_mem_C_zero {m : Finset (I ⊕ₗ U) → M} (hm : m ∈ C (P := P) (I :=
    I ⊕ₗ U)
    M 0) :
    coneProj P U M m = 0 := funext fun T =>
  hm _ (by rw [card_insert_top_map]; omega)

omit [Fintype I] [Fintype U] in
theorem coneInclLin_mem_C {p : ℕ} {a : Finset I → M} (ha : a ∈ C (P := P) (I := I) M p) :
    coneInclLin P U M a ∈ C (P := P) (I := I ⊕ₗ U) M p := by
  intro S hS
  by_cases h : top I U ∈ S
  · exact coneInclLin_apply_of_mem _ _ h
  · rw [coneInclLin_apply_of_notMem _ _ h]
    exact ha _ (by rwa [card_down_of_notMem h])

omit [Fintype I] [Fintype U] in
private theorem coneCoprojLin_mem_C {p : ℕ} {b : Finset I → M}
    (hb : b ∈ C (P := P) (I := I) M p) : coneCoprojLin P U M b ∈ C (P := P)
    (I := I ⊕ₗ U) M (p + 1) := by
  intro S hS
  by_cases h : top I U ∈ S
  · rw [coneCoprojLin_apply_of_mem _ _ h]
    exact hb _ (fun h' => hS (by rw [← card_down_of_mem h, h']))
  · exact coneCoprojLin_apply_of_notMem _ _ h

noncomputable def coneIncl : ChainMap x M (snoc U x t) M where
  toLinearMap := coneInclLin P U M
  comm := LinearMap.ext fun a => (d_coneInclLin x t M a).symm
  map_C _ _ ha := coneInclLin_mem_C M ha

theorem coneProj_mem_Z {p : ℕ} {m : Finset (I ⊕ₗ U) → M}
    (hm : m ∈ Z (snoc U x t) M (p + 1)) : coneProj P U M m ∈ Z x M p :=
  ⟨coneProj_mem_C M hm.1, by
    change d x M (coneProj P U M m) = 0
    rw [← coneProj_d, LinearMap.mem_ker.mp hm.2, map_zero]⟩

theorem coneProj_mem_B {p : ℕ} {m : Finset (I ⊕ₗ U) → M}
    (hm : m ∈ B (snoc U x t) M (p + 1)) : coneProj P U M m ∈ B x M p := by
  obtain ⟨n, hn, rfl⟩ := hm
  exact ⟨coneProj P U M n, coneProj_mem_C M hn, (coneProj_d x t M n).symm⟩

def coneProjH (p : ℕ) : H (snoc U x t) M (p + 1) →ₗ[P] H x M p :=
  Submodule.mapQ _ _ ((coneProj P U M).restrict fun _ hm => coneProj_mem_Z x t M hm)
    fun _ hm => coneProj_mem_B x t M hm

private theorem coneProjH_mk (p : ℕ) (z : Z (snoc U x t) M (p + 1)) :
    coneProjH x t M p (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨coneProj P U M z, coneProj_mem_Z x t M z.2⟩ := rfl

private theorem neg_one_pow_mul_self' (p : ℕ) : ((-1 : P) ^ p) * (-1) ^ p = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

@[scoped simp] private theorem coneIncl_coe_mapZ {p : ℕ} (z : Z x M p) :
    ((coneIncl x t M (U := U)).toHMap.mapZ p z : Finset (I ⊕ₗ U) → M) = coneInclLin P U M z := rfl

private theorem cone_exact₁ (p : ℕ) :
    Function.Exact (fun h : H x M p => t • h) ((coneIncl x t M (U := U)).mapH p) := by
  intro h
  constructor
  · intro h0
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [HMap.mapH_mk, H_mk_eq_zero_iff, coneIncl_coe_mapZ] at h0
    obtain ⟨w, hw, hdw⟩ := h0
    have hres : (z : Finset I → M) =
        d x M (coneRes P U M w) + ((-1 : P) ^ p * t) • coneProj P U M w := by
      have h1 := congrArg (coneRes P U M) hdw
      rwa [coneRes_d', coneRes_coneInclLin, coneTw_of_mem_C t M (coneProj_mem_C M hw),
          eq_comm] at h1
    have hproj : coneProj P U M w ∈ LinearMap.ker (d x M) := by
      have h2 := congrArg (coneProj P U M) hdw
      rwa [coneProj_d, coneProj_coneInclLin] at h2
    refine ⟨((-1 : P) ^ p) • Submodule.Quotient.mk ⟨coneProj P U M w, coneProj_mem_C M hw, hproj⟩,
        ?_⟩
    change t • ((-1 : P) ^ p • _) = _
    rw [smul_smul, ← Submodule.Quotient.mk_smul, H_mk_eq_mk_iff, Submodule.coe_smul]
    refine ⟨-coneRes P U M w, Submodule.neg_mem _ (coneRes_mem_C M hw), ?_⟩
    rw [map_neg, hres, mul_comm t]
    abel
  · rintro ⟨h₀, rfl⟩
    obtain ⟨z₀, rfl⟩ := Submodule.Quotient.mk_surjective _ h₀
    change (coneIncl x t M).mapH p (t • Submodule.Quotient.mk z₀) = 0
    rw [← Submodule.Quotient.mk_smul, HMap.mapH_mk, H_mk_eq_zero_iff, coneIncl_coe_mapZ,
        Submodule.coe_smul]
    refine ⟨((-1 : P) ^ p) • coneCoprojLin P U M z₀,
      Submodule.smul_mem _ _ (coneCoprojLin_mem_C M z₀.2.1), ?_⟩
    rw [map_smul, d_coneCoprojLin, LinearMap.mem_ker.mp z₀.2.2, map_zero, add_zero,
      coneTw_of_mem_C t M z₀.2.1, map_smul, smul_smul, ← mul_assoc, neg_one_pow_mul_self', one_mul,
      map_smul]

private theorem cone_exact₂ (p : ℕ) :
    Function.Exact ((coneIncl x t M (U := U)).mapH (p + 1)) (coneProjH x t M (U := U) p) := by
  intro h'
  constructor
  · intro h0
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ h'
    rw [coneProjH_mk, H_mk_eq_zero_iff] at h0
    obtain ⟨n, hn, hdn⟩ := h0
    have hm'proj : coneProj P U M ((m : Finset (I ⊕ₗ U) → M) - d (snoc U x t) M
        (coneCoprojLin P U M n)) = 0 := by
      rw [map_sub, coneProj_d, coneProj_coneCoprojLin, hdn]; exact sub_self _
    have hm'd : d (snoc U x t) M ((m : Finset (I ⊕ₗ U) → M) - d (snoc U x t) M
        (coneCoprojLin P U M n)) = 0 := by
      rw [map_sub, d_d, sub_zero]; exact LinearMap.mem_ker.mp m.2.2
    have hm'C : (m : Finset (I ⊕ₗ U) → M) - d (snoc U x t) M (coneCoprojLin P U M n) ∈
        C (P := P) (I := I ⊕ₗ U) M (p + 1) :=
      sub_mem m.2.1 (d_mem_C _ _ (coneCoprojLin_mem_C M hn))
    have haZ : coneRes P U M ((m : Finset (I ⊕ₗ U) → M) - d (snoc U x t) M
        (coneCoprojLin P U M n)) ∈ Z x M (p + 1) := by
      refine ⟨coneRes_mem_C M hm'C, ?_⟩
      change d x M _ = 0
      have h1 := coneRes_d' x t M ((m : Finset (I ⊕ₗ U) → M) - d (snoc U x t) M
          (coneCoprojLin P U M n))
      rw [hm'd, map_zero, hm'proj, map_zero, add_zero] at h1
      exact h1.symm
    refine ⟨Submodule.Quotient.mk ⟨_, haZ⟩, ?_⟩
    rw [HMap.mapH_mk, H_mk_eq_mk_iff, coneIncl_coe_mapZ]
    have hsplit := coneInclLin_coneRes_add (P := P) M
      ((m : Finset (I ⊕ₗ U) → M) - d (snoc U x t) M (coneCoprojLin P U M n))
    rw [hm'proj, map_zero, add_zero] at hsplit
    rw [hsplit, sub_sub_cancel_left]
    exact Submodule.neg_mem _ ⟨coneCoprojLin P U M n, coneCoprojLin_mem_C M hn, rfl⟩
  · rintro ⟨h, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [HMap.mapH_mk, coneProjH_mk, H_mk_eq_zero_iff]
    change coneProj P U M (coneInclLin P U M (z : Finset I → M)) ∈ _
    rw [coneProj_coneInclLin]
    exact Submodule.zero_mem _

private theorem cone_surjective₀ : Function.Surjective ((coneIncl x t M (U := U)).mapH 0) := by
  intro h'
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ h'
  have hproj : coneProj P U M (m : Finset (I ⊕ₗ U) → M) = 0 :=
      coneProj_eq_zero_of_mem_C_zero M m.2.1
  have haZ : coneRes P U M (m : Finset (I ⊕ₗ U) → M) ∈ Z x M 0 := by
    refine ⟨coneRes_mem_C M m.2.1, ?_⟩
    change d x M _ = 0
    have h1 := coneRes_d' x t M (m : Finset (I ⊕ₗ U) → M)
    rw [LinearMap.mem_ker.mp m.2.2, map_zero, hproj, map_zero, add_zero] at h1
    exact h1.symm
  refine ⟨Submodule.Quotient.mk ⟨_, haZ⟩, ?_⟩
  rw [HMap.mapH_mk]
  congr 1
  apply Subtype.ext
  rw [coneIncl_coe_mapZ]
  have hsplit := coneInclLin_coneRes_add (P := P) M (m : Finset (I ⊕ₗ U) → M)
  rwa [hproj, map_zero, add_zero] at hsplit

private theorem cone_exact₃ (p : ℕ) :
    Function.Exact (coneProjH x t M (U := U) p) (fun h : H x M p => t • h) := by
  intro h
  constructor
  · intro h0
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    change t • Submodule.Quotient.mk b = 0 at h0
    rw [← Submodule.Quotient.mk_smul, H_mk_eq_zero_iff, Submodule.coe_smul] at h0
    obtain ⟨a, ha, hda⟩ := h0
    have hmC : coneCoprojLin P U M b + coneInclLin P U M ((-((-1 : P) ^ p)) • a) ∈
        C (P := P) (I := I ⊕ₗ U) M (p + 1) :=
      add_mem (coneCoprojLin_mem_C M b.2.1) (coneInclLin_mem_C M (Submodule.smul_mem _ _ ha))
    have hmd : coneCoprojLin P U M b + coneInclLin P U M ((-((-1 : P) ^ p)) • a) ∈
        LinearMap.ker (d (snoc U x t) M) := by
      change d (snoc U x t) M _ = 0
      rw [map_add, d_coneCoprojLin, d_coneInclLin, LinearMap.mem_ker.mp b.2.2, map_zero, add_zero,
          map_smul,
        hda, coneTw_of_mem_C t M b.2.1, ← map_add, smul_smul, ← add_smul]
      convert (coneInclLin P U M).map_zero
      convert zero_smul P (b : Finset I → M) using 2
      ring
    refine ⟨Submodule.Quotient.mk ⟨_, hmC, hmd⟩, ?_⟩
    rw [coneProjH_mk]
    congr 1
    apply Subtype.ext
    change coneProj P U M (coneCoprojLin P U M b + coneInclLin P U M ((-((-1 : P) ^ p)) • a)) = b
    rw [map_add, coneProj_coneCoprojLin, coneProj_coneInclLin, add_zero]
  · rintro ⟨h', rfl⟩
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ h'
    change t • coneProjH x t M p (Submodule.Quotient.mk m) = 0
    rw [coneProjH_mk, ← Submodule.Quotient.mk_smul, H_mk_eq_zero_iff, Submodule.coe_smul]
    change t • coneProj P U M (m : Finset (I ⊕ₗ U) → M) ∈ B x M p
    have h1 := coneRes_d' x t M (m : Finset (I ⊕ₗ U) → M)
    rw [LinearMap.mem_ker.mp m.2.2, map_zero, coneTw_of_mem_C t M (coneProj_mem_C M m.2.1)] at h1
    refine ⟨(-((-1 : P) ^ p)) • coneRes P U M m, Submodule.smul_mem _ _ (coneRes_mem_C M m.2.1), ?_⟩
    rw [map_smul, eq_neg_of_add_eq_zero_left h1.symm, smul_neg, neg_smul, neg_neg, smul_smul,
        ← mul_assoc,
      neg_one_pow_mul_self', one_mul]

variable (P) in
def homog (p : ℕ) : (Finset I → M) →ₗ[P] (Finset I → M) where
  toFun m T := if T.card = p then m T else 0
  map_add' m m' := by funext T; by_cases h : T.card = p <;> simp [h]
  map_smul' c m := by funext T; by_cases h : T.card = p <;> simp [h]

omit [LinearOrder I] [Fintype I] in
private theorem homog_mem_C (p : ℕ) (m : Finset I → M) : homog P M p m ∈ C (P := P) (I := I) M p :=
  fun _ hT => ite_eq_right hT

omit [LinearOrder I] in
private theorem sum_homog (m : Finset I → M) : ∑ p ∈ Finset.range (Fintype.card I + 1),
    homog P M p m = m := by
  funext T
  rw [Finset.sum_apply, Finset.sum_eq_single T.card]
  · exact ite_eq_left rfl
  · intro p _ hp; exact ite_eq_right (Ne.symm hp)
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ T))) h

omit [LinearOrder I] [LinearOrder J] [Fintype J] [Fintype I] in
private theorem map_coneTw [Finite I] (f : (Finset I → M) →ₗ[P] (Finset J → N))
    (hf : ∀ p, C (P := P) (I := I) M p ≤ (C (P := P) (I := J) N p).comap f) (m : Finset I → M) :
    f (coneTw t M m) = coneTw t N (f m) := by
  have := Fintype.ofFinite I
  conv_lhs => rw [← sum_homog (P := P) M m]
  conv_rhs => rw [← sum_homog (P := P) M m]
  rw [map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coneTw_of_mem_C t M (homog_mem_C M p m), map_smul,
      coneTw_of_mem_C t N (hf p (homog_mem_C M p m))]

omit [Fintype U] in
private theorem coneRes_coneMapLin (f : ChainMap x M y N) (m : Finset (I ⊕ₗ U) → M) :
    coneRes P U N ((coneInclLin P U N ∘ₗ f.toLinearMap ∘ₗ coneRes P U M +
      coneCoprojLin P U N ∘ₗ f.toLinearMap ∘ₗ coneProj P U M) m) =
          f.toLinearMap (coneRes P U M m) := by
  rw [LinearMap.add_apply, map_add, LinearMap.comp_apply, LinearMap.comp_apply, coneRes_coneInclLin,
    LinearMap.comp_apply, LinearMap.comp_apply, coneRes_coneCoprojLin, add_zero]

omit [Fintype U] in
private theorem coneProj_coneMapLin (f : ChainMap x M y N) (m : Finset (I ⊕ₗ U) → M) :
    coneProj P U N ((coneInclLin P U N ∘ₗ f.toLinearMap ∘ₗ coneRes P U M +
      coneCoprojLin P U N ∘ₗ f.toLinearMap ∘ₗ coneProj P U M) m) =
          f.toLinearMap (coneProj P U M m) := by
  rw [LinearMap.add_apply, map_add, LinearMap.comp_apply, LinearMap.comp_apply,
      coneProj_coneInclLin,
    LinearMap.comp_apply, LinearMap.comp_apply, coneProj_coneCoprojLin, zero_add]

noncomputable def coneMap (f : ChainMap x M y N) : ChainMap (snoc U x t) M (snoc U y t) N where
  toLinearMap := coneInclLin P U N ∘ₗ f.toLinearMap ∘ₗ coneRes P U M +
    coneCoprojLin P U N ∘ₗ f.toLinearMap ∘ₗ coneProj P U M
  comm := by
    refine LinearMap.ext fun m => cone_ext (P := P) N ?_ ?_
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, coneRes_coneMapLin, coneRes_d', coneRes_d',
        map_add, f.comm_apply, map_coneTw t M (f := f.toLinearMap) (fun p _ hm => f.map_C p hm),
            coneRes_coneMapLin,
        coneProj_coneMapLin]
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, coneProj_coneMapLin, coneProj_d, coneProj_d,
        f.comm_apply, coneProj_coneMapLin]
  map_C p m hm := by
    rw [Submodule.mem_comap, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.comp_apply]
    cases p with
    | zero =>
      rw [coneProj_eq_zero_of_mem_C_zero M hm, map_zero, map_zero, add_zero]
      exact coneInclLin_mem_C N (f.map_C 0 (coneRes_mem_C M hm))
    | succ q =>
      exact add_mem (coneInclLin_mem_C N (f.map_C (q + 1) (coneRes_mem_C M hm)))
        (coneCoprojLin_mem_C N (f.map_C q (coneProj_mem_C M hm)))

@[scoped simp] private theorem coneMap_toLinearMap_apply (f : ChainMap x M y N) (m : Finset (I ⊕ₗ
    U) → M) :
    (coneMap x t M f (U := U)).toLinearMap m =
      coneInclLin P U N (f.toLinearMap (coneRes P U M m)) +
          coneCoprojLin P U N (f.toLinearMap (coneProj P U M m)) :=
  rfl

private theorem coneMap_mapH_inclMapH (f : ChainMap x M y N) (p : ℕ) (h : H x M p) :
    (coneMap x t M f).mapH p ((coneIncl x t M (U := U)).mapH p h) =
      (coneIncl y t N (U := U)).mapH p (f.mapH p h) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  rw [HMap.mapH_mk, HMap.mapH_mk, HMap.mapH_mk, HMap.mapH_mk]
  congr 1
  apply Subtype.ext
  change (coneMap x t M f (U := U)).toLinearMap (coneInclLin P U M z) =
      coneInclLin P U N (f.toLinearMap z)
  rw [coneMap_toLinearMap_apply, coneRes_coneInclLin, coneProj_coneInclLin, map_zero, map_zero,
      add_zero]

private theorem coneProjH_coneMap_mapH (f : ChainMap x M y N) (p : ℕ)
    (h : H (snoc U x t) M (p + 1)) : coneProjH y t N p ((coneMap x t M f).mapH (p + 1) h) =
    f.mapH p (coneProjH x t M p h) := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  rw [HMap.mapH_mk, coneProjH_mk, coneProjH_mk, HMap.mapH_mk]
  congr 1
  apply Subtype.ext
  change coneProj P U N ((coneMap x t M f (U := U)).toLinearMap m) =
      f.toLinearMap (coneProj P U M m)
  exact coneProj_coneMapLin x M f (m : Finset (I ⊕ₗ U) → M)

end Cone
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section Peel

variable {P : Type u'} [CommRing P] {J : Type} [LinearOrder J] [Fintype J] {I : Type} [LinearOrder
    I] [Fintype I]
variable (y : J → P) (x : I → P) (M : Type v') [AddCommGroup M] [Module P M]

def concat (y : J → P) (x : I → P) : J ⊕ₗ I → P := fun k => Sum.elim y x (ofLex k)

variable (J) in
def inrₗ : I ↪ J ⊕ₗ I := ⟨fun i => toLex (Sum.inr i), fun _ _ h => Sum.inr_injective
    (toLex.injective h)⟩

variable (I) in
def inlₗ' : J ↪ J ⊕ₗ I := ⟨fun j => toLex (Sum.inl j), fun _ _ h => Sum.inl_injective
    (toLex.injective h)⟩

abbrev ModSpan (y : J → P) (M : Type v') [AddCommGroup M] [Module P M] : Type v' :=
  M ⧸ (Ideal.span (Set.range y) • ⊤ : Submodule P M)

omit [CommRing P] [LinearOrder J] [Fintype J] [LinearOrder I] [Fintype I] in
@[scoped simp] private theorem concat_inlₗ' (j : J) : concat y x (inlₗ' I j) = y j := rfl
omit [CommRing P] [LinearOrder J] [Fintype J] [LinearOrder I] [Fintype I] in
@[scoped simp] private theorem concat_inrₗ (i : I) : concat y x (inrₗ J i) = x i := rfl

omit [LinearOrder J] [LinearOrder I] in
private theorem sum_lex₂ {A : Type*} [AddCommMonoid A] (f : J ⊕ₗ I → A) :
    ∑ k, f k = ∑ j, f (inlₗ' I j) + ∑ i, f (inrₗ J i) := by
  rw [← Fintype.sum_equiv toLex (fun k => f (toLex k)) f (fun _ => rfl), Fintype.sum_sum_type]
  rfl

omit [Fintype J] [Fintype I] in
private theorem map_insert_inrₗ (i : I) (T : Finset I) :
    (insert i T).map (inrₗ J) = insert (inrₗ J i) (T.map (inrₗ J)) := Finset.map_insert _ _ _

omit [Fintype J] [Fintype I] in
private theorem map_insert_inlₗ' (j : J) (T : Finset J) :
    (insert j T).map (inlₗ' I) = insert (inlₗ' I j) (T.map (inlₗ' I)) := Finset.map_insert _ _ _

omit [Fintype J] [Fintype I] in
private theorem sgn_inrₗ_map (i : I) (T : Finset I) : sgn P (inrₗ J i)
    (T.map (inrₗ J)) = sgn P i T := by
  rw [sgn, sgn, Finset.filter_map, Finset.card_map]
  congr 2

omit [Fintype J] [Fintype I] in
private theorem sgn_inlₗ'_map (j : J) (T : Finset J) : sgn P (inlₗ' I j)
    (T.map (inlₗ' I)) = sgn P j T := by
  rw [sgn, sgn, Finset.filter_map, Finset.card_map]
  congr 2

omit [Fintype J] [Fintype I] in
private theorem coef_concat_inrₗ_map (i : I) (T : Finset I) :
    coef (concat y x) (inrₗ J i) (T.map (inrₗ J)) = coef x i T := by
  by_cases hi : i ∈ T
  · rw [coef_of_mem _ ((Finset.mem_map' _).mpr hi), coef_of_mem _ hi]
  · rw [coef_of_not_mem _ (fun h => hi ((Finset.mem_map' _).mp h)), coef_of_not_mem _ hi,
      sgn_inrₗ_map, concat_inrₗ]

omit [Fintype J] [Fintype I] in
private theorem coef_concat_inlₗ'_map (j : J) (T : Finset J) :
    coef (concat y x) (inlₗ' I j) (T.map (inlₗ' I)) = coef y j T := by
  by_cases hj : j ∈ T
  · rw [coef_of_mem _ ((Finset.mem_map' _).mpr hj), coef_of_mem _ hj]
  · rw [coef_of_not_mem _ (fun h => hj ((Finset.mem_map' _).mp h)), coef_of_not_mem _ hj,
      sgn_inlₗ'_map, concat_inlₗ']

omit [Fintype J] [Fintype I] in
private theorem coef_concat_inlₗ'_smul_mem (j : J) (S : Finset (J ⊕ₗ I)) (v : M) :
    coef (concat y x) (inlₗ' I j) S • v ∈ (Ideal.span (Set.range y) • ⊤ : Submodule P M) := by
  by_cases h : inlₗ' I j ∈ S
  · rw [coef_of_mem _ h, zero_smul]; exact Submodule.zero_mem _
  · rw [coef_of_not_mem _ h, concat_inlₗ', mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem_smul (Ideal.subset_span ⟨j,
        rfl⟩) Submodule.mem_top)

omit [Fintype J] [Fintype I] in
private theorem coef_concat_inrₗ_smul_mem (i : I) (S : Finset (J ⊕ₗ I)) (v : M) :
    coef (concat y x) (inrₗ J i) S • v ∈ (Ideal.span (Set.range x) • ⊤ : Submodule P M) := by
  by_cases h : inrₗ J i ∈ S
  · rw [coef_of_mem _ h, zero_smul]; exact Submodule.zero_mem _
  · rw [coef_of_not_mem _ h, concat_inrₗ, mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem_smul (Ideal.subset_span ⟨i,
        rfl⟩) Submodule.mem_top)

def peel : ChainMap (concat y x) M x (ModSpan y M) where
  toLinearMap :=
    { toFun := fun m T => Submodule.Quotient.mk (m (T.map (inrₗ J)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm := by
    refine LinearMap.ext fun m => funext fun T => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, d_apply x (ModSpan y M)]
    change (Submodule.mkQ (Ideal.span (Set.range y) • ⊤ : Submodule P M))
        (d (concat y x) M m (T.map (inrₗ J))) =
      ∑ i, coef x i T •
        (Submodule.mkQ (Ideal.span (Set.range y) • ⊤ : Submodule P M))
            (m ((insert i T).map (inrₗ J)))
    have hcross : ∑ j, (Submodule.mkQ (Ideal.span (Set.range y) • ⊤ : Submodule P M))
        (coef (concat y x) (inlₗ' I j) (T.map (inrₗ J)) •
            m (insert (inlₗ' I j) (T.map (inrₗ J)))) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact coef_concat_inlₗ'_smul_mem y x M j _ _
    rw [d_apply, sum_lex₂, map_add, map_sum, map_sum]
    erw [hcross]
    rw [zero_add]
    exact Finset.sum_congr rfl fun i _ =>
        by rw [map_smul, coef_concat_inrₗ_map, map_insert_inrₗ]; rfl
  map_C p m hm T hT := by
    change Submodule.Quotient.mk (m (T.map (inrₗ J))) = 0
    rw [hm _ (by rwa [Finset.card_map]), Submodule.Quotient.mk_zero]

@[scoped simp] private theorem peel_apply (m : Finset (J ⊕ₗ I) → M) (T : Finset I) :
    (peel y x M).toLinearMap m T = Submodule.Quotient.mk (m (T.map (inrₗ J))) := rfl

end Peel
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section PeelTop

variable {P : Type u'} [CommRing P] {I : Type} [LinearOrder I] [Fintype I] {J : Type} [LinearOrder
    J] [Fintype J]
variable (x : I → P) (y : J → P) (M : Type v') [AddCommGroup M] [Module P M]

def peelTop : ChainMap (concat x y) M x (ModSpan y M) where
  toLinearMap :=
    { toFun := fun m T => Submodule.Quotient.mk (m (T.map (inlₗ' J)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm := by
    refine LinearMap.ext fun m => funext fun T => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, d_apply x (ModSpan y M)]
    change (Submodule.mkQ (Ideal.span (Set.range y) • ⊤ : Submodule P M))
        (d (concat x y) M m (T.map (inlₗ' J))) =
      ∑ i, coef x i T •
        (Submodule.mkQ (Ideal.span (Set.range y) • ⊤ : Submodule P M))
            (m ((insert i T).map (inlₗ' J)))
    have hcross : ∑ j, (Submodule.mkQ (Ideal.span (Set.range y) • ⊤ : Submodule P M))
        (coef (concat x y) (inrₗ I j) (T.map (inlₗ' J)) •
            m (insert (inrₗ I j) (T.map (inlₗ' J)))) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact coef_concat_inrₗ_smul_mem x y M j _ _
    rw [d_apply, sum_lex₂, map_add, map_sum, map_sum]
    erw [hcross]
    rw [add_zero]
    exact Finset.sum_congr rfl fun i _ =>
        by rw [map_smul, coef_concat_inlₗ'_map, map_insert_inlₗ']; rfl
  map_C p m hm T hT := by
    change Submodule.Quotient.mk (m (T.map (inlₗ' J))) = 0
    rw [hm _ (by rwa [Finset.card_map]), Submodule.Quotient.mk_zero]

end PeelTop
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

end Koszul
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

namespace Koszul

open Finset

universe u v

section CastFamily

variable {P : Type u} [CommRing P] {I : Type} [LinearOrder I] [Fintype I]
variable (M : Type v) [AddCommGroup M] [Module P M]

def castHMap {x x' : I → P} (h : x = x') : HMap x M x' M where
  toLinearMap := LinearMap.id
  map_Z p := by subst h; exact fun _ hz => hz
  map_B p := by subst h; exact fun _ hz => hz

@[scoped simp] private theorem castHMap_toLinearMap {x x' : I → P} (h : x = x') :
    (castHMap M h).toLinearMap = LinearMap.id := rfl

private theorem castHMap_bijective {x x' : I → P} (h : x = x') (p : ℕ) :
    Function.Bijective ((castHMap M h).mapH p) := by
  subst h
  rw [HMap.mapH_congr (f := castHMap M rfl) (g := HMap.id x M) rfl, HMap.mapH_id]
  exact Function.bijective_id

end CastFamily
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section RemoveTop

variable {I : Type} [LinearOrder I] (i₀ : I)

def belowTopFun : {i // i < i₀} ⊕ₗ Unit → I := fun k => Sum.elim Subtype.val (fun _ => i₀) (ofLex k)

theorem belowTopFun_strictMono : StrictMono (belowTopFun i₀) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := toLex.surjective a
  obtain ⟨b, rfl⟩ := toLex.surjective b
  rcases a with a | a <;> rcases b with b | b
  · have h : a < b := Sum.Lex.inl_lt_inl_iff.mp hab
    exact h
  · change (a : I) < i₀
    exact a.2
  · exact absurd hab Sum.Lex.not_inr_lt_inl
  · have h := Sum.Lex.inr_lt_inr_iff.mp hab
    rw [Subsingleton.elim a b] at h
    exact absurd h (lt_irrefl b)

theorem belowTopFun_surjective (hi₀ : ∀ i, i ≤ i₀) : Function.Surjective (belowTopFun i₀) := by
  intro i
  by_cases h : i < i₀
  · exact ⟨toLex (Sum.inl ⟨i, h⟩), rfl⟩
  · exact ⟨toLex (Sum.inr ()), le_antisymm (not_lt.mp h) (hi₀ i)⟩

noncomputable def removeTopIso (hi₀ : ∀ i, i ≤ i₀) : {i // i < i₀} ⊕ₗ Unit ≃o I :=
  StrictMono.orderIsoOfSurjective (belowTopFun i₀) (belowTopFun_strictMono i₀)
      (belowTopFun_surjective i₀ hi₀)

end RemoveTop
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section PeelStep

variable {P : Type u} [CommRing P]
variable {J : Type} [LinearOrder J] [Fintype J] {I : Type} [LinearOrder I] [Fintype I]
variable {I' : Type} [LinearOrder I'] [Fintype I'] {U : Type} [LinearOrder U] [Fintype U] [Unique U]
variable (y : J → P) (x : I → P) (M : Type v) [AddCommGroup M] [Module P M] (e : I' ⊕ₗ U ≃o I)

variable (J) in
def liftIso (e : I' ⊕ₗ U ≃o I) : (J ⊕ₗ I') ⊕ₗ U ≃o J ⊕ₗ I :=
  (OrderIso.sumLexAssoc J I' U).trans (OrderIso.sumLexCongr (OrderIso.refl J) e)

def shorten : I' → P := fun i => x (e (inlₗ U i))

omit [CommRing P] [Fintype I] [Fintype I'] [Fintype U] in
private theorem comp_eq_snoc : x ∘ e = snoc U (shorten x e) (x (e (top I' U))) := by
  funext k
  rcases lex_cases k with ⟨i, rfl⟩ | rfl <;> rfl

omit [LinearOrder J] [Fintype J] [LinearOrder I'] [Fintype I'] in
private theorem lex_cases₂ (k : J ⊕ₗ I') : (∃ j, k = inlₗ' I' j) ∨ ∃ i, k = inrₗ J i := by
  obtain ⟨k, rfl⟩ := toLex.surjective k
  rcases k with j | i
  · exact Or.inl ⟨j, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

omit [CommRing P] [Fintype J] [Fintype I] [Fintype I'] [Fintype U] in
private theorem concat_comp_liftIso :
    concat y x ∘ liftIso J e = snoc U (concat y (shorten x e)) (x (e (top I' U))) := by
  funext k
  rcases lex_cases k with ⟨k, rfl⟩ | rfl
  · rcases lex_cases₂ k with ⟨j, rfl⟩ | ⟨i, rfl⟩ <;> rfl
  · rfl

omit [Fintype J] [Fintype I] [Fintype I'] [Fintype U] [Unique U] in
private theorem map_map_liftIso (T : Finset I') :
    ((T.map (inlₗ U)).map e.toEquiv.toEmbedding).map (inrₗ J) =
      ((T.map (inrₗ J)).map (inlₗ U)).map (liftIso J e).toEquiv.toEmbedding := by
  simp only [Finset.map_map]
  rfl

private theorem reindexLin_peel (m : Finset (J ⊕ₗ I) → M) :
    reindexLin P (ModSpan y M) e.toEquiv ((peel y x M).toLinearMap m) =
      (coneMap (concat y (shorten x e)) (x (e (top I' U))) M (peel y (shorten x e) M) (U :=
          U)).toLinearMap
        (reindexLin P M (liftIso J e).toEquiv m) := by
  funext S
  rw [reindexLin_apply, peel_apply, coneMap_toLinearMap_apply, Pi.add_apply]
  by_cases hS : top I' U ∈ S
  · rw [coneInclLin_apply_of_mem _ _ hS, coneCoprojLin_apply_of_mem _ _ hS, zero_add, peel_apply,
      coneProj_apply, reindexLin_apply]
    conv_lhs => rw [eq_insert_map_down hS, Finset.map_insert, Finset.map_insert, map_map_liftIso]
    rw [Finset.map_insert]
    rfl
  · rw [coneInclLin_apply_of_notMem _ _ hS, coneCoprojLin_apply_of_notMem _ _ hS, add_zero,
      peel_apply, coneRes_apply, reindexLin_apply]
    conv_lhs => rw [eq_map_down hS, map_map_liftIso]

private theorem coneMap_mapH_bijective {c : I' → P} (t : P) {N : Type v} [AddCommGroup N]
    [Module P N] {c₂ : I → P} (f : ChainMap c M c₂ N) (hf : ∀ q, Function.Bijective (f.mapH q))
    (q : ℕ) : Function.Bijective ((coneMap c t M f (U := U)).mapH q) := by
  have hsq : ∀ r, (t • LinearMap.id : H c₂ N r →ₗ[P] H c₂ N r).comp (f.mapH r) =
      (f.mapH r).comp (t • LinearMap.id) := fun r => by
    ext h
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
  have hincl : ∀ r, ((coneIncl c₂ t N (U := U)).mapH r).comp (f.mapH r) =
      ((coneMap c t M f (U := U)).mapH r).comp ((coneIncl c t M (U := U)).mapH r) := fun r =>
    LinearMap.ext fun h => (coneMap_mapH_inclMapH c t M f r h).symm
  cases q with
  | zero =>
    exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact
      (t • LinearMap.id) ((coneIncl c t M (U := U)).mapH 0) (t • LinearMap.id)
          ((coneIncl c₂ t N (U := U)).mapH 0)
      (f.mapH 0) (f.mapH 0) ((coneMap c t M f (U := U)).mapH 0) (hsq 0) (hincl 0)
      (cone_exact₁ c t M (U := U) 0) (cone_exact₁ c₂ t N (U := U) 0) (hf 0).2 (hf 0)
      (cone_surjective₀ c t M) (cone_surjective₀ c₂ t N)
  | succ p =>
    exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (t • LinearMap.id) ((coneIncl c t M (U := U)).mapH (p + 1)) (coneProjH c t M (U := U) p)
          (t • LinearMap.id)
      (t • LinearMap.id) ((coneIncl c₂ t N (U := U)).mapH (p + 1)) (coneProjH c₂ t N (U := U) p)
      (t • LinearMap.id)
      (f.mapH (p + 1)) (f.mapH (p + 1)) ((coneMap c t M f (U := U)).mapH (p + 1)) (f.mapH p)
          (f.mapH p)
      (hsq (p + 1)) (hincl (p + 1)) (LinearMap.ext fun h => coneProjH_coneMap_mapH c t M f p h)
          (hsq p)
      (cone_exact₁ c t M (U := U) (p + 1)) (cone_exact₂ c t M (U := U) p) (cone_exact₃ c t M (U :=
          U) p)
      (cone_exact₁ c₂ t N (U := U) (p + 1)) (cone_exact₂ c₂ t N (U := U) p)
          (cone_exact₃ c₂ t N (U := U) p)
      (hf (p + 1)).2 (hf (p + 1)) (hf p) (hf p).1

private theorem reindex_mapH_bijective {K L : Type} [LinearOrder K] [Fintype K] [LinearOrder L]
    [Fintype L] (N : Type v) [AddCommGroup N] [Module P N] (e : K ≃o L) (c : L → P)
    (p : ℕ) : Function.Bijective ((reindex N e c).toHMap.mapH p) :=
  (reindexH N e c p).symm.bijective

omit [Fintype U] in
private theorem peel_mapH_bijective_step (hIH : ∀ q, Function.Bijective
    ((peel y (shorten x e) M).mapH q)) (p : ℕ) : Function.Bijective ((peel y x M).mapH p) := by
  have key : ((reindex (ModSpan y M) e x).toHMap.comp (peel y x M).toHMap).toLinearMap =
      ((castHMap (ModSpan y M) (comp_eq_snoc x e).symm).comp
        ((coneMap (concat y (shorten x e)) (x (e (top I' U))) M (peel y (shorten x e) M) (U :=
            U)).toHMap.comp
          ((castHMap M (concat_comp_liftIso y x e)).comp
            (reindex M (liftIso J e) (concat y x)).toHMap))).toLinearMap := by
    simp only [HMap.comp_toLinearMap, ChainMap.toHMap_toLinearMap, castHMap_toLinearMap,
        LinearMap.id_comp]
    exact LinearMap.ext fun m => reindexLin_peel y x M e m
  have hH := HMap.mapH_congr key p
  simp only [HMap.mapH_comp] at hH
  have hfun := congrArg DFunLike.coe hH
  simp only [LinearMap.coe_comp] at hfun
  have hrhs : Function.Bijective (((castHMap (ModSpan y M) (comp_eq_snoc x e).symm).mapH p) ∘
      ((coneMap (concat y (shorten x e)) (x (e (top I' U))) M (peel y (shorten x e) M) (U :=
          U)).toHMap.mapH p) ∘
      ((castHMap M (concat_comp_liftIso y x e)).mapH p) ∘
          ((reindex M (liftIso J e) (concat y x)).toHMap.mapH p)) :=
    (castHMap_bijective _ _ p).comp ((coneMap_mapH_bijective M _ (peel y (shorten x e) M) hIH
        p).comp
      ((castHMap_bijective _ _ p).comp (reindex_mapH_bijective M (liftIso J e) (concat y x) p)))
  rw [← hfun] at hrhs
  exact (Function.Bijective.of_comp_iff' (reindex_mapH_bijective (ModSpan y M) e x p) _).mp hrhs

end PeelStep
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section PeelMain

variable {P : Type u} [CommRing P]
variable {J : Type} [LinearOrder J] [Fintype J] {I : Type} [LinearOrder I] [Fintype I]
variable (y : J → P) (x : I → P) (M : Type v) [AddCommGroup M] [Module P M]

omit [CommRing P] [Fintype J] [Fintype I] in
private theorem concat_eq_comp_sumLexEmpty [IsEmpty I] :
    concat y x = y ∘ (OrderIso.sumLexEmpty : J ⊕ₗ I ≃o J) := by
  funext k
  obtain ⟨k, rfl⟩ := toLex.surjective k
  rcases k with j | i
  · rfl
  · exact isEmptyElim i

private theorem peel_mapH_bijective_of_isEmpty [IsEmpty I] (hy : ∀ p,
    0 < p → Subsingleton (H y M p)) (p :
    ℕ) :
    Function.Bijective ((peel y x M).mapH p) := by
  cases p with
  | succ p =>
    have : Subsingleton (H (concat y x) M (p + 1)) := by
      rw [concat_eq_comp_sumLexEmpty y x]
      have := hy (p + 1) p.succ_pos
      exact (reindexH M (OrderIso.sumLexEmpty : J ⊕ₗ I ≃o J) y (p + 1)).toEquiv.subsingleton
    have : Subsingleton (H x (ModSpan y M) (p + 1)) :=
      subsingleton_H_of_card_lt x (ModSpan y M) (by rw [Fintype.card_eq_zero]; exact p.succ_pos)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  | zero =>
    have hx : (Ideal.span (Set.range x) • ⊤ : Submodule P (ModSpan y M)) = ⊥ := by
      rw [Set.range_eq_empty x, Ideal.span_empty, Submodule.bot_smul]
    have hle : (Ideal.span (Set.range y) • ⊤ : Submodule P M) ≤
        Ideal.span (Set.range (concat y x)) • ⊤ :=
      Submodule.smul_mono_left (Ideal.span_mono fun a ⟨j, hj⟩ => ⟨inlₗ' I j, hj⟩)
    constructor
    · rw [injective_iff_map_eq_zero]
      intro h hh
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
      have h1 := congrArg (HZeroEquiv x (ModSpan y M)) hh
      rw [map_zero, HMap.mapH_mk, HZeroEquiv_mk, HMap.coe_mapZ, ChainMap.toHMap_toLinearMap,
          peel_apply,
        Finset.map_empty, Submodule.Quotient.mk_eq_zero, hx, Submodule.mem_bot,
            Submodule.Quotient.mk_eq_zero] at h1
      rw [← (HZeroEquiv (concat y x) M).map_eq_zero_iff, HZeroEquiv_mk,
          Submodule.Quotient.mk_eq_zero]
      exact hle h1
    · intro h'
      obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ h'
      obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ ((z' : Finset I → ModSpan y M) ∅)
      have hC : (Pi.single (∅ : Finset (J ⊕ₗ I)) v : Finset (J ⊕ₗ I) → M) ∈ C (P := P)
          (I := J ⊕ₗ I) M 0 :=
        fun T hT => Pi.single_eq_of_ne (M := fun _ => M) (fun h : T = ∅ => hT
            (by rw [h, Finset.card_empty])) v
      let z₀ : Z (concat y x) M 0 := ⟨Pi.single ∅ v, hC, LinearMap.mem_ker.mpr
          (d_eq_zero_of_mem_C_zero _ M hC)⟩
      refine ⟨Submodule.Quotient.mk z₀, (HZeroEquiv x (ModSpan y M)).injective ?_⟩
      rw [HMap.mapH_mk, HZeroEquiv_mk, HZeroEquiv_mk, HMap.coe_mapZ, ChainMap.toHMap_toLinearMap,
          peel_apply,
        Finset.map_empty, ← hv]
      exact congrArg _ (congrArg _ (Pi.single_eq_same (M := fun _ : Finset (J ⊕ₗ I) => M) ∅ v))

private theorem peel_mapH_bijective_aux (hy : ∀ p, 0 < p → Subsingleton (H y M p)) (n : ℕ) :
    ∀ {I : Type} [LinearOrder I] [Fintype I] (x : I → P), Fintype.card I = n →
      ∀ p, Function.Bijective ((peel y x M).mapH p) := by
  induction n with
  | zero =>
    intro I _ _ x hI p
    have : IsEmpty I := Fintype.card_eq_zero_iff.mp hI
    exact peel_mapH_bijective_of_isEmpty y x M hy p
  | succ k ih =>
    intro I _ _ x hI p
    have : Nonempty I := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset I) id Finset.univ_nonempty
    let e := removeTopIso i₀ fun i => hi₀ i (Finset.mem_univ i)
    have hcard : Fintype.card {i // i < i₀} = k := by
      have hc := Fintype.card_congr e.toEquiv
      rw [Fintype.card_lex, Fintype.card_sum, Fintype.card_unit] at hc
      omega
    exact peel_mapH_bijective_step y x M e (fun q => ih (shorten x e) hcard q) p

private theorem peel_bijective (hy : ∀ p, 0 < p → Subsingleton (H y M p)) (p : ℕ) :
    Function.Bijective ((peel y x M).mapH p) :=
  peel_mapH_bijective_aux y M hy (Fintype.card I) x rfl p

end PeelMain
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section PeelTopProof

variable {P : Type u} [CommRing P]
variable {I : Type} [LinearOrder I] [Fintype I] {J : Type} [LinearOrder J] [Fintype J]
variable (x : I → P) (y : J → P) (M : Type v) [AddCommGroup M] [Module P M]

omit [CommRing P] [Fintype I] [Fintype J] in
private theorem concat_dual :
    (concat x y ∘ (OrderDual.ofDual : (I ⊕ₗ J)ᵒᵈ ≃ I ⊕ₗ J)) ∘
        (OrderIso.sumLexDualAntidistrib I J).symm =
      concat (y ∘ OrderDual.ofDual) (x ∘ OrderDual.ofDual) := by
  funext k
  rcases lex_cases₂ k with ⟨j, rfl⟩ | ⟨i, rfl⟩ <;> rfl

omit [Fintype I] [Fintype J] in
private theorem map_dual_chain (T : Finset I) :
    (((T.map (OrderDual.toDual : I ≃ Iᵒᵈ).toEmbedding).map (inrₗ Jᵒᵈ)).map
        (OrderIso.sumLexDualAntidistrib I J).symm.toEquiv.toEmbedding).map
      (OrderDual.ofDual : (I ⊕ₗ J)ᵒᵈ ≃ I ⊕ₗ J).toEmbedding = T.map (inlₗ' J) := by
  simp only [Finset.map_map]
  rfl

private theorem peelTop_eq_reverse (m : Finset (I ⊕ₗ J) → M) :
    (peelTop x y M).toLinearMap m =
      (reverseInv (ModSpan y M) x).toLinearMap
        ((peel (y ∘ OrderDual.ofDual) (x ∘ OrderDual.ofDual) M).toLinearMap
          (reindexLin P M (OrderIso.sumLexDualAntidistrib I J).symm.toEquiv
            (reindexLin P M (OrderDual.ofDual : (I ⊕ₗ J)ᵒᵈ ≃ I ⊕ₗ J) m))) := by
  funext T
  change Submodule.Quotient.mk (m (T.map (inlₗ' J))) =
    Submodule.Quotient.mk (m ((((T.map (OrderDual.toDual : I ≃ Iᵒᵈ).toEmbedding).map (inrₗ Jᵒᵈ)).map
      (OrderIso.sumLexDualAntidistrib I J).symm.toEquiv.toEmbedding).map
        (OrderDual.ofDual : (I ⊕ₗ J)ᵒᵈ ≃ I ⊕ₗ J).toEmbedding))
  rw [map_dual_chain]

private theorem peelTop_bijective (hy : ∀ p, 0 < p → Subsingleton (H y M p)) (p : ℕ) :
    Function.Bijective ((peelTop x y M).mapH p) := by
  have hy' : ∀ q, 0 < q → Subsingleton (H (y ∘ OrderDual.ofDual) M q) := fun q hq =>
    haveI := hy q hq
    (reverseH M y q).toEquiv.subsingleton
  let big : HMap (concat x y) M x (ModSpan (y ∘ OrderDual.ofDual) M) :=
    (reverseInv (ModSpan (y ∘ OrderDual.ofDual) M) x).comp
      ((peel (y ∘ OrderDual.ofDual) (x ∘ OrderDual.ofDual) M).toHMap.comp
        ((castHMap M (concat_dual x y)).comp
          ((reindex M (OrderIso.sumLexDualAntidistrib I J).symm (concat x y ∘
              OrderDual.ofDual)).toHMap.comp
            (reverse M (concat x y)))))
  have hbig : Function.Bijective (big.mapH p) := by
    simp only [big, HMap.mapH_comp, LinearMap.coe_comp]
    exact (reverseH (ModSpan (y ∘ OrderDual.ofDual) M) x p).bijective.comp
      ((peel_bijective (y ∘ OrderDual.ofDual) (x ∘ OrderDual.ofDual) M hy' p).comp
        ((castHMap_bijective M _ p).comp
          ((reindex_mapH_bijective M _ _ p).comp (reverseH M (concat x y) p).symm.bijective)))
  have key : (peelTop x y M).toHMap.toLinearMap = big.toLinearMap := by
    simp only [big, HMap.comp_toLinearMap, ChainMap.toHMap_toLinearMap, castHMap_toLinearMap,
        LinearMap.id_comp]
    exact LinearMap.ext fun m => peelTop_eq_reverse x y M m
  change Function.Bijective ((peelTop x y M).toHMap.mapH p)
  rw [HMap.mapH_congr key p]
  exact hbig

end PeelTopProof
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

end Koszul
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

namespace Koszul

open Finset CliffordAlgebra ExteriorAlgebra Set.powersetCard

universe u v u' v'

section Exterior

variable {R : Type u'} [CommRing R] {M : Type v'} [AddCommGroup M] [Module R M]

private theorem contractLeft_ιMulti_succ (d : Module.Dual R M) {n : ℕ} (v : Fin (n + 1) → M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d (ιMulti R (n + 1) v) =
      ∑ k : Fin (n + 1), ((-1 : R) ^ (k : ℕ) * d (v k)) • ιMulti R n (Fin.removeNth k v) := by
  rw [ExteriorAlgebra.contractLeft_ιMulti R M d n v]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul]
  rfl

private theorem contractLeft_ιMulti_of_forall_eq_zero (d : Module.Dual R M) {n : ℕ} (v : Fin n → M)
    (hv : ∀ i, d (v i) = 0) : contractLeft (Q := (0 : QuadraticForm R M)) d (ιMulti R n v) = 0 := by
  cases n with
  | zero => rw [ιMulti_zero_apply, contractLeft_one]
  | succ n => rw [contractLeft_ιMulti_succ]; simp [hv]

private theorem contractLeft_apply_ιMulti_removeNth (d : Module.Dual R M) {n : ℕ}
    (v : Fin (n + 1) → M) :
    exteriorPower.contractLeft R M d n (exteriorPower.ιMulti R (n + 1) v) =
      ∑ k : Fin (n + 1), ((-1 : R) ^ (k : ℕ) * d (v k)) •
          exteriorPower.ιMulti R n (Fin.removeNth k v) := by
  rw [exteriorPower.contractLeft_apply_ιMulti]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul]
  rfl

variable {I : Type} [LinearOrder I] {n : ℕ}

def eraseNth (s : Set.powersetCard I (n + 1)) (k : Fin (n + 1)) : Set.powersetCard I n :=
  ofFinEmbEquiv ((Fin.succAboveOrderEmb k).trans (ofFinEmbEquiv.symm s))

private theorem ofFinEmbEquiv_symm_eraseNth (s : Set.powersetCard I (n + 1))
    (k : Fin (n + 1)) : ofFinEmbEquiv.symm (eraseNth s k) =
    (Fin.succAboveOrderEmb k).trans (ofFinEmbEquiv.symm s) :=
  Equiv.symm_apply_apply _ _

private theorem coe_ofFinEmbEquiv_symm_eraseNth (s : Set.powersetCard I (n + 1))
    (k : Fin (n + 1)) : ⇑(ofFinEmbEquiv.symm (eraseNth s k)) =
    Fin.removeNth k ⇑(ofFinEmbEquiv.symm s) := by
  rw [ofFinEmbEquiv_symm_eraseNth]; rfl

private theorem mem_eraseNth_iff (s : Set.powersetCard I (n + 1)) (k : Fin (n + 1)) (i : I) :
    i ∈ eraseNth s k ↔ i ∈ s ∧ i ≠ ofFinEmbEquiv.symm s k := by
  rw [← mem_range_ofFinEmbEquiv_symm_iff_mem, coe_ofFinEmbEquiv_symm_eraseNth,
    ← mem_range_ofFinEmbEquiv_symm_iff_mem]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨_, rfl⟩, fun h => Fin.succAbove_ne k j ((ofFinEmbEquiv.symm s).injective h)⟩
  · rintro ⟨⟨j, rfl⟩, hne⟩
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq (fun h => hne (congrArg _ h))
    exact ⟨j', rfl⟩

private theorem val_eraseNth (s : Set.powersetCard I (n + 1)) (k : Fin (n + 1)) :
    (eraseNth s k : Finset I) = (s : Finset I).erase (ofFinEmbEquiv.symm s k) := by
  ext i
  rw [Finset.mem_erase, mem_coe_iff, mem_eraseNth_iff, mem_coe_iff, and_comm]

private theorem card_filter_lt_ofFinEmbEquiv_symm (s : Set.powersetCard I n) (k : Fin n) :
    ((s : Finset I).filter (· < ofFinEmbEquiv.symm s k)).card = k := by
  have hS : (s : Finset I) = Finset.univ.map (ofFinEmbEquiv.symm s).toEmbedding := by
    ext i
    rw [Finset.mem_map, mem_coe_iff, ← mem_range_ofFinEmbEquiv_symm_iff_mem]
    simp
  rw [hS, Finset.filter_map, Finset.card_map]
  have : (Finset.univ.filter ((· < ofFinEmbEquiv.symm s k) ∘ (ofFinEmbEquiv.symm s).toEmbedding)) =
      Finset.Iio k := by
    ext j; simp [(ofFinEmbEquiv.symm s).lt_iff_lt]
  rw [this, Fin.card_Iio]

private theorem contractLeft_basis (b : Module.Basis I R M) (d : Module.Dual R M)
    (s : Set.powersetCard I (n + 1)) :
    exteriorPower.contractLeft R M d n (b.exteriorPower (n + 1) s) =
      ∑ k : Fin (n + 1), ((-1 : R) ^ (k : ℕ) * d (b (ofFinEmbEquiv.symm s k))) •
        b.exteriorPower n (eraseNth s k) := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, contractLeft_apply_ιMulti_removeNth]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, Function.comp_apply,
    coe_ofFinEmbEquiv_symm_eraseNth]
  rfl

end Exterior
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section DualVec

variable {P : Type u} [CommRing P] {I : Type} [Fintype I]

def dualVec (x : I → P) : Module.Dual P (I → P) := ∑ i, x i • LinearMap.proj i

private theorem dualVec_apply (x v : I → P) : dualVec x v = ∑ i, x i * v i := by
  simp only [dualVec, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.coe_proj,
    Function.eval, smul_eq_mul]

private theorem dualVec_single [DecidableEq I] (x : I → P)
    (i : I) : dualVec x (Pi.single i 1) = x i := by
  rw [dualVec_apply, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
    (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same, mul_one]

end DualVec
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section Chains

variable {P : Type u} [CommRing P] {I : Type} (M : Type v) [AddCommGroup M] [Module P M]

private theorem single_mem_C [DecidableEq I] {p : ℕ} (S : Finset I) (hS : S.card = p)
    (m : M) : Pi.single S m ∈ C (P := P) (I := I) M p :=
  fun T hT => Pi.single_eq_of_ne (M := fun _ => M) (fun h : T = S => hT (by rw [h, hS])) m

def C.equivFun (p : ℕ) : C (P := P) (I := I) M p ≃ₗ[P] (Set.powersetCard I p → M) where
  toFun m s := (m : Finset I → M) s
  invFun c := ⟨fun T => if h : T.card = p then c ⟨T, mem_iff.mpr h⟩ else 0,
    fun T hT => dite_eq_right hT⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv m := by
    refine Subtype.ext (funext fun T => ?_)
    dsimp only
    split_ifs with h
    · rfl
    · exact (m.2 T h).symm
  right_inv c := by
    funext s
    dsimp only
    rw [dite_eq_left (mem_iff.mp s.prop)]

variable {M}

private theorem C.equivFun_symm_apply {p : ℕ} (c : Set.powersetCard I p → M) (T : Finset I)
    (hT : T.card = p) : ((C.equivFun (P := P) M p).symm c : Finset I → M) T = c ⟨T,
    mem_iff.mpr hT⟩ := dite_eq_left hT

end Chains
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section Basis

variable {P : Type u} [CommRing P] {I : Type} [LinearOrder I] [Fintype I]

variable (P I)

noncomputable def toExterior (p : ℕ) : C (P := P) (I := I) P p ≃ₗ[P] ⋀[P]^p (I → P) :=
  (C.equivFun P p).trans ((Pi.basisFun P I).exteriorPower p).equivFun.symm

variable {P I}

private theorem toExterior_apply {p : ℕ} (m : C (P := P) (I := I) P p) :
    toExterior P I p m = ∑ s : Set.powersetCard I p, (m : Finset I → P) s • (Pi.basisFun P
        I).exteriorPower p s := by
  rw [toExterior, LinearEquiv.trans_apply, Module.Basis.equivFun_symm_apply]; rfl

private theorem toExterior_symm_apply {p : ℕ} (ω : ⋀[P]^p (I → P)) (T : Finset I)
    (hT : T.card = p) : ((toExterior P I p).symm ω : Finset I → P) T =
    ((Pi.basisFun P I).exteriorPower p).repr ω ⟨T,
        mem_iff.mpr hT⟩ := by
  rw [toExterior, LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
    C.equivFun_symm_apply _ T hT, Module.Basis.equivFun_apply]

private theorem toExterior_single (S : Finset I) {p : ℕ} (hS : S.card = p) :
    toExterior P I p ⟨Pi.single S 1, single_mem_C P S hS 1⟩ = (Pi.basisFun P I).exteriorPower p ⟨S,
        mem_iff.mpr hS⟩ := by
  rw [toExterior_apply, Finset.sum_eq_single ⟨S, mem_iff.mpr hS⟩]
  · simp
  · intro s _ hs
    change (Pi.single S (1 : P) : Finset I → P) s • _ = 0
    rw [Pi.single_eq_of_ne (fun h => hs (Subtype.ext h)), zero_smul]
  · exact fun h => (h (Finset.mem_univ _)).elim

private theorem toExterior_symm_basis {p : ℕ} (s : Set.powersetCard I p) :
    (toExterior P I p).symm ((Pi.basisFun P I).exteriorPower p s) =
      ⟨Pi.single (s : Finset I) 1, single_mem_C P (s : Finset I) (mem_iff.mp s.prop) 1⟩ := by
  rw [LinearEquiv.symm_apply_eq, toExterior_single (s : Finset I) (mem_iff.mp s.prop)]

private theorem dualVec_basisFun (x : I → P) (i : I) : dualVec x (Pi.basisFun P I i) = x i := by
  rw [Pi.basisFun_apply, dualVec_single]

omit [Fintype I] in
private theorem ofFinEmbEquiv_symm_mem {p : ℕ} (s : Set.powersetCard I p) (k : Fin p) :
    ofFinEmbEquiv.symm s k ∈ (s : Finset I) :=
  mem_coe_iff.mpr ((mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨k, rfl⟩)

private theorem eq_sum_single {p : ℕ} {m : Finset I → P} (hm : m ∈ C (P := P) (I := I) P p) :
    m = ∑ s : Set.powersetCard I p, m s • (Pi.single (s : Finset I) (1 : P) : Finset I → P) := by
  funext T
  rw [Finset.sum_apply]
  by_cases hT : T.card = p
  · rw [Finset.sum_eq_single ⟨T, mem_iff.mpr hT⟩]
    · simp
    · intro s _ hs
      rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h => hs (Subtype.ext h.symm)), smul_zero]
    · exact fun h => (h (Finset.mem_univ _)).elim
  · rw [hm T hT, Finset.sum_eq_zero]
    intro s _
    rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h : T = ↑s => hT
        (by rw [h]; exact mem_iff.mp s.prop)),
      smul_zero]

private theorem d_single (x : I → P) {p : ℕ} (s : Set.powersetCard I (p + 1)) :
    d x P (Pi.single (s : Finset I) (1 : P)) =
      ∑ k : Fin (p + 1), ((-1 : P) ^ (k : ℕ) * x (ofFinEmbEquiv.symm s k)) •
        (Pi.single ((eraseNth s k : Set.powersetCard I p) : Finset I) (1 : P) : Finset I → P) := by
  funext T
  rw [d_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, val_eraseNth]
  by_cases hT : ∃ i ∈ (s : Finset I), (s : Finset I).erase i = T
  · obtain ⟨i₀, hi₀, rfl⟩ := hT
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, ofFinEmbEquiv.symm s k₀ = i₀ :=
      (mem_range_ofFinEmbEquiv_symm_iff_mem s i₀).mpr (mem_coe_iff.mp hi₀)
    rw [Finset.sum_eq_single i₀, Finset.sum_eq_single k₀]
    · rw [Finset.insert_erase hi₀, Pi.single_eq_same, hk₀, Pi.single_eq_same, mul_one, mul_one,
        coef_of_not_mem x (Finset.notMem_erase i₀ _), sgn, Finset.filter_erase,
        Finset.erase_eq_of_notMem (by simp), ← hk₀, card_filter_lt_ofFinEmbEquiv_symm]
    · intro k _ hk
      rw [Pi.single_eq_of_ne, mul_zero]
      intro h
      apply hk
      apply (ofFinEmbEquiv.symm s).injective
      rw [hk₀]
      by_contra hne
      have hmem : ofFinEmbEquiv.symm s k ∈ (s : Finset I).erase i₀ :=
        Finset.mem_erase.mpr ⟨hne, ofFinEmbEquiv_symm_mem s k⟩
      rw [h] at hmem
      exact Finset.notMem_erase _ _ hmem
    · exact fun h => (h (Finset.mem_univ _)).elim
    · intro i _ hi
      by_cases hiT : i ∈ (s : Finset I).erase i₀
      · rw [coef_of_mem x hiT, zero_mul]
      · rw [Pi.single_eq_of_ne, mul_zero]
        intro h
        have hiS : i ∈ (s : Finset I) := h ▸ Finset.mem_insert_self i _
        exact hiT (Finset.mem_erase.mpr ⟨hi, hiS⟩)
    · exact fun h => (h (Finset.mem_univ _)).elim
  · push Not at hT
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro k _
      rw [Pi.single_eq_of_ne (fun h => hT _ (ofFinEmbEquiv_symm_mem s k) h.symm), mul_zero]
    · intro i _
      by_cases hiT : i ∈ T
      · rw [coef_of_mem x hiT, zero_mul]
      · rw [Pi.single_eq_of_ne, mul_zero]
        intro h
        exact hT i (h ▸ Finset.mem_insert_self i T) (by rw [← h, Finset.erase_insert hiT])

set_option synthInstance.maxHeartbeats 200000 in
-- Instance search through these linear-equivalence coercions is slow.
private theorem toExterior_d (x : I → P) {p : ℕ} (m : Finset I → P)
    (hm : m ∈ C (P := P) (I := I) P (p + 1)) : toExterior P I p ⟨d x P m, d_mem_C x P hm⟩ =
    exteriorPower.contractLeft _ _ (dualVec x) p (toExterior P I (p + 1) ⟨m, hm⟩) := by
  rw [← LinearEquiv.eq_symm_apply]
  apply Subtype.ext
  change d x P m = _
  rw [toExterior_apply, map_sum, map_sum]
  simp only [map_smul, contractLeft_basis, dualVec_basisFun, map_sum, toExterior_symm_basis,
      Submodule.coe_sum,
    Submodule.coe_smul]
  conv_lhs => rw [eq_sum_single hm, map_sum]
  simp only [map_smul, d_single]

private theorem d_toExterior_symm (x : I → P) {p : ℕ} (ω : ⋀[P]^(p + 1) (I → P)) :
    d x P ((toExterior P I (p + 1)).symm ω) =
      (toExterior P I p).symm (exteriorPower.contractLeft _ _ (dualVec x) p ω) := by
  have h := toExterior_d x ((toExterior P I (p + 1)).symm ω) ((toExterior P I (p + 1)).symm ω).2
  rw [Subtype.coe_eta, LinearEquiv.apply_symm_apply, ← LinearEquiv.eq_symm_apply] at h
  exact congrArg Subtype.val h

end Basis
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section Cycle

variable {P : Type u} [CommRing P]

omit [CommRing P] in
private theorem concat_inl {J I : Type} [LinearOrder J] [LinearOrder I]
    (f : J → P) (x : I → P) (j : J) : concat f x (toLex (Sum.inl j)) = f j := rfl

omit [CommRing P] in
private theorem concat_inr {J I : Type} [LinearOrder J] [LinearOrder I]
    (f : J → P) (x : I → P) (i : I) : concat f x (toLex (Sum.inr i)) = x i := rfl

variable {n : ℕ}

def inlOrderEmb (n : ℕ) : Fin n ↪o Fin n ⊕ₗ Fin n :=
  OrderEmbedding.ofStrictMono (fun j => toLex (Sum.inl j)) fun _ _ h => Sum.Lex.inl_lt_inl_iff.mpr h

def inrOrderEmb (n : ℕ) : Fin n ↪o Fin n ⊕ₗ Fin n :=
  OrderEmbedding.ofStrictMono (fun i => toLex (Sum.inr i)) fun _ _ h => Sum.Lex.inr_lt_inr_iff.mpr h

def inlBlock (n : ℕ) : Finset (Fin n ⊕ₗ Fin n) := Finset.univ.map (inlₗ' (Fin n))

def inrBlock (n : ℕ) : Finset (Fin n ⊕ₗ Fin n) := Finset.univ.map (inrₗ (Fin n))

private theorem card_inlBlock (n : ℕ) : (inlBlock n).card = n := by simp [inlBlock]
private theorem card_inrBlock (n : ℕ) : (inrBlock n).card = n := by simp [inrBlock]

private theorem ofFinEmbEquiv_symm_inlBlock :
    ofFinEmbEquiv.symm ⟨inlBlock n, mem_iff.mpr (card_inlBlock n)⟩ = inlOrderEmb n := by
  rw [ofFinEmbEquiv_symm_apply]
  exact (Finset.orderEmbOfFin_unique' (card_inlBlock n)
      fun j => Finset.mem_map_of_mem _ (Finset.mem_univ j)).symm

private theorem ofFinEmbEquiv_symm_inrBlock :
    ofFinEmbEquiv.symm ⟨inrBlock n, mem_iff.mpr (card_inrBlock n)⟩ = inrOrderEmb n := by
  rw [ofFinEmbEquiv_symm_apply]
  exact (Finset.orderEmbOfFin_unique' (card_inrBlock n)
      fun j => Finset.mem_map_of_mem _ (Finset.mem_univ j)).symm

def cycleVec (g : Matrix (Fin n) (Fin n) P) (j : Fin n) : Fin n ⊕ₗ Fin n → P :=
  Pi.single (toLex (Sum.inl j)) 1 - ∑ i, g j i • Pi.single (toLex (Sum.inr i)) 1

private theorem dualVec_concat_cycleVec (f x : Fin n → P) (g : Matrix (Fin n) (Fin n) P)
    (hf : ∀ j, f j = ∑ i, g j i * x i) (j : Fin n) : dualVec (concat f x) (cycleVec g j) = 0 := by
  rw [cycleVec, map_sub, map_sum, dualVec_single, concat_inl, hf, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, dualVec_single, concat_inr, smul_eq_mul]

noncomputable def tateCycle (g : Matrix (Fin n) (Fin n) P) : ⋀[P]^n (Fin n ⊕ₗ Fin n → P) :=
  exteriorPower.ιMulti P n (cycleVec g)

private theorem contractLeft_tateCycle (f x : Fin n → P) (g : Matrix (Fin n) (Fin n) P)
    (hf : ∀ j, f j = ∑ i, g j i * x i) :
    contractLeft (Q := (0 : QuadraticForm P (Fin n ⊕ₗ Fin n → P))) (dualVec (concat f x))
      (tateCycle g : ExteriorAlgebra P (Fin n ⊕ₗ Fin n → P)) = 0 :=
  contractLeft_ιMulti_of_forall_eq_zero _ _ (dualVec_concat_cycleVec f x g hf)

noncomputable def tateChain (g : Matrix (Fin n) (Fin n) P) : Finset (Fin n ⊕ₗ Fin n) → P :=
  (toExterior P (Fin n ⊕ₗ Fin n) n).symm (tateCycle g)

private theorem tateChain_mem_C (g : Matrix (Fin n) (Fin n) P) : tateChain g ∈ C (P := P) P n :=
  ((toExterior P (Fin n ⊕ₗ Fin n) n).symm (tateCycle g)).2

set_option synthInstance.maxHeartbeats 200000 in
-- Instance search through these linear-equivalence coercions is slow.
theorem d_tateChain (f x : Fin n → P) (g : Matrix (Fin n) (Fin n) P)
    (hf : ∀ j, f j = ∑ i, g j i * x i) : d (concat f x) P (tateChain g) = 0 := by
  cases n with
  | zero =>
    funext T
    rw [d_apply]
    exact Finset.sum_eq_zero fun i _ => isEmptyElim (ofLex i : Fin 0 ⊕ Fin 0)
  | succ n =>
    rw [tateChain, d_toExterior_symm]
    have : exteriorPower.contractLeft _ _ (dualVec (concat f x)) n (tateCycle g) = 0 :=
      Subtype.ext (contractLeft_tateCycle f x g hf)
    rw [this, map_zero]
    rfl

private theorem tateChain_apply (g : Matrix (Fin n) (Fin n) P) (T : Finset (Fin n ⊕ₗ Fin n))
    (hT : T.card = n) : tateChain g T = (Matrix.of fun i j => cycleVec g i (ofFinEmbEquiv.symm ⟨T,
        mem_iff.mpr hT⟩ j)).det := by
  rw [tateChain, toExterior_symm_apply _ T hT, exteriorPower.basis_repr_apply, tateCycle,
    exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [Module.Basis.coord_apply, Pi.basisFun_repr]

private theorem cycleVec_inl (g : Matrix (Fin n) (Fin n) P) (i j : Fin n) :
    cycleVec g i (toLex (Sum.inl j)) = (1 : Matrix (Fin n) (Fin n) P) i j := by
  simp [cycleVec, Pi.single_apply, Matrix.one_apply, eq_comm]

private theorem cycleVec_inr (g : Matrix (Fin n) (Fin n) P) (i j : Fin n) :
    cycleVec g i (toLex (Sum.inr j)) = -g i j := by
  simp [cycleVec, Pi.single_apply]

private theorem tateChain_inlBlock (g : Matrix (Fin n) (Fin n) P) : tateChain g (inlBlock n) = 1 :=
    by
  rw [tateChain_apply g _ (card_inlBlock n), ofFinEmbEquiv_symm_inlBlock]
  have : (Matrix.of fun i j => cycleVec g i (inlOrderEmb n j)) = 1 := by
    ext i j; exact cycleVec_inl g i j
  rw [this, Matrix.det_one]

private theorem tateChain_inrBlock (g : Matrix (Fin n) (Fin n) P) :
    tateChain g (inrBlock n) = (-1) ^ n * g.det := by
  rw [tateChain_apply g _ (card_inrBlock n), ofFinEmbEquiv_symm_inrBlock]
  have : (Matrix.of fun i j => cycleVec g i (inrOrderEmb n j)) = -g := by
    ext i j; exact cycleVec_inr g i j
  rw [this, Matrix.det_neg, Fintype.card_fin]

end Cycle
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section Reg

variable {P : Type u} [CommRing P] {I : Type} [LinearOrder I] [Fintype I] (x : I → P)

private theorem subsingleton_H_of_isWeaklyRegular_of_step
    (step : ∀ (N : Type v) [AddCommGroup N] [Module P N] (r : P), r ∈ Ideal.span (Set.range x) →
      IsSMulRegular N r → ∀ p : ℕ, Subsingleton (H x (QuotSMulTop r N) (p + 1)) →
          Subsingleton (H x N p))
    (M : Type v) [AddCommGroup M] [Module P M] (rs : List P)
    (hreg : RingTheory.Sequence.IsWeaklyRegular M rs) (hrs : ∀ r ∈ rs, r ∈ Ideal.span (Set.range x))
    (p : ℕ) (hp : Fintype.card I < p + rs.length) : Subsingleton (H x M p) := by
  induction rs generalizing M p with
  | nil => exact subsingleton_H_of_card_lt x M (by simpa using hp)
  | cons r rs ih =>
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hreg
    refine step M r (hrs r List.mem_cons_self) hreg.1 p
      (ih (QuotSMulTop r M) hreg.2 (fun s hs => hrs s (List.mem_cons_of_mem r hs)) (p + 1) ?_)
    rw [List.length_cons] at hp
    omega

end Reg
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section Func

open CategoryTheory

variable {P : Type u} [CommRing P] {I : Type} [LinearOrder I] [Fintype I] (x : I → P)
variable {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module P M₁] [AddCommGroup M₂] [Module P M₂]
  [AddCommGroup M₃] [Module P M₃] (φ : M₁ →ₗ[P] M₂) (ψ : M₂ →ₗ[P] M₃)

private theorem mapC_ofLinearMap_injective (hφ : Function.Injective φ) (p : ℕ) :
    Function.Injective ((ChainMap.ofLinearMap x φ).mapC p) := fun _ _ h =>
  Subtype.ext (funext fun T => hφ (congr_fun (congrArg Subtype.val h) T))

private theorem mapC_ofLinearMap_surjective (hψ : Function.Surjective ψ) (p : ℕ) :
    Function.Surjective ((ChainMap.ofLinearMap x ψ).mapC p) := fun m₃ => by
  refine ⟨⟨fun T => if T.card = p then Function.surjInv hψ ((m₃ : Finset I → M₃) T) else 0,
    fun T hT => ite_eq_right hT⟩, Subtype.ext (funext fun T => ?_)⟩
  change ψ (if T.card = p then Function.surjInv hψ ((m₃ : Finset I → M₃) T) else 0) = _
  by_cases hT : T.card = p
  · rw [ite_eq_left hT]; exact Function.surjInv_eq hψ _
  · rw [ite_eq_right hT, map_zero, m₃.2 T hT]

private theorem mapC_ofLinearMap_exact (hex : Function.Exact φ ψ) (p : ℕ) :
    Function.Exact ((ChainMap.ofLinearMap x φ).mapC p) ((ChainMap.ofLinearMap x ψ).mapC p) := by
  intro m₂
  constructor
  · intro hm
    have hT : ∀ T, ∃ a, φ a = (m₂ : Finset I → M₂) T := fun T =>
      (hex _).mp (congr_fun (congrArg Subtype.val hm) T)
    choose m₁ hm₁ using hT
    refine ⟨⟨fun T => if T.card = p then m₁ T else 0, fun T hT => ite_eq_right hT⟩,
        Subtype.ext (funext fun T => ?_)⟩
    change φ (if T.card = p then m₁ T else 0) = _
    by_cases hT : T.card = p
    · rw [ite_eq_left hT, hm₁]
    · rw [ite_eq_right hT, map_zero, m₂.2 T hT]
  · rintro ⟨m₁, rfl⟩
    exact Subtype.ext (funext fun T => (hex _).mpr ⟨_, rfl⟩)

noncomputable def mapSC (h : ψ ∘ₗ φ = 0) : ShortComplex (ChainComplex (ModuleCat.{v} P) ℕ) :=
  ShortComplex.mk (ChainMap.ofLinearMap x φ).toHom (ChainMap.ofLinearMap x ψ).toHom
    (HomologicalComplex.hom_ext _ _ fun p => by
      rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
      ext m : 2
      refine Subtype.ext (funext fun T => ?_)
      exact congr($h ((show C (P := P) (I := I) M₁ p from m).1 T)))

private theorem mapSC_shortExact (h : ψ ∘ₗ φ = 0) (hφ : Function.Injective φ) (hψ :
    Function.Surjective ψ)
    (hex : Function.Exact φ ψ) : (mapSC x φ ψ h).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p =>
    ModuleCat.shortComplex_shortExact _ (mapC_ofLinearMap_exact x φ ψ hex p)
      (mapC_ofLinearMap_injective x φ hφ p) (mapC_ofLinearMap_surjective x ψ hψ p)

variable {N : Type v} [AddCommGroup N] [Module P N] (r : P)

open scoped Pointwise in
noncomputable def smulSC : ShortComplex (ChainComplex (ModuleCat.{v} P) ℕ) :=
  mapSC x (r • LinearMap.id : N →ₗ[P] N) (r • (⊤ : Submodule P N)).mkQ (by
    ext n
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul n r ⊤ Submodule.mem_top)

open scoped Pointwise in
private theorem smulSC_shortExact (hr : IsSMulRegular N r) : (smulSC x (N := N) r).ShortExact :=
  mapSC_shortExact x _ _ _ (fun _ _ h => hr h) (Submodule.mkQ_surjective _) fun n => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨m, -, rfl⟩; exact ⟨m, rfl⟩
    · rintro ⟨m, rfl⟩; exact ⟨m, Submodule.mem_top, rfl⟩

private theorem mapH_ofLinearMap_smul_id (p : ℕ) (h : H x N p) :
    (ChainMap.ofLinearMap x (r • LinearMap.id : N →ₗ[P] N)).mapH p h = r • h := by
  induction h using Submodule.Quotient.induction_on with
  | H z =>
    rw [ChainMap.mapH, HMap.mapH_mk, ← Submodule.Quotient.mk_smul]
    rfl

private theorem subsingleton_H_of_subsingleton_H_quotSMulTop (hr : IsSMulRegular N r) {p : ℕ}
    (htpy : ∀ h : H x N p, r • h = 0) (hq : Subsingleton (H x (QuotSMulTop r N) (p + 1))) :
    Subsingleton (H x N p) := by
  have hS := smulSC_shortExact x r hr
  have hex := hS.homology_exact₁ (p + 1) p rfl
  have hzero : HomologicalComplex.homologyMap (smulSC x (N := N) r).f p = 0 := by
    change HomologicalComplex.homologyMap (ChainMap.ofLinearMap x
        (r • LinearMap.id : N →ₗ[P] N)).toHom p = 0
    rw [← cancel_mono (bridge x N p).hom, ChainMap.homologyMap_bridge, Limits.zero_comp]
    have h0 : (ChainMap.ofLinearMap x (r • LinearMap.id : N →ₗ[P] N)).mapH p = 0 :=
      LinearMap.ext fun h => (mapH_ofLinearMap_smul_id x r p h).trans (htpy h)
    rw [h0, ModuleCat.ofHom_zero, Limits.comp_zero]
  have hepi : Epi (hS.δ (p + 1) p rfl) := hex.epi_f hzero
  have hsurj := (ModuleCat.epi_iff_surjective _).mp hepi
  have : Subsingleton (ModuleCat.of P (H x (QuotSMulTop r N) (p + 1))) := hq
  have : Subsingleton ((smulSC x (N := N) r).X₃.homology (p + 1)) :=
    (bridge x (QuotSMulTop r N) (p + 1)).toLinearEquiv.toEquiv.subsingleton
  have : Subsingleton (ModuleCat.of P (H x N p)) :=
    haveI : Subsingleton ((complex x N).homology p) := hsurj.subsingleton
    (bridge x N p).toLinearEquiv.symm.toEquiv.subsingleton
  exact this

private theorem subsingleton_H_of_isWeaklyRegular (M : Type v) [AddCommGroup M] [Module P M]
    {r : ℕ} (y : Fin r → P) (hy : RingTheory.Sequence.IsWeaklyRegular M (List.ofFn y)) (hyx : ∀ k,
        y k ∈ Ideal.span (Set.range x))
    (p : ℕ) (hp : Fintype.card I < p + r) : Subsingleton (H x M p) :=
  subsingleton_H_of_isWeaklyRegular_of_step x
    (fun N _ _ a ha hreg q hq => subsingleton_H_of_subsingleton_H_quotSMulTop x a hreg
      (fun h => smul_H_eq_zero_of_mem_span a ha h) hq)
    M (List.ofFn y) hy (fun a ha => by obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha; exact hyx k) p
    (by rwa [List.length_ofFn])

private theorem subsingleton_H_of_isWeaklyRegular_of_card_eq (M : Type v) [AddCommGroup M]
    [Module P M] {r : ℕ} (y : Fin r → P) (hy : RingTheory.Sequence.IsWeaklyRegular M (List.ofFn y))
    (hyx : ∀ k, y k ∈ Ideal.span (Set.range x)) (hr : r = Fintype.card I) (p : ℕ)
    (hp : 0 < p) : Subsingleton (H x M p) :=
  subsingleton_H_of_isWeaklyRegular x M y hy hyx p (by omega)

end Func
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

section Wiebe

variable {P : Type u} [CommRing P] {n : ℕ} (x f : Fin n → P) (g : Matrix (Fin n) (Fin n) P)

private theorem mem_span_of_eq (hf : ∀ i, f i = ∑ j, g i j * x j)
    (i : Fin n) : f i ∈ Ideal.span (Set.range x) := by
  rw [hf i]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

private theorem span_le_span_of_eq (hf : ∀ i, f i = ∑ j, g i j * x j) :
    Ideal.span (Set.range f) ≤ Ideal.span (Set.range x) :=
  Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact mem_span_of_eq x f g hf i)

private theorem mul_det_mem_span (hf : ∀ i, f i = ∑ j, g i j * x j) (j : Fin n) :
    x j * g.det ∈ Ideal.span (Set.range f) := by
  have hgx : g.mulVec x = f := funext fun i => (hf i).symm
  have key : x j * g.det = g.adjugate.mulVec f j := by
    rw [← hgx, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [key]
  change ∑ i, g.adjugate j i * f i ∈ _
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

private theorem mul_det_mem_span_of_mem (hf : ∀ i, f i = ∑ j, g i j * x j) {a : P}
    (ha : a ∈ Ideal.span (Set.range x)) : a * g.det ∈ Ideal.span (Set.range f) := by
  induction ha using Submodule.span_induction with
  | mem b hb => obtain ⟨j, rfl⟩ := hb; exact mul_det_mem_span x f g hf j
  | zero => rw [zero_mul]; exact Ideal.zero_mem _
  | add b c _ _ hb hc => rw [add_mul]; exact Ideal.add_mem _ hb hc
  | smul r b _ hb => rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ r hb

theorem mk_det_mem_torsionBySet (hf : ∀ i, f i = ∑ j, g i j * x j) :
    Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ∈
      Submodule.torsionBySet P (P ⧸ Ideal.span (Set.range f)) (Set.range x) := by
  rw [Submodule.mem_torsionBySet_iff]
  rintro ⟨_, j, rfl⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact mul_det_mem_span x f g hf j

noncomputable def wiebeMap (hf : ∀ i, f i = ∑ j, g i j * x j) :
    (P ⧸ Ideal.span (Set.range x)) →ₗ[P]
      Submodule.torsionBySet P (P ⧸ Ideal.span (Set.range f)) (Set.range x) :=
  Submodule.liftQ (Ideal.span (Set.range x))
    (LinearMap.toSpanSingleton P _ ⟨_, mk_det_mem_torsionBySet x f g hf⟩) (by
      intro a ha
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      apply Subtype.ext
      have h : Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ∈ Submodule.torsionBySet P
          (P ⧸ Ideal.span (Set.range f)) ↑(Ideal.span (Set.range x)) := by
        rw [← Submodule.torsionBySet_eq_torsionBySet_span]
        exact mk_det_mem_torsionBySet x f g hf
      exact (Submodule.mem_torsionBySet_iff _ _).mp h ⟨a, ha⟩)

private theorem coe_wiebeMap_mk (hf : ∀ i, f i = ∑ j, g i j * x j) (a : P) :
    (wiebeMap x f g hf (Ideal.Quotient.mk _ a) : P ⧸ Ideal.span (Set.range f)) =
      Ideal.Quotient.mk _ (a * g.det) := by
  change ((LinearMap.toSpanSingleton P _ ⟨_, mk_det_mem_torsionBySet x f g hf⟩ a :
    Submodule.torsionBySet P (P ⧸ Ideal.span (Set.range f)) (Set.range x)) :
        P ⧸ Ideal.span (Set.range f)) = _
  rw [LinearMap.toSpanSingleton_apply, Submodule.coe_smul, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq,
    map_mul]

private theorem wiebeMap_mk_eq_zero_iff (hf : ∀ i, f i = ∑ j, g i j * x j) (a : P) :
    wiebeMap x f g hf (Ideal.Quotient.mk _ a) = 0 ↔ a * g.det ∈ Ideal.span (Set.range f) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coe_wiebeMap_mk x f g hf a]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩

private theorem colon_span_eq_of_surjective (hf : ∀ i, f i = ∑ j, g i j * x j)
    (hs : Function.Surjective (wiebeMap x f g hf)) :
    (Ideal.span (Set.range f)).colon (Ideal.span (Set.range x)) =
      Ideal.span (Set.range f) ⊔ Ideal.span {g.det} := by
  apply le_antisymm
  · intro a ha
    rw [Submodule.mem_colon] at ha
    have hmem : Ideal.Quotient.mk (Ideal.span (Set.range f)) a ∈
        Submodule.torsionBySet P (P ⧸ Ideal.span (Set.range f)) (Set.range x) := by
      rw [Submodule.mem_torsionBySet_iff]
      rintro ⟨_, j, rfl⟩
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
          Ideal.Quotient.eq_zero_iff_mem, mul_comm]
      exact ha (x j) (Ideal.subset_span ⟨j, rfl⟩)
    obtain ⟨q, hq⟩ := hs ⟨_, hmem⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hq' := congrArg Subtype.val hq
    rw [coe_wiebeMap_mk, Ideal.Quotient.eq] at hq'
    rw [show a = b * g.det - (b * g.det - a) by ring]
    exact Submodule.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨b, rfl⟩))
      (Ideal.mem_sup_left hq')
  · rw [sup_le_iff]
    constructor
    · intro a ha
      rw [Submodule.mem_colon]
      intro s _
      rw [smul_eq_mul, mul_comm]
      exact Ideal.mul_mem_left _ s ha
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_colon]
      intro s hs
      rw [smul_eq_mul, mul_comm]
      exact mul_det_mem_span_of_mem x f g hf hs

private theorem colon_det_eq_of_injective (hf : ∀ i, f i = ∑ j, g i j * x j)
    (hi : Function.Injective (wiebeMap x f g hf)) :
    (Ideal.span (Set.range f)).colon (Ideal.span {g.det}) = Ideal.span (Set.range x) := by
  apply le_antisymm
  · intro a ha
    rw [Ideal.mem_colon_span_singleton] at ha
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hi ((wiebeMap_mk_eq_zero_iff x f g hf a).mpr ha ▸ (map_zero _).symm)
  · intro a ha
    rw [Ideal.mem_colon_span_singleton]
    exact mul_det_mem_span_of_mem x f g hf ha

end Wiebe
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

end Koszul
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

namespace Koszul

open Finset

universe u v

section WiebeAssembly

variable {P : Type u} [CommRing P] {n : ℕ} (x f : Fin n → P) (g : Matrix (Fin n) (Fin n) P)

private theorem mem_smul_top_iff {I : Ideal P} {a : P} : a ∈ I • (⊤ : Submodule P P) ↔ a ∈ I := by
  rw [show I • (⊤ : Submodule P P) = I * ⊤ from rfl, Ideal.mul_top]

noncomputable def tateZ (hf : ∀ i, f i = ∑ j, g i j * x j) :
    Z (concat f x) P (Fintype.card (Fin n)) :=
  ⟨tateChain g, ⟨by rw [Fintype.card_fin]; exact tateChain_mem_C g,
    LinearMap.mem_ker.mpr (d_tateChain f x g hf)⟩⟩

@[scoped simp] private theorem coe_tateZ (hf : ∀ i, f i = ∑ j, g i j * x j) :
    ((tateZ x f g hf : Z (concat f x) P _) : Finset (Fin n ⊕ₗ Fin n) → P) = tateChain g := rfl

noncomputable def tateClass (hf : ∀ i, f i = ∑ j, g i j * x j) :
    H (concat f x) P (Fintype.card (Fin n)) :=
  Submodule.Quotient.mk (tateZ x f g hf)

private theorem coe_HTopEquiv_peel_smul_tateClass (hf : ∀ i, f i = ∑ j, g i j * x j)
    (a : P) : ((HTopEquiv x (ModSpan f P) ((peel f x P).mapH _ (a • tateClass x f g hf)) :
        annihilatedBy x (ModSpan f P)) : ModSpan f P) =
      Submodule.Quotient.mk (a * ((-1) ^ n * g.det)) := by
  rw [map_smul, map_smul, Submodule.coe_smul, tateClass, ChainMap.mapH, HMap.mapH_mk, HTopEquiv_mk,
    HMap.coe_mapZ, ChainMap.toHMap_toLinearMap, coe_tateZ]
  change a • (Submodule.Quotient.mk (tateChain g (inrBlock n)) : ModSpan f P) = _
  rw [tateChain_inrBlock, ← Submodule.Quotient.mk_smul]
  rfl

private theorem coe_HTopEquiv_peelTop_smul_tateClass (hf : ∀ i, f i = ∑ j, g i j * x j)
    (a : P) : ((HTopEquiv f (ModSpan x P) ((peelTop f x P).mapH _ (a • tateClass x f g hf)) :
        annihilatedBy f (ModSpan x P)) : ModSpan x P) =
      Submodule.Quotient.mk a := by
  rw [map_smul, map_smul, Submodule.coe_smul, tateClass, ChainMap.mapH, HMap.mapH_mk, HTopEquiv_mk,
    HMap.coe_mapZ, ChainMap.toHMap_toLinearMap, coe_tateZ]
  change a • (Submodule.Quotient.mk (tateChain g (inlBlock n)) : ModSpan x P) = _
  rw [tateChain_inlBlock, ← Submodule.Quotient.mk_smul]
  exact congrArg _ (mul_one a)

private theorem exists_eq_smul_tateClass (hf : ∀ i, f i = ∑ j, g i j * x j)
    (hxK : ∀ p, 0 < p → Subsingleton (H x P p)) (h : H (concat f x) P (Fintype.card (Fin n))) :
    ∃ b : P, h = b • tateClass x f g hf := by
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _
    ((HTopEquiv f (ModSpan x P) ((peelTop f x P).mapH (Fintype.card (Fin n)) h) :
      annihilatedBy f (ModSpan x P)) : ModSpan x P)
  refine ⟨b, (peelTop_bijective f x P hxK (Fintype.card (Fin n))).1
    ((HTopEquiv f (ModSpan x P)).injective (Subtype.ext ?_))⟩
  rw [coe_HTopEquiv_peelTop_smul_tateClass]
  exact hb.symm

set_option synthInstance.maxHeartbeats 200000 in
-- Instance search through these linear-equivalence coercions is slow.
private theorem wiebeMap_bijective (hf : ∀ i, f i = ∑ j, g i j * x j)
    (hxK : ∀ p, 0 < p → Subsingleton (H x P p)) (hfK : ∀ p, 0 < p → Subsingleton (H f P p)) :
    Function.Bijective (wiebeMap x f g hf) := by
  have hu : (-1 : P) ^ n * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  let E₁ : H (concat f x) P (Fintype.card (Fin n)) ≃ₗ[P] annihilatedBy x (ModSpan f P) :=
    (LinearEquiv.ofBijective _ (peel_bijective f x P hfK _)).trans (HTopEquiv x (ModSpan f P))
  have hE₁ : ∀ a : P, ((E₁ (a • tateClass x f g hf) : annihilatedBy x (ModSpan f P)) :
      ModSpan f P) = Submodule.Quotient.mk (a * ((-1) ^ n * g.det)) := fun a =>
    coe_HTopEquiv_peel_smul_tateClass x f g hf a
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [wiebeMap_mk_eq_zero_iff] at hq
    have h1 : E₁ (((-1) ^ n * a) • tateClass x f g hf) = 0 := by
      apply Subtype.ext
      rw [hE₁, Submodule.coe_zero, Submodule.Quotient.mk_eq_zero, mem_smul_top_iff,
        show (-1 : P) ^ n * a * ((-1) ^ n * g.det) = ((-1 : P) ^ n * (-1) ^ n) *
            (a * g.det) by ring, hu,
        one_mul]
      exact hq
    have h2 : ((-1) ^ n * a) • tateClass x f g hf = 0 := E₁.injective (by rw [h1, map_zero])
    have h3 := coe_HTopEquiv_peelTop_smul_tateClass x f g hf ((-1) ^ n * a)
    rw [h2, map_zero, map_zero, Submodule.coe_zero, eq_comm, Submodule.Quotient.mk_eq_zero,
      mem_smul_top_iff] at h3
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have h4 := Ideal.mul_mem_left _ ((-1 : P) ^ n) h3
    rwa [← mul_assoc, hu, one_mul] at h4
  · intro t
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (t : P ⧸ Ideal.span (Set.range f))
    have hs' : (Submodule.Quotient.mk s : ModSpan f P) ∈ annihilatedBy x (ModSpan f P) := by
      intro i
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_smul_top_iff,
          smul_eq_mul]
      have := (Submodule.mem_torsionBySet_iff _ _).mp t.2 ⟨x i, Set.mem_range_self i⟩
      rw [← hs, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
          Ideal.Quotient.eq_zero_iff_mem] at this
      exact this
    obtain ⟨b, hb⟩ := exists_eq_smul_tateClass x f g hf hxK (E₁.symm ⟨_, hs'⟩)
    have hb' := congrArg (fun h => ((E₁ h : annihilatedBy x (ModSpan f P)) : ModSpan f P)) hb
    simp only [LinearEquiv.apply_symm_apply] at hb'
    rw [hE₁, Submodule.Quotient.eq, mem_smul_top_iff] at hb'
    refine ⟨Ideal.Quotient.mk _ (b * (-1) ^ n), Subtype.ext ?_⟩
    rw [coe_wiebeMap_mk, ← hs, Ideal.Quotient.eq, show b * (-1) ^ n * g.det - s =
        -(s - b * ((-1) ^ n * g.det)) by ring]
    exact neg_mem hb'

private theorem colon_span_eq_sup_span_det_of_isWeaklyRegular
    (x f : Fin n → P) (g : Matrix (Fin n) (Fin n) P) (hf : ∀ i, f i = ∑ j, g i j * x j)
    (hy : ∃ y : Fin n → P, RingTheory.Sequence.IsWeaklyRegular P (List.ofFn y) ∧
      ∀ i, y i ∈ Ideal.span (Set.range f)) :
    (Ideal.span (Set.range f)).colon (Ideal.span (Set.range x)) =
        Ideal.span (Set.range f) ⊔ Ideal.span {g.det} ∧
      (Ideal.span (Set.range f)).colon (Ideal.span {g.det}) = Ideal.span (Set.range x) := by
  obtain ⟨y, hy, hyf⟩ := hy
  have hfK : ∀ p, 0 < p → Subsingleton (H f P p) :=
    subsingleton_H_of_isWeaklyRegular_of_card_eq f P y hy hyf (Fintype.card_fin n).symm
  have hxK : ∀ p, 0 < p → Subsingleton (H x P p) :=
    subsingleton_H_of_isWeaklyRegular_of_card_eq x P y hy
      (fun k => span_le_span_of_eq x f g hf (hyf k)) (Fintype.card_fin n).symm
  have hb := wiebeMap_bijective x f g hf hxK hfK
  exact ⟨colon_span_eq_of_surjective x f g hf hb.2, colon_det_eq_of_injective x f g hf hb.1⟩

end WiebeAssembly
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

end Koszul
open scoped JacobianSquarePresentation.KoszulColon.Koszul.HMap
  JacobianSquarePresentation.KoszulColon.Koszul.ChainMap
  JacobianSquarePresentation.KoszulColon.Koszul

universe u

private theorem solution
    {P : Type u} [CommRing P] {n : ℕ} (x f : Fin n → P) (g : Matrix (Fin n) (Fin n) P)
    (hf : ∀ i, f i = ∑ j, g i j * x j)
    (hy : ∃ y : Fin n → P, RingTheory.Sequence.IsWeaklyRegular P (List.ofFn y) ∧
      ∀ i, y i ∈ Ideal.span (Set.range f)) :
    (Ideal.span (Set.range f)).colon (Ideal.span (Set.range x)) =
        Ideal.span (Set.range f) ⊔ Ideal.span {g.det} ∧
      (Ideal.span (Set.range f)).colon (Ideal.span {g.det}) = Ideal.span (Set.range x) :=
  Koszul.colon_span_eq_sup_span_det_of_isWeaklyRegular x f g hf hy
end JacobianSquarePresentation.KoszulColon

namespace JacobianSquarePresentation.QuotientDetMem

universe u

open MvPowerSeries

namespace TateK

section Support

variable {σ : Type*} {R : Type*} [CommRing R]

def upperPart (i : σ) (N : ℕ) (h : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun m => if N ≤ m i then coeff m h else 0

private theorem coeff_upperPart (i : σ) (N : ℕ) (h : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff m (upperPart i N h) = if N ≤ m i then coeff m h else 0 := rfl

private theorem X_pow_dvd_upperPart (i : σ) (N : ℕ) (h : MvPowerSeries σ R) :
    (X i : MvPowerSeries σ R) ^ N ∣ upperPart i N h :=
  X_pow_dvd_iff.mpr fun m hm => by rw [coeff_upperPart, ite_eq_right (not_le.mpr hm)]

private theorem coeff_sub_upperPart_of_le {i : σ} {N : ℕ} (h : MvPowerSeries σ R) {m : σ →₀ ℕ}
    (hm : N ≤ m i) : coeff m (h - upperPart i N h) = 0 := by
  rw [map_sub, coeff_upperPart, ite_eq_left hm, sub_self]

private theorem coeff_sub_upperPart_of_lt {i : σ} {N : ℕ} (h : MvPowerSeries σ R) {m : σ →₀ ℕ}
    (hm : m i < N) : coeff m (h - upperPart i N h) = coeff m h := by
  rw [map_sub, coeff_upperPart, ite_eq_right (not_le.mpr hm), sub_zero]

private theorem coeff_eq_zero_of_mem_span (T : Set σ) (N : σ → ℕ) {h : MvPowerSeries σ R}
    (hmem : h ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ R) ^ N i) '' T))
    (m : σ →₀ ℕ) (hm : ∀ i ∈ T, m i < N i) : coeff m h = 0 := by
  classical
  induction hmem using Submodule.span_induction generalizing m with
  | mem p hp =>
    obtain ⟨i, hi, rfl⟩ := hp
    rw [coeff_X_pow, ite_eq_right]
    intro hmi
    have := hm i hi
    rw [hmi, Finsupp.single_eq_same] at this
    exact lt_irrefl _ this
  | zero => exact map_zero _
  | add p q _ _ hp hq => rw [map_add, hp m hm, hq m hm, add_zero]
  | smul a p _ hp =>
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun uv huv => ?_
    rw [hp uv.2 (fun i hi => lt_of_le_of_lt ?_ (hm i hi)), mul_zero]
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
    rw [← this, Finsupp.add_apply]
    exact Nat.le_add_left _ _

private theorem mem_span_X_pow_iff (S : Finset σ) (N : σ → ℕ) (h : MvPowerSeries σ R) :
    h ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ R) ^ N i) '' (↑S : Set σ)) ↔
      ∀ m : σ →₀ ℕ, (∀ i ∈ S, m i < N i) → coeff m h = 0 := by
  classical
  refine ⟨fun hmem m hm => coeff_eq_zero_of_mem_span _ N hmem m (fun i hi => hm i hi), ?_⟩
  induction S using Finset.induction_on generalizing h with
  | empty =>
    intro H
    have : h = 0 := MvPowerSeries.ext fun m =>
        by rw [H m (fun i hi => absurd hi (Finset.notMem_empty i)), map_zero]
    rw [this]
    exact Submodule.zero_mem _
  | insert i S hi IH =>
    intro H
    have h1 : upperPart i (N i) h ∈
        Ideal.span ((fun i => (X i : MvPowerSeries σ R) ^ N i) '' (↑(insert i S) : Set σ)) := by
      obtain ⟨q, hq⟩ := X_pow_dvd_upperPart i (N i) h
      rw [hq]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, Finset.mem_insert_self i S, rfl⟩)
    have h2 : h - upperPart i (N i) h ∈
        Ideal.span ((fun i => (X i : MvPowerSeries σ R) ^ N i) '' (↑(insert i S) : Set σ)) := by
      refine Ideal.span_mono (Set.image_mono (Finset.coe_subset.mpr (Finset.subset_insert i S)))
          (IH _ ?_)
      intro m hm
      by_cases hle : N i ≤ m i
      · exact coeff_sub_upperPart_of_le h hle
      · rw [coeff_sub_upperPart_of_lt h (not_le.mp hle)]
        exact H m fun j hj => by
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact not_le.mp hle
          · exact hm j hj
    have := add_mem h2 h1
    rwa [sub_add_cancel] at this

private theorem mem_span_range_X_iff [Finite σ] (h : MvPowerSeries σ R) :
    h ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ↔ constantCoeff h = 0 := by
  have := Fintype.ofFinite σ
  have hset : Set.range (X : σ → MvPowerSeries σ R) =
      (fun i => (X i : MvPowerSeries σ R) ^ (fun _ => 1) i) ''
          (↑(Finset.univ : Finset σ) : Set σ) := by
    rw [Finset.coe_univ, Set.image_univ]
    exact congrArg Set.range (funext fun i => (pow_one _).symm)
  rw [hset, mem_span_X_pow_iff, ← coeff_zero_eq_constantCoeff_apply]
  constructor
  · intro H; exact H 0 fun i _ => Nat.one_pos
  · intro H m hm
    have : m = 0 := Finsupp.ext fun i => Nat.lt_one_iff.mp (hm i (Finset.mem_univ i))
    rw [this, H]

end Support

section Regular

variable {R : Type*} [CommRing R]

private theorem isSMulRegular_quotient_ideal (I : Ideal R) (r : R)
    (H : ∀ h, r * h ∈ I → h ∈ I) : IsSMulRegular (R ⧸ (I • ⊤ : Submodule R R)) r := by
  have hI : (I • ⊤ : Submodule R R) = I := by rw [Ideal.smul_eq_mul, Ideal.mul_top]
  intro a b hab
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  change r • Submodule.Quotient.mk a = r • Submodule.Quotient.mk b at hab
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
      ← smul_sub, hI,
    smul_eq_mul] at hab
  rw [Submodule.Quotient.eq, hI]
  exact H _ hab

variable {n : ℕ}

private theorem setOf_mem_take_ofFn {α : Type*} (y : Fin n → α) (j : ℕ) :
    {r | r ∈ (List.ofFn y).take j} = y '' {i : Fin n | (i : ℕ) < j} := by
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_image, List.mem_iff_getElem, List.length_take,
      List.length_ofFn,
    List.getElem_take, List.getElem_ofFn]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, (lt_min_iff.mp hi).2⟩, (lt_min_iff.mp hi).1, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, lt_min_iff.mpr ⟨hi, i.2⟩, rfl⟩

private theorem isWeaklyRegular_X_pow (N : Fin n → ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries (Fin n) R)
      (List.ofFn fun i : Fin n => (X i : MvPowerSeries (Fin n) R) ^ N i) := by
  classical
  refine (RingTheory.Sequence.isWeaklyRegular_iff_Fin _ _).mpr fun j => ?_
  rw [Fin.getElem_fin, List.getElem_ofFn]
  apply isSMulRegular_quotient_ideal
  intro h hmem
  have hS : {r | r ∈ (List.ofFn fun i : Fin n => (X i : MvPowerSeries (Fin n) R) ^ N i).take j} =
      (fun i => (X i : MvPowerSeries (Fin n) R) ^ (N i)) ''
        (↑(Finset.univ.filter fun i : Fin n => (i : ℕ) < j) : Set (Fin n)) := by
    rw [setOf_mem_take_ofFn, Finset.coe_filter]
    simp
  dsimp only [Ideal.ofList] at hmem ⊢
  rw [hS, mem_span_X_pow_iff (N := fun i => N i)] at hmem ⊢
  intro m hm
  have hjn : (j : ℕ) < n := by simpa using j.2
  have key := hmem (Finsupp.single (⟨j, hjn⟩ : Fin n) (N ⟨j, hjn⟩) + m) fun i hi => by
    have hij : (i : ℕ) < j := (Finset.mem_filter.mp hi).2
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne, zero_add]
    · exact hm i hi
    · intro h'; rw [h'] at hij; exact lt_irrefl (j : ℕ) hij
  rwa [X_pow_eq, coeff_add_monomial_mul, one_mul] at key

end Regular

section Powers

variable {k : Type u} [Field k] {σ : Type*}

private theorem exists_X_pow_mem (I : Ideal (MvPowerSeries σ k))
    [Module.Finite k (MvPowerSeries σ k ⧸ I)] (i : σ) : ∃ N :
    ℕ, (X i : MvPowerSeries σ k) ^ N ∈ I := by
  obtain ⟨p, pmonic, hp⟩ : IsIntegral k (Ideal.Quotient.mk I (X i)) :=
      Algebra.IsIntegral.isIntegral _
  have hpI : Polynomial.aeval (X i : MvPowerSeries σ k) p ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk k,
        ← Polynomial.aeval_algHom_apply,
      Ideal.Quotient.mkₐ_eq_mk]
    exact hp
  obtain ⟨q, hq⟩ : (Polynomial.X : Polynomial k) ^ p.natTrailingDegree ∣ p :=
    Polynomial.X_pow_dvd_iff.mpr fun d hd => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
  have hq0 : q.coeff 0 ≠ 0 := by
    have := Polynomial.coeff_X_pow_mul q p.natTrailingDegree 0
    rw [zero_add, ← hq] at this
    rw [← this]
    exact mt Polynomial.trailingCoeff_eq_zero.mp pmonic.ne_zero
  have hunit : IsUnit (Polynomial.aeval (X i : MvPowerSeries σ k) q) := by
    rw [isUnit_iff_constantCoeff, Polynomial.aeval_def, Polynomial.hom_eval₂, constantCoeff_X,
      Polynomial.eval₂_at_zero]
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← c_eq_algebraMap, constantCoeff_C]
    exact isUnit_iff_ne_zero.mpr hq0
  refine ⟨p.natTrailingDegree, ?_⟩
  rw [hq, map_mul, map_pow, Polynomial.aeval_X] at hpI
  obtain ⟨u, hu⟩ := hunit
  rw [← hu] at hpI
  have := I.mul_mem_right (↑u⁻¹ : MvPowerSeries σ k) hpI
  rwa [mul_assoc, Units.mul_inv, mul_one] at this

end Powers

section Socle

variable {B : Type*} [CommRing B]

private theorem exists_mul_ne_zero_and_forall_mul_eq_zero (𝔪 : Ideal B) (h𝔪 : IsNilpotent 𝔪)
    {y : B} (hy : y ≠ 0) : ∃ w : B, w * y ≠ 0 ∧ ∀ v ∈ 𝔪, v * (w * y) = 0 := by
  classical
  let Q : ℕ → Prop := fun t => ∀ w ∈ 𝔪 ^ t, w * y = 0
  obtain ⟨R, hR⟩ := h𝔪
  have hex : ∃ t, Q t := ⟨R, fun w hw =>
      by rw [hR] at hw; rw [(Submodule.mem_bot B).mp hw, zero_mul]⟩
  have h0 : ¬Q 0 := fun H => hy (by simpa using H 1 (by rw [pow_zero, Ideal.one_eq_top]; trivial))
  have hpos : 0 < Nat.find hex := Nat.pos_of_ne_zero fun h => h0 (h ▸ Nat.find_spec hex)
  have hnot : ¬Q (Nat.find hex - 1) := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
  simp only [Q, not_forall, exists_prop] at hnot
  obtain ⟨w, hw, hwy⟩ := hnot
  refine ⟨w, hwy, fun v hv => ?_⟩
  rw [← mul_assoc]
  apply Nat.find_spec hex
  have : Nat.find hex = Nat.find hex - 1 + 1 := (Nat.sub_add_cancel hpos).symm
  rw [this, pow_succ']
  exact Ideal.mul_mem_mul hv hw

end Socle

section Main

variable {k : Type u} [Field k] {n : ℕ}

private theorem span_range_X_ne_top : Ideal.span (Set.range
    (X : Fin n → MvPowerSeries (Fin n) k)) ≠ ⊤ := by
  intro h
  have h1 : (1 : MvPowerSeries (Fin n) k) ∈ Ideal.span (Set.range
      (X : Fin n → MvPowerSeries (Fin n) k)) := by
    rw [h]; trivial
  rw [mem_span_range_X_iff, map_one] at h1
  exact one_ne_zero h1

private theorem main (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) k))
    (f : Fin n → MvPowerSeries (Fin n) k) (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))] :
    Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ≠ 0 ∧
      ∀ J : Ideal (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f)), J ≠ ⊥ →
        Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ∈ J := by
  classical
  choose N hN using fun i : Fin n => exists_X_pow_mem (Ideal.span (Set.range f)) i
  obtain ⟨hcol₁, hcol₂⟩ := JacobianSquarePresentation.KoszulColon.solution
    (fun j : Fin n => (X j : MvPowerSeries (Fin n) k)) f g hf ⟨fun i => X i ^ N i,
        isWeaklyRegular_X_pow N, hN⟩
  have hXtop : Ideal.span (Set.range fun j : Fin n => (X j : MvPowerSeries (Fin n) k)) ≠ ⊤ :=
    span_range_X_ne_top
  have hdet : g.det ∉ Ideal.span (Set.range f) := fun hmem => hXtop <| by
    rw [← hcol₂]
    exact Submodule.colon_eq_top_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
  refine ⟨fun h0 => hdet (Ideal.Quotient.eq_zero_iff_mem.mp h0), fun J hJ => ?_⟩
  set d := Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det with hd
  set 𝔪 : Ideal (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f)) :=
    Ideal.span (Set.range fun j : Fin n => Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j)) with
        h𝔪
  have hxd : ∀ j : Fin n, Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j) * d = 0 := fun j => by
    rw [hd, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_colon_span_singleton, hcol₂]
    exact Ideal.subset_span ⟨j, rfl⟩
  have h𝔪d : ∀ v ∈ 𝔪, v * d = 0 := by
    have hle : 𝔪 ≤ (⊥ : Ideal (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))).colon {d} :=
      Ideal.span_le.mpr fun v ⟨j, hj⟩ => by
        rw [← hj, SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul, hxd j]
        exact Submodule.zero_mem _
    intro v hv
    have := hle hv
    rwa [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot] at this
  have h𝔪nil : IsNilpotent 𝔪 := by
    have hfg : 𝔪.FG := ⟨Finset.univ.image fun j : Fin n => Ideal.Quotient.mk
        (Ideal.span (Set.range f)) (X j), by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
    refine (Ideal.FG.isNilpotent_iff_le_nilradical hfg).mpr (Ideal.span_le.mpr ?_)
    rintro v ⟨j, rfl⟩
    exact mem_nilradical.mpr ⟨N j, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hN j⟩
  obtain ⟨y, hyJ, hy0⟩ := (Submodule.ne_bot_iff J).mp hJ
  obtain ⟨w, hz0, hz𝔪⟩ := exists_mul_ne_zero_and_forall_mul_eq_zero 𝔪 h𝔪nil hy0
  have hzJ : w * y ∈ J := J.mul_mem_left w hyJ
  obtain ⟨zt, hzt⟩ := Ideal.Quotient.mk_surjective (w * y)
  have hzt_col : zt ∈ (Ideal.span (Set.range f)).colon
      (Ideal.span (Set.range fun j : Fin n => (X j : MvPowerSeries (Fin n) k))) := by
    rw [Ideal.colon_span, Submodule.mem_colon]
    rintro _ ⟨j, rfl⟩
    rw [smul_eq_mul, mul_comm, ← Ideal.Quotient.eq_zero_iff_mem, map_mul, hzt]
    exact hz𝔪 _ (Ideal.subset_span ⟨j, rfl⟩)
  rw [hcol₁] at hzt_col
  obtain ⟨a, ha, bd, hbd, habd⟩ := Submodule.mem_sup.mp hzt_col
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hbd
  have hz : w * y = Ideal.Quotient.mk (Ideal.span (Set.range f)) b * d := by
    rw [← hzt, ← habd, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, map_mul]
  have hb𝔪 : Ideal.Quotient.mk (Ideal.span (Set.range f)) (b - C (constantCoeff b)) ∈ 𝔪 := by
    have hmem : b - C (constantCoeff b) ∈ Ideal.span (Set.range
        (X : Fin n → MvPowerSeries (Fin n) k)) := by
      rw [mem_span_range_X_iff, map_sub, constantCoeff_C, sub_self]
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span (Set.range f))) hmem
    rwa [Ideal.map_span, ← Set.range_comp] at this
  have hz' : w * y = Ideal.Quotient.mk (Ideal.span (Set.range f)) (C (constantCoeff b)) * d := by
    have hsplit : Ideal.Quotient.mk (Ideal.span (Set.range f)) b =
        Ideal.Quotient.mk (Ideal.span (Set.range f)) (C (constantCoeff b)) +
          Ideal.Quotient.mk (Ideal.span (Set.range f)) (b - C (constantCoeff b)) := by
      rw [← map_add, add_sub_cancel]
    rw [hz, hsplit, add_mul, h𝔪d _ hb𝔪, add_zero]
  have hb0 : constantCoeff b ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero, zero_mul] at hz'
    exact hz0 hz'
  have : d = Ideal.Quotient.mk (Ideal.span (Set.range f)) (C (constantCoeff b)⁻¹) * (w * y) := by
    rw [hz', ← mul_assoc, ← map_mul, ← map_mul (C : k →+* MvPowerSeries (Fin n) k),
        inv_mul_cancel₀ hb0,
      map_one, map_one, one_mul]
  rw [this]
  exact J.mul_mem_left _ hzJ

end Main

end TateK

private theorem solution
    {k : Type u} [Field k] {n : ℕ} (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) k))
    (f : Fin n → MvPowerSeries (Fin n) k) (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))] :
    Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ≠ 0 ∧
      ∀ J : Ideal (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f)), J ≠ ⊥ →
        Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det ∈ J := by
  exact TateK.main g f hf
end JacobianSquarePresentation.QuotientDetMem

namespace JacobianSquarePresentation.BijectiveCompr2

universe u

private theorem solution {k : Type u} [Field k] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) k)) (f : Fin n → MvPowerSeries (Fin n) k)
    (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))] :
    ∃ l : (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f)) →ₗ[k] k,
      Function.Bijective ((LinearMap.mul k (MvPowerSeries (Fin n) k ⧸ Ideal.span
          (Set.range f))).compr₂ l) := by
  obtain ⟨hs0, hsJ⟩ := JacobianSquarePresentation.QuotientDetMem.solution g f hf
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero k hs0
  refine ⟨l, ?_⟩
  have hinj : Function.Injective
      ((LinearMap.mul k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range f))).compr₂ l) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    have hne : Ideal.span {a} ≠ ⊥ := by
      rwa [Ne, Ideal.span_singleton_eq_bot]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hsJ _ hne)
    apply hl
    have h := LinearMap.congr_fun ha b
    rw [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.zero_apply, mul_comm, hb] at h
    exact h
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).mp hinj⟩
end JacobianSquarePresentation.BijectiveCompr2


namespace JacobianSquarePresentation.ArtinianQuotientPow

open scoped TensorProduct

section

private theorem main (A : Type*) [CommRing A] [IsArtinianRing A] (𝔫 : Ideal A) [h𝔫 : 𝔫.IsMaximal]
    (N : ℕ) (hN : (Ideal.jacobson (⊥ : Ideal A)) ^ N = ⊥) :
    Nonempty ((A ⧸ 𝔫 ^ N) ≃ₐ[A] Localization.AtPrime 𝔫) := by
  classical
  let f : A →ₐ[A] Localization.AtPrime 𝔫 := Algebra.ofId A _
  have hf : Function.Surjective f := IsArtinianRing.localization_surjective 𝔫.primeCompl _
  have hcomax : ∀ s : A, s ∉ 𝔫 → Ideal.span {s} ⊔ 𝔫 ^ N = ⊤ := by
    intro s hs
    apply Ideal.sup_pow_eq_top
    have hlt : 𝔫 < Ideal.span {s} ⊔ 𝔫 := by
      refine lt_of_le_of_ne le_sup_right fun h => hs ?_
      rw [h]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self s)
    exact h𝔫.out.2 _ hlt
  have hker : RingHom.ker f = 𝔫 ^ N := by
    ext a
    rw [RingHom.mem_ker]
    change algebraMap A (Localization.AtPrime 𝔫) a = 0 ↔ _
    rw [IsLocalization.map_eq_zero_iff 𝔫.primeCompl]
    constructor
    · rintro ⟨⟨s, hs⟩, hsa⟩
      have h1 : (1 : A) ∈ Ideal.span {s} ⊔ 𝔫 ^ N := by rw [hcomax s hs]; trivial
      obtain ⟨u, hu, n, hn, hun⟩ := Submodule.mem_sup.1 h1
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu
      have : a = a * n := by
        calc a = a * (c * s + n) := by rw [hun, mul_one]
          _ = c * (s * a) + a * n := by ring
          _ = a * n := by rw [hsa, mul_zero, zero_add]
      rw [this]
      exact Ideal.mul_mem_left _ _ hn
    · intro ha
      let T : Finset (Ideal A) := (IsArtinianRing.setOfPred_isMaximal_finite A).toFinset.erase 𝔫
      have hT : ∀ M ∈ T, M.IsMaximal ∧ M ≠ 𝔫 := fun M hM => by
        rw [Finset.mem_erase, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hM
        exact ⟨hM.2, hM.1⟩
      have hcop : IsCoprime (∏ M ∈ T, M ^ N) 𝔫 := by
        refine IsCoprime.prod_left fun M hM => ?_
        refine IsCoprime.pow_left ?_
        rw [Ideal.isCoprime_iff_sup_eq]
        exact (hT M hM).1.coprime_of_ne h𝔫 (hT M hM).2
      rw [Ideal.isCoprime_iff_sup_eq] at hcop
      have h1 : (1 : A) ∈ (∏ M ∈ T, M ^ N) ⊔ 𝔫 := by rw [hcop]; trivial
      obtain ⟨s, hs, n, hn, hsn⟩ := Submodule.mem_sup.1 h1
      have hs𝔫 : s ∉ 𝔫 := fun h => h𝔫.ne_top ((Ideal.eq_top_iff_one _).2
          (by rw [← hsn]; exact Ideal.add_mem _ h hn))
      refine ⟨⟨s, hs𝔫⟩, ?_⟩
      have hall : (∏ M ∈ T, M ^ N) * 𝔫 ^ N ≤ Ideal.jacobson (⊥ : Ideal A) ^ N := by
        have hprod : (∏ M ∈ T, M ^ N) * 𝔫 ^ N = (∏ M ∈ insert 𝔫 T, M) ^ N := by
          rw [Finset.prod_insert (Finset.notMem_erase 𝔫 _), mul_pow, Finset.prod_pow, mul_comm]
        rw [hprod]
        refine Ideal.pow_right_mono ?_ N
        refine le_trans Ideal.prod_le_inf ?_
        rw [Ideal.jacobson]
        refine le_sInf fun J hJ => Finset.inf_le ?_
        rw [Finset.mem_insert]
        by_cases hJ𝔫 : J = 𝔫
        · exact Or.inl hJ𝔫
        · refine Or.inr ?_
          rw [Finset.mem_erase, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
          exact ⟨hJ𝔫, hJ.2⟩
      have hmem : s * a ∈ Ideal.jacobson (⊥ : Ideal A) ^ N := hall (Ideal.mul_mem_mul hs ha)
      rw [hN, Ideal.mem_bot] at hmem
      simpa using hmem
  exact ⟨(Ideal.quotientEquivAlgOfEq A hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hf)⟩

end

private theorem solution
    (A : Type*) [CommRing A] [IsArtinianRing A] (𝔫 : Ideal A) [𝔫.IsMaximal]
    (N : ℕ) (hN : (Ideal.jacobson (⊥ : Ideal A)) ^ N = ⊥) :
    Nonempty ((A ⧸ 𝔫 ^ N) ≃ₐ[A] Localization.AtPrime 𝔫) :=
  main A 𝔫 N hN
end JacobianSquarePresentation.ArtinianQuotientPow

namespace JacobianSquarePresentation.BijectiveBaseChange

open scoped TensorProduct

private theorem solution
    {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
        [Module.Free R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N)
    (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], Function.Bijective (f.baseChange (R ⧸ 𝔪))) :
    Function.Bijective f := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton M := Module.subsingleton R M
    have : Subsingleton N := Module.subsingleton R N
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  let bM := Module.Free.chooseBasis R M
  let bN := Module.Free.chooseBasis R N
  obtain ⟨𝔪₀, h𝔪₀⟩ := Ideal.exists_maximal R
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R M) = Fintype.card
      (Module.Free.ChooseBasisIndex R N) := by
    have := h𝔪₀
    let e := LinearEquiv.ofBijective (f.baseChange (R ⧸ 𝔪₀)) (h 𝔪₀)
    have h1 := e.finrank_eq
    rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (R ⧸ 𝔪₀) bM),
      Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (R ⧸ 𝔪₀) bN)] at h1
    exact h1
  let σ : Module.Free.ChooseBasisIndex R N ≃ Module.Free.ChooseBasisIndex R M :=
      (Fintype.equivOfCardEq hcard).symm
  let bN' : Module.Basis (Module.Free.ChooseBasisIndex R M) R N := bN.reindex σ
  let A := LinearMap.toMatrix bM bN' f
  suffices hdet : IsUnit A.det by
    exact (LinearEquiv.ofIsUnitDet hdet).bijective
  by_contra hndet
  obtain ⟨𝔪, h𝔪, hmem⟩ := exists_max_ideal_of_mem_nonunits hndet
  have := h𝔪
  have hzero : (A.map (algebraMap R (R ⧸ 𝔪))).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hA : LinearMap.toMatrix (Algebra.TensorProduct.basis (R ⧸ 𝔪) bM)
      (Algebra.TensorProduct.basis (R ⧸ 𝔪) bN')
      (f.baseChange (R ⧸ 𝔪)) = A.map (algebraMap R (R ⧸ 𝔪)) := LinearMap.toMatrix_baseChange _ _ _ _
  have hunit : IsUnit (LinearMap.toMatrix (Algebra.TensorProduct.basis (R ⧸ 𝔪) bM)
      (Algebra.TensorProduct.basis (R ⧸ 𝔪) bN')
      (f.baseChange (R ⧸ 𝔪))).det := by
    have := LinearEquiv.isUnit_det (LinearEquiv.ofBijective (f.baseChange (R ⧸ 𝔪)) (h 𝔪))
      (Algebra.TensorProduct.basis (R ⧸ 𝔪) bM) (Algebra.TensorProduct.basis (R ⧸ 𝔪) bN')
    exact this
  rw [hA, hzero] at hunit
  exact not_isUnit_zero hunit
end JacobianSquarePresentation.BijectiveBaseChange

namespace JacobianSquarePresentation.BezoutianField

open scoped TensorProduct

universe u

namespace SchejaStorch

open TensorProduct

section general

variable {R : Type*} [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
  (a : Fin m → Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
  (S : Type*) [CommRing S] [Algebra R S]

abbrev Q := MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)

noncomputable def theta : Module.Dual R (Q f) →ₗ[R] Q f where
  toFun φ := Algebra.TensorProduct.lid R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))
        (LinearMap.rTensor (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) φ
          (Algebra.TensorProduct.map
              (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
                  (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
            (Matrix.det (Matrix.of a))))
  map_add' φ ψ := by simp [LinearMap.rTensor_add]
  map_smul' r φ := by simp [LinearMap.rTensor_smul]

noncomputable def mapP : MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) S :=
  MvPolynomial.mapAlgHom (Algebra.ofId R S)

@[scoped simp] private lemma mapP_X (j : Fin m) : mapP (m := m) S (MvPolynomial.X j : MvPolynomial
    (Fin m)
    R) = MvPolynomial.X j := by
  simp [mapP]

noncomputable def fS : Fin m → MvPolynomial (Fin m) S := fun i => mapP S (f i)

noncomputable def psi : MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R →ₐ[R]
    MvPolynomial (Fin m) S ⊗[S] MvPolynomial (Fin m) S :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft (R := S) (S := R) (A := MvPolynomial (Fin m) S)
      (B := MvPolynomial (Fin m) S)).comp (mapP S))
    (((Algebra.TensorProduct.includeRight (R := S) (A := MvPolynomial (Fin m) S)
      (B := MvPolynomial (Fin m) S)).restrictScalars R).comp (mapP S))
    (fun _ _ => Commute.all _ _)

@[scoped simp] private lemma psi_tmul (p q : MvPolynomial (Fin m) R) :
    psi (m := m) S (p ⊗ₜ q) = mapP S p ⊗ₜ mapP S q := by
  simp [psi]

noncomputable def aS : Fin m → Fin m → MvPolynomial (Fin m) S ⊗[S] MvPolynomial (Fin m) S :=
  fun i j => psi S (a i j)

private lemma det_aS : Matrix.det (Matrix.of (aS a S)) = psi S (Matrix.det (Matrix.of a)) := by
  rw [AlgHom.map_det]
  rfl

private lemma bezout_aS
    (ha : ∀ i, f i ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] f i =
      ∑ j, a i j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) :
    ∀ i, fS f S i ⊗ₜ[S] (1 : MvPolynomial (Fin m) S) - (1 : MvPolynomial (Fin m) S) ⊗ₜ[S] fS f S i =
      ∑ j, aS a S i j * (MvPolynomial.X j ⊗ₜ[S] 1 - 1 ⊗ₜ[S] MvPolynomial.X j) := by
  intro i
  have := congrArg (psi S) (ha i)
  simpa [map_sub, map_sum, map_mul, fS, aS] using this

noncomputable def iota : Q f →ₐ[R] Q (fS f S) :=
  Ideal.quotientMapₐ _ (mapP S) (by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨i, rfl⟩)

@[scoped simp] private lemma iota_mk (p : MvPolynomial (Fin m) R) :
    iota f S (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (mapP S p) := rfl

noncomputable def deltaFwd : S ⊗[R] Q f →ₐ[S] Q (fS f S) :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (iota f S) (fun _ _ => Commute.all _ _)

@[scoped simp] private lemma deltaFwd_tmul (s : S) (x : Q f) : deltaFwd f S (s ⊗ₜ x) = s • iota f S
    x := by
  simp [deltaFwd, ← Algebra.smul_def]

noncomputable def evalX : MvPolynomial (Fin m) S →ₐ[S] S ⊗[R] Q f :=
  MvPolynomial.aeval fun j => (1 : S) ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range f))
      (MvPolynomial.X j)

private lemma evalX_mapP (p : MvPolynomial (Fin m) R) :
    evalX f S (mapP S p) = (1 : S) ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range f)) p := by
  suffices h : ((evalX f S).restrictScalars R).comp (mapP S) =
      (Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
          from
    congr($h p)
  apply MvPolynomial.algHom_ext
  intro j
  simp [evalX]

noncomputable def deltaInv : Q (fS f S) →ₐ[S] S ⊗[R] Q f :=
  Ideal.Quotient.liftₐ _ (evalX f S) (by
    intro p hp
    have hle : Ideal.span (Set.range (fS f S)) ≤ RingHom.ker (evalX f S) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have h0 : Ideal.Quotient.mk (Ideal.span (Set.range f)) (f i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
      simp [fS, evalX_mapP, h0]
    exact hle hp)

@[scoped simp] private lemma deltaInv_mk (p : MvPolynomial (Fin m) S) :
    deltaInv f S (Ideal.Quotient.mk _ p) = evalX f S p := rfl

lemma deltaFwd_comp_deltaInv : (deltaFwd f S).comp (deltaInv f S) = AlgHom.id S _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  simp [evalX]

lemma deltaInv_comp_deltaFwd : (deltaInv f S).comp (deltaFwd f S) = AlgHom.id S _ := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    simp [evalX]

noncomputable def delta : S ⊗[R] Q f ≃ₐ[S] Q (fS f S) :=
  AlgEquiv.ofAlgHom (deltaFwd f S) (deltaInv f S) (deltaFwd_comp_deltaInv f S)
      (deltaInv_comp_deltaFwd f S)

lemma isBaseChange : IsBaseChange S (iota f S).toLinearMap :=
  IsBaseChange.of_equiv (delta f S).toLinearEquiv fun x => by simp [delta]

private lemma finite_baseChange [Module.Finite R (Q f)] : Module.Finite S (Q (fS f S)) :=
  Module.Finite.equiv (delta f S).toLinearEquiv

private lemma key (φ : Module.Dual R (Q f)) (φ' : Module.Dual S (Q (fS f S)))
    (h : ∀ p : MvPolynomial (Fin m) R, φ' (Ideal.Quotient.mk _ (mapP S p)) =
        algebraMap R S (φ (Ideal.Quotient.mk _ p)))
    (z : MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R) :
    Algebra.TensorProduct.lid S (Q (fS f S)) (LinearMap.rTensor (Q (fS f S)) φ'
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ S (Ideal.span (Set.range (fS f S))))
          (Ideal.Quotient.mkₐ S (Ideal.span (Set.range (fS f S)))) (psi S z)))
      = iota f S (Algebra.TensorProduct.lid R (Q f) (LinearMap.rTensor (Q f) φ
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
          (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) z))) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p q =>
    simp [h]

variable [Module.Free R (Q f)] [Module.Finite R (Q f)]

noncomputable def gamma : S ⊗[R] Module.Dual R (Q f) ≃ₗ[S] Module.Dual S (Q (fS f S)) :=
  (isBaseChange f S).toDualBaseChange

private lemma gamma_tmul (φ : Module.Dual R (Q f)) (x : Q f) :
    gamma f S (1 ⊗ₜ φ) (iota f S x) = algebraMap R S (φ x) := by
  have := (isBaseChange f S).toDualBaseChange_tmul 1 φ x
  simpa [gamma] using this

private lemma square :
    (delta f S).toLinearEquiv.toLinearMap ∘ₗ (theta f a).baseChange S
      = (theta (fS f S) (aS a S)) ∘ₗ (gamma f S).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s φ
  have hk := key f S φ (gamma f S (1 ⊗ₜ φ)) (fun p => gamma_tmul f S φ (Ideal.Quotient.mk _ p))
    (Matrix.det (Matrix.of a))
  have hs : s ⊗ₜ[R] φ = s • ((1 : S) ⊗ₜ[R] φ) := by simp [TensorProduct.smul_tmul']
  rw [hs, map_smul, map_smul]
  congr 1
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.baseChange_tmul,
    AlgEquiv.toLinearEquiv_apply]
  change deltaFwd f S (1 ⊗ₜ theta f a φ) = _
  rw [deltaFwd_tmul, one_smul]
  change iota f S (theta f a φ) = theta (fS f S) (aS a S) (gamma f S (1 ⊗ₜ φ))
  simp only [theta, LinearMap.coe_mk, AddHom.coe_mk]
  rw [det_aS]
  exact hk.symm

private lemma bijective_iff :
    Function.Bijective (theta (fS f S) (aS a S)) ↔ Function.Bijective ((theta f a).baseChange S) :=
        by
  have hsq := square f a S
  have hfun : ⇑(theta (fS f S) (aS a S)) = (delta f S).toLinearEquiv ∘ (theta f a).baseChange S ∘
      (gamma f S).symm := by
    funext ω
    have := congr($hsq ((gamma f S).symm ω))
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.apply_symm_apply] at this
    simpa using this.symm
  rw [hfun, EquivLike.comp_bijective, EquivLike.bijective_comp]

end general

private lemma bijective_of_bijective_baseChange {k : Type*} (K : Type*) [Field k] [Field K]
    [Algebra k K] {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (T : V →ₗ[k] W) (h : Function.Bijective (T.baseChange K)) : Function.Bijective T := by
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective k K T,
      ← LinearMap.baseChange_eq_lTensor]
  exact h

end SchejaStorch
open scoped JacobianSquarePresentation.BezoutianField.SchejaStorch

open SchejaStorch in
private theorem solution
    (R : Type u) [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    [Module.Finite R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))]
    [Module.Free R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))]
    (a : Fin m → Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : ∀ i, f i ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] f i =
      ∑ j, a i j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j))
    (hfield : ∀ (K : Type u) [Field K] [IsAlgClosed K] (g : Fin m → MvPolynomial (Fin m) K)
      [Module.Finite K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))]
      (b : Fin m → Fin m → MvPolynomial (Fin m) K ⊗[K] MvPolynomial (Fin m) K),
      (∀ i, g i ⊗ₜ[K] (1 : MvPolynomial (Fin m) K) - (1 : MvPolynomial (Fin m) K) ⊗ₜ[K] g i =
        ∑ j, b i j * (MvPolynomial.X j ⊗ₜ[K] 1 - 1 ⊗ₜ[K] MvPolynomial.X j)) →
      Function.Bijective (fun φ : Module.Dual K (MvPolynomial (Fin m) K ⧸ Ideal.span
          (Set.range g)) =>
      Algebra.TensorProduct.lid K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))
        (LinearMap.rTensor (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) φ
          (Algebra.TensorProduct.map
              (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
                  (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
            (Matrix.det (Matrix.of b)))))) :
    Function.Bijective (fun φ : Module.Dual R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) =>
      Algebra.TensorProduct.lid R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))
        (LinearMap.rTensor (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) φ
          (Algebra.TensorProduct.map
              (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
                  (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
            (Matrix.det (Matrix.of a))))) := by
  change Function.Bijective (theta f a)
  apply JacobianSquarePresentation.BijectiveBaseChange.solution
  intro 𝔪 _
  let := Ideal.Quotient.field 𝔪
  rw [← bijective_iff f a (R ⧸ 𝔪)]
  have : Module.Finite (R ⧸ 𝔪) (Q (fS f (R ⧸ 𝔪))) := finite_baseChange f (R ⧸ 𝔪)
  apply bijective_of_bijective_baseChange (AlgebraicClosure (R ⧸ 𝔪))
  rw [← bijective_iff (fS f (R ⧸ 𝔪)) (aS a (R ⧸ 𝔪)) (AlgebraicClosure (R ⧸ 𝔪))]
  have : Module.Finite (AlgebraicClosure (R ⧸ 𝔪))
      (Q (fS (fS f (R ⧸ 𝔪)) (AlgebraicClosure (R ⧸ 𝔪)))) := finite_baseChange _ _
  exact hfield (AlgebraicClosure (R ⧸ 𝔪)) (fS (fS f (R ⧸ 𝔪)) (AlgebraicClosure (R ⧸ 𝔪)))
    (aS (aS a (R ⧸ 𝔪)) (AlgebraicClosure (R ⧸ 𝔪)))
    (bezout_aS _ _ _ (bezout_aS f a (R ⧸ 𝔪) ha))
end JacobianSquarePresentation.BezoutianField

namespace JacobianSquarePresentation.BezoutianTmul

open scoped TensorProduct

section

private theorem adjugate_mulVec_mulVec {n : Type*} [Fintype n] [DecidableEq n] {S : Type*}
    [CommRing S] (A : Matrix n n S) (v : n → S) : A.adjugate.mulVec (A.mulVec v) = A.det • v := by
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply, Finset.sum_ite_eq, ite_mul]

private theorem map_det_mul_map_eq_zero {R P B : Type*} [CommRing R] [CommRing P] [Algebra R P]
    [Semiring B] [Algebra R B] (π : P ⊗[R] P →ₐ[R] B) {m : ℕ} (x f : Fin m → P)
    (a : Fin m → Fin m → P ⊗[R] P) (ha : ∀ i, f i ⊗ₜ[R] (1 : P) - (1 : P) ⊗ₜ[R] f i = ∑ j,
    a i j * (x j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] x j)) (hf : ∀ i, π (f i ⊗ₜ[R] (1 : P) - (1 : P) ⊗ₜ[R] f i) = 0)
    (j : Fin m) : π (Matrix.det (Matrix.of a)) * π (x j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] x j) = 0 := by
  classical
  have hmat : (Matrix.of a).mulVec (fun j => x j ⊗ₜ[R] (1 : P) - 1 ⊗ₜ[R] x j) =
      fun i => f i ⊗ₜ[R] 1 - 1 ⊗ₜ[R] f i := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    exact (ha i).symm
  have hcramer : Matrix.det (Matrix.of a) * (x j ⊗ₜ[R] (1 : P) - 1 ⊗ₜ[R] x j) =
      ∑ i, (Matrix.of a).adjugate j i * (f i ⊗ₜ[R] 1 - 1 ⊗ₜ[R] f i) := by
    have h := congrArg (fun v => v j) (adjugate_mulVec_mulVec (Matrix.of a)
        (fun j => x j ⊗ₜ[R] (1 : P) - 1 ⊗ₜ[R] x j))
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [← h, hmat]
    rfl
  rw [← map_mul, hcramer, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_mul, hf, mul_zero]

private theorem balanced_of_adjoin {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Δ : A ⊗[R] A) (S : Set A) (hS : Algebra.adjoin R S = ⊤)
    (hgen : ∀ x ∈ S, (x ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] x) * Δ)
        (s : A) :
    (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ := by
  have hs : s ∈ Algebra.adjoin R S := by rw [hS]; exact Algebra.mem_top
  induction hs using Algebra.adjoin_induction with
  | mem x hx => exact hgen x hx
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y _ _ hx hy =>
    rw [TensorProduct.add_tmul, TensorProduct.tmul_add, add_mul, add_mul, hx, hy]
  | mul x y _ _ hx hy =>
    have e1 : ((x * y) ⊗ₜ[R] (1 : A)) = (x ⊗ₜ[R] (1 : A)) * (y ⊗ₜ[R] (1 : A)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have e2 : ((1 : A) ⊗ₜ[R] (x * y)) = ((1 : A) ⊗ₜ[R] x) * ((1 : A) ⊗ₜ[R] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [e1, e2, mul_assoc, hy, ← mul_assoc, mul_comm (x ⊗ₜ[R] (1 : A)), mul_assoc, hx, ← mul_assoc,
      mul_comm ((1 : A) ⊗ₜ[R] y) ((1 : A) ⊗ₜ[R] x)]

end

private theorem solution
    (R : Type*) [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    (a : Fin m → Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : ∀ i, f i ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] f i =
      ∑ j, a i j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j))
    (s : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) :
    (s ⊗ₜ[R] (1 : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))) *
        Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
          (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Matrix.det (Matrix.of a)) =
      ((1 : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) ⊗ₜ[R] s) *
        Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
          (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Matrix.det (Matrix.of a)) := by
  classical
  refine balanced_of_adjoin _
    (Set.range fun j : Fin m => (Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.X j)))
    ?_ ?_ s
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hp : p ∈ Algebra.adjoin R (Set.range (MvPolynomial.X : Fin m → MvPolynomial (Fin m) R)) :=
        by
      rw [MvPolynomial.adjoin_range_X]; exact Algebra.mem_top
    have hrange : (Set.range fun j : Fin m => (Ideal.Quotient.mk (Ideal.span (Set.range f))
        (MvPolynomial.X j))) = (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) ''
        Set.range (MvPolynomial.X : Fin m →
            MvPolynomial (Fin m) R) := by
      ext y; simp [Ideal.Quotient.mkₐ_eq_mk]
    rw [hrange, ← AlgHom.map_adjoin]
    exact ⟨p, hp, rfl⟩
  · rintro _ ⟨j, rfl⟩
    have h := map_det_mul_map_eq_zero
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
          (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))))
      MvPolynomial.X f a ha (fun i => ?_) j
    · rw [map_sub, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul] at h
      simp only [map_one, Ideal.Quotient.mkₐ_eq_mk] at h ⊢
      linear_combination h
    · rw [map_sub, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      simp only [map_one, Ideal.Quotient.mkₐ_eq_mk]
      have hfi : Ideal.Quotient.mk (Ideal.span (Set.range f)) (f i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
      rw [hfi, TensorProduct.zero_tmul, TensorProduct.tmul_zero, sub_self]
end JacobianSquarePresentation.BezoutianTmul

namespace JacobianSquarePresentation.BezoutianAlgClosed

open scoped TensorProduct

universe u

private theorem _root_.JacobianSquarePresentation.lid_rTensor_comp_mulLeft
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    (Δ : A ⊗[R] A) (hbal : ∀ s : A, (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ)
    (φ : Module.Dual R A) (s : A) :
    Algebra.TensorProduct.lid R A (LinearMap.rTensor A (φ.comp (LinearMap.mulLeft R s)) Δ) =
      s * Algebra.TensorProduct.lid R A (LinearMap.rTensor A φ Δ) := by
  have h2 : ∀ z : A ⊗[R] A, LinearMap.rTensor A (LinearMap.mulLeft R s) z = (s ⊗ₜ[R] (1 : A)) *
      z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  have h3 : ∀ z : A ⊗[R] A, ((1 : A) ⊗ₜ[R] s) * z = LinearMap.lTensor A (LinearMap.mulLeft R s)
      z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  have h4 : ∀ w : R ⊗[R] A, Algebra.TensorProduct.lid R A
      (LinearMap.lTensor R (LinearMap.mulLeft R s) w) = s * Algebra.TensorProduct.lid R A w := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul r x => simp [Algebra.TensorProduct.lid_tmul]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  have h5 : LinearMap.rTensor A φ (LinearMap.lTensor A (LinearMap.mulLeft R s) Δ) =
      LinearMap.lTensor R (LinearMap.mulLeft R s) (LinearMap.rTensor A φ Δ) := by
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
        LinearMap.comp_apply]
  rw [LinearMap.rTensor_comp, LinearMap.comp_apply, h2, hbal, h3, h5, h4]

section

variable {K : Type u} [Field K]

section Frame
variable {A : Type u} [CommRing A] [Algebra K A] (Δ : A ⊗[K] A)

noncomputable def thetaₗ : Module.Dual K A →ₗ[K] A where
  toFun φ := Algebra.TensorProduct.lid K A (LinearMap.rTensor A φ Δ)
  map_add' φ ψ := by simp [LinearMap.rTensor_add]
  map_smul' c φ := by simp [LinearMap.rTensor_smul]

private theorem thetaₗ_apply (φ : Module.Dual K A) : thetaₗ (K := K) Δ φ =
    Algebra.TensorProduct.lid K A
    (LinearMap.rTensor A φ Δ) := rfl

private theorem apply_thetaₗ (ε : A →ₗ[K] K) (φ : Module.Dual K A) :
    ε (thetaₗ (K := K) Δ φ) = φ (Algebra.TensorProduct.rid K K A (LinearMap.lTensor A ε Δ)) := by
  rw [thetaₗ_apply]
  induction Δ using TensorProduct.inductionOn with
  | tmul x y => simp [Algebra.TensorProduct.lid_tmul, Algebra.TensorProduct.rid_tmul, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem thetaₗ_comp_mulLeft (hbal : ∀ s : A, (s ⊗ₜ[K] (1 : A)) * Δ = ((1 : A) ⊗ₜ[K] s) * Δ)
    (φ : Module.Dual K A) (s : A) : thetaₗ (K := K) Δ (φ.comp (LinearMap.mulLeft K s)) = s * thetaₗ
        (K := K) Δ φ :=
  lid_rTensor_comp_mulLeft K A Δ hbal φ s

private theorem bijective_thetaₗ_of_injective [FiniteDimensional K A]
    (hinj : Function.Injective (thetaₗ (K := K) Δ)) : Function.Bijective (thetaₗ (K := K) Δ) := by
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  exact Subspace.dual_finrank_eq

private theorem injective_thetaₗ_of_forall_factor
    (hbal : ∀ s : A, (s ⊗ₜ[K] (1 : A)) * Δ = ((1 : A) ⊗ₜ[K] s) * Δ)
    {ι : Type*} [Finite ι] (𝔫 : ι → Ideal A) (N : ℕ)
    (hcrt : Function.Bijective (RingHom.pi fun i => Ideal.Quotient.mk (𝔫 i ^ N)))
    (hloc : ∀ (i : ι) (χ : Module.Dual K A), (∀ x ∈ 𝔫 i ^ N, χ x = 0) → thetaₗ (K := K) Δ χ = 0 →
        χ = 0) :
    Function.Injective (thetaₗ (K := K) Δ) := by
  classical
  have := Fintype.ofFinite ι
  set π : A →+* ((i : ι) → A ⧸ 𝔫 i ^ N) := RingHom.pi fun i => Ideal.Quotient.mk (𝔫 i ^ N) with hπ
  have hsurj := hcrt.2
  choose e he using fun i => hsurj (Pi.single i 1)
  have hπe : ∀ i j, Ideal.Quotient.mk (𝔫 j ^ N) (e i) =
      Pi.single (M := fun j => A ⧸ 𝔫 j ^ N) i 1 j := fun i j => congrFun (he i) j
  have hsum : ∑ i, e i = 1 := by
    apply hcrt.1
    rw [map_sum, map_one]
    funext j
    simp only [Finset.sum_apply, Pi.one_apply, hπ, RingHom.pi_apply, hπe]
    rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)]
    simp
  have hekill : ∀ i, ∀ x ∈ 𝔫 i ^ N, e i * x = 0 := by
    intro i x hx
    apply hcrt.1
    rw [map_mul, map_zero, he]
    funext j
    simp only [Pi.mul_apply, Pi.zero_apply, hπ, RingHom.pi_apply]
    by_cases hij : j = i
    · subst hij; rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, mul_zero]
    · simp [hij]
  intro φ φ' hφφ'
  rw [← sub_eq_zero] at hφφ' ⊢
  rw [← map_sub] at hφφ'
  set χ := φ - φ' with hχ
  have hvan : ∀ i, ∀ x ∈ 𝔫 i ^ N, (χ.comp (LinearMap.mulLeft K (e i))) x = 0 := fun i x hx => by
    simp [hekill i x hx]
  have hψ0 : ∀ i, χ.comp (LinearMap.mulLeft K (e i)) = 0 := fun i =>
    hloc i _ (hvan i) (by rw [thetaₗ_comp_mulLeft Δ hbal, hφφ', mul_zero])
  have hdecomp : χ = ∑ i, χ.comp (LinearMap.mulLeft K (e i)) := by
    ext x
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [← map_sum, ← Finset.sum_mul, hsum, one_mul]
  rw [hdecomp]
  exact Finset.sum_eq_zero fun i _ => hψ0 i

end Frame

section Socle
variable {m : ℕ}

private theorem apply_mk_det_ne_zero (q : Matrix (Fin m) (Fin m) (MvPowerSeries (Fin m) K))
    (f : Fin m → MvPowerSeries (Fin m) K) (hf : ∀ i, f i = ∑ j, q i j * MvPowerSeries.X j)
    [Module.Finite K (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f))]
    (l : (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f)) →ₗ[K] K)
    (hl : Function.Bijective ((LinearMap.mul K (MvPowerSeries (Fin m) K ⧸ Ideal.span
        (Set.range f))).compr₂ l)) :
    l (Ideal.Quotient.mk (Ideal.span (Set.range f)) q.det) ≠ 0 := by
  classical
  obtain ⟨hs0, hsJ⟩ := JacobianSquarePresentation.QuotientDetMem.solution q f hf
  set s := Ideal.Quotient.mk (Ideal.span (Set.range f)) q.det with hs
  have hkill : ∀ φ : MvPowerSeries (Fin m) K, MvPowerSeries.constantCoeff φ = 0 →
      s * Ideal.Quotient.mk (Ideal.span (Set.range f)) φ = 0 := by
    intro φ hφ
    by_contra hne
    have hmem := hsJ (Ideal.span {s * Ideal.Quotient.mk (Ideal.span (Set.range f)) φ})
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
    rw [Ideal.mem_span_singleton'] at hmem
    obtain ⟨t, ht⟩ := hmem
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    have hu : IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range f)) (1 - t' * φ)) := by
      refine (MvPowerSeries.isUnit_iff_constantCoeff.mpr ?_).map _
      rw [map_sub, map_one, map_mul, hφ, mul_zero, sub_zero]
      exact isUnit_one
    apply hs0
    have h1 : s * Ideal.Quotient.mk (Ideal.span (Set.range f)) (1 - t' * φ) = 0 := by
      rw [map_sub, map_one, mul_sub, mul_one, map_mul, sub_eq_zero]
      calc s = Ideal.Quotient.mk _ t' * (s * Ideal.Quotient.mk _ φ) := ht.symm
        _ = s * (Ideal.Quotient.mk _ t' * Ideal.Quotient.mk _ φ) := by ring
    exact hu.mul_left_eq_zero.mp h1
  intro hl0
  apply hs0
  apply hl.1
  refine LinearMap.ext fun r => ?_
  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.mul_apply',
      zero_mul, map_zero]
  have hC : ∀ c : K, s * Ideal.Quotient.mk (Ideal.span (Set.range f))
      (MvPowerSeries.C c) = c • s := by
    intro c
    have h1 : (c • s : MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f)) =
        algebraMap K (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f)) c * s :=
            Algebra.smul_def c s
    rw [h1, mul_comm]
    change _ = Ideal.Quotient.mk _ (algebraMap K (MvPowerSeries (Fin m) K) c) * s
    congr 2
  have hsplit : s * Ideal.Quotient.mk (Ideal.span (Set.range f)) φ =
      MvPowerSeries.constantCoeff φ • s := by
    have hφ : φ = MvPowerSeries.C (MvPowerSeries.constantCoeff φ) +
        (φ - MvPowerSeries.C (MvPowerSeries.constantCoeff φ)) := by ring
    conv_lhs => rw [hφ]
    rw [map_add, mul_add, hC, hkill (φ - MvPowerSeries.C (MvPowerSeries.constantCoeff φ))
        (by simp), add_zero]
  rw [hsplit, map_smul, hl0, smul_zero]

end Socle

section Local
variable {m : ℕ} (g : Fin m → MvPolynomial (Fin m) K)
  (b : Fin m → Fin m → MvPolynomial (Fin m) K ⊗[K] MvPolynomial (Fin m) K)

local notation "P" => MvPolynomial (Fin m) K
local notation "A" => MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)

noncomputable def Δb : A ⊗[K] A :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
      (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
    (Matrix.det (Matrix.of b))

noncomputable def evR (ξ : Fin m → K) : MvPolynomial (Fin m) K ⊗[K] MvPolynomial (Fin m) K →ₐ[K]
    MvPolynomial (Fin m) K :=
  (Algebra.TensorProduct.lmul' (S := MvPolynomial (Fin m) K) K).comp
    (Algebra.TensorProduct.map (AlgHom.id K (MvPolynomial (Fin m) K))
      (MvPolynomial.aeval fun j => MvPolynomial.C (ξ j)))

noncomputable def bAt (ξ : Fin m → K) (i j : Fin m) : MvPolynomial (Fin m) K := evR ξ (b i j)

noncomputable def transl (ξ : Fin m → K) : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K :=
  MvPolynomial.aeval fun j => MvPolynomial.X j + MvPolynomial.C (ξ j)

omit g b in
theorem transl_comp_transl_neg (ξ : Fin m → K) : (transl (K := K) ξ).comp (transl (-ξ)) =
    AlgHom.id K P := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [transl]

noncomputable def translEquiv (ξ : Fin m → K) : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m)
    K :=
  AlgEquiv.ofAlgHom (transl ξ) (transl (-ξ)) (transl_comp_transl_neg ξ)
    (by simpa using transl_comp_transl_neg (K := K) (-ξ))

omit g b in
private theorem aeval_C_comp (ξ : Fin m → K) (p : P) :
    MvPolynomial.aeval (fun j => (MvPolynomial.C (ξ j) : P)) p = (MvPolynomial.C
        (MvPolynomial.aeval ξ p) : P) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, MvPolynomial.aeval_X]

omit g b in
private theorem evR_tmul (ξ : Fin m → K) (p p' : P) :
    evR ξ (p ⊗ₜ[K] p') = p * MvPolynomial.C (MvPolynomial.aeval ξ p') := by
  change Algebra.TensorProduct.lmul' (S := P) K (Algebra.TensorProduct.map (AlgHom.id K P)
    (MvPolynomial.aeval fun j => (MvPolynomial.C (ξ j) : P)) (p ⊗ₜ[K] p')) = _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.id_apply,
      aeval_C_comp]

private theorem g_sub_C_eq_sum_bAt
    (hb : ∀ i, g i ⊗ₜ[K] (1 : MvPolynomial (Fin m) K) - (1 : MvPolynomial (Fin m) K) ⊗ₜ[K] g i =
      ∑ j, b i j * (MvPolynomial.X j ⊗ₜ[K] 1 - 1 ⊗ₜ[K] MvPolynomial.X j))
    (ξ : Fin m → K) (i : Fin m) :
    g i - MvPolynomial.C (MvPolynomial.aeval ξ (g i)) =
      ∑ j, bAt b ξ i j * (MvPolynomial.X j - MvPolynomial.C (ξ j)) := by
  have := congrArg (evR ξ) (hb i)
  simpa [map_sub, map_sum, map_mul, evR_tmul, bAt] using this

private theorem exists_point_of_isMaximal [IsAlgClosed K] (𝔫 : Ideal A) [𝔫.IsMaximal] :
    ∃ ξ : Fin m → K, ∀ p : P,
      Ideal.Quotient.mk (Ideal.span (Set.range g)) p ∈ 𝔫 ↔ MvPolynomial.aeval ξ p = 0 := by
  have hmax : (𝔫.comap (Ideal.Quotient.mk (Ideal.span (Set.range g)))).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨ξ, hξ⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hmax
  refine ⟨ξ, fun p => ?_⟩
  rw [← MvPolynomial.mem_vanishingIdeal_singleton_iff, ← hξ, Ideal.mem_comap]

set_option synthInstance.maxHeartbeats 800000 in
-- Instance search through these linear-equivalence coercions is slow.

private theorem eval_thetaₗ_Δb (ξ : Fin m → K) (hI : ∀ a ∈ Ideal.span (Set.range g),
    MvPolynomial.aeval ξ a = 0)
    (φ : Module.Dual K A) :
    Ideal.Quotient.liftₐ (Ideal.span (Set.range g)) (MvPolynomial.aeval ξ)
        hI (thetaₗ (K := K) (Δb g b) φ) =
      φ (Ideal.Quotient.mk (Ideal.span (Set.range g)) (Matrix.det (Matrix.of (bAt b ξ)))) := by
  classical
  set ε := Ideal.Quotient.liftₐ (Ideal.span (Set.range g)) (MvPolynomial.aeval ξ) hI with hεdef
  have hε : ∀ p, ε (Ideal.Quotient.mk _ p) = MvPolynomial.aeval ξ p := fun _ => rfl
  have key : ∀ z : P ⊗[K] P, Algebra.TensorProduct.rid K K A
      (LinearMap.lTensor A ε.toLinearMap (Algebra.TensorProduct.map
      (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
        (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g))) z)) =
      Ideal.Quotient.mk (Ideal.span (Set.range g)) (evR ξ z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul p p' =>
      rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul, Algebra.TensorProduct.rid_tmul,
          evR_tmul, map_mul,
        AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, hε, Algebra.smul_def, mul_comm]
      congr 1
    | add x y hx hy => simp only [map_add, hx, hy]
  have h := apply_thetaₗ (K := K) (Δb g b) ε.toLinearMap φ
  rw [AlgHom.toLinearMap_apply] at h
  rw [h]
  congr 1
  show _ = _
  rw [Δb, key, AlgHom.map_det]
  congr 2

variable [Module.Finite K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))]
  (hb : ∀ i, g i ⊗ₜ[K] (1 : MvPolynomial (Fin m) K) - (1 : MvPolynomial (Fin m) K) ⊗ₜ[K] g i =
    ∑ j, b i j * (MvPolynomial.X j ⊗ₜ[K] 1 - 1 ⊗ₜ[K] MvPolynomial.X j))

include hb

private theorem exists_local_model (ξ : Fin m → K) (𝔫 : Ideal A) [𝔫.IsMaximal]
    (h𝔫 : ∀ p : P, Ideal.Quotient.mk (Ideal.span (Set.range g)) p ∈ 𝔫 ↔ MvPolynomial.aeval ξ p = 0)
    (N : ℕ) (hN : (Ideal.jacobson (⊥ : Ideal A)) ^ N = ⊥) :
    ∃ (q : Matrix (Fin m) (Fin m) (MvPowerSeries (Fin m) K)) (f : Fin m → MvPowerSeries (Fin m) K)
      (_ : ∀ i, f i = ∑ j, q i j * MvPowerSeries.X j)
      (_ : Module.Finite K (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f)))
      (Φ : (A ⧸ 𝔫 ^ N) ≃ₐ[K] (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f))),
      Φ (Ideal.Quotient.mk (𝔫 ^ N) (Ideal.Quotient.mk (Ideal.span (Set.range g)) (Matrix.det
          (Matrix.of (bAt b ξ))))) =
        Ideal.Quotient.mk (Ideal.span (Set.range f)) (Matrix.det q) := by
  classical
  have hξ : ∀ i, MvPolynomial.aeval ξ (g i) = 0 := fun i =>
    (h𝔫 (g i)).mp (by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))]
      exact Ideal.zero_mem _)
  let σ : P ≃ₐ[K] P := translEquiv ξ
  have hσ : ∀ p, σ p = transl ξ p := fun _ => rfl
  have hσX : ∀ j, σ (MvPolynomial.X j - MvPolynomial.C (ξ j)) = MvPolynomial.X j := by
    intro j; simp [hσ, transl]
  let g' : Fin m → P := fun i => σ (g i)
  let f : Fin m → MvPowerSeries (Fin m) K := fun i => (g' i : MvPowerSeries (Fin m) K)
  let q : Matrix (Fin m) (Fin m) (MvPowerSeries (Fin m) K) :=
      fun i j => ((σ (bAt b ξ i j) : P) : MvPowerSeries (Fin m) K)
  have hgb : ∀ i, g i = ∑ j, bAt b ξ i j * (MvPolynomial.X j - MvPolynomial.C (ξ j)) := by
    intro i
    have := g_sub_C_eq_sum_bAt g b hb ξ i
    rwa [hξ i, map_zero, sub_zero] at this
  have hg' : ∀ i, g' i = ∑ j, σ (bAt b ξ i j) * MvPolynomial.X j := by
    intro i
    change σ (g i) = _
    conv_lhs => rw [hgb i]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hσX]
  have hcoe : ∀ p : P, (p : MvPowerSeries (Fin m) K) = MvPolynomial.coeToMvPowerSeries.ringHom p :=
      fun _ => rfl
  have hf : ∀ i, f i = ∑ j, q i j * MvPowerSeries.X j := by
    intro i
    change ((g' i : P) : MvPowerSeries (Fin m) K) = _
    rw [hg' i, hcoe, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← hcoe, ← hcoe, MvPolynomial.coe_X]
  have hIJ : Ideal.span (Set.range g') = Ideal.map (σ : P →+* P) (Ideal.span (Set.range g)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  let τ : A ≃ₐ[K] (P ⧸ Ideal.span (Set.range g')) := Ideal.quotientEquivAlg _ _ σ hIJ
  have hτ : ∀ p, τ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (σ p) := fun _ => rfl
  let 𝔫' : Ideal (P ⧸ Ideal.span (Set.range g')) := Ideal.map
      (τ : A →+* (P ⧸ Ideal.span (Set.range g'))) 𝔫
  have h𝔫'max : 𝔫'.IsMaximal := Ideal.IsMaximal.map_bijective _
      (by exact τ.bijective) inferInstance
  have h𝔫'X : ∀ j, Ideal.Quotient.mk (Ideal.span (Set.range g')) (MvPolynomial.X j) ∈ 𝔫' := by
    intro j
    have h1 : Ideal.Quotient.mk (Ideal.span (Set.range g))
        (MvPolynomial.X j - MvPolynomial.C (ξ j)) ∈ 𝔫 :=
      (h𝔫 _).mpr (by simp)
    have h2 : τ (Ideal.Quotient.mk (Ideal.span (Set.range g))
        (MvPolynomial.X j - MvPolynomial.C (ξ j))) ∈ 𝔫' :=
      Ideal.mem_map_of_mem (τ : A →+* (P ⧸ Ideal.span (Set.range g'))) h1
    rwa [hτ, hσX] at h2
  let τN : (A ⧸ 𝔫 ^ N) ≃ₐ[K] ((P ⧸ Ideal.span (Set.range g')) ⧸ 𝔫' ^ N) :=
    Ideal.quotientEquivAlg (𝔫 ^ N) (𝔫' ^ N) τ (by rw [Ideal.map_pow])
  have hτN : ∀ a, τN (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (τ a) := fun _ => rfl
  have : Module.Finite K (P ⧸ Ideal.span (Set.range g')) := Module.Finite.equiv τ.toLinearEquiv
  have : IsArtinianRing (P ⧸ Ideal.span (Set.range g')) := IsArtinianRing.of_finite K _
  have hN' : (Ideal.jacobson (⊥ : Ideal (P ⧸ Ideal.span (Set.range g')))) ^ N = ⊥ := by
    have hsurj : Function.Surjective (τ : A →+* (P ⧸ Ideal.span (Set.range g'))) := τ.surjective
    have hker : RingHom.ker (τ : A →+* (P ⧸ Ideal.span (Set.range g'))) ≤ ⊥ :=
      ((RingHom.injective_iff_ker_eq_bot _).mp τ.injective).le
    have hj := Ideal.map_jacobson_of_surjective hsurj hker
    rw [Ideal.map_bot] at hj
    rw [← hj, ← Ideal.map_pow, hN, Ideal.map_bot]
  obtain ⟨e₁⟩ := JacobianSquarePresentation.ArtinianQuotientPow.solution _ 𝔫' N hN'
  have : Module.Finite K (Localization.AtPrime 𝔫') := Module.Finite.equiv
      (e₁.restrictScalars K).toLinearEquiv
  obtain ⟨e₂, he₂⟩ :=
    MvPolynomial.exists_algEquiv_localization_atPrime_mvPowerSeries_quotient_apply_mk K g' 𝔫' h𝔫'X
  have hfin : Module.Finite K (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f)) :=
    Module.Finite.equiv e₂.toLinearEquiv
  let Φ : (A ⧸ 𝔫 ^ N) ≃ₐ[K] (MvPowerSeries (Fin m) K ⧸ Ideal.span (Set.range f)) :=
    (τN.trans (e₁.restrictScalars K)).trans e₂
  have hdet : ((σ (Matrix.det (Matrix.of (bAt b ξ))) : P) : MvPowerSeries (Fin m) K) =
      Matrix.det q := by
    let ρ : P →+* MvPowerSeries (Fin m) K := MvPolynomial.coeToMvPowerSeries.ringHom.comp
        (σ : P →+* P)
    have hρ : ∀ p, ((σ p : P) : MvPowerSeries (Fin m) K) = ρ p := fun _ => rfl
    rw [hρ, RingHom.map_det]
    congr 1
  refine ⟨q, f, hf, hfin, Φ, ?_⟩
  have he₁ : ∀ x, e₁ (Ideal.Quotient.mk (𝔫' ^ N) x) = algebraMap _ (Localization.AtPrime 𝔫') x :=
    fun x => e₁.commutes x
  calc Φ (Ideal.Quotient.mk (𝔫 ^ N) (Ideal.Quotient.mk (Ideal.span (Set.range g))
      (Matrix.det (Matrix.of (bAt b ξ))))) = e₂ (e₁.restrictScalars K (τN (Ideal.Quotient.mk (𝔫 ^ N)
          (Ideal.Quotient.mk (Ideal.span (Set.range g)) (Matrix.det (Matrix.of (bAt b ξ))))))) :=
              rfl
    _ = e₂ (algebraMap _ (Localization.AtPrime 𝔫')
          (Ideal.Quotient.mk (Ideal.span (Set.range g'))
              (σ (Matrix.det (Matrix.of (bAt b ξ)))))) := by
        rw [AlgEquiv.restrictScalars_apply, hτN, hτ, he₁]
    _ = Ideal.Quotient.mk (Ideal.span (Set.range f)) (Matrix.det q) := by
        rw [he₂, hdet]

private theorem exists_frobenius_form_factor (ξ : Fin m → K) (𝔫 : Ideal A) [𝔫.IsMaximal]
    (h𝔫 : ∀ p : P, Ideal.Quotient.mk (Ideal.span (Set.range g)) p ∈ 𝔫 ↔ MvPolynomial.aeval ξ p = 0)
    (N : ℕ) (hN : (Ideal.jacobson (⊥ : Ideal A)) ^ N = ⊥) :
    ∃ lam : Module.Dual K (A ⧸ 𝔫 ^ N),
      (∀ ψ : Module.Dual K (A ⧸ 𝔫 ^ N), ∃ c : A ⧸ 𝔫 ^ N, ψ = lam.comp (LinearMap.mulLeft K c)) ∧
      (∀ c : A ⧸ 𝔫 ^ N, lam.comp (LinearMap.mulLeft K c) = 0 → c = 0) ∧
      lam (Ideal.Quotient.mk (𝔫 ^ N)
        (Ideal.Quotient.mk (Ideal.span (Set.range g)) (Matrix.det (Matrix.of (bAt b ξ))))) ≠ 0 := by
  classical
  obtain ⟨q, f, hf, hfin, Φ, hΦ⟩ := exists_local_model g b hb ξ 𝔫 h𝔫 N hN
  have := hfin
  obtain ⟨l, hl⟩ := JacobianSquarePresentation.BijectiveCompr2.solution q f hf
  have hls := apply_mk_det_ne_zero (K := K) q f hf l hl
  refine ⟨l.comp Φ.toLinearEquiv.toLinearMap, ?_, ?_, ?_⟩
  · intro ψ
    obtain ⟨x, hx⟩ := hl.2 (ψ.comp Φ.symm.toLinearEquiv.toLinearMap)
    refine ⟨Φ.symm x, LinearMap.ext fun y => ?_⟩
    have := LinearMap.congr_fun hx (Φ y)
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.comp_apply,
        LinearEquiv.coe_coe,
      AlgEquiv.toLinearEquiv_apply, AlgEquiv.symm_apply_apply] at this
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearEquiv.coe_coe,
        AlgEquiv.toLinearEquiv_apply,
      map_mul, AlgEquiv.apply_symm_apply]
    exact this.symm
  · intro c hc
    have h0 : (LinearMap.mul K _).compr₂ l (Φ c) = (LinearMap.mul K _).compr₂ l 0 := by
      refine LinearMap.ext fun y => ?_
      have := LinearMap.congr_fun hc (Φ.symm y)
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearEquiv.coe_coe,
          AlgEquiv.toLinearEquiv_apply,
        map_mul, AlgEquiv.apply_symm_apply, LinearMap.zero_apply] at this
      simpa [LinearMap.compr₂_apply, LinearMap.mul_apply'] using this
    simpa using hl.1 h0
  · simpa [hΦ] using hls

private theorem functional_eq_zero_of_forall_mem_pow (ξ : Fin m → K) (𝔫 : Ideal A) [𝔫.IsMaximal]
    (h𝔫 : ∀ p : P, Ideal.Quotient.mk (Ideal.span (Set.range g)) p ∈ 𝔫 ↔ MvPolynomial.aeval ξ p = 0)
    (N : ℕ) (hN : (Ideal.jacobson (⊥ : Ideal A)) ^ N = ⊥) (χ : Module.Dual K A)
    (hχ : ∀ x ∈ 𝔫 ^ N, χ x = 0) (hθ : thetaₗ (K := K) (Δb g b) χ = 0) : χ =
        0 := by
  classical
  obtain ⟨lam, h1, h2, h3⟩ := exists_frobenius_form_factor g b hb ξ 𝔫 h𝔫 N hN
  have hbal : ∀ s : A, (s ⊗ₜ[K] (1 : A)) * Δb g b = ((1 : A) ⊗ₜ[K] s) * Δb g b :=
    fun s => JacobianSquarePresentation.BezoutianTmul.solution K g b hb s
  have hle : (𝔫 ^ N).restrictScalars K ≤ LinearMap.ker χ :=
      fun x hx => LinearMap.mem_ker.mpr (hχ x hx)
  let ψ : Module.Dual K (A ⧸ 𝔫 ^ N) :=
    (((𝔫 ^ N).restrictScalars K).liftQ χ hle).comp (Submodule.Quotient.restrictScalarsEquiv K
        (𝔫 ^ N)).symm.toLinearMap
  have hψ : ∀ x, ψ (Ideal.Quotient.mk (𝔫 ^ N) x) = χ x := fun x => rfl
  obtain ⟨c, hc⟩ := h1 ψ
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  set y := thetaₗ (K := K) (Δb g b) (lam.comp (Ideal.Quotient.mkₐ K (𝔫 ^ N)).toLinearMap) with hy
  have hχ' : χ = (lam.comp (Ideal.Quotient.mkₐ K (𝔫 ^ N)).toLinearMap).comp
      (LinearMap.mulLeft K c') := by
    refine LinearMap.ext fun x => ?_
    rw [← hψ x, hc]
    simp [map_mul]
  have hθ' : c' * y = 0 := by rw [hy, ← thetaₗ_comp_mulLeft _ hbal, ← hχ', hθ]
  have hI : ∀ a ∈ Ideal.span (Set.range g), MvPolynomial.aeval ξ a = 0 := fun a ha =>
    (h𝔫 a).mp (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact Ideal.zero_mem _)
  have hεy := eval_thetaₗ_Δb g b ξ hI (lam.comp (Ideal.Quotient.mkₐ K (𝔫 ^ N)).toLinearMap)
  rw [← hy] at hεy
  have hy𝔫 : y ∉ 𝔫 := by
    intro hmem
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective y
    have hp0 : MvPolynomial.aeval ξ p = 0 := (h𝔫 p).mp (hp ▸ hmem)
    apply h3
    have : Ideal.Quotient.liftₐ (Ideal.span (Set.range g)) (MvPolynomial.aeval ξ) hI y = 0 := by
      rw [← hp]; exact hp0
    rw [this] at hεy
    exact hεy.symm
  obtain ⟨z, w, hw, hzw⟩ := Ideal.IsMaximal.exists_inv ‹𝔫.IsMaximal› hy𝔫
  have hcw : ∀ k : ℕ, c' = c' * w ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc c' = c' * 1 * w ^ k := by rw [mul_one]; exact ih
        _ = c' * (z * y + w) * w ^ k := by rw [hzw]
        _ = (z * (c' * y) + c' * w) * w ^ k := by ring
        _ = c' * w ^ (k + 1) := by rw [hθ', mul_zero, zero_add, mul_assoc, ← pow_succ']
  have hc'mem : c' ∈ 𝔫 ^ N := by
    rw [hcw N]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hw N)
  rw [hχ']
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply,
      LinearMap.zero_apply]
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mul_mem_right x _ hc'mem), map_zero]

omit g b hb in
private theorem iInf_le_prod_of_pairwise_isCoprime' {R : Type*} [CommRing R] {ι : Type*}
    [Fintype ι] (I : ι → Ideal R) (h : Pairwise (Function.onFun IsCoprime I)) :
    ⨅ i, I i ≤ ∏ i, I i := by
  classical
  suffices hs : ∀ s : Finset ι, ⨅ i, I i ≤ ∏ i ∈ s, I i from hs Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    have hcop : IsCoprime (I j) (∏ i ∈ s, I i) :=
      IsCoprime.prod_right fun i hi => h (fun heq => hj (heq ▸ hi))
    rw [Ideal.mul_eq_inf_of_isCoprime hcop]
    exact le_inf (iInf_le _ j) ih

omit g b hb in
private theorem crt_bijective {R : Type*} [CommRing R] {ι : Type*} [Finite ι] (I : ι → Ideal R)
    (hcop : Pairwise (Function.onFun IsCoprime I)) (hinf : ⨅ i, I i = ⊥) :
    Function.Bijective (RingHom.pi fun i => Ideal.Quotient.mk (I i)) := by
  let e := Ideal.quotientInfRingEquivPiQuotient I hcop
  have hmk : Function.Bijective (Ideal.Quotient.mk (⨅ i, I i)) :=
    ⟨(injective_iff_map_eq_zero _).mpr fun a ha => by
        rwa [Ideal.Quotient.eq_zero_iff_mem, hinf, Ideal.mem_bot] at ha,
      Ideal.Quotient.mk_surjective⟩
  have hcomp : ⇑(RingHom.pi fun i => Ideal.Quotient.mk (I i)) = e ∘ Ideal.Quotient.mk _ := by
    funext x
    exact (Ideal.quotientInfToPiQuotient_mk I x).symm
  rw [hcomp]
  exact e.bijective.comp hmk

private theorem bijective_thetaₗ_Δb [IsAlgClosed K] : Function.Bijective
    (thetaₗ (K := K) (Δb g b)) := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite K _
  obtain ⟨N, hN0⟩ := IsArtinianRing.isNilpotent_jacobson A
  have hN : (Ideal.jacobson (⊥ : Ideal A)) ^ N = ⊥ := by
    rw [Ideal.jacobson_bot]
    exact hN0.trans Submodule.zero_eq_bot
  have hfinι : Finite ↥{I : Ideal A | I.IsMaximal} := (IsArtinianRing.setOfPred_isMaximal_finite
      _).to_subtype
  have := Fintype.ofFinite ↥{I : Ideal A | I.IsMaximal}
  have hbal : ∀ s : A, (s ⊗ₜ[K] (1 : A)) * Δb g b = ((1 : A) ⊗ₜ[K] s) * Δb g b :=
    fun s => JacobianSquarePresentation.BezoutianTmul.solution K g b hb s
  have hcop : Pairwise (Function.onFun IsCoprime fun i :
      ↥{I : Ideal A | I.IsMaximal} => i.1 ^ N) := by
    intro i j hij
    have : (i.1).IsMaximal := i.2
    have : (j.1).IsMaximal := j.2
    exact (Ideal.isCoprime_of_isMaximal (fun h => hij (Subtype.ext h))).pow
  have hinf : (⨅ i : ↥{I : Ideal A | I.IsMaximal}, i.1 ^ N) = ⊥ := by
    refine le_bot_iff.mp ((iInf_le_prod_of_pairwise_isCoprime' _ hcop).trans ?_)
    rw [Finset.prod_pow, ← hN]
    refine Ideal.pow_right_mono ?_ N
    refine Ideal.prod_le_inf.trans ?_
    rw [Ideal.jacobson]
    exact le_sInf fun J hJ => Finset.inf_le (Finset.mem_univ (⟨J,
        hJ.2⟩ : ↥{I : Ideal A | I.IsMaximal}))
  have hcrt := crt_bijective (fun i : ↥{I : Ideal A | I.IsMaximal} => i.1 ^ N) hcop hinf
  refine bijective_thetaₗ_of_injective _ (injective_thetaₗ_of_forall_factor (K := K) (Δb g b) hbal
    (ι := ↥{I : Ideal A | I.IsMaximal}) (fun i => i.1) N hcrt ?_)
  rintro ⟨𝔫, h𝔫max⟩ χ hχ hθ
  have : 𝔫.IsMaximal := h𝔫max
  obtain ⟨ξ, hξ⟩ := exists_point_of_isMaximal g 𝔫
  exact functional_eq_zero_of_forall_mem_pow g b hb ξ 𝔫 hξ N hN χ hχ hθ

end Local

end

private theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] {m : ℕ} (g : Fin m → MvPolynomial (Fin m) K)
    [Module.Finite K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))]
    (b : Fin m → Fin m → MvPolynomial (Fin m) K ⊗[K] MvPolynomial (Fin m) K)
    (hb : ∀ i, g i ⊗ₜ[K] (1 : MvPolynomial (Fin m) K) - (1 : MvPolynomial (Fin m) K) ⊗ₜ[K] g i =
      ∑ j, b i j * (MvPolynomial.X j ⊗ₜ[K] 1 - 1 ⊗ₜ[K] MvPolynomial.X j)) :
    Function.Bijective (fun φ : Module.Dual K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) =>
      TensorProduct.lid K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))
        (LinearMap.rTensor (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) φ
          (Algebra.TensorProduct.map
              (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
                  (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
            (Matrix.det (Matrix.of b))))) := by
  have key := bijective_thetaₗ_Δb g b hb
  have hfun : (fun φ : Module.Dual K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) =>
      TensorProduct.lid K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))
        (LinearMap.rTensor (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) φ
          (Algebra.TensorProduct.map
              (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
                  (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
            (Matrix.det (Matrix.of b))))) = ⇑(thetaₗ (K := K) (Δb g b)) := by
    funext φ
    rfl
  rw [hfun]
  exact key
end JacobianSquarePresentation.BezoutianAlgClosed

namespace JacobianSquarePresentation.BezoutianSquare

open scoped TensorProduct

private theorem solution
    (R : Type*) [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    [Module.Finite R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))]
    [Module.Free R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))]
    (a : Fin m → Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : ∀ i, f i ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] f i =
      ∑ j, a i j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) :
    Function.Bijective (fun φ : Module.Dual R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) =>
      TensorProduct.lid R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))
        (LinearMap.rTensor (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) φ
          (Algebra.TensorProduct.map
              (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
                  (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
            (Matrix.det (Matrix.of a))))) := by
  exact JacobianSquarePresentation.BezoutianField.solution R f a ha
    (fun K _ _ g _ b hb => JacobianSquarePresentation.BezoutianAlgClosed.solution K g b hb)
end JacobianSquarePresentation.BezoutianSquare

namespace JacobianSquarePresentation.TmulSubSum

open scoped TensorProduct

section

open scoped TensorProduct
open MvPolynomial

private theorem main (R : Type*) [CommRing R] {m : ℕ} (g : MvPolynomial (Fin m) R) :
    ∃ a : Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R,
      g ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] g =
        ∑ j, a j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j) := by
  classical
  induction g using MvPolynomial.induction_on with
  | C r =>
    refine ⟨0, ?_⟩
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    rw [sub_eq_zero, MvPolynomial.C_eq_smul_one, TensorProduct.smul_tmul]
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b, ?_⟩
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ← ha, ← hb, TensorProduct.add_tmul,
      TensorProduct.tmul_add]
    abel
  | mul_X p n hp =>
    obtain ⟨a, ha⟩ := hp
    refine ⟨fun k => a k * (X n ⊗ₜ[R] 1) + if k = n then (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] p else
        0, ?_⟩
    have key : (p * X n) ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R]
        (p * X n) = (p ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] p) *
        (X n ⊗ₜ[R]
            1) +
          ((1 : MvPolynomial (Fin m) R) ⊗ₜ[R] p) * (X n ⊗ₜ[R] 1 - 1 ⊗ₜ[R] X n) := by
      simp only [sub_mul, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      abel
    rw [key, ha, Finset.sum_mul]
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      ring
    · simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end

private theorem solution
    (R : Type*) [CommRing R] {m : ℕ} (g : MvPolynomial (Fin m) R) :
    ∃ a : Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R,
      g ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] g =
        ∑ j, a j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j) :=
  main R g
end JacobianSquarePresentation.TmulSubSum

namespace JacobianSquarePresentation.LmulPderiv

open scoped TensorProduct

section

open scoped TensorProduct
open MvPolynomial

variable (R : Type*) [CommRing R] {m : ℕ}

noncomputable def contract (j : Fin m) :
    MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R →ₗ[R] MvPolynomial (Fin m) R :=
  LinearMap.mul' R (MvPolynomial (Fin m) R) ∘ₗ
    TensorProduct.map LinearMap.id
      ((pderiv j : Derivation R (MvPolynomial (Fin m) R) (MvPolynomial (Fin m) R)) :
        MvPolynomial (Fin m) R →ₗ[R] MvPolynomial (Fin m) R)

private theorem contract_tmul (j : Fin m) (u v : MvPolynomial (Fin m) R) :
    contract R j (u ⊗ₜ[R] v) = u * pderiv j v := by
  simp only [contract, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.mul'_apply, Derivation.coeFn_coe]

private theorem contract_mul_X_sub (j k : Fin m) (w : MvPolynomial (Fin m) R ⊗[R] MvPolynomial
    (Fin m) R) : contract R j (w * (X k ⊗ₜ[R] 1 - 1 ⊗ₜ[R] X k)) =
      -(if k = j then Algebra.TensorProduct.lmul' R w else 0) := by
  classical
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
    rw [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        mul_one,
      map_sub, contract_tmul, contract_tmul, Algebra.TensorProduct.lmul'_apply_tmul, pderiv_mul,
          pderiv_X]
    by_cases hkj : k = j
    · subst hkj
      simp only [Pi.single_eq_same, ite_true]
      ring
    · have : (Pi.single j (1 : MvPolynomial (Fin m) R) : Fin m → MvPolynomial (Fin m) R) k = 0 :=
        Pi.single_eq_of_ne hkj _
      simp only [this, ite_eq_right hkj, mul_zero, add_zero, neg_zero]
      ring
  | add x y hx hy =>
    rw [add_mul, map_add, hx, hy, map_add]
    split_ifs <;> ring

private theorem main (g : MvPolynomial (Fin m) R)
    (a : Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : g ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] g =
        ∑ j, a j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) (j : Fin m) :
    Algebra.TensorProduct.lmul' R (a j) = MvPolynomial.pderiv j g := by
  classical
  have h := congrArg (contract R j) ha
  rw [map_sub, contract_tmul, contract_tmul, pderiv_one, mul_zero, zero_sub, one_mul, map_sum] at h
  simp only [contract_mul_X_sub, Finset.sum_neg_distrib, neg_inj] at h
  rw [Finset.sum_ite_eq' Finset.univ j, ite_eq_left (Finset.mem_univ j)] at h
  exact h.symm

end

private theorem solution
    (R : Type*) [CommRing R] {m : ℕ} (g : MvPolynomial (Fin m) R)
    (a : Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : g ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] g =
        ∑ j, a j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) (j : Fin m) :
    Algebra.TensorProduct.lmul' R (a j) = MvPolynomial.pderiv j g :=
  main R g a ha j
end JacobianSquarePresentation.LmulPderiv

namespace JacobianSquarePresentation.LmulBezoutian

open scoped TensorProduct

private theorem solution
    (R : Type*) [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    (a : Fin m → Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : ∀ i, f i ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] f i =
      ∑ j, a i j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) :
    Algebra.TensorProduct.lmul' R
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
          (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Matrix.det (Matrix.of a))) =
      Ideal.Quotient.mk (Ideal.span (Set.range f)) (Matrix.det (Matrix.of fun i j =>
          MvPolynomial.pderiv j (f i))) := by
  classical
  have hcomm : (Algebra.TensorProduct.lmul' (S := MvPolynomial (Fin m) R ⧸ Ideal.span
      (Set.range f)) R).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
            (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))) =
      (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))).comp (Algebra.TensorProduct.lmul' (S :=
          MvPolynomial (Fin m) R) R) := by
    ext x
    · simp
    · simp
  have h := DFunLike.congr_fun hcomm (Matrix.det (Matrix.of a))
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h
  rw [h, Ideal.Quotient.mkₐ_eq_mk]
  congr 1
  rw [show Algebra.TensorProduct.lmul' (S := MvPolynomial (Fin m) R) R (Matrix.det (Matrix.of a)) =
      ((Algebra.TensorProduct.lmul' (S := MvPolynomial (Fin m) R) R : MvPolynomial (Fin m) R ⊗[R]
          MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R) : MvPolynomial (Fin m) R ⊗[R]
          MvPolynomial (Fin m) R →+* MvPolynomial (Fin m) R) (Matrix.det (Matrix.of a)) from rfl,
    RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  exact JacobianSquarePresentation.LmulPderiv.solution R (f i) (a i) (ha i) j
end JacobianSquarePresentation.LmulBezoutian

namespace JacobianSquarePresentation.TraceDualLmul

open scoped TensorProduct

section

open Module
open scoped TensorProduct

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]

private theorem lid_rTensor_sum (φ : Dual R A) (S : Finset (A × A)) :
    TensorProduct.lid R A (LinearMap.rTensor A φ (∑ p ∈ S, p.1 ⊗ₜ[R] p.2)) = ∑ p ∈ S,
        φ p.1 • p.2 := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

private theorem main [Module.Finite R A] [Module.Free R A]
    (τ : Dual R A) (Δ : A ⊗[R] A)
    (hbal : ∀ s : A, (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ)
    (hτ : TensorProduct.lid R A (LinearMap.rTensor A τ Δ) = 1) (x : A) :
    Algebra.trace R A x = τ (LinearMap.mul' R A Δ * x) := by
  classical
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset Δ
  have hone : ∑ p ∈ S, τ p.1 • p.2 = 1 := by rw [← lid_rTensor_sum R A τ S, ← hS, hτ]
  have key : ∀ a : A, ∑ p ∈ S, τ (a * p.1) • p.2 = a := by
    intro a
    have hl : (a ⊗ₜ[R] (1 : A)) * Δ = ∑ p ∈ S, (a * p.1) ⊗ₜ[R] p.2 := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hr : ((1 : A) ⊗ₜ[R] a) * Δ = ∑ p ∈ S, p.1 ⊗ₜ[R] (a * p.2) := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h := congrArg (fun z => TensorProduct.lid R A (LinearMap.rTensor A τ z)) (hbal a)
    simp only [hl, hr, map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h
    rw [h]
    calc ∑ p ∈ S, τ p.1 • (a * p.2) = a * ∑ p ∈ S, τ p.1 • p.2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [mul_smul_comm]
      _ = a := by rw [hone, mul_one]
  have hlmul : Algebra.lmul R A x =
      dualTensorHom R A A (∑ p ∈ S, (τ.comp (LinearMap.mulLeft R (x * p.1))) ⊗ₜ[R] p.2) := by
    apply LinearMap.ext
    intro m
    rw [map_sum, LinearMap.sum_apply]
    simp only [dualTensorHom_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
    have := key (x * m)
    calc Algebra.lmul R A x m = x * m := rfl
      _ = ∑ p ∈ S, τ (x * m * p.1) • p.2 := this.symm
      _ = ∑ p ∈ S, τ (x * p.1 * m) • p.2 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [mul_right_comm]
  rw [Algebra.trace_apply, hlmul, LinearMap.trace_eq_contract_apply, map_sum]
  simp only [contractLeft_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [← map_sum]
  congr 1
  rw [hS, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [LinearMap.mul'_apply]
  ring

end

private theorem solution
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A] [Module.Finite R A]
        [Module.Free R A]
    (τ : Module.Dual R A) (Δ : A ⊗[R] A)
    (hbal : ∀ s : A, (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ)
    (hτ : TensorProduct.lid R A (LinearMap.rTensor A τ Δ) = 1) (x : A) :
    Algebra.trace R A x = τ (LinearMap.mul' R A Δ * x) :=
  main R A τ Δ hbal hτ x
end JacobianSquarePresentation.TraceDualLmul

namespace JacobianSquarePresentation.DualJacobian

open scoped TensorProduct

private theorem solution
    (R : Type*) [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    [Module.Finite R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))]
    [Module.Free R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))] :
    ∃ τ : (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) →ₗ[R] R,
      Function.Bijective (fun a : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f) =>
        τ.comp (LinearMap.mulLeft R a)) ∧
      ∀ a : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f),
        Algebra.trace R _ a =
          τ (Ideal.Quotient.mk (Ideal.span (Set.range f))
              (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i))) * a) := by
  classical
  choose a ha using fun i => JacobianSquarePresentation.TmulSubSum.solution R (f i)
  let A := MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)
  let Δ : A ⊗[R] A := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
      (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Matrix.det (Matrix.of a))
  let θ : Module.Dual R A → A := fun φ => Algebra.TensorProduct.lid R A (LinearMap.rTensor A φ Δ)
  have hθ : Function.Bijective θ := JacobianSquarePresentation.BezoutianSquare.solution R f a ha
  have hbal : ∀ s : A, (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ :=
    fun s => JacobianSquarePresentation.BezoutianTmul.solution R f a ha s
  have hlin : ∀ (φ : Module.Dual R A) (s : A), θ (φ.comp (LinearMap.mulLeft R s)) = s * θ φ :=
    fun φ s => lid_rTensor_comp_mulLeft R A Δ hbal φ s
  obtain ⟨τ, hτ⟩ := hθ.2 1
  refine ⟨τ, ⟨?_, ?_⟩, ?_⟩
  · intro s s' hss'
    have h := congrArg θ hss'
    simp only [hlin, hτ, mul_one] at h
    exact h
  · intro φ
    refine ⟨θ φ, hθ.1 ?_⟩
    change θ (τ.comp (LinearMap.mulLeft R (θ φ))) = θ φ
    rw [hlin, hτ, mul_one]
  · intro x
    have hmul : ∀ z : A ⊗[R] A, LinearMap.mul' R A z = Algebra.TensorProduct.lmul' (S := A) R z :=
        fun z => by
      induction z using TensorProduct.inductionOn with
      | tmul u v => simp
      | add u v hu hv => simp only [map_add, hu, hv]
    rw [JacobianSquarePresentation.TraceDualLmul.solution R A τ Δ hbal hτ x, hmul,
      JacobianSquarePresentation.LmulBezoutian.solution R f a ha]
end JacobianSquarePresentation.DualJacobian

namespace JacobianSquarePresentation.DetDualNorm

open scoped TensorProduct

section

open Module

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem mul_basis_eq_sum (b : Basis ι R A) (c : A) (j : ι) :
    c * b j = ∑ k, Algebra.leftMulMatrix b c k j • b k := by
  conv_lhs => rw [← b.sum_repr (c * b j)]
  simp only [Algebra.leftMulMatrix_eq_repr_mul]

private theorem of_dual_mul_mul_eq (b : Basis ι R A) (τ : Dual R A) (c : A) :
    (Matrix.of fun i j => τ (c * b i * b j)) =
      (Algebra.leftMulMatrix b c).transpose * Matrix.of fun i j => τ (b i * b j) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [mul_basis_eq_sum R A b c i, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]

private theorem main3 (b : Basis ι R A) (τ : Dual R A) (c : A) :
    (Matrix.of fun i j => τ (c * b i * b j)).det = Algebra.norm R c *
        (Matrix.of fun i j => τ (b i * b j)).det := by
  rw [of_dual_mul_mul_eq R A b τ c, Matrix.det_mul, Matrix.det_transpose,
      Algebra.norm_eq_matrix_det b]

end

private theorem solution
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (τ : Module.Dual R A) (c : A) :
    (Matrix.of fun i j => τ (c * b i * b j)).det = Algebra.norm R c *
        (Matrix.of fun i j => τ (b i * b j)).det :=
  main3 R A b τ c
end JacobianSquarePresentation.DetDualNorm

namespace JacobianSquarePresentation.IsUnitDetDual

open scoped TensorProduct

section

open Module

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def dualMulMap (τ : Dual R A) : A →ₗ[R] Dual R A := (LinearMap.mul R A).compr₂ τ

private theorem coe_dualMulMap (τ : Dual R A) :
    ⇑(dualMulMap R A τ) = fun a : A => τ.comp (LinearMap.mulLeft R a) := by
  funext a
  apply LinearMap.ext
  intro x
  rfl

private theorem main4 (b : Basis ι R A) (τ : Dual R A)
    (hτ : Function.Bijective (fun a : A => τ.comp (LinearMap.mulLeft R a))) :
    IsUnit (Matrix.of fun i j => τ (b i * b j)).det := by
  have hbij : Function.Bijective (dualMulMap R A τ) := by rw [coe_dualMulMap]; exact hτ
  let e : A ≃ₗ[R] Dual R A := LinearEquiv.ofBijective (dualMulMap R A τ) hbij
  have hmat : LinearMap.toMatrix b b.dualBasis (e : A →ₗ[R] Dual R A) =
      (Matrix.of fun i j => τ (b i * b j)).transpose := by
    ext i j
    rw [LinearMap.toMatrix_apply, Basis.dualBasis_repr, Matrix.transpose_apply, Matrix.of_apply]
    change dualMulMap R A τ (b j) (b i) = τ (b j * b i)
    rfl
  have h := LinearEquiv.isUnit_det e b b.dualBasis
  rwa [hmat, Matrix.det_transpose] at h

end

private theorem solution
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (τ : Module.Dual R A)
    (hτ : Function.Bijective (fun a : A => τ.comp (LinearMap.mulLeft R a))) :
    IsUnit (Matrix.of fun i j => τ (b i * b j)).det :=
  main4 R A b τ hτ
end JacobianSquarePresentation.IsUnitDetDual

namespace JacobianSquarePresentation.Assembly

open scoped TensorProduct

private theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {A : Type*} [CommRing A]
        [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A)
    {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    (e : (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) ≃ₐ[R] A) :
    Associated (Algebra.discr R b) (Algebra.norm R (e (Ideal.Quotient.mk _
        (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i)))))) := by
  classical
  have : Module.Free R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) :=
      Module.Free.of_equiv e.toLinearEquiv.symm
  have : Module.Finite R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) :=
      Module.Finite.equiv e.toLinearEquiv.symm
  obtain ⟨τ, hτbij, htr⟩ :=
    JacobianSquarePresentation.DualJacobian.solution R f
  set J : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f) :=
    Ideal.Quotient.mk (Ideal.span (Set.range f)) (Matrix.det (Matrix.of fun i j =>
        MvPolynomial.pderiv j (f i))) with hJ
  let b' : Module.Basis ι R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) :=
      b.map e.toLinearEquiv.symm
  have hb' : ∀ i, b' i = e.symm (b i) := fun i => by simp [b']
  have hdisc : Algebra.discr R b = (Matrix.of fun i j => τ (J * b' i * b' j)).det := by
    rw [Algebra.discr_eq_discr_of_algEquiv b e.symm, Algebra.discr_def]
    congr 1
    ext i j
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.of_apply, htr, mul_assoc]
    simp only [Function.comp_apply, hb']
  have hnorm : Algebra.norm R (e J) = Algebra.norm R J := Algebra.norm_eq_of_algEquiv e J
  rw [hdisc, JacobianSquarePresentation.DetDualNorm.solution R _ b' τ J]
  change Associated (Algebra.norm R J * (Matrix.of fun i j => τ (b' i * b' j)).det)
      (Algebra.norm R (e _))
  rw [hnorm]
  obtain ⟨u, hu⟩ := JacobianSquarePresentation.IsUnitDetDual.solution R _ b' τ hτbij
  rw [← hu]
  exact (associated_mul_unit_right (Algebra.norm R J) u u.isUnit).symm
end JacobianSquarePresentation.Assembly

/-- Let `R` be a Noetherian domain and `A` a finite free `R`-algebra presented as
`R[X₁, …, Xₘ] ⧸ (f₁, …, fₘ)` by `e`. Then the discriminant of any basis of `A` is
associated to the norm of the image under `e` of the Jacobian determinant
`det (∂fᵢ/∂Xⱼ)`. -/
public theorem Algebra.associated_discr_norm_jacobianDet_of_square_presentation
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {A : Type*} [CommRing A]
    [Algebra R A] [Module.Free R A] [Module.Finite R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A)
    {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    (e : (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) ≃ₐ[R] A) :
    Associated (Algebra.discr R b) (Algebra.norm R (e (Ideal.Quotient.mk _
      (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i)))))) :=
  JacobianSquarePresentation.Assembly.solution b f e
