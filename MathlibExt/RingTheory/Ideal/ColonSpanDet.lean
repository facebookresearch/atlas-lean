/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Ideal_colon_span_eq_sup_span_det_of_isWeaklyRegular.lean`
and
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
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Order.Hom.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Data.Finset.Preimage
import Mathlib.Order.Sum.Order
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import MathlibExt.Algebra.Homology.KoszulComplexFamily
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.FiveLemma
import Mathlib.Order.Hom.Set
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring

/-!
# Colon ideals of a weakly regular span and a determinant

Let `x f : Fin n → P` with `f = g • x` for an `n × n` matrix `g`, and suppose the ideal
`(f)` contains a weakly regular sequence of length `n`. Using Koszul homology we show
`(f) : (x) = (f) + (det g)` and `(f) : (det g) = (x)`.

## References

* A. Corso, C. Polini and W. V. Vasconcelos, *Links of prime ideals*, Math. Proc. Cambridge
  Philos. Soc. 115 (1994), 431–436, Theorem 2.5.
* D. G. Northcott, *A homological investigation of a certain residual ideal*, Math. Ann. 150
  (1963), 99–110.
-/


namespace ColonSpanDet

open Finset

namespace Koszul

universe u v

section Sign

variable (P : Type u) [CommRing P] {I : Type} [LinearOrder I]

def sgn (i : I) (T : Finset I) : P := (-1) ^ (T.filter (· < i)).card

theorem sgn_mul_self (i : I) (T : Finset I) : sgn P i T * sgn P i T = 1 := by
  rw [sgn, ← pow_add, ← two_mul, pow_mul]; simp

theorem sgn_insert_of_lt {i j : I} {T : Finset I} (hj : j ∉ T) (h : j < i) :
    sgn P i (insert j T) = -sgn P i T := by
  rw [sgn, sgn, filter_insert, ite_eq_left h, card_insert_of_notMem (by simp [hj]), pow_succ]
  ring

theorem sgn_insert_of_not_lt {i j : I} {T : Finset I} (h : ¬j < i) :
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

theorem mem_C {p : ℕ} {m : Finset I → M} : m ∈ C (P := P) M p ↔ ∀ T, T.card ≠ p → m T = 0 :=
  Iff.rfl

end Chains

section Differential

variable {P : Type u} [CommRing P] {I : Type} [LinearOrder I] [Fintype I]
variable (x : I → P) (M : Type v) [AddCommGroup M] [Module P M]

def coef (i : I) (T : Finset I) : P := if i ∈ T then 0 else sgn P i T * x i

omit [Fintype I] in
theorem coef_of_mem {i : I} {T : Finset I} (h : i ∈ T) : coef x i T = 0 := ite_eq_left h

omit [Fintype I] in
theorem coef_of_not_mem {i : I} {T : Finset I} (h : i ∉ T) : coef x i T = sgn P i T * x i
    := ite_eq_right h

private def d : (Finset I → M) →ₗ[P] (Finset I → M) :=
  ∑ i : I, LinearMap.pi fun T => coef x i T • LinearMap.proj (insert i T)

theorem d_apply (m : Finset I → M) (T : Finset I) :
    d x M m T = ∑ i, coef x i T • m (insert i T) := by
  simp [d, LinearMap.sum_apply]

theorem d_d (m : Finset I → M) : d x M (d x M m) = 0 := by
  classical
  funext U
  simp only [d_apply, Pi.zero_apply, smul_sum, smul_smul]
  rw [← sum_product' univ univ
      (fun j i => (coef x j U * coef x i (insert j U)) • m (insert i (insert j U)))]
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

theorem B_le_Z (p : ℕ) : B x M p ≤ Z x M p := by
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨d_mem_C x M hm, by simp [LinearMap.mem_ker, d_d]⟩

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

@[scoped simp] theorem coe_dC_apply (p : ℕ) (m : C (P := P) (I := I) M (p + 1)) :
    (dC x M p m : Finset I → M) = d x M m := rfl

theorem dC_dC (p : ℕ) (m : C (P := P) (I := I) M (p + 2)) : dC x M p (dC x M (p + 1) m) = 0 := by
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

@[scoped simp] theorem complex_X (p : ℕ) : (complex x M).X p = ModuleCat.of P
    (C (P := P) (I := I) M p) := rfl

theorem complex_d (p : ℕ) : (complex x M).d (p + 1) p = ModuleCat.ofHom (dC x M p) := by
  simp [complex]

noncomputable def scZ (p : ℕ) : ShortComplex (ModuleCat.{v'} P) :=
  ShortComplex.mk (ModuleCat.ofHom (dC x M p) : ModuleCat.of P (C (P := P) (I := I) M (p + 1)) ⟶
      ModuleCat.of P (C (P := P) (I := I) M p))
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
      rw [(complex x M).shape 0 _ (by simp)]
      erw [Limits.zero_comp]
      ext m : 2
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
    (LinearMap.ker (scZ x M p).g.hom ⧸ LinearMap.range (scZ x M p).moduleCatToCycles) ≃ₗ[P] H x M
        p :=
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
        rw [(complex x M).shape 0 _ (by simp)]
        erw [Limits.comp_zero]
      | succ q =>
        rw [show (ComplexShape.down ℕ).next (q + 1) = q from ChainComplex.next_nat_succ q,
            complex_d]
        ext z : 2
        exact Subtype.ext (LinearMap.mem_ker.mp z.2.2))

theorem ZToCycles_comp (p : ℕ) :
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

theorem ZToCycles_π_bridge (p : ℕ) :
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

@[scoped simp] theorem coe_mapZ (f : HMap x M y N) (p : ℕ) (z : Z x M p) :
    (f.mapZ p z : Finset J → N) = f.toLinearMap z := rfl

def mapH (f : HMap x M y N) (p : ℕ) : H x M p →ₗ[P] H y N p :=
  Submodule.mapQ _ _ (f.mapZ p) fun _ hz => f.map_B p hz

@[scoped simp] theorem mapH_mk (f : HMap x M y N) (p : ℕ) (z : Z x M p) :
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

@[scoped simp] theorem id_toLinearMap : (HMap.id x M).toLinearMap = LinearMap.id := rfl
@[scoped simp] theorem comp_toLinearMap (g : HMap y N w O) (f : HMap x M y N) :
    (g.comp f).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap := rfl

theorem mapH_id (p : ℕ) : (HMap.id x M).mapH p = LinearMap.id := by
  ext; rfl

theorem mapH_comp (g : HMap y N w O) (f : HMap x M y N) (p : ℕ) :
    (g.comp f).mapH p = g.mapH p ∘ₗ f.mapH p := by
  ext; rfl

theorem mapH_congr {f g : HMap x M y N} (h : f.toLinearMap = g.toLinearMap) (p : ℕ) :
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

@[scoped simp] theorem mapHEquiv_apply (f : HMap x M y N) (g : HMap y N x M) (hfg hgf) (p : ℕ)
    (z : H x M p) : f.mapHEquiv g hfg hgf p z = f.mapH p z := rfl

@[scoped simp] theorem mapHEquiv_symm_apply (f : HMap x M y N) (g : HMap y N x M) (hfg hgf) (p : ℕ)
    (z : H y N p) : (f.mapHEquiv g hfg hgf p).symm z = g.mapH p z := rfl

end HMap
open scoped ColonSpanDet.Koszul.HMap

variable (x M y N) in
structure ChainMap where
  toLinearMap : (Finset I → M) →ₗ[P] (Finset J → N)
  comm : toLinearMap ∘ₗ d x M = d y N ∘ₗ toLinearMap
  map_C : ∀ p, C (P := P) (I := I) M p ≤ (C (P := P) (I := J) N p).comap toLinearMap

namespace ChainMap

theorem comm_apply (f : ChainMap x M y N) (m : Finset I → M) :
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

@[scoped simp] theorem toHMap_toLinearMap (f : ChainMap x M y N) :
    f.toHMap.toLinearMap = f.toLinearMap := rfl

abbrev mapH (f : ChainMap x M y N) (p : ℕ) : H x M p →ₗ[P] H y N p := f.toHMap.mapH p

variable (x M) in
protected def id : ChainMap x M x M where
  toLinearMap := LinearMap.id
  comm := rfl
  map_C _ _ hm := hm

def comp (g : ChainMap y N w O) (f : ChainMap x M y N) : ChainMap x M w O where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  comm := by rw [LinearMap.comp_assoc, f.comm, ← LinearMap.comp_assoc, g.comm, LinearMap.comp_assoc]
  map_C p _ hm := g.map_C p (f.map_C p hm)

def mapC (f : ChainMap x M y N) (p : ℕ) :
    C (P := P) (I := I) M p →ₗ[P] C (P := P) (I := J) N p :=
  f.toLinearMap.restrict fun _ hm => f.map_C p hm

@[scoped simp] theorem coe_mapC (f : ChainMap x M y N) (p : ℕ) (m : C (P := P) (I := I) M p) :
    (f.mapC p m : Finset J → N) = f.toLinearMap m := rfl

noncomputable def toHom (f : ChainMap x M y N) : complex x M ⟶ complex y N where
  f p := ModuleCat.ofHom (f.mapC p)
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [complex_d, complex_d]
    ext m : 2
    apply Subtype.ext
    exact (f.comm_apply _).symm

theorem ZToCycles_cyclesMap (f : ChainMap x M y N) (p : ℕ) :
    ZToCycles x M p ≫ HomologicalComplex.cyclesMap f.toHom p =
      ModuleCat.ofHom (f.toHMap.mapZ p) ≫ ZToCycles y N p := by
  rw [← cancel_mono ((complex y N).iCycles p), Category.assoc, Category.assoc,
    HomologicalComplex.cyclesMap_i, ZToCycles, ZToCycles]
  erw [HomologicalComplex.liftCycles_i_assoc, HomologicalComplex.liftCycles_i]
  rfl

theorem homologyMap_bridge (f : ChainMap x M y N) (p : ℕ) :
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
    refine LinearMap.ext fun m => funext fun T => ?_
    simp [d_apply, map_sum, map_smul]
  map_C p m hm T hT := by
    change φ (m T) = 0
    rw [hm T hT, map_zero]

@[scoped simp] theorem ofLinearMap_apply {M' : Type v'} [AddCommGroup M'] [Module P M']
    (φ : M →ₗ[P] M')
    (m : Finset I → M) (T : Finset I) : (ofLinearMap x φ).toLinearMap m T = φ (m T) := rfl

end ChainMap
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap

end Functoriality
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap

end Koszul
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

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
@[scoped simp] theorem reindexLin_apply (e : I ≃ J) (m : Finset J → M) (S : Finset I) :
    reindexLin P M e m S = m (S.map e.toEmbedding) := rfl

omit [LinearOrder I] [Fintype I] [LinearOrder J] [Fintype J] in
@[scoped simp] theorem reindexLin_symm (e : I ≃ J) :
    (reindexLin P M e).symm = reindexLin P M e.symm := rfl

omit [LinearOrder I] [Fintype I] [LinearOrder J] [Fintype J] in
theorem reindexLin_mem_C_iff (e : I ≃ J) {p : ℕ} {m : Finset J → M} :
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
theorem sgn_map_orderIso (e : I ≃o J) (i : I) (T : Finset I) :
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

theorem reindexH_symm_mk (e : I ≃o J) (x : J → P) (p : ℕ) (z : Z x M p) :
    (reindexH M e x p).symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((reindex M e x).toHMap.mapZ p z) := rfl

private theorem neg_one_pow_mul_self (n : ℕ) : ((-1 : P) ^ n) * (-1) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

omit [LinearOrder I] [Fintype I] in
private theorem map_toDual_map_ofDual (S : Finset I) :
    (S.map OrderDual.toDual.toEmbedding).map OrderDual.ofDual.toEmbedding = S := by
  rw [Finset.map_map, ← OrderDual.toDual_symm_eq,
    Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding, Finset.map_refl]

omit [LinearOrder I] [Fintype I] in
private theorem map_ofDual_map_toDual (T : Finset Iᵒᵈ) :
    (T.map OrderDual.ofDual.toEmbedding).map OrderDual.toDual.toEmbedding = T := by
  rw [Finset.map_map, ← OrderDual.ofDual_symm_eq,
    Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding, Finset.map_refl]

omit [Fintype I] in
theorem sgn_dual (i : I) (T : Finset I) (hi : i ∉ T) :
    sgn P (OrderDual.toDual i) (T.map OrderDual.toDual.toEmbedding) =
      (-1) ^ T.card * sgn P i T := by
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
    sgn P i T =
      (-1) ^ T.card * sgn P (OrderDual.ofDual i) (T.map OrderDual.ofDual.toEmbedding) := by
  have h := sgn_dual (P := P) (OrderDual.ofDual i) (T.map OrderDual.ofDual.toEmbedding)
    fun h => hi ((Finset.mem_map' _).mp h)
  rw [Finset.card_map, ← OrderDual.ofDual_symm_eq, Equiv.symm_apply_apply, Finset.map_map,
    Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding, Finset.map_refl] at h
  exact h

theorem d_reindexLin_dual (x : I → P) (m : Finset I → M) (T : Finset Iᵒᵈ) :
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
    · rw [d_mem_C x M hm' (T.map OrderDual.ofDual.toEmbedding) (by rwa [Finset.card_map]),
        smul_zero]

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
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section Ends

variable {P : Type u'} [CommRing P] {I : Type} [LinearOrder I] [Fintype I]
variable (x : I → P) (M : Type v') [AddCommGroup M] [Module P M]

def annihilatedBy : Submodule P M where
  carrier := {m | ∀ i, x i • m = 0}
  add_mem' ha hb i := by simp [smul_add, ha i, hb i]
  zero_mem' i := smul_zero _
  smul_mem' c m hm i := by rw [smul_comm, hm i, smul_zero]

omit [LinearOrder I] [Fintype I] in
@[scoped simp] theorem mem_annihilatedBy {m : M} : m ∈ annihilatedBy x M ↔ ∀ i, x i • m = 0
    := Iff.rfl

omit [LinearOrder I] in
theorem C_eq_bot_of_card_lt {p : ℕ} (hp : Fintype.card I < p) : C (P := P) (I := I) M p = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun m hm => funext fun T => hm T ?_
  have := Finset.card_le_univ T
  omega

theorem subsingleton_H_of_card_lt {p : ℕ} (hp : Fintype.card I < p) : Subsingleton (H x M p) := by
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

private theorem smul_apply_univ_eq_zero {m : Finset I → M} (hm : d x M m = 0) (i : I) :
    x i • m univ = 0 := by
  have h : (sgn P i (univ.erase i) * x i) • m univ = 0 := by
    rw [← d_apply_univ_erase, hm, Pi.zero_apply]
  calc x i • m univ = sgn P i (univ.erase i) • ((sgn P i (univ.erase i) * x i) • m univ) := by
        rw [smul_smul, ← mul_assoc, sgn_mul_self, one_mul]
    _ = 0 := by rw [h, smul_zero]

private def evalTop : Z x M (Fintype.card I) →ₗ[P] annihilatedBy x M where
  toFun z := ⟨(z : Finset I → M) univ, fun i =>
    smul_apply_univ_eq_zero x M (LinearMap.mem_ker.mp z.2.2) i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem single_univ_mem_C (m : M) :
    Pi.single (univ : Finset I) m ∈ C (P := P) (I := I) M (Fintype.card I) :=
  fun _ hT => Pi.single_eq_of_ne (fun h => hT (by rw [h, Finset.card_univ])) _

private theorem d_single_univ (m : annihilatedBy x M) :
    d x M (Pi.single (univ : Finset I) (m : M)) = 0 := by
  funext T
  rw [d_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : insert i T = univ
  · rw [h, Pi.single_eq_same]
    exact coef_smul_of_forall_smul_eq_zero x M m.2 i T
  · rw [Pi.single_eq_of_ne h, smul_zero]

private def topCycle : annihilatedBy x M →ₗ[P] Z x M (Fintype.card I) where
  toFun m := ⟨Pi.single (univ : Finset I) (m : M), single_univ_mem_C M (m : M),
    LinearMap.mem_ker.mpr (d_single_univ x M m)⟩
  map_add' a b := Subtype.ext (Pi.single_add (f := fun _ : Finset I => M) univ (a : M) (b : M))
  map_smul' c a := Subtype.ext (Pi.single_smul' (univ : Finset I) c (a : M))

private theorem topCycle_evalTop (z : Z x M (Fintype.card I)) :
    topCycle x M (evalTop x M z) = z := by
  refine Subtype.ext (funext fun T => ?_)
  change (Pi.single univ ((z : Finset I → M) univ) : Finset I → M) T = (z : Finset I → M) T
  by_cases hT : T = univ
  · rw [hT, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hT]
    exact (z.2.1 T fun h => hT (Finset.eq_univ_of_card T h)).symm

private theorem evalTop_topCycle (m : annihilatedBy x M) : evalTop x M (topCycle x M m) = m :=
  Subtype.ext (Pi.single_eq_same (M := fun _ : Finset I => M) univ (m : M))

private theorem comap_B_top_eq_bot :
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

theorem HTopEquiv_mk (z : Z x M (Fintype.card I)) :
    (HTopEquiv x M (Submodule.Quotient.mk z) : M) = (z : Finset I → M) Finset.univ := by
  rfl

omit [Fintype I] in
private theorem sgn_emptyset (i : I) : sgn P i ∅ = 1 := by
  simp [sgn]

omit [Fintype I] in
private theorem single_empty_mem_C (m : M) :
    Pi.single (∅ : Finset I) m ∈ C (P := P) (I := I) M 0 :=
  fun _ hT => Pi.single_eq_of_ne (fun h => hT (Finset.card_eq_zero.mpr h)) _

omit [Fintype I] in
private theorem single_singleton_mem_C (i : I) (n : M) :
    Pi.single ({i} : Finset I) n ∈ C (P := P) (I := I) M 1 :=
  fun _ hT => Pi.single_eq_of_ne (fun h => hT (by rw [h, Finset.card_singleton])) _

private def zeroCycleEquiv : Z x M 0 ≃ₗ[P] M where
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

private theorem map_zeroCycleEquiv_comap_B :
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

theorem HZeroEquiv_mk (z : Z x M 0) :
    HZeroEquiv x M (Submodule.Quotient.mk z) = Submodule.Quotient.mk ((z : Finset I → M) ∅) := by
  rfl

theorem HZeroEquiv_mapH {M' : Type v'} [AddCommGroup M'] [Module P M'] (φ : M →ₗ[P] M')
    (h : H x M 0) :
    HZeroEquiv x M' ((ChainMap.ofLinearMap x φ).mapH 0 h) =
      Submodule.mapQ _ _ φ (fun m hm => by
        refine Submodule.smul_induction_on hm (fun r hr n _ => ?_) fun a b ha hb => add_mem ha hb
        rw [Submodule.mem_comap, map_smul]
        exact Submodule.smul_mem_smul hr Submodule.mem_top) (HZeroEquiv x M h) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  rfl

theorem HTopEquiv_mapH {M' : Type v'} [AddCommGroup M'] [Module P M'] (φ : M →ₗ[P] M')
    (h : H x M (Fintype.card I)) :
    (HTopEquiv x M' ((ChainMap.ofLinearMap x φ).mapH _ h) : M') = φ (HTopEquiv x M h) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  rfl

end Ends
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section Htpy

variable (P : Type u') [CommRing P] {I : Type} [LinearOrder I] [Fintype I]
variable (M : Type v') [AddCommGroup M] [Module P M]

def contract (i : I) : (Finset I → M) →ₗ[P] (Finset I → M) where
  toFun m T := if i ∈ T then sgn P i (T.erase i) • m (T.erase i) else 0
  map_add' m m' := by funext T; by_cases h : i ∈ T <;> simp [h]
  map_smul' c m := by funext T; by_cases h : i ∈ T <;> simp [h, smul_comm c]

omit [Fintype I] in
theorem contract_apply (i : I) (m : Finset I → M) (T : Finset I) :
    contract P M i m T = if i ∈ T then sgn P i (T.erase i) • m (T.erase i) else 0 := rfl

variable {P M} (x : I → P)

theorem d_contract_add_contract_d (i : I) (m : Finset I → M) :
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
      rw [ite_eq_left
          (Finset.mem_insert_of_mem (Finset.mem_insert_self i S) : i ∈ insert j (insert i S)),
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
          smul_smul,
        mul_right_comm, sgn_mul_self, one_mul]
    · intro j _ hji
      rw [ite_eq_right, smul_zero]
      simp [Ne.symm hji, hi]
    · intro h; exact absurd (Finset.mem_univ i) h

omit [Fintype I] in
theorem contract_mem_C (i : I) {p : ℕ} {m : Finset I → M} (hm : m ∈ C (P := P) (I := I) M p) :
    contract P M i m ∈ C (P := P) (I := I) M (p + 1) := by
  intro T hT
  rw [contract_apply]
  split_ifs with hiT
  · rw [hm _ (fun h => hT (by rw [← Finset.card_erase_add_one hiT, h])), smul_zero]
  · rfl

variable {x}

theorem smul_H_eq_zero (i : I) {p : ℕ} (h : H x M p) : x i • h = 0 := by
  induction h using Submodule.Quotient.induction_on with
  | H z =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_smul]
    refine ⟨contract P M i z, contract_mem_C i z.2.1, ?_⟩
    have h := d_contract_add_contract_d x i (z : Finset I → M)
    rwa [LinearMap.mem_ker.mp z.2.2, map_zero, add_zero] at h

theorem smul_H_eq_zero_of_mem_span {p : ℕ} (a : P) (ha : a ∈ Ideal.span (Set.range x))
    (h : H x M p) :
    a • h = 0 := by
  induction ha using Submodule.span_induction with
  | mem r hr => obtain ⟨i, rfl⟩ := hr; exact smul_H_eq_zero i h
  | zero => exact zero_smul P h
  | add r s _ _ hr hs => rw [add_smul, hr, hs, add_zero]
  | smul r s _ hs => rw [smul_eq_mul, mul_smul, hs, smul_zero]

variable (x M) in
theorem span_range_le_annihilator (p : ℕ) :
    Ideal.span (Set.range x) ≤ Module.annihilator P (H x M p) := fun a ha =>
  Module.mem_annihilator.mpr fun h => smul_H_eq_zero_of_mem_span a ha h

end Htpy
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section ClassLemmas

variable {P : Type u'} [CommRing P] {I : Type} [LinearOrder I] [Fintype I]
variable {x : I → P} {M : Type v'} [AddCommGroup M] [Module P M]

theorem H_mk_eq_zero_iff {p : ℕ} (z : Z x M p) :
    (Submodule.Quotient.mk z : H x M p) = 0 ↔ (z : Finset I → M) ∈ B x M p := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]

theorem H_mk_eq_mk_iff {p : ℕ} (z z' : Z x M p) :
    (Submodule.Quotient.mk z : H x M p) = Submodule.Quotient.mk z' ↔ (z : Finset I → M) - z' ∈ B x
        M p := by
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub]

end ClassLemmas
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section Cone

variable {P : Type u'} [CommRing P] {I : Type} [LinearOrder I] [Fintype I]
variable {U : Type} [LinearOrder U] [Fintype U] [Unique U]
variable {J : Type} [LinearOrder J] [Fintype J]

variable (U) in
def snoc (x : I → P) (t : P) : I ⊕ₗ U → P := fun k => Sum.elim x (fun _ => t) (ofLex k)

variable (I U) in
def top : I ⊕ₗ U := toLex (Sum.inr default)

variable (U) in
def inlₗ : I ↪ I ⊕ₗ U := ⟨fun i => toLex (Sum.inl i),
    fun _ _ h => Sum.inl_injective (toLex.injective h)⟩

omit [CommRing P] [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] [Unique U] in
@[scoped simp] theorem snoc_inl (x : I → P) (t : P) (i : I) : snoc U x t (inlₗ U i) = x i := rfl
omit [CommRing P] [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] in
@[scoped simp] theorem snoc_top (x : I → P) (t : P) : snoc U x t (top I U) = t := rfl

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] in
theorem lex_cases (k : I ⊕ₗ U) : (∃ i, k = inlₗ U i) ∨ k = top I U := by
  obtain ⟨k, rfl⟩ := toLex.surjective k
  rcases k with i | u
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr (by rw [Subsingleton.elim u default]; rfl)

omit [Fintype I] [Fintype U] [Unique U] in
theorem inlₗ_lt_inlₗ {i j : I} : inlₗ U i < inlₗ U j ↔ i < j := Sum.Lex.inl_lt_inl_iff

omit [Fintype I] [Fintype U] in
theorem inlₗ_lt_top (i : I) : inlₗ U i < top I U := Sum.Lex.inl_lt_inr _ _

omit [Fintype I] [Fintype U] in
theorem not_top_lt_inlₗ (i : I) : ¬top I U < inlₗ U i := Sum.Lex.not_inr_lt_inl

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] in
theorem inlₗ_ne_top (i : I) : inlₗ U i ≠ top I U := fun h => Sum.inl_ne_inr (toLex.injective h)

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] in
theorem top_notMem_map (T : Finset I) : top I U ∉ T.map (inlₗ U) := by
  simp only [Finset.mem_map, not_exists, not_and]
  exact fun i _ h => inlₗ_ne_top i h

variable (U) in
private noncomputable def down (S : Finset (I ⊕ₗ U)) : Finset I
    := S.preimage (inlₗ U) (inlₗ U).injective.injOn

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] [Unique U] in
@[scoped simp] theorem mem_down {S : Finset (I ⊕ₗ U)} {i : I} : i ∈ down U S ↔ inlₗ U i ∈ S :=
  Finset.mem_preimage

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] [Unique U] in
@[scoped simp] theorem down_map (T : Finset I) : down U (T.map (inlₗ U)) = T := by
  ext i; simp

omit [Fintype I] [Fintype U] in
@[scoped simp] theorem down_insert_top (S : Finset (I ⊕ₗ U)) : down U (insert (top I U) S) = down U
    S := by
  ext i; simp [inlₗ_ne_top]

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] in
theorem eq_map_down {S : Finset (I ⊕ₗ U)} (h : top I U ∉ S) : S = (down U S).map (inlₗ U) := by
  ext k
  rcases lex_cases k with ⟨i, rfl⟩ | rfl
  · simp
  · simp only [top_notMem_map, iff_false]; exact h

omit [Fintype I] [Fintype U] in
theorem eq_insert_map_down {S : Finset (I ⊕ₗ U)} (h : top I U ∈ S) :
    S = insert (top I U) ((down U S).map (inlₗ U)) := by
  ext k
  rcases lex_cases k with ⟨i, rfl⟩ | rfl
  · simp [inlₗ_ne_top]
  · simp only [Finset.mem_insert, true_or, iff_true]; exact h

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] in
theorem card_down_of_notMem {S : Finset (I ⊕ₗ U)} (h : top I U ∉ S) : (down U S).card = S.card := by
  rw [← Finset.card_map (inlₗ U), ← eq_map_down h]

omit [Fintype I] [Fintype U] in
theorem card_insert_top_map (T : Finset I) :
    (insert (top I U) (T.map (inlₗ U))).card = T.card + 1 := by
  rw [Finset.card_insert_of_notMem (top_notMem_map T), Finset.card_map]

omit [Fintype I] [Fintype U] in
theorem card_down_of_mem {S : Finset (I ⊕ₗ U)} (h : top I U ∈ S) :
    (down U S).card + 1 = S.card := by
  rw [← card_insert_top_map (U := U) (down U S), ← eq_insert_map_down h]

omit [Fintype I] [Fintype U] [Unique U] in
theorem map_insert_inlₗ (i : I) (T : Finset I) :
    (insert i T).map (inlₗ U) = insert (inlₗ U i) (T.map (inlₗ U)) := Finset.map_insert _ _ _

omit [LinearOrder I] [LinearOrder U] in
theorem sum_lex {A : Type*} [AddCommMonoid A] (f : I ⊕ₗ U → A) :
    ∑ k, f k = ∑ i, f (inlₗ U i) + f (top I U) := by
  rw [← Fintype.sum_equiv toLex (fun k => f (toLex k)) f (fun _ => rfl), Fintype.sum_sum_type]
  congr 1
  exact Fintype.sum_unique (fun u : U => f (toLex (Sum.inr u)))

omit [Fintype I] [Fintype U] [Unique U] in
theorem sgn_inlₗ_map (i : I) (T : Finset I) : sgn P (inlₗ U i) (T.map (inlₗ U)) = sgn P i T := by
  rw [sgn, sgn, Finset.filter_map, Finset.card_map]
  congr 2

omit [Fintype I] [Fintype U] in
theorem sgn_inlₗ_insert_top (i : I) (T : Finset I) :
    sgn P (inlₗ U i) (insert (top I U) (T.map (inlₗ U))) = sgn P i T := by
  erw [sgn_insert_of_not_lt P (not_top_lt_inlₗ i)]
  rw [sgn_inlₗ_map]

omit [Fintype I] [Fintype U] in
theorem sgn_top_map (T : Finset I) : sgn P (top I U) (T.map (inlₗ U)) = (-1) ^ T.card := by
  rw [sgn, Finset.filter_true_of_mem, Finset.card_map]
  simp only [Finset.mem_map, forall_exists_index, and_imp]
  rintro _ i _ rfl; exact inlₗ_lt_top i

omit [Fintype I] [Fintype U] [Unique U] in
theorem coef_snoc_inlₗ_map (x : I → P) (t : P) (i : I) (T : Finset I) :
    coef (snoc U x t) (inlₗ U i) (T.map (inlₗ U)) = coef x i T := by
  by_cases hi : i ∈ T
  · rw [coef_of_mem _ ((Finset.mem_map' _).mpr hi), coef_of_mem _ hi]
  · rw [coef_of_not_mem _ (fun h => hi ((Finset.mem_map' _).mp h)), coef_of_not_mem _ hi,
        sgn_inlₗ_map,
      snoc_inl]

omit [Fintype I] [Fintype U] in
theorem coef_snoc_inlₗ_insert_top (x : I → P) (t : P) (i : I) (T : Finset I) :
    coef (snoc U x t) (inlₗ U i) (insert (top I U) (T.map (inlₗ U))) = coef x i T := by
  have hmem : inlₗ U i ∈ insert (top I U) (T.map (inlₗ U)) ↔ i ∈ T := by
    simp [inlₗ_ne_top]
  by_cases hi : i ∈ T
  · rw [coef_of_mem _ (hmem.mpr hi), coef_of_mem _ hi]
  · rw [coef_of_not_mem _ (fun h => hi (hmem.mp h)), coef_of_not_mem _ hi, sgn_inlₗ_insert_top,
        snoc_inl]

omit [Fintype I] [Fintype U] in
theorem coef_snoc_top_map (x : I → P) (t : P) (T : Finset I) :
    coef (snoc U x t) (top I U) (T.map (inlₗ U)) = (-1) ^ T.card * t := by
  rw [coef_of_not_mem _ (top_notMem_map T), sgn_top_map, snoc_top]

theorem d_snoc_apply_map (x : I → P) (t : P) {M : Type v'} [AddCommGroup M] [Module P M]
    (m : Finset (I ⊕ₗ U) → M) (T : Finset I) :
    d (snoc U x t) M m (T.map (inlₗ U)) =
      ∑ i, coef x i T • m ((insert i T).map (inlₗ U)) + ((-1) ^ T.card * t) • m
          (insert (top I U) (T.map (inlₗ U))) := by
  rw [d_apply, sum_lex]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by rw [coef_snoc_inlₗ_map, map_insert_inlₗ]; rfl
  · rw [coef_snoc_top_map]; rfl

theorem d_snoc_apply_insert_top (x : I → P) (t : P) {M : Type v'} [AddCommGroup M] [Module P M]
    (m : Finset (I ⊕ₗ U) → M) (T : Finset I) :
    d (snoc U x t) M m (insert (top I U) (T.map (inlₗ U))) =
      ∑ i, coef x i T • m (insert (top I U) ((insert i T).map (inlₗ U))) := by
  rw [d_apply, sum_lex, coef_of_mem _ (Finset.mem_insert_self _ _), zero_smul, add_zero]
  exact Finset.sum_congr rfl fun i _ => by
    rw [coef_snoc_inlₗ_insert_top, map_insert_inlₗ, Finset.insert_comm]; rfl

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
@[scoped simp] theorem coneRes_apply (m : Finset (I ⊕ₗ U) → M) (T : Finset I) :
    coneRes P U M m T = m (T.map (inlₗ U)) := rfl

omit [Fintype I] [Fintype U] in
@[scoped simp] theorem coneProj_apply (m : Finset (I ⊕ₗ U) → M) (T : Finset I) :
    coneProj P U M m T = m (insert (top I U) (T.map (inlₗ U))) := rfl

omit [Fintype I] [Fintype U] in
theorem coneInclLin_apply_of_mem (m : Finset I → M) {S : Finset (I ⊕ₗ U)} (h : top I U ∈ S) :
    coneInclLin P U M m S = 0 := ite_eq_left h

omit [Fintype I] [Fintype U] in
theorem coneInclLin_apply_of_notMem (m : Finset I → M) {S : Finset (I ⊕ₗ U)} (h : top I U ∉ S) :
    coneInclLin P U M m S = m (down U S) := ite_eq_right h

omit [Fintype I] [Fintype U] in
@[scoped simp] theorem coneInclLin_apply_map (m : Finset I → M) (T : Finset I) :
    coneInclLin P U M m (T.map (inlₗ U)) = m T := by
  rw [coneInclLin_apply_of_notMem _ _ (top_notMem_map T), down_map]

omit [Fintype I] [Fintype U] in
@[scoped simp] theorem coneInclLin_apply_insert_top (m : Finset I → M) (S : Finset (I ⊕ₗ U)) :
    coneInclLin P U M m (insert (top I U) S) = 0 :=
  coneInclLin_apply_of_mem _ _ (Finset.mem_insert_self _ _)

omit [Fintype I] [Fintype U] in
theorem coneCoprojLin_apply_of_mem (m : Finset I → M) {S : Finset (I ⊕ₗ U)} (h : top I U ∈ S) :
    coneCoprojLin P U M m S = m (down U S) := ite_eq_left h

omit [Fintype I] [Fintype U] in
theorem coneCoprojLin_apply_of_notMem (m : Finset I → M) {S : Finset (I ⊕ₗ U)} (h : top I U ∉ S) :
    coneCoprojLin P U M m S = 0 := ite_eq_right h

omit [Fintype I] [Fintype U] in
@[scoped simp] theorem coneCoprojLin_apply_map (m : Finset I → M) (T : Finset I) :
    coneCoprojLin P U M m (T.map (inlₗ U)) = 0 :=
  coneCoprojLin_apply_of_notMem _ _ (top_notMem_map T)

omit [Fintype I] [Fintype U] in
@[scoped simp] theorem coneCoprojLin_apply_insert_top_map (m : Finset I → M) (T : Finset I) :
    coneCoprojLin P U M m (insert (top I U) (T.map (inlₗ U))) = m T := by
  rw [coneCoprojLin_apply_of_mem _ _ (Finset.mem_insert_self _ _), down_insert_top, down_map]

omit [Fintype I] [Fintype U] in
theorem coneInclLin_coneRes_add (m : Finset (I ⊕ₗ U) → M) :
    coneInclLin P U M (coneRes P U M m) + coneCoprojLin P U M (coneProj P U M m) = m := by
  funext S
  rw [Pi.add_apply]
  by_cases h : top I U ∈ S
  · rw [coneInclLin_apply_of_mem _ _ h, coneCoprojLin_apply_of_mem _ _ h, zero_add, coneProj_apply,
      ← eq_insert_map_down h]
  · rw [coneInclLin_apply_of_notMem _ _ h, coneCoprojLin_apply_of_notMem _ _ h, add_zero,
        coneRes_apply,
      ← eq_map_down h]

omit [Fintype I] [Fintype U] in
@[scoped simp] theorem coneRes_coneInclLin (m : Finset I → M) : coneRes P U M (coneInclLin P U M m)
    = m := by
  funext T; simp
omit [Fintype I] [Fintype U] in
@[scoped simp] theorem coneProj_coneInclLin (m : Finset I → M) : coneProj P U M
    (coneInclLin P U M m) = 0 := by
  funext T; simp
omit [Fintype I] [Fintype U] in
@[scoped simp] theorem coneRes_coneCoprojLin (m : Finset I → M) : coneRes P U M
    (coneCoprojLin P U M m) = 0 := by
  funext T; simp
omit [Fintype I] [Fintype U] in
@[scoped simp] theorem coneProj_coneCoprojLin (m : Finset I → M) : coneProj P U M
    (coneCoprojLin P U M m) = m := by
  funext T; simp

omit [Fintype I] [Fintype U] in
theorem cone_ext {m m' : Finset (I ⊕ₗ U) → M} (h₁ : coneRes P U M m = coneRes P U M m')
    (h₂ : coneProj P U M m = coneProj P U M m') : m = m' := by
  rw [← coneInclLin_coneRes_add (P := P) M m, ← coneInclLin_coneRes_add (P := P) M m', h₁, h₂]

def coneTw : (Finset I → M) →ₗ[P] (Finset I → M) where
  toFun m T := ((-1 : P) ^ T.card * t) • m T
  map_add' m m' := by funext T; simp [smul_add]
  map_smul' c m := by funext T; simp [smul_comm c]

omit [LinearOrder I] [Fintype I] in
@[scoped simp] theorem coneTw_apply (m : Finset I → M) (T : Finset I) :
    coneTw t M m T = ((-1 : P) ^ T.card * t) • m T := rfl

omit [LinearOrder I] [Fintype I] in
theorem coneTw_of_mem_C {p : ℕ} {m : Finset I → M} (hm : m ∈ C (P := P) (I := I) M p) :
    coneTw t M m = ((-1 : P) ^ p * t) • m := by
  funext T
  rw [coneTw_apply, Pi.smul_apply]
  by_cases hT : T.card = p
  · rw [hT]
  · rw [hm T hT, smul_zero, smul_zero]

omit [LinearOrder I] [Fintype I] in
theorem coneTw_mem_C {p : ℕ} {m : Finset I → M} (hm : m ∈ C (P := P) (I := I) M p) :
    coneTw t M m ∈ C (P := P) (I := I) M p := by
  rw [coneTw_of_mem_C t M hm]; exact Submodule.smul_mem _ _ hm

theorem coneProj_d (m : Finset (I ⊕ₗ U) → M) :
    coneProj P U M (d (snoc U x t) M m) = d x M (coneProj P U M m) := by
  funext T
  rw [coneProj_apply, d_snoc_apply_insert_top, d_apply]
  rfl

theorem coneRes_d (m : Finset (I ⊕ₗ U) → M) (T : Finset I) :
    coneRes P U M (d (snoc U x t) M m) T =
      d x M (coneRes P U M m) T + ((-1 : P) ^ T.card * t) • coneProj P U M m T := by
  rw [coneRes_apply, d_snoc_apply_map, d_apply]
  rfl

theorem coneRes_d' (m : Finset (I ⊕ₗ U) → M) :
    coneRes P U M (d (snoc U x t) M m) =
      d x M (coneRes P U M m) + coneTw t M (coneProj P U M m) := by
  funext T; rw [coneRes_d]; rfl

theorem d_coneInclLin (a : Finset I → M) :
    d (snoc U x t) M (coneInclLin P U M a) = coneInclLin P U M (d x M a) := by
  apply cone_ext (P := P) M
  · rw [coneRes_d', coneRes_coneInclLin, coneProj_coneInclLin, map_zero, add_zero,
        coneRes_coneInclLin]
  · rw [coneProj_d, coneProj_coneInclLin, coneProj_coneInclLin, map_zero]

theorem d_coneCoprojLin (b : Finset I → M) :
    d (snoc U x t) M (coneCoprojLin P U M b) =
      coneInclLin P U M (coneTw t M b) + coneCoprojLin P U M (d x M b) := by
  apply cone_ext (P := P) M
  · rw [coneRes_d', coneRes_coneCoprojLin, coneProj_coneCoprojLin, map_zero, zero_add, map_add,
      coneRes_coneInclLin, coneRes_coneCoprojLin, add_zero]
  · rw [coneProj_d, coneProj_coneCoprojLin, map_add, coneProj_coneInclLin, coneProj_coneCoprojLin,
        zero_add]

omit [LinearOrder I] [Fintype I] [LinearOrder U] [Fintype U] [Unique U] in
theorem coneRes_mem_C {p : ℕ} {m : Finset (I ⊕ₗ U) → M} (hm : m ∈ C (P := P) (I := I ⊕ₗ U) M p) :
    coneRes P U M m ∈ C (P := P) (I := I) M p := fun T hT =>
  hm _ (by rwa [Finset.card_map])

omit [Fintype I] [Fintype U] in
theorem coneProj_mem_C {p : ℕ} {m : Finset (I ⊕ₗ U) → M}
    (hm : m ∈ C (P := P) (I := I ⊕ₗ U) M (p + 1)) :
    coneProj P U M m ∈ C (P := P) (I := I) M p := fun T hT =>
  hm _ (by rw [card_insert_top_map]; omega)

omit [Fintype I] [Fintype U] in
theorem coneProj_eq_zero_of_mem_C_zero {m : Finset (I ⊕ₗ U) → M}
    (hm : m ∈ C (P := P) (I := I ⊕ₗ U) M 0) :
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
theorem coneCoprojLin_mem_C {p : ℕ} {b : Finset I → M} (hb : b ∈ C (P := P) (I := I) M p) :
    coneCoprojLin P U M b ∈ C (P := P) (I := I ⊕ₗ U) M (p + 1) := by
  intro S hS
  by_cases h : top I U ∈ S
  · rw [coneCoprojLin_apply_of_mem _ _ h]
    exact hb _ (fun h' => hS (by rw [← card_down_of_mem h, h']))
  · exact coneCoprojLin_apply_of_notMem _ _ h

noncomputable def coneIncl : ChainMap x M (snoc U x t) M where
  toLinearMap := coneInclLin P U M
  comm := LinearMap.ext fun a => (d_coneInclLin x t M a).symm
  map_C _ _ ha := coneInclLin_mem_C M ha

@[scoped simp] theorem coneIncl_toLinearMap : (coneIncl x t M (U := U)).toLinearMap = coneInclLin P
    U M := rfl

theorem coneProj_mem_Z {p : ℕ} {m : Finset (I ⊕ₗ U) → M} (hm : m ∈ Z (snoc U x t) M (p + 1)) :
    coneProj P U M m ∈ Z x M p :=
  ⟨coneProj_mem_C M hm.1, by
    change d x M (coneProj P U M m) = 0
    rw [← coneProj_d, LinearMap.mem_ker.mp hm.2, map_zero]⟩

theorem coneProj_mem_B {p : ℕ} {m : Finset (I ⊕ₗ U) → M} (hm : m ∈ B (snoc U x t) M (p + 1)) :
    coneProj P U M m ∈ B x M p := by
  obtain ⟨n, hn, rfl⟩ := hm
  exact ⟨coneProj P U M n, coneProj_mem_C M hn, (coneProj_d x t M n).symm⟩

def coneProjH (p : ℕ) : H (snoc U x t) M (p + 1) →ₗ[P] H x M p :=
  Submodule.mapQ _ _ ((coneProj P U M).restrict fun _ hm => coneProj_mem_Z x t M hm)
    fun _ hm => coneProj_mem_B x t M hm

theorem coneProjH_mk (p : ℕ) (z : Z (snoc U x t) M (p + 1)) :
    coneProjH x t M p (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨coneProj P U M z, coneProj_mem_Z x t M z.2⟩ := rfl

@[scoped simp] theorem coneIncl_coe_mapZ {p : ℕ} (z : Z x M p) :
    ((coneIncl x t M (U := U)).toHMap.mapZ p z : Finset (I ⊕ₗ U) → M) = coneInclLin P U M z := rfl

theorem cone_exact₁ (p : ℕ) :
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
      coneTw_of_mem_C t M z₀.2.1, map_smul, smul_smul, ← mul_assoc, neg_one_pow_mul_self, one_mul,
      map_smul]

theorem cone_exact₂ (p : ℕ) :
    Function.Exact ((coneIncl x t M (U := U)).mapH (p + 1)) (coneProjH x t M (U := U) p) := by
  intro h'
  constructor
  · intro h0
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ h'
    rw [coneProjH_mk, H_mk_eq_zero_iff] at h0
    obtain ⟨n, hn, hdn⟩ := h0
    have hm'proj : coneProj P U M
        ((m : Finset (I ⊕ₗ U) → M) - d (snoc U x t) M (coneCoprojLin P U M n)) = 0 := by
      rw [map_sub, coneProj_d, coneProj_coneCoprojLin, hdn]; exact sub_self _
    have hm'd : d (snoc U x t) M
        ((m : Finset (I ⊕ₗ U) → M) - d (snoc U x t) M (coneCoprojLin P U M n)) = 0 := by
      rw [map_sub, d_d, sub_zero]; exact LinearMap.mem_ker.mp m.2.2
    have hm'C : (m : Finset (I ⊕ₗ U) → M) - d (snoc U x t) M (coneCoprojLin P U M n) ∈
        C (P := P) (I := I ⊕ₗ U) M (p + 1) :=
      sub_mem m.2.1 (d_mem_C _ _ (coneCoprojLin_mem_C M hn))
    have haZ : coneRes P U M ((m : Finset (I ⊕ₗ U) → M) - d (snoc U x t) M (coneCoprojLin P U M n))
        ∈
        Z x M (p + 1) := by
      refine ⟨coneRes_mem_C M hm'C, ?_⟩
      change d x M _ = 0
      have h1 := coneRes_d' x t M
          ((m : Finset (I ⊕ₗ U) → M) - d (snoc U x t) M (coneCoprojLin P U M n))
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

theorem cone_surjective₀ : Function.Surjective ((coneIncl x t M (U := U)).mapH 0) := by
  intro h'
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ h'
  have hproj : coneProj P U M (m : Finset (I ⊕ₗ U) → M) = 0
      := coneProj_eq_zero_of_mem_C_zero M m.2.1
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

theorem cone_exact₃ (p : ℕ) :
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
      convert map_zero (coneInclLin P U M)
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
      neg_one_pow_mul_self, one_mul]

variable (P) in
def homog (p : ℕ) : (Finset I → M) →ₗ[P] (Finset I → M) where
  toFun m T := if T.card = p then m T else 0
  map_add' m m' := by funext T; by_cases h : T.card = p <;> simp [h]
  map_smul' c m := by funext T; by_cases h : T.card = p <;> simp [h]

omit [LinearOrder I] [Fintype I] in
theorem homog_mem_C (p : ℕ) (m : Finset I → M) : homog P M p m ∈ C (P := P) (I := I) M p :=
  fun _ hT => ite_eq_right hT

omit [LinearOrder I] in
theorem sum_homog (m : Finset I → M) :
    ∑ p ∈ Finset.range (Fintype.card I + 1), homog P M p m = m := by
  funext T
  rw [Finset.sum_apply, Finset.sum_eq_single T.card]
  · exact ite_eq_left rfl
  · intro p _ hp; exact ite_eq_right (Ne.symm hp)
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ T))) h

omit [LinearOrder I] [LinearOrder J] [Fintype J] [Fintype I] in
theorem map_coneTw [Finite I] (f : (Finset I → M) →ₗ[P] (Finset J → N))
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
theorem coneRes_coneMapLin (f : ChainMap x M y N) (m : Finset (I ⊕ₗ U) → M) :
    coneRes P U N ((coneInclLin P U N ∘ₗ f.toLinearMap ∘ₗ coneRes P U M +
      coneCoprojLin P U N ∘ₗ f.toLinearMap ∘ₗ coneProj P U M) m) = f.toLinearMap
          (coneRes P U M m) := by
  rw [LinearMap.add_apply, map_add, LinearMap.comp_apply, LinearMap.comp_apply, coneRes_coneInclLin,
    LinearMap.comp_apply, LinearMap.comp_apply, coneRes_coneCoprojLin, add_zero]

omit [Fintype U] in
theorem coneProj_coneMapLin (f : ChainMap x M y N) (m : Finset (I ⊕ₗ U) → M) :
    coneProj P U N ((coneInclLin P U N ∘ₗ f.toLinearMap ∘ₗ coneRes P U M +
      coneCoprojLin P U N ∘ₗ f.toLinearMap ∘ₗ coneProj P U M) m) = f.toLinearMap
          (coneProj P U M m) := by
  rw [LinearMap.add_apply, map_add, LinearMap.comp_apply, LinearMap.comp_apply,
      coneProj_coneInclLin,
    LinearMap.comp_apply, LinearMap.comp_apply, coneProj_coneCoprojLin, zero_add]

noncomputable def coneMap (f : ChainMap x M y N) : ChainMap (snoc U x t) M (snoc U y t) N where
  toLinearMap := coneInclLin P U N ∘ₗ f.toLinearMap ∘ₗ coneRes P U M +
    coneCoprojLin P U N ∘ₗ f.toLinearMap ∘ₗ coneProj P U M
  comm := by
    refine LinearMap.ext fun m => cone_ext (P := P) N ?_ ?_
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, coneRes_coneMapLin, coneRes_d', coneRes_d',
          map_add,
        f.comm_apply, map_coneTw t M (f := f.toLinearMap) (fun p _ hm => f.map_C p hm),
            coneRes_coneMapLin,
        coneProj_coneMapLin]
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, coneProj_coneMapLin, coneProj_d, coneProj_d,
          f.comm_apply,
        coneProj_coneMapLin]
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

@[scoped simp] theorem coneMap_toLinearMap_apply (f : ChainMap x M y N) (m : Finset (I ⊕ₗ U) → M) :
    (coneMap x t M f (U := U)).toLinearMap m =
      coneInclLin P U N (f.toLinearMap (coneRes P U M m)) + coneCoprojLin P U N
          (f.toLinearMap (coneProj P U M m)) :=
  rfl

theorem coneMap_mapH_inclMapH (f : ChainMap x M y N) (p : ℕ) (h : H x M p) :
    (coneMap x t M f).mapH p ((coneIncl x t M (U := U)).mapH p h) =
      (coneIncl y t N (U := U)).mapH p (f.mapH p h) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  rw [HMap.mapH_mk, HMap.mapH_mk, HMap.mapH_mk, HMap.mapH_mk]
  congr 1
  apply Subtype.ext
  change (coneMap x t M f (U := U)).toLinearMap (coneInclLin P U M z) = coneInclLin P U N
      (f.toLinearMap z)
  rw [coneMap_toLinearMap_apply, coneRes_coneInclLin, coneProj_coneInclLin, map_zero, map_zero,
      add_zero]

theorem coneProjH_coneMap_mapH (f : ChainMap x M y N) (p : ℕ) (h : H (snoc U x t) M (p + 1)) :
    coneProjH y t N p ((coneMap x t M f).mapH (p + 1) h) = f.mapH p (coneProjH x t M p h) := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  rw [HMap.mapH_mk, coneProjH_mk, coneProjH_mk, HMap.mapH_mk]
  congr 1
  apply Subtype.ext
  change coneProj P U N ((coneMap x t M f (U := U)).toLinearMap m) = f.toLinearMap
      (coneProj P U M m)
  exact coneProj_coneMapLin x M f (m : Finset (I ⊕ₗ U) → M)

end Cone
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section Peel

variable {P : Type u'} [CommRing P] {J : Type} [LinearOrder J] [Fintype J] {I : Type}
    [LinearOrder I] [Fintype I]
variable (y : J → P) (x : I → P) (M : Type v') [AddCommGroup M] [Module P M]

def concat (y : J → P) (x : I → P) : J ⊕ₗ I → P := fun k => Sum.elim y x (ofLex k)

variable (J) in
def inrₗ : I ↪ J ⊕ₗ I := ⟨fun i => toLex (Sum.inr i),
    fun _ _ h => Sum.inr_injective (toLex.injective h)⟩

variable (I) in
def inlₗ' : J ↪ J ⊕ₗ I := ⟨fun j => toLex (Sum.inl j),
    fun _ _ h => Sum.inl_injective (toLex.injective h)⟩

abbrev ModSpan (y : J → P) (M : Type v') [AddCommGroup M] [Module P M] : Type v' :=
  M ⧸ (Ideal.span (Set.range y) • ⊤ : Submodule P M)

omit [CommRing P] [LinearOrder J] [Fintype J] [LinearOrder I] [Fintype I] in
@[scoped simp] theorem concat_inlₗ' (j : J) : concat y x (inlₗ' I j) = y j := rfl
omit [CommRing P] [LinearOrder J] [Fintype J] [LinearOrder I] [Fintype I] in
@[scoped simp] theorem concat_inrₗ (i : I) : concat y x (inrₗ J i) = x i := rfl

omit [LinearOrder J] [LinearOrder I] in
theorem sum_lex₂ {A : Type*} [AddCommMonoid A] (f : J ⊕ₗ I → A) :
    ∑ k, f k = ∑ j, f (inlₗ' I j) + ∑ i, f (inrₗ J i) := by
  rw [← Fintype.sum_equiv toLex (fun k => f (toLex k)) f (fun _ => rfl), Fintype.sum_sum_type]
  rfl

omit [Fintype J] [Fintype I] in
theorem map_insert_inrₗ (i : I) (T : Finset I) :
    (insert i T).map (inrₗ J) = insert (inrₗ J i) (T.map (inrₗ J)) := Finset.map_insert _ _ _

omit [Fintype J] [Fintype I] in
theorem map_insert_inlₗ' (j : J) (T : Finset J) :
    (insert j T).map (inlₗ' I) = insert (inlₗ' I j) (T.map (inlₗ' I)) := Finset.map_insert _ _ _

omit [Fintype J] [Fintype I] in
theorem sgn_inrₗ_map (i : I) (T : Finset I) : sgn P (inrₗ J i) (T.map (inrₗ J)) = sgn P i T := by
  rw [sgn, sgn, Finset.filter_map, Finset.card_map]
  congr 2

omit [Fintype J] [Fintype I] in
theorem sgn_inlₗ'_map (j : J) (T : Finset J) : sgn P (inlₗ' I j) (T.map (inlₗ' I)) = sgn P j T := by
  rw [sgn, sgn, Finset.filter_map, Finset.card_map]
  congr 2

omit [Fintype J] [Fintype I] in
theorem coef_concat_inrₗ_map (i : I) (T : Finset I) :
    coef (concat y x) (inrₗ J i) (T.map (inrₗ J)) = coef x i T := by
  by_cases hi : i ∈ T
  · rw [coef_of_mem _ ((Finset.mem_map' _).mpr hi), coef_of_mem _ hi]
  · rw [coef_of_not_mem _ (fun h => hi ((Finset.mem_map' _).mp h)), coef_of_not_mem _ hi,
        sgn_inrₗ_map,
      concat_inrₗ]

omit [Fintype J] [Fintype I] in
theorem coef_concat_inlₗ'_map (j : J) (T : Finset J) :
    coef (concat y x) (inlₗ' I j) (T.map (inlₗ' I)) = coef y j T := by
  by_cases hj : j ∈ T
  · rw [coef_of_mem _ ((Finset.mem_map' _).mpr hj), coef_of_mem _ hj]
  · rw [coef_of_not_mem _ (fun h => hj ((Finset.mem_map' _).mp h)), coef_of_not_mem _ hj,
        sgn_inlₗ'_map,
      concat_inlₗ']

omit [Fintype J] [Fintype I] in
theorem coef_concat_inlₗ'_smul_mem (j : J) (S : Finset (J ⊕ₗ I)) (v : M) :
    coef (concat y x) (inlₗ' I j) S • v ∈ (Ideal.span (Set.range y) • ⊤ : Submodule P M) := by
  by_cases h : inlₗ' I j ∈ S
  · rw [coef_of_mem _ h, zero_smul]; exact Submodule.zero_mem _
  · rw [coef_of_not_mem _ h, concat_inlₗ', mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem_smul (Ideal.subset_span ⟨j,
        rfl⟩) Submodule.mem_top)

omit [Fintype J] [Fintype I] in
theorem coef_concat_inrₗ_smul_mem (i : I) (S : Finset (J ⊕ₗ I)) (v : M) :
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
        (coef (concat y x) (inlₗ' I j) (T.map (inrₗ J)) • m (insert (inlₗ' I j) (T.map (inrₗ J))))
            = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact coef_concat_inlₗ'_smul_mem y x M j _ _
    rw [d_apply, sum_lex₂, map_add, map_sum, map_sum]
    erw [hcross]
    rw [zero_add]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul, coef_concat_inrₗ_map, map_insert_inrₗ]; rfl
  map_C p m hm T hT := by
    change Submodule.Quotient.mk (m (T.map (inrₗ J))) = 0
    rw [hm _ (by rwa [Finset.card_map]), Submodule.Quotient.mk_zero]

@[scoped simp] theorem peel_apply (m : Finset (J ⊕ₗ I) → M) (T : Finset I) :
    (peel y x M).toLinearMap m T = Submodule.Quotient.mk (m (T.map (inrₗ J))) := rfl

end Peel
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section PeelTop

variable {P : Type u'} [CommRing P] {I : Type} [LinearOrder I] [Fintype I] {J : Type}
    [LinearOrder J] [Fintype J]
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
        (coef (concat x y) (inrₗ I j) (T.map (inlₗ' J)) • m (insert (inrₗ I j) (T.map (inlₗ' J))))
            = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact coef_concat_inrₗ_smul_mem x y M j _ _
    rw [d_apply, sum_lex₂, map_add, map_sum, map_sum]
    erw [hcross]
    rw [add_zero]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul, coef_concat_inlₗ'_map, map_insert_inlₗ']; rfl
  map_C p m hm T hT := by
    change Submodule.Quotient.mk (m (T.map (inlₗ' J))) = 0
    rw [hm _ (by rwa [Finset.card_map]), Submodule.Quotient.mk_zero]

@[scoped simp] theorem peelTop_apply (m : Finset (I ⊕ₗ J) → M) (T : Finset I) :
    (peelTop x y M).toLinearMap m T = Submodule.Quotient.mk (m (T.map (inlₗ' J))) := rfl

end PeelTop
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

end Koszul
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

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

@[scoped simp] theorem castHMap_toLinearMap {x x' : I → P} (h : x = x') :
    (castHMap M h).toLinearMap = LinearMap.id := rfl

theorem castHMap_bijective {x x' : I → P} (h : x = x') (p : ℕ) :
    Function.Bijective ((castHMap M h).mapH p) := by
  subst h
  rw [HMap.mapH_congr (f := castHMap M rfl) (g := HMap.id x M) rfl, HMap.mapH_id]
  exact Function.bijective_id

end CastFamily
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

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
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section PeelStep

variable {P : Type u} [CommRing P]
variable {J : Type} [LinearOrder J] [Fintype J] {I : Type} [LinearOrder I] [Fintype I]
variable {I' : Type} [LinearOrder I'] [Fintype I'] {U : Type} [LinearOrder U] [Fintype U] [Unique U]
variable (y : J → P) (x : I → P) (M : Type v) [AddCommGroup M] [Module P M] (e : I' ⊕ₗ U ≃o I)

variable (J) in
def liftIso (e : I' ⊕ₗ U ≃o I) : (J ⊕ₗ I') ⊕ₗ U ≃o J ⊕ₗ I :=
  (OrderIso.sumLexAssoc J I' U).trans (OrderIso.sumLexCongr (OrderIso.refl J) e)

omit [Fintype J] [Fintype I] [Fintype I'] [Fintype U] [Unique U] in
theorem liftIso_inl_inl (j : J) : liftIso J e (inlₗ U (inlₗ' I' j)) = inlₗ' I j := rfl

omit [Fintype J] [Fintype I] [Fintype I'] [Fintype U] [Unique U] in
theorem liftIso_inl_inr (i : I') : liftIso J e (inlₗ U (inrₗ J i)) = inrₗ J (e (inlₗ U i)) := rfl

omit [Fintype J] [Fintype I] [Fintype I'] [Fintype U] in
theorem liftIso_top : liftIso J e (top (J ⊕ₗ I') U) = inrₗ J (e (top I' U)) := rfl

def shorten : I' → P := fun i => x (e (inlₗ U i))

omit [CommRing P] [Fintype I] [Fintype I'] [Fintype U] in
theorem comp_eq_snoc : x ∘ e = snoc U (shorten x e) (x (e (top I' U))) := by
  funext k
  rcases lex_cases k with ⟨i, rfl⟩ | rfl <;> rfl

omit [LinearOrder J] [Fintype J] [LinearOrder I'] [Fintype I'] in
theorem lex_cases₂ (k : J ⊕ₗ I') : (∃ j, k = inlₗ' I' j) ∨ ∃ i, k = inrₗ J i := by
  obtain ⟨k, rfl⟩ := toLex.surjective k
  rcases k with j | i
  · exact Or.inl ⟨j, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

omit [CommRing P] [Fintype J] [Fintype I] [Fintype I'] [Fintype U] in
theorem concat_comp_liftIso :
    concat y x ∘ liftIso J e = snoc U (concat y (shorten x e)) (x (e (top I' U))) := by
  funext k
  rcases lex_cases k with ⟨k, rfl⟩ | rfl
  · rcases lex_cases₂ k with ⟨j, rfl⟩ | ⟨i, rfl⟩ <;> rfl
  · rfl

omit [Fintype J] [Fintype I] [Fintype I'] [Fintype U] [Unique U] in
theorem map_map_liftIso (T : Finset I') :
    ((T.map (inlₗ U)).map e.toEquiv.toEmbedding).map (inrₗ J) =
      ((T.map (inrₗ J)).map (inlₗ U)).map (liftIso J e).toEquiv.toEmbedding := by
  simp only [Finset.map_map]
  rfl

theorem reindexLin_peel (m : Finset (J ⊕ₗ I) → M) :
    reindexLin P (ModSpan y M) e.toEquiv ((peel y x M).toLinearMap m) =
      (coneMap (concat y (shorten x e)) (x (e (top I' U))) M (peel y (shorten x e) M)
          (U := U)).toLinearMap
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
        peel_apply,
      coneRes_apply, reindexLin_apply]
    conv_lhs => rw [eq_map_down hS, map_map_liftIso]

theorem coneMap_mapH_bijective {c : I' → P} (t : P) {N : Type v} [AddCommGroup N] [Module P N]
    {c₂ : I → P} (f : ChainMap c M c₂ N) (hf : ∀ q, Function.Bijective (f.mapH q)) (q : ℕ) :
    Function.Bijective ((coneMap c t M f (U := U)).mapH q) := by
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
      (cone_exact₁ c t M (U := U) (p + 1)) (cone_exact₂ c t M (U := U) p)
          (cone_exact₃ c t M (U := U) p)
      (cone_exact₁ c₂ t N (U := U) (p + 1)) (cone_exact₂ c₂ t N (U := U) p)
          (cone_exact₃ c₂ t N (U := U) p)
      (hf (p + 1)).2 (hf (p + 1)) (hf p) (hf p).1

theorem reindex_mapH_bijective {K L : Type} [LinearOrder K] [Fintype K] [LinearOrder L] [Fintype L]
    (N : Type v) [AddCommGroup N] [Module P N] (e : K ≃o L) (c : L → P) (p : ℕ) :
    Function.Bijective ((reindex N e c).toHMap.mapH p) :=
  (reindexH N e c p).symm.bijective

omit [Fintype U] in
theorem peel_mapH_bijective_step [Finite U]
    (hIH : ∀ q, Function.Bijective ((peel y (shorten x e) M).mapH q)) (p : ℕ) :
    Function.Bijective ((peel y x M).mapH p) := by
  have := Fintype.ofFinite U
  have key : ((reindex (ModSpan y M) e x).toHMap.comp (peel y x M).toHMap).toLinearMap =
      ((castHMap (ModSpan y M) (comp_eq_snoc x e).symm).comp
        ((coneMap (concat y (shorten x e)) (x (e (top I' U))) M (peel y (shorten x e) M)
            (U := U)).toHMap.comp
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
      ((coneMap (concat y (shorten x e)) (x (e (top I' U))) M (peel y (shorten x e) M)
          (U := U)).toHMap.mapH p) ∘
      ((castHMap M (concat_comp_liftIso y x e)).mapH p) ∘
          ((reindex M (liftIso J e) (concat y x)).toHMap.mapH p)) :=
    (castHMap_bijective _ _ p).comp
        ((coneMap_mapH_bijective M _ (peel y (shorten x e) M) hIH p).comp
      ((castHMap_bijective _ _ p).comp (reindex_mapH_bijective M (liftIso J e) (concat y x) p)))
  rw [← hfun] at hrhs
  exact (Function.Bijective.of_comp_iff' (reindex_mapH_bijective (ModSpan y M) e x p) _).mp hrhs

end PeelStep
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section PeelMain

variable {P : Type u} [CommRing P]
variable {J : Type} [LinearOrder J] [Fintype J] {I : Type} [LinearOrder I] [Fintype I]
variable (y : J → P) (x : I → P) (M : Type v) [AddCommGroup M] [Module P M]

omit [CommRing P] [Fintype J] [Fintype I] in
theorem concat_eq_comp_sumLexEmpty [IsEmpty I] :
    concat y x = y ∘ (OrderIso.sumLexEmpty : J ⊕ₗ I ≃o J) := by
  funext k
  obtain ⟨k, rfl⟩ := toLex.surjective k
  rcases k with j | i
  · rfl
  · exact isEmptyElim i

theorem peel_mapH_bijective_of_isEmpty [IsEmpty I] (hy : ∀ p,
    0 < p → Subsingleton (H y M p)) (p : ℕ) :
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
    have hle : (Ideal.span (Set.range y) • ⊤ : Submodule P M) ≤ Ideal.span (Set.range (concat y x))
        • ⊤ :=
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
        fun T hT => Pi.single_eq_of_ne (M := fun _ => M) (fun h : T = ∅ => hT (by
          rw [h, Finset.card_empty])) v
      let z₀ : Z (concat y x) M 0 := ⟨Pi.single ∅ v, hC,
          LinearMap.mem_ker.mpr (d_eq_zero_of_mem_C_zero _ M hC)⟩
      refine ⟨Submodule.Quotient.mk z₀, (HZeroEquiv x (ModSpan y M)).injective ?_⟩
      rw [HMap.mapH_mk, HZeroEquiv_mk, HZeroEquiv_mk, HMap.coe_mapZ, ChainMap.toHMap_toLinearMap,
          peel_apply,
        Finset.map_empty, ← hv]
      exact congrArg _ (congrArg _ (Pi.single_eq_same (M := fun _ : Finset (J ⊕ₗ I) => M) ∅ v))

theorem peel_mapH_bijective_aux (hy : ∀ p, 0 < p → Subsingleton (H y M p)) (n : ℕ) :
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

theorem peel_bijective (hy : ∀ p, 0 < p → Subsingleton (H y M p)) (p : ℕ) :
    Function.Bijective ((peel y x M).mapH p) :=
  peel_mapH_bijective_aux y M hy (Fintype.card I) x rfl p

end PeelMain
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section PeelTopProof

variable {P : Type u} [CommRing P]
variable {I : Type} [LinearOrder I] [Fintype I] {J : Type} [LinearOrder J] [Fintype J]
variable (x : I → P) (y : J → P) (M : Type v) [AddCommGroup M] [Module P M]

omit [CommRing P] [Fintype I] [Fintype J] in
theorem concat_dual :
    (concat x y ∘ (OrderDual.ofDual : (I ⊕ₗ J)ᵒᵈ ≃ I ⊕ₗ J)) ∘
        (OrderIso.sumLexDualAntidistrib I J).symm =
      concat (y ∘ OrderDual.ofDual) (x ∘ OrderDual.ofDual) := by
  funext k
  rcases lex_cases₂ k with ⟨j, rfl⟩ | ⟨i, rfl⟩ <;> rfl

omit [Fintype I] [Fintype J] in
theorem map_dual_chain (T : Finset I) :
    (((T.map (OrderDual.toDual : I ≃ Iᵒᵈ).toEmbedding).map (inrₗ Jᵒᵈ)).map
        (OrderIso.sumLexDualAntidistrib I J).symm.toEquiv.toEmbedding).map
      (OrderDual.ofDual : (I ⊕ₗ J)ᵒᵈ ≃ I ⊕ₗ J).toEmbedding = T.map (inlₗ' J) := by
  simp only [Finset.map_map]
  rfl

theorem peelTop_eq_reverse (m : Finset (I ⊕ₗ J) → M) :
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

theorem peelTop_bijective (hy : ∀ p, 0 < p → Subsingleton (H y M p)) (p : ℕ) :
    Function.Bijective ((peelTop x y M).mapH p) := by
  have hy' : ∀ q, 0 < q → Subsingleton (H (y ∘ OrderDual.ofDual) M q) := fun q hq =>
    haveI := hy q hq
    (reverseH M y q).toEquiv.subsingleton
  let big : HMap (concat x y) M x (ModSpan (y ∘ OrderDual.ofDual) M) :=
    (reverseInv (ModSpan (y ∘ OrderDual.ofDual) M) x).comp
      ((peel (y ∘ OrderDual.ofDual) (x ∘ OrderDual.ofDual) M).toHMap.comp
        ((castHMap M (concat_dual x y)).comp
          ((reindex M (OrderIso.sumLexDualAntidistrib I J).symm
              (concat x y ∘ OrderDual.ofDual)).toHMap.comp
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
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

end Koszul
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

namespace Koszul

open Finset ExteriorAlgebra Set.powersetCard
open KoszulComplex (familyComplex familyFunctional familyFunctional_single)

universe u v u' v'

section Exterior

variable {I : Type} [LinearOrder I] {n : ℕ}

def eraseNth (s : Set.powersetCard I (n + 1)) (k : Fin (n + 1)) : Set.powersetCard I n :=
  ofFinEmbEquiv ((Fin.succAboveOrderEmb k).trans (ofFinEmbEquiv.symm s))

theorem ofFinEmbEquiv_symm_eraseNth (s : Set.powersetCard I (n + 1)) (k : Fin (n + 1)) :
    ofFinEmbEquiv.symm (eraseNth s k) = (Fin.succAboveOrderEmb k).trans (ofFinEmbEquiv.symm s) :=
  Equiv.symm_apply_apply _ _

theorem coe_ofFinEmbEquiv_symm_eraseNth (s : Set.powersetCard I (n + 1)) (k : Fin (n + 1)) :
    ⇑(ofFinEmbEquiv.symm (eraseNth s k)) = Fin.removeNth k ⇑(ofFinEmbEquiv.symm s) := by
  rw [ofFinEmbEquiv_symm_eraseNth]; rfl

theorem mem_eraseNth_iff (s : Set.powersetCard I (n + 1)) (k : Fin (n + 1)) (i : I) :
    i ∈ eraseNth s k ↔ i ∈ s ∧ i ≠ ofFinEmbEquiv.symm s k := by
  rw [← mem_range_ofFinEmbEquiv_symm_iff_mem, coe_ofFinEmbEquiv_symm_eraseNth,
    ← mem_range_ofFinEmbEquiv_symm_iff_mem]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨_, rfl⟩, fun h => Fin.succAbove_ne k j ((ofFinEmbEquiv.symm s).injective h)⟩
  · rintro ⟨⟨j, rfl⟩, hne⟩
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq (fun h => hne (congrArg _ h))
    exact ⟨j', rfl⟩

theorem val_eraseNth (s : Set.powersetCard I (n + 1)) (k : Fin (n + 1)) :
    (eraseNth s k : Finset I) = (s : Finset I).erase (ofFinEmbEquiv.symm s k) := by
  ext i
  rw [Finset.mem_erase, mem_coe_iff, mem_eraseNth_iff, mem_coe_iff, and_comm]

theorem card_filter_lt_ofFinEmbEquiv_symm (s : Set.powersetCard I n) (k : Fin n) :
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

end Exterior
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section Chains

variable {P : Type u} [CommRing P] {I : Type} (M : Type v) [AddCommGroup M] [Module P M]

theorem single_mem_C [DecidableEq I] {p : ℕ} (S : Finset I) (hS : S.card = p) (m : M) :
    Pi.single S m ∈ C (P := P) (I := I) M p :=
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

theorem C.equivFun_apply {p : ℕ} (m : C (P := P) (I := I) M p) (s : Set.powersetCard I p) :
    C.equivFun M p m s = (m : Finset I → M) s := rfl

theorem C.equivFun_symm_apply {p : ℕ} (c : Set.powersetCard I p → M) (T : Finset I)
    (hT : T.card = p) :
    ((C.equivFun (P := P) M p).symm c : Finset I → M) T = c ⟨T, mem_iff.mpr hT⟩ := dite_eq_left hT

end Chains
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section Basis

variable {P : Type u} [CommRing P] {I : Type} [LinearOrder I] [Fintype I]

variable (P I)

noncomputable def toExterior (p : ℕ) : C (P := P) (I := I) P p ≃ₗ[P] ⋀[P]^p (I → P) :=
  (C.equivFun P p).trans ((Pi.basisFun P I).exteriorPower p).equivFun.symm

variable {P I}

theorem toExterior_apply {p : ℕ} (m : C (P := P) (I := I) P p) :
    toExterior P I p m = ∑ s : Set.powersetCard I p, (m : Finset I → P) s •
        (Pi.basisFun P I).exteriorPower p s := by
  rw [toExterior, LinearEquiv.trans_apply, Module.Basis.equivFun_symm_apply]; rfl

theorem toExterior_symm_apply {p : ℕ} (ω : ⋀[P]^p (I → P)) (T : Finset I) (hT : T.card = p) :
    ((toExterior P I p).symm ω : Finset I → P) T = ((Pi.basisFun P I).exteriorPower p).repr ω ⟨T,
        mem_iff.mpr hT⟩ := by
  rw [toExterior, LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
    C.equivFun_symm_apply _ T hT, Module.Basis.equivFun_apply]

theorem toExterior_symm_apply_of_card_ne {p : ℕ} (ω : ⋀[P]^p (I → P)) (T : Finset I)
    (hT : T.card ≠ p) :
    ((toExterior P I p).symm ω : Finset I → P) T = 0 :=
  ((toExterior P I p).symm ω).2 T hT

theorem toExterior_single (S : Finset I) {p : ℕ} (hS : S.card = p) :
    toExterior P I p ⟨Pi.single S 1, single_mem_C P S hS 1⟩ = (Pi.basisFun P I).exteriorPower p ⟨S,
        mem_iff.mpr hS⟩ := by
  rw [toExterior_apply, Finset.sum_eq_single ⟨S, mem_iff.mpr hS⟩]
  · simp
  · intro s _ hs
    change (Pi.single S (1 : P) : Finset I → P) s • _ = 0
    rw [Pi.single_eq_of_ne (fun h => hs (Subtype.ext h)), zero_smul]
  · exact fun h => (h (Finset.mem_univ _)).elim

theorem toExterior_symm_basis {p : ℕ} (s : Set.powersetCard I p) :
    (toExterior P I p).symm ((Pi.basisFun P I).exteriorPower p s) =
      ⟨Pi.single (s : Finset I) 1, single_mem_C P (s : Finset I) (mem_iff.mp s.prop) 1⟩ := by
  rw [LinearEquiv.symm_apply_eq, toExterior_single (s : Finset I) (mem_iff.mp s.prop)]

-- The differential of `familyComplex P x` from degree `p + 1` to degree `p`, as a linear map
-- between the exterior powers that are its terms.
abbrev familyComplexD (x : I → P) (p : ℕ) : ⋀[P]^(p + 1) (I → P) →ₗ[P] ⋀[P]^p (I → P) :=
  ((familyComplex P x).d (p + 1) p).hom

omit [LinearOrder I] in
theorem familyComplexD_apply (x : I → P) (p : ℕ) (ω : ⋀[P]^(p + 1) (I → P)) :
    familyComplexD x p ω = KoszulComplex.differential P (I → P) (familyFunctional P x) p ω :=
  congrArg (fun φ => ModuleCat.Hom.hom φ ω)
    (KoszulComplex.complex_d_succ P (I → P) (familyFunctional P x) p)

theorem familyDifferential_basisFun (x : I → P) {p : ℕ} (s : Set.powersetCard I (p + 1)) :
    KoszulComplex.differential P (I → P) (familyFunctional P x) p
        ((Pi.basisFun P I).exteriorPower (p + 1) s) =
      ∑ k : Fin (p + 1), ((-1 : P) ^ (k : ℕ) * x (ofFinEmbEquiv.symm s k)) •
        (Pi.basisFun P I).exteriorPower p (eraseNth s k) := by
  simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family, Function.comp_def,
    Pi.basisFun_apply]
  rw [KoszulComplex.familyDifferential_apply_basis P x p (ofFinEmbEquiv.symm s)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coe_ofFinEmbEquiv_symm_eraseNth]
  rfl

omit [Fintype I] in
theorem ofFinEmbEquiv_symm_mem {p : ℕ} (s : Set.powersetCard I p) (k : Fin p) :
    ofFinEmbEquiv.symm s k ∈ (s : Finset I) :=
  mem_coe_iff.mpr ((mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨k, rfl⟩)

theorem eq_sum_single {p : ℕ} {m : Finset I → P} (hm : m ∈ C (P := P) (I := I) P p) :
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
    rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h : T = ↑s => hT (by
      rw [h]; exact mem_iff.mp s.prop)),
      smul_zero]

theorem d_single (x : I → P) {p : ℕ} (s : Set.powersetCard I (p + 1)) :
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

theorem toExterior_d (x : I → P) {p : ℕ} (m : Finset I → P)
    (hm : m ∈ C (P := P) (I := I) P (p + 1)) :
    toExterior P I p ⟨d x P m, d_mem_C x P hm⟩ =
      familyComplexD x p (toExterior P I (p + 1) ⟨m, hm⟩) := by
  rw [familyComplexD_apply, ← LinearEquiv.eq_symm_apply]
  apply Subtype.ext
  change d x P m = _
  rw [toExterior_apply, map_sum, map_sum]
  simp only [map_smul, familyDifferential_basisFun, map_sum, toExterior_symm_basis,
    Submodule.coe_sum, Submodule.coe_smul]
  conv_lhs => rw [eq_sum_single hm, map_sum]
  simp only [map_smul, d_single]

theorem d_toExterior_symm (x : I → P) {p : ℕ} (ω : ⋀[P]^(p + 1) (I → P)) :
    d x P ((toExterior P I (p + 1)).symm ω) =
      (toExterior P I p).symm (familyComplexD x p ω) := by
  have h := toExterior_d x ((toExterior P I (p + 1)).symm ω) ((toExterior P I (p + 1)).symm ω).2
  rw [Subtype.coe_eta, LinearEquiv.apply_symm_apply, ← LinearEquiv.eq_symm_apply] at h
  exact congrArg Subtype.val h

end Basis
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section Cycle

variable {P : Type u} [CommRing P]

omit [CommRing P] in
theorem concat_inl {J I : Type} [LinearOrder J] [LinearOrder I] (f : J → P) (x : I → P)
    (j : J) : concat f x (toLex (Sum.inl j)) = f j := rfl

omit [CommRing P] in
theorem concat_inr {J I : Type} [LinearOrder J] [LinearOrder I] (f : J → P) (x : I → P)
    (i : I) : concat f x (toLex (Sum.inr i)) = x i := rfl

variable {n : ℕ}

def inlOrderEmb (n : ℕ) : Fin n ↪o Fin n ⊕ₗ Fin n :=
  OrderEmbedding.ofStrictMono (fun j => toLex (Sum.inl j)) fun _ _ h => Sum.Lex.inl_lt_inl_iff.mpr h

def inrOrderEmb (n : ℕ) : Fin n ↪o Fin n ⊕ₗ Fin n :=
  OrderEmbedding.ofStrictMono (fun i => toLex (Sum.inr i)) fun _ _ h => Sum.Lex.inr_lt_inr_iff.mpr h

theorem inlOrderEmb_apply (j : Fin n) : inlOrderEmb n j = toLex (Sum.inl j) := rfl
theorem inrOrderEmb_apply (i : Fin n) : inrOrderEmb n i = toLex (Sum.inr i) := rfl

def inlBlock (n : ℕ) : Finset (Fin n ⊕ₗ Fin n) := Finset.univ.map (inlₗ' (Fin n))

def inrBlock (n : ℕ) : Finset (Fin n ⊕ₗ Fin n) := Finset.univ.map (inrₗ (Fin n))

theorem card_inlBlock (n : ℕ) : (inlBlock n).card = n := by simp [inlBlock]
theorem card_inrBlock (n : ℕ) : (inrBlock n).card = n := by simp [inrBlock]

theorem ofFinEmbEquiv_symm_inlBlock :
    ofFinEmbEquiv.symm ⟨inlBlock n, mem_iff.mpr (card_inlBlock n)⟩ = inlOrderEmb n := by
  rw [ofFinEmbEquiv_symm_apply]
  exact (Finset.orderEmbOfFin_unique' (card_inlBlock n) fun j => Finset.mem_map_of_mem _
      (Finset.mem_univ j)).symm

theorem ofFinEmbEquiv_symm_inrBlock :
    ofFinEmbEquiv.symm ⟨inrBlock n, mem_iff.mpr (card_inrBlock n)⟩ = inrOrderEmb n := by
  rw [ofFinEmbEquiv_symm_apply]
  exact (Finset.orderEmbOfFin_unique' (card_inrBlock n) fun j => Finset.mem_map_of_mem _
      (Finset.mem_univ j)).symm

def cycleVec (g : Matrix (Fin n) (Fin n) P) (j : Fin n) : Fin n ⊕ₗ Fin n → P :=
  Pi.single (toLex (Sum.inl j)) 1 - ∑ i, g j i • Pi.single (toLex (Sum.inr i)) 1

theorem familyFunctional_concat_cycleVec (f x : Fin n → P) (g : Matrix (Fin n) (Fin n) P)
    (hf : ∀ j, f j = ∑ i, g j i * x i) (j : Fin n) :
    familyFunctional P (concat f x) (cycleVec g j) = 0 := by
  rw [cycleVec, map_sub, map_sum, familyFunctional_single, concat_inl, hf, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, familyFunctional_single, concat_inr, smul_eq_mul]

noncomputable def tateCycle (g : Matrix (Fin n) (Fin n) P) : ⋀[P]^n (Fin n ⊕ₗ Fin n → P) :=
  exteriorPower.ιMulti P n (cycleVec g)

theorem familyComplexD_tateCycle (f x : Fin (n + 1) → P)
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) P) (hf : ∀ j, f j = ∑ i, g j i * x i) :
    familyComplexD (concat f x) n (tateCycle g) = 0 := by
  rw [familyComplexD_apply, tateCycle, KoszulComplex.differential_apply_ιMulti]
  simp [familyFunctional_concat_cycleVec f x g hf]

noncomputable def tateChain (g : Matrix (Fin n) (Fin n) P) : Finset (Fin n ⊕ₗ Fin n) → P :=
  (toExterior P (Fin n ⊕ₗ Fin n) n).symm (tateCycle g)

theorem tateChain_mem_C (g : Matrix (Fin n) (Fin n) P) : tateChain g ∈ C (P := P) P n :=
  ((toExterior P (Fin n ⊕ₗ Fin n) n).symm (tateCycle g)).2

theorem d_tateChain (f x : Fin n → P) (g : Matrix (Fin n) (Fin n) P) (hf : ∀ j, f j = ∑ i,
    g j i * x i) :
    d (concat f x) P (tateChain g) = 0 := by
  cases n with
  | zero =>
    funext T
    rw [d_apply]
    exact Finset.sum_eq_zero fun i _ => isEmptyElim (ofLex i : Fin 0 ⊕ Fin 0)
  | succ n =>
    rw [tateChain, d_toExterior_symm, familyComplexD_tateCycle f x g hf, map_zero]
    rfl

theorem tateChain_apply (g : Matrix (Fin n) (Fin n) P) (T : Finset (Fin n ⊕ₗ Fin n))
    (hT : T.card = n) :
    tateChain g T = (Matrix.of fun i j => cycleVec g i (ofFinEmbEquiv.symm ⟨T,
        mem_iff.mpr hT⟩ j)).det := by
  rw [tateChain, toExterior_symm_apply _ T hT, exteriorPower.basis_repr_apply, tateCycle,
    exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [Module.Basis.coord_apply, Pi.basisFun_repr]

theorem cycleVec_inl (g : Matrix (Fin n) (Fin n) P) (i j : Fin n) :
    cycleVec g i (toLex (Sum.inl j)) = (1 : Matrix (Fin n) (Fin n) P) i j := by
  simp [cycleVec, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem cycleVec_inr (g : Matrix (Fin n) (Fin n) P) (i j : Fin n) :
    cycleVec g i (toLex (Sum.inr j)) = -g i j := by
  simp [cycleVec, Pi.single_apply]

theorem tateChain_inlBlock (g : Matrix (Fin n) (Fin n) P) : tateChain g (inlBlock n) = 1 := by
  rw [tateChain_apply g _ (card_inlBlock n), ofFinEmbEquiv_symm_inlBlock]
  have : (Matrix.of fun i j => cycleVec g i (inlOrderEmb n j)) = 1 := by
    ext i j; exact cycleVec_inl g i j
  rw [this, Matrix.det_one]

theorem tateChain_inrBlock (g : Matrix (Fin n) (Fin n) P) : tateChain g (inrBlock n) = (-1) ^ n *
    g.det := by
  rw [tateChain_apply g _ (card_inrBlock n), ofFinEmbEquiv_symm_inrBlock]
  have : (Matrix.of fun i j => cycleVec g i (inrOrderEmb n j)) = -g := by
    ext i j; exact cycleVec_inr g i j
  rw [this, Matrix.det_neg, Fintype.card_fin]

end Cycle
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section Reg

variable {P : Type u} [CommRing P] {I : Type} [LinearOrder I] [Fintype I] (x : I → P)

theorem subsingleton_H_of_isWeaklyRegular_of_step
    (step : ∀ (N : Type v) [AddCommGroup N] [Module P N] (r : P), r ∈ Ideal.span (Set.range x) →
      IsSMulRegular N r → ∀ p : ℕ, Subsingleton (H x (QuotSMulTop r N) (p + 1)) → Subsingleton
          (H x N p))
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
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section Func

open CategoryTheory

variable {P : Type u} [CommRing P] {I : Type} [LinearOrder I] [Fintype I] (x : I → P)
variable {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module P M₁] [AddCommGroup M₂] [Module P M₂]
  [AddCommGroup M₃] [Module P M₃] (φ : M₁ →ₗ[P] M₂) (ψ : M₂ →ₗ[P] M₃)

theorem mapC_ofLinearMap_injective (hφ : Function.Injective φ) (p : ℕ) :
    Function.Injective ((ChainMap.ofLinearMap x φ).mapC p) := fun _ _ h =>
  Subtype.ext (funext fun T => hφ (congr_fun (congrArg Subtype.val h) T))

theorem mapC_ofLinearMap_surjective (hψ : Function.Surjective ψ) (p : ℕ) :
    Function.Surjective ((ChainMap.ofLinearMap x ψ).mapC p) := fun m₃ => by
  refine ⟨⟨fun T => if T.card = p then Function.surjInv hψ ((m₃ : Finset I → M₃) T) else 0,
    fun T hT => ite_eq_right hT⟩, Subtype.ext (funext fun T => ?_)⟩
  change ψ (if T.card = p then Function.surjInv hψ ((m₃ : Finset I → M₃) T) else 0) = _
  by_cases hT : T.card = p
  · rw [ite_eq_left hT]; exact Function.surjInv_eq hψ _
  · rw [ite_eq_right hT, map_zero, m₃.2 T hT]

theorem mapC_ofLinearMap_exact (hex : Function.Exact φ ψ) (p : ℕ) :
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

theorem mapSC_shortExact (h : ψ ∘ₗ φ = 0) (hφ : Function.Injective φ) (hψ : Function.Surjective ψ)
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
theorem smulSC_shortExact (hr : IsSMulRegular N r) : (smulSC x (N := N) r).ShortExact :=
  mapSC_shortExact x _ _ _ (fun _ _ h => hr h) (Submodule.mkQ_surjective _) fun n => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨m, -, rfl⟩; exact ⟨m, rfl⟩
    · rintro ⟨m, rfl⟩; exact ⟨m, Submodule.mem_top, rfl⟩

theorem mapH_ofLinearMap_smul_id (p : ℕ) (h : H x N p) :
    (ChainMap.ofLinearMap x (r • LinearMap.id : N →ₗ[P] N)).mapH p h = r • h := by
  induction h using Submodule.Quotient.induction_on with
  | H z =>
    rw [ChainMap.mapH, HMap.mapH_mk, ← Submodule.Quotient.mk_smul]
    rfl

theorem subsingleton_H_of_subsingleton_H_quotSMulTop (hr : IsSMulRegular N r) {p : ℕ}
    (htpy : ∀ h : H x N p, r • h = 0) (hq : Subsingleton (H x (QuotSMulTop r N) (p + 1))) :
    Subsingleton (H x N p) := by
  have hS := smulSC_shortExact x r hr
  have hex := hS.homology_exact₁ (p + 1) p rfl
  have hzero : HomologicalComplex.homologyMap (smulSC x (N := N) r).f p = 0 := by
    change HomologicalComplex.homologyMap
        (ChainMap.ofLinearMap x (r • LinearMap.id : N →ₗ[P] N)).toHom p = 0
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

theorem subsingleton_H_of_isWeaklyRegular (M : Type v) [AddCommGroup M] [Module P M] {r : ℕ}
    (y : Fin r → P)
    (hy : RingTheory.Sequence.IsWeaklyRegular M (List.ofFn y)) (hyx : ∀ k,
        y k ∈ Ideal.span (Set.range x))
    (p : ℕ) (hp : Fintype.card I < p + r) : Subsingleton (H x M p) :=
  subsingleton_H_of_isWeaklyRegular_of_step x
    (fun N _ _ a ha hreg q hq => subsingleton_H_of_subsingleton_H_quotSMulTop x a hreg
      (fun h => smul_H_eq_zero_of_mem_span a ha h) hq)
    M (List.ofFn y) hy (fun a ha => by obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha; exact hyx k) p
    (by rwa [List.length_ofFn])

theorem subsingleton_H_of_isWeaklyRegular_of_card_eq (M : Type v) [AddCommGroup M] [Module P M]
    {r : ℕ}
    (y : Fin r → P) (hy : RingTheory.Sequence.IsWeaklyRegular M (List.ofFn y))
    (hyx : ∀ k, y k ∈ Ideal.span (Set.range x)) (hr : r = Fintype.card I) (p : ℕ) (hp : 0 < p) :
    Subsingleton (H x M p) :=
  subsingleton_H_of_isWeaklyRegular x M y hy hyx p (by omega)

end Func
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

section Wiebe

variable {P : Type u} [CommRing P] {n : ℕ} (x f : Fin n → P) (g : Matrix (Fin n) (Fin n) P)

theorem mem_span_of_eq (hf : ∀ i, f i = ∑ j,
    g i j * x j) (i : Fin n) : f i ∈ Ideal.span (Set.range x) := by
  rw [hf i]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

theorem span_le_span_of_eq (hf : ∀ i, f i = ∑ j, g i j * x j) :
    Ideal.span (Set.range f) ≤ Ideal.span (Set.range x) :=
  Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact mem_span_of_eq x f g hf i)

theorem mul_det_mem_span (hf : ∀ i, f i = ∑ j, g i j * x j) (j : Fin n) :
    x j * g.det ∈ Ideal.span (Set.range f) := by
  have hgx : g.mulVec x = f := funext fun i => (hf i).symm
  have key : x j * g.det = g.adjugate.mulVec f j := by
    rw [← hgx, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [key]
  change ∑ i, g.adjugate j i * f i ∈ _
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

theorem mul_det_mem_span_of_mem (hf : ∀ i, f i = ∑ j, g i j * x j) {a : P}
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

theorem coe_wiebeMap_mk (hf : ∀ i, f i = ∑ j, g i j * x j) (a : P) :
    (wiebeMap x f g hf (Ideal.Quotient.mk _ a) : P ⧸ Ideal.span (Set.range f)) =
      Ideal.Quotient.mk _ (a * g.det) := by
  change ((LinearMap.toSpanSingleton P _ ⟨_, mk_det_mem_torsionBySet x f g hf⟩ a :
    Submodule.torsionBySet P (P ⧸ Ideal.span (Set.range f)) (Set.range x)) : P ⧸ Ideal.span
        (Set.range f)) = _
  rw [LinearMap.toSpanSingleton_apply, Submodule.coe_smul, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq,
    map_mul]

theorem wiebeMap_mk_eq_zero_iff (hf : ∀ i, f i = ∑ j, g i j * x j) (a : P) :
    wiebeMap x f g hf (Ideal.Quotient.mk _ a) = 0 ↔ a * g.det ∈ Ideal.span (Set.range f) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coe_wiebeMap_mk x f g hf a]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩

theorem colon_span_eq_of_surjective (hf : ∀ i, f i = ∑ j, g i j * x j)
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

theorem colon_det_eq_of_injective (hf : ∀ i, f i = ∑ j, g i j * x j)
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

theorem det_not_mem_span_of_injective (hf : ∀ i, f i = ∑ j, g i j * x j)
    (hi : Function.Injective (wiebeMap x f g hf)) (hx : Ideal.span (Set.range x) ≠ ⊤) :
    g.det ∉ Ideal.span (Set.range f) := by
  intro h
  apply hx
  rw [Ideal.eq_top_iff_one]
  exact (colon_det_eq_of_injective x f g hf hi).le (Ideal.mem_colon_span_singleton.mpr (by
    rwa [one_mul]))

end Wiebe
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

end Koszul
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

namespace Koszul

open Finset

universe u v

section WiebeAssembly

variable {P : Type u} [CommRing P] {n : ℕ} (x f : Fin n → P) (g : Matrix (Fin n) (Fin n) P)

theorem mem_smul_top_iff {I : Ideal P} {a : P} : a ∈ I • (⊤ : Submodule P P) ↔ a ∈ I := by
  rw [show I • (⊤ : Submodule P P) = I * ⊤ from rfl, Ideal.mul_top]

noncomputable def tateZ (hf : ∀ i, f i = ∑ j,
    g i j * x j) : Z (concat f x) P (Fintype.card (Fin n)) :=
  ⟨tateChain g, ⟨by rw [Fintype.card_fin]; exact tateChain_mem_C g,
    LinearMap.mem_ker.mpr (d_tateChain f x g hf)⟩⟩

@[scoped simp] theorem coe_tateZ (hf : ∀ i, f i = ∑ j, g i j * x j) :
    ((tateZ x f g hf : Z (concat f x) P _) : Finset (Fin n ⊕ₗ Fin n) → P) = tateChain g := rfl

noncomputable def tateClass (hf : ∀ i, f i = ∑ j,
    g i j * x j) : H (concat f x) P (Fintype.card (Fin n)) :=
  Submodule.Quotient.mk (tateZ x f g hf)

theorem coe_HTopEquiv_peel_smul_tateClass (hf : ∀ i, f i = ∑ j, g i j * x j) (a : P) :
    ((HTopEquiv x (ModSpan f P) ((peel f x P).mapH _ (a • tateClass x f g hf)) :
        annihilatedBy x (ModSpan f P)) : ModSpan f P) =
      Submodule.Quotient.mk (a * ((-1) ^ n * g.det)) := by
  rw [map_smul, map_smul, Submodule.coe_smul, tateClass, ChainMap.mapH, HMap.mapH_mk, HTopEquiv_mk,
    HMap.coe_mapZ, ChainMap.toHMap_toLinearMap, coe_tateZ]
  change a • (Submodule.Quotient.mk (tateChain g (inrBlock n)) : ModSpan f P) = _
  rw [tateChain_inrBlock, ← Submodule.Quotient.mk_smul]
  rfl

theorem coe_HTopEquiv_peelTop_smul_tateClass (hf : ∀ i, f i = ∑ j, g i j * x j) (a : P) :
    ((HTopEquiv f (ModSpan x P) ((peelTop f x P).mapH _ (a • tateClass x f g hf)) :
        annihilatedBy f (ModSpan x P)) : ModSpan x P) =
      Submodule.Quotient.mk a := by
  rw [map_smul, map_smul, Submodule.coe_smul, tateClass, ChainMap.mapH, HMap.mapH_mk, HTopEquiv_mk,
    HMap.coe_mapZ, ChainMap.toHMap_toLinearMap, coe_tateZ]
  change a • (Submodule.Quotient.mk (tateChain g (inlBlock n)) : ModSpan x P) = _
  rw [tateChain_inlBlock, ← Submodule.Quotient.mk_smul]
  exact congrArg _ (mul_one a)

theorem exists_eq_smul_tateClass (hf : ∀ i, f i = ∑ j, g i j * x j)
    (hxK : ∀ p, 0 < p → Subsingleton (H x P p)) (h : H (concat f x) P (Fintype.card (Fin n))) :
    ∃ b : P, h = b • tateClass x f g hf := by
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _
    ((HTopEquiv f (ModSpan x P) ((peelTop f x P).mapH (Fintype.card (Fin n)) h) :
      annihilatedBy f (ModSpan x P)) : ModSpan x P)
  refine ⟨b, (peelTop_bijective f x P hxK (Fintype.card (Fin n))).1
    ((HTopEquiv f (ModSpan x P)).injective (Subtype.ext ?_))⟩
  rw [coe_HTopEquiv_peelTop_smul_tateClass]
  exact hb.symm

theorem wiebeMap_bijective (hf : ∀ i, f i = ∑ j, g i j * x j)
    (hxK : ∀ p, 0 < p → Subsingleton (H x P p)) (hfK : ∀ p, 0 < p → Subsingleton (H f P p)) :
    Function.Bijective (wiebeMap x f g hf) := by
  have hu : (-1 : P) ^ n * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  let E₁ : H (concat f x) P (Fintype.card (Fin n)) ≃ₗ[P] annihilatedBy x (ModSpan f P) :=
    (LinearEquiv.ofBijective _ (peel_bijective f x P hfK _)).trans (HTopEquiv x (ModSpan f P))
  have hE₁ : ∀ a : P, ((E₁ (a • tateClass x f g hf) : annihilatedBy x (ModSpan f P)) : ModSpan f P)
      =
      Submodule.Quotient.mk (a * ((-1) ^ n * g.det)) := fun a =>
    coe_HTopEquiv_peel_smul_tateClass x f g hf a
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [wiebeMap_mk_eq_zero_iff] at hq
    have h1 : E₁ (((-1) ^ n * a) • tateClass x f g hf) = 0 := by
      apply Subtype.ext
      rw [hE₁, Submodule.coe_zero, Submodule.Quotient.mk_eq_zero, mem_smul_top_iff,
        show (-1 : P) ^ n * a * ((-1) ^ n * g.det) = ((-1 : P) ^ n * (-1) ^ n) * (a * g.det) by
          ring, hu,
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
    rw [coe_wiebeMap_mk, ← hs, Ideal.Quotient.eq,
        show b * (-1) ^ n * g.det - s = -(s - b * ((-1) ^ n * g.det)) by ring]
    exact neg_mem hb'

end WiebeAssembly
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

end Koszul
open scoped ColonSpanDet.Koszul.HMap ColonSpanDet.Koszul.ChainMap ColonSpanDet.Koszul

end ColonSpanDet

@[expose] public section

/-- **Colon ideals for a square matrix relation.** Let `P` be a commutative ring, let `x` and `f` be
`n`-tuples of elements of `P`, and let `g` be an `n × n` matrix over `P` with `f = g • x`.
Suppose the ideal `(f)` contains a weakly regular sequence of length `n`. Then
`(f) : (x) = (f) + (det g)` and `(f) : (det g) = (x)`.

Source: A. Corso, C. Polini and W. V. Vasconcelos, *Links of prime ideals*, Math. Proc.
Cambridge Philos. Soc. 115 (1994), 431–436, Theorem 2.5 (b) and (c), which it attributes to
D. G. Northcott, *A homological investigation of a certain residual ideal*, Math. Ann. 150
(1963), 99–110. It states both identities for a Noetherian ring in which `(f)` has grade `n` and
`(f) + (det g) ≠ P`, the second in the form `(f) : ((f) + (det g)) = (x)`; the two colon ideals
agree. In a Noetherian ring with `(f) ≠ P` the hypothesis here gives grade `n`: a weakly regular
sequence in a proper ideal is regular, and Krull's height theorem bounds the grade of `(f)` by
`n`. -/
public theorem Ideal.colon_span_eq_sup_span_det_of_isWeaklyRegular
    {P : Type*} [CommRing P] {n : ℕ} (x f : Fin n → P) (g : Matrix (Fin n) (Fin n) P)
    (hf : ∀ i, f i = ∑ j, g i j * x j)
    (hy : ∃ y : Fin n → P, RingTheory.Sequence.IsWeaklyRegular P (List.ofFn y) ∧
      ∀ i, y i ∈ Ideal.span (Set.range f)) :
    (Ideal.span (Set.range f)).colon (Ideal.span (Set.range x)) =
        Ideal.span (Set.range f) ⊔ Ideal.span {g.det} ∧
      (Ideal.span (Set.range f)).colon (Ideal.span {g.det}) = Ideal.span (Set.range x) := by
  obtain ⟨y, hy, hyf⟩ := hy
  have hfK : ∀ p, 0 < p → Subsingleton (ColonSpanDet.Koszul.H f P p) :=
    ColonSpanDet.Koszul.subsingleton_H_of_isWeaklyRegular_of_card_eq f P y hy hyf
      (Fintype.card_fin n).symm
  have hxK : ∀ p, 0 < p → Subsingleton (ColonSpanDet.Koszul.H x P p) :=
    ColonSpanDet.Koszul.subsingleton_H_of_isWeaklyRegular_of_card_eq x P y hy
      (fun k => ColonSpanDet.Koszul.span_le_span_of_eq x f g hf (hyf k)) (Fintype.card_fin n).symm
  have hb := ColonSpanDet.Koszul.wiebeMap_bijective x f g hf hxK hfK
  exact ⟨ColonSpanDet.Koszul.colon_span_eq_of_surjective x f g hf hb.2,
    ColonSpanDet.Koszul.colon_det_eq_of_injective x f g hf hb.1⟩

end
