/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn.lean`
and
`P2M/Sol/S_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn.lean`
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

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.FieldTheory.Galois.Basic
public import MathlibExt.RingTheory.Valuation.Henselian
public import MathlibExt.RingTheory.Valuation.InertiaRootsOfUnity
import Mathlib.Algebra.Polynomial.GroupRingAction
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

universe u

open IsLocalRing Polynomial

noncomputable section

namespace HenselianFixedFieldAux

variable {K L : Type u} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
variable (I : Subgroup (L ≃ₐ[K] L))

private theorem isUnit_of_sub_mem {R : Type u} [CommRing R] [IsLocalRing R] {x y : R}
    (hx : IsUnit x) (hxy : y - x ∈ maximalIdeal R) : IsUnit y := by
  by_contra hy
  have hy' : y ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hy
  have hx' : x ∈ maximalIdeal R := by
    have hsub := Ideal.sub_mem _ hy' hxy
    rwa [sub_sub_cancel] at hsub
  exact (mem_maximalIdeal _).mp hx' hx

private theorem eval_sub_eval_mem {R : Type u} [CommRing R] [IsLocalRing R] (g : R[X])
    {x y : R} (hxy : x - y ∈ maximalIdeal R) :
    g.eval x - g.eval y ∈ maximalIdeal R := by
  obtain ⟨c, hc⟩ := sub_dvd_eval_sub x y g
  rw [hc]
  exact Ideal.mul_mem_right _ _ hxy

private theorem root_unique {R : Type u} [CommRing R] [IsLocalRing R] (f : R[X]) (a₀ : R)
    (hu : IsUnit (f.derivative.eval a₀)) {α β : R} (hα : f.IsRoot α)
    (hα₀ : α - a₀ ∈ maximalIdeal R) (hβ : f.IsRoot β) (hβ₀ : β - a₀ ∈ maximalIdeal R) :
    β = α := by
  set g := f /ₘ (X - C α) with hg
  have hfac : (X - C α) * g = f := mul_divByMonic_eq_iff_isRoot.mpr hα
  have hder : f.derivative.eval α = g.eval α := by
    conv_lhs => rw [← hfac]
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
      eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  have hgα : IsUnit (g.eval α) := by
    rw [← hder]
    exact isUnit_of_sub_mem hu (eval_sub_eval_mem f.derivative hα₀)
  have hβα : β - α ∈ maximalIdeal R := by
    have hsub := Ideal.sub_mem _ hβ₀ hα₀
    rwa [sub_sub_sub_cancel_right] at hsub
  have hgβ : IsUnit (g.eval β) := isUnit_of_sub_mem hgα (eval_sub_eval_mem g hβα)
  have h0 : (β - α) * g.eval β = 0 := by
    have hroot := hβ.eq_zero
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at hroot
    exact hroot
  have hba : β - α = 0 := hgβ.mul_left_eq_zero.mp h0
  exact sub_eq_zero.mp hba

private abbrev OI : Subring L := A.toSubring ⊓ (IntermediateField.fixedField I).toSubring

private def incl : ↥(OI A I) →+* ↥A := Subring.inclusion inf_le_left

private theorem incl_coe (o : ↥(OI A I)) : ((incl A I o : ↥A) : L) = (o : L) := rfl

private theorem incl_injective : Function.Injective (incl A I) := fun x y h =>
  Subtype.ext (by rw [← incl_coe A I x, ← incl_coe A I y, h])

private theorem mem_fixed (o : ↥(OI A I)) :
    (o : L) ∈ IntermediateField.fixedField I := (Subring.mem_inf.mp o.2).2

private theorem isUnit_iff (o : ↥(OI A I)) : IsUnit o ↔ IsUnit (incl A I o) := by
  refine ⟨fun h => h.map _, fun h => ?_⟩
  have ho' : (o : L) ≠ 0 := by
    intro h0
    apply h.ne_zero
    exact Subtype.ext h0
  obtain ⟨w, hw⟩ := h.exists_left_inv
  have h1 : ((w : ↥A) : L) * (o : L) = 1 := by
    have hcongr := congrArg (fun a : ↥A => (a : L)) hw
    simpa [incl_coe] using hcongr
  have hwL : ((w : ↥A) : L) = ((o : L))⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hinvA : (o : L)⁻¹ ∈ A := by rw [← hwL]; exact w.2
  have hinvF : (o : L)⁻¹ ∈ IntermediateField.fixedField I := inv_mem (mem_fixed A I o)
  have hinvO : (o : L)⁻¹ ∈ OI A I := Subring.mem_inf.mpr ⟨hinvA, hinvF⟩
  refine IsUnit.of_mul_eq_one ⟨_, hinvO⟩ ?_
  apply Subtype.ext
  show (o : L) * (o : L)⁻¹ = 1
  exact mul_inv_cancel₀ ho'

private instance isLocalRingOI : IsLocalRing ↥(OI A I) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, isUnit_iff A I, ← mem_nonunits_iff, ← mem_maximalIdeal] at ha hb ⊢
  rw [map_add]
  exact Ideal.add_mem _ ha hb

private theorem mem_maximalIdeal_iff (o : ↥(OI A I)) :
    o ∈ maximalIdeal ↥(OI A I) ↔ incl A I o ∈ maximalIdeal ↥A := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_iff A I]

private theorem exists_decomp_of_mem {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.inertiaSubgroupIn K) :
    ∃ τ : ↥(A.decompositionSubgroup K), τ ∈ A.inertiaSubgroup K ∧
      (τ : L ≃ₐ[K] L) = σ := by
  obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.mp hσ
  exact ⟨τ, hτ, hτσ⟩

private theorem smul_sub_mem (τ : ↥(A.decompositionSubgroup K)) (hτ : τ ∈ A.inertiaSubgroup K)
    (a : ↥A) : τ • a - a ∈ maximalIdeal ↥A := by
  have h1 : MulSemiringAction.toRingAut (↥(A.decompositionSubgroup K))
      (ResidueField ↥A) τ = 1 := MonoidHom.mem_ker.mp hτ
  have h2 : τ • residue ↥A a = residue ↥A a := by
    have hcongr := congrArg (fun e : RingAut (ResidueField ↥A) => e (residue ↥A a)) h1
    simpa [MulSemiringAction.toRingAut_apply] using hcongr
  rw [← ResidueField.residue_smul] at h2
  exact Ideal.Quotient.eq.mp h2

private theorem coe_smul (τ : ↥(A.decompositionSubgroup K)) (a : ↥A) :
    ((τ • a : ↥A) : L) = (τ : L ≃ₐ[K] L) (a : L) := rfl

private theorem smul_incl (τ : ↥(A.decompositionSubgroup K))
    (hτI : (τ : L ≃ₐ[K] L) ∈ I) (o : ↥(OI A I)) :
    τ • incl A I o = incl A I o := by
  apply Subtype.ext
  rw [coe_smul, incl_coe A I]
  exact (IntermediateField.mem_fixedField_iff _ _).mp (mem_fixed A I o) _ hτI

variable [IsAlgClosed L]

private theorem henselian (hI : I ≤ A.inertiaSubgroupIn K) :
    HenselianLocalRing ↥(OI A I) where
  toIsLocalRing := inferInstance
  is_henselian f hf a₀ h₀ hu := by
    haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
    set ι := incl A I with hι
    set fA := f.map ι with hfA
    have hfAm : fA.Monic := hf.map ι
    have hev : ∀ o, fA.eval (ι o) = ι (f.eval o) := fun o => by
      rw [hfA, eval_map, eval₂_hom]
    have h₀A : fA.eval (ι a₀) ∈ maximalIdeal ↥A := by
      rw [hev]; exact (mem_maximalIdeal_iff A I _).mp h₀
    have huA : IsUnit (fA.derivative.eval (ι a₀)) := by
      rw [hfA, derivative_map, eval_map, eval₂_hom]; exact hu.map ι
    obtain ⟨α, hα, hα₀⟩ := HenselianLocalRing.is_henselian fA hfAm (ι a₀) h₀A huA
    have hfix : ∀ σ ∈ I, σ (α : L) = α := by
      intro σ hσ
      obtain ⟨τ, hτ, rfl⟩ := exists_decomp_of_mem A (hI hσ)
      have hsm : τ • fA = fA := by
        ext n
        rw [coeff_smul, hfA, coeff_map, smul_incl A I τ hσ]
      have hβroot : fA.IsRoot (τ • α) := by
        show fA.eval (τ • α) = 0
        conv_lhs => rw [← hsm]
        rw [smul_eval_smul, (show fA.eval α = 0 from hα), smul_zero]
      have hβ₀ : τ • α - ι a₀ ∈ maximalIdeal ↥A := by
        have hadd := Ideal.add_mem _ (smul_sub_mem A τ hτ α) hα₀
        rwa [sub_add_sub_cancel] at hadd
      have hβα : τ • α = α := root_unique fA (ι a₀) huA hα hα₀ hβroot hβ₀
      exact congrArg (fun a : ↥A => (a : L)) hβα
    have hαK : (α : L) ∈ IntermediateField.fixedField I :=
      (IntermediateField.mem_fixedField_iff _ _).mpr hfix
    let a : ↥(OI A I) := ⟨(α : L), Subring.mem_inf.mpr ⟨α.2, hαK⟩⟩
    have ha : ι a = α := Subtype.ext rfl
    refine ⟨a, ?_, ?_⟩
    · apply incl_injective A I
      show ι (f.eval a) = ι 0
      rw [map_zero, ← hev, ha]
      exact hα
    · rw [mem_maximalIdeal_iff A I, map_sub]
      show ι a - ι a₀ ∈ maximalIdeal ↥A
      rw [ha]
      exact hα₀

end HenselianFixedFieldAux

namespace ValuationSubring

/-- Intersecting a valuation subring of an algebraically closed field with
the fixed field of a subgroup of its inertia subgroup gives a Henselian
local ring. -/
public theorem henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] (A : ValuationSubring L)
    (I : Subgroup (L ≃ₐ[K] L)) (hI : I ≤ A.inertiaSubgroupIn K) :
    HenselianLocalRing ↥(A.toSubring ⊓ (IntermediateField.fixedField I).toSubring) :=
  HenselianFixedFieldAux.henselian A I hI

end ValuationSubring

end
