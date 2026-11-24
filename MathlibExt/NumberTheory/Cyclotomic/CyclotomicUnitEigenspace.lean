/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ClassGroup_GaloisAction.lean` and
`Definitions/Def_ExtCitation_CyclotomicUnits.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import MathlibExt.NumberTheory.Cyclotomic.Stickelberger

@[expose] public section

open scoped NumberField nonZeroDivisors
open Polynomial


section ClassGroupFunctoriality
variable {R : Type*} [CommRing R] [IsDomain R]
variable {R' : Type*} [CommRing R'] [IsDomain R']

def Ideal.mapNonZero (g : R ≃+* R') (P : (Ideal R)⁰) : (Ideal R')⁰ :=
  ⟨(P : Ideal R).map (g : R →+* R'), by
    have hinj : Function.Injective ((g : R →+* R') : R → R') := g.injective
    refine mem_nonZeroDivisors_iff_ne_zero.mpr fun hbot => ?_
    refine mem_nonZeroDivisors_iff_ne_zero.mp P.2 ?_
    rw [Ideal.zero_eq_bot] at hbot ⊢
    exact (Ideal.map_eq_bot_iff_of_injective hinj).mp hbot⟩

@[simp] lemma Ideal.coe_mapNonZero (g : R ≃+* R') (P : (Ideal R)⁰) :
    (Ideal.mapNonZero g P : Ideal R') = (P : Ideal R).map (g : R →+* R') := rfl

variable [IsDedekindDomain R] [IsDedekindDomain R']

theorem ClassGroup.mulEquiv_mk0_mapNonZero (g : R ≃+* R') (P : (Ideal R)⁰) :
    ClassGroup.mulEquiv g (ClassGroup.mk0 P) =
      ClassGroup.mk0 (Ideal.mapNonZero g P) :=
  ClassGroup.mulEquiv_mk0 g P

theorem ClassGroup.mulEquiv_refl_apply (C : ClassGroup R) :
    ClassGroup.mulEquiv (RingEquiv.refl R) C = C := by
  obtain ⟨P, rfl⟩ := ClassGroup.mk0_surjective C
  rw [ClassGroup.mulEquiv_mk0_mapNonZero]
  congr 1
  refine Subtype.ext ?_
  rw [Ideal.coe_mapNonZero,
    show ((RingEquiv.refl R : R ≃+* R) : R →+* R) = RingHom.id R from RingHom.ext fun _ => rfl,
    Ideal.map_id]

theorem ClassGroup.mulEquiv_trans_apply {R'' : Type*} [CommRing R''] [IsDomain R'']
    [IsDedekindDomain R''] (g : R ≃+* R') (h : R' ≃+* R'') (C : ClassGroup R) :
    ClassGroup.mulEquiv (g.trans h) C = ClassGroup.mulEquiv h (ClassGroup.mulEquiv g C) := by
  obtain ⟨P, rfl⟩ := ClassGroup.mk0_surjective C
  rw [ClassGroup.mulEquiv_mk0_mapNonZero, ClassGroup.mulEquiv_mk0_mapNonZero,
    ClassGroup.mulEquiv_mk0_mapNonZero]
  congr 1
  refine Subtype.ext ?_
  rw [Ideal.coe_mapNonZero, Ideal.coe_mapNonZero, Ideal.coe_mapNonZero,
    show ((g.trans h : R ≃+* R'') : R →+* R'') = (h : R' →+* R'').comp (g : R →+* R') from
      RingHom.ext fun _ => rfl,
    ← Ideal.map_map]

end ClassGroupFunctoriality

section GalRestrict

def algAutToRingAut (A B : Type*) [CommSemiring A] [Semiring B] [Algebra A B] :
    (B ≃ₐ[A] B) →* (B ≃+* B) where
  toFun := AlgEquiv.toRingEquiv
  map_one' := RingEquiv.ext fun _ => rfl
  map_mul' _ _ := RingEquiv.ext fun _ => rfl

@[simp] lemma algAutToRingAut_apply {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    (e : B ≃ₐ[A] B) (x : B) : algAutToRingAut A B e x = e x := rfl

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
  [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]

noncomputable def galRestrictionDatum : (L ≃ₐ[K] L) →* (B ≃+* B) :=
  (algAutToRingAut A B).comp (galRestrict A K L B).toMonoidHom

@[simp] lemma galRestrictionDatum_apply (g : L ≃ₐ[K] L) (x : B) :
    galRestrictionDatum A K L B g x = galRestrict A K L B g x := rfl

end GalRestrict


namespace JacobiSumStickelberger


section ClassGroupCarrier

variable (p : ℕ) [NeZero p]

section DedekindAction

variable (R : Type*) [CommRing R] [IsDomain R]

variable {R} in
variable [IsDedekindDomain R] in

theorem clEnd_clProj_mk0 (g : R ≃+* R) (P : (Ideal R)⁰) :
    clEnd p g (clProj p R (Additive.ofMul (ClassGroup.mk0 P))) =
      clProj p R (Additive.ofMul (ClassGroup.mk0 (Ideal.mapNonZero g P))) := by
  rw [clEnd_clProj, ClassGroup.mulEquiv_mk0_mapNonZero]

variable {R} in
variable [IsDedekindDomain R] in

noncomputable def clEndHom : (R ≃+* R) →* Module.End (ZMod p) (ClGalModule p R) where
  toFun := clEnd p
  map_one' := by
    refine LinearMap.ext fun a => ?_
    obtain ⟨C, rfl⟩ := clProj_surjective p R a
    rw [Module.End.one_apply]
    show clProj p R (Additive.ofMul (ClassGroup.mulEquiv (RingEquiv.refl R) C.toMul)) =
      clProj p R C
    rw [ClassGroup.mulEquiv_refl_apply]; rfl
  map_mul' g h := by
    refine LinearMap.ext fun a => ?_
    obtain ⟨C, rfl⟩ := clProj_surjective p R a
    rw [Module.End.mul_apply]
    show clProj p R (Additive.ofMul (ClassGroup.mulEquiv (h.trans g) C.toMul)) =
      clEnd p g (clProj p R (Additive.ofMul (ClassGroup.mulEquiv h C.toMul)))
    rw [clEnd_clProj, ClassGroup.mulEquiv_trans_apply]

end DedekindAction

section Cyclotomic

variable (K : Type*) [Field K] [NumberField K]

noncomputable def cycloGalEquiv [IsCyclotomicExtension {p} ℚ K] :
    (K ≃ₐ[ℚ] K) ≃* (ZMod p)ˣ :=
  IsCyclotomicExtension.autEquivPow K
    (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (NeZero.ne p)))

noncomputable def clRingAction [IsCyclotomicExtension {p} ℚ K] :
    (ZMod p)ˣ →* ((𝓞 K) ≃+* (𝓞 K)) :=
  (galRestrictionDatum ℤ ℚ K (𝓞 K)).comp (cycloGalEquiv p K).symm.toMonoidHom

noncomputable def clGalAction [IsCyclotomicExtension {p} ℚ K] :
    (ZMod p)ˣ →* Module.End (ZMod p) (ClGalModule p (𝓞 K)) :=
  (clEndHom p).comp (clRingAction p K)

theorem clGalAction_clProj_mk0 [IsCyclotomicExtension {p} ℚ K] (d : (ZMod p)ˣ)
    (P : (Ideal (𝓞 K))⁰) :
    clGalAction p K d (clProj p (𝓞 K) (Additive.ofMul (ClassGroup.mk0 P))) =
      clProj p (𝓞 K) (Additive.ofMul (ClassGroup.mk0
        (Ideal.mapNonZero (clRingAction p K d) P))) :=
  clEnd_clProj_mk0 p (clRingAction p K d) P

end Cyclotomic

end ClassGroupCarrier


end JacobiSumStickelberger

namespace ExtCitation.Cyclotomic


open NumberField JacobiSumStickelberger Stickelberger

variable (p : ℕ) [Fact p.Prime]

section UnitsGalAction

variable (R : Type*) [CommRing R]

noncomputable def unitsEnd (g : R ≃+* R) :
    Module.End (ZMod p) (ModP p (Additive Rˣ)) :=
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ModP.mapEnd p (MulEquiv.toAdditive (Units.mapEquiv g.toMulEquiv)).toAddMonoidHom

variable {R} in
@[simp] lemma unitsEnd_proj (g : R ≃+* R) (u : Rˣ) :
    unitsEnd p R g (ModP.proj p (Additive Rˣ) (Additive.ofMul u)) =
      ModP.proj p (Additive Rˣ) (Additive.ofMul (Units.mapEquiv g.toMulEquiv u)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rfl

noncomputable def unitsEndHom : (R ≃+* R) →* Module.End (ZMod p) (ModP p (Additive Rˣ)) where
  toFun := unitsEnd p R
  map_one' := by
    ext a
    obtain ⟨u, rfl⟩ := ModP.proj_surjective p (Additive Rˣ) a
    exact unitsEnd_proj p (RingEquiv.refl R) u.toMul
  map_mul' g h := by
    ext a
    obtain ⟨u, rfl⟩ := ModP.proj_surjective p (Additive Rˣ) a
    simp only [Module.End.mul_apply]
    rfl

end UnitsGalAction

set_option backward.isDefEq.respectTransparency false in

noncomputable instance instIsCycExt :
    IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
  inferInstance

noncomputable def unitsGalAction :
    (ZMod p)ˣ →* Module.End (ZMod p)
      (ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)) :=
  (unitsEndHom p (𝓞 (CyclotomicField p ℚ))).comp (clRingAction p (CyclotomicField p ℚ))

def unitsOmegaEigenspace (i : ℕ) :
    Submodule (ZMod p) (ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)) where
  carrier := {a | IsOmegaEigenvector (unitsGalAction p) i a}
  add_mem' {a b} ha hb d := by
    simp only [Set.mem_setOf_eq, IsOmegaEigenvector] at *
    rw [map_add, ha d, hb d, smul_add]
  zero_mem' d := by simp
  smul_mem' c a ha d := by
    simp only [Set.mem_setOf_eq, IsOmegaEigenvector] at *
    rw [map_smul, ha d, smul_comm]

noncomputable def omegaIdempotent {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    (ρ : (ZMod p)ˣ →* Module.End (ZMod p) M) (i : ℕ) : Module.End (ZMod p) M :=
  (Nat.card (ZMod p)ˣ : ZMod p)⁻¹ • ∑ d : (ZMod p)ˣ, (((d : ZMod p) ^ i)⁻¹) • ρ d


/-- Membership in the omega eigenspace is the eigenvector condition. -/
theorem mem_unitsOmegaEigenspace {i : ℕ} {a : ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)} :
    a ∈ unitsOmegaEigenspace p i ↔
      Stickelberger.IsOmegaEigenvector (unitsGalAction p) i a :=
  Iff.rfl

end ExtCitation.Cyclotomic
