/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Gamma0HeckeOperatorHom.lean`,
`Definitions/Def_Gamma0CoeffCohomology.lean`,
`Theorems/Thm_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.lean`
`P2M/Sol/S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.lean`,
`Theorems/Thm_HeckeEis_sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries.lean`,
`P2M/Sol/S_HeckeEis_sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries.lean`,
`Theorems/Thm_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.lean`
and
`P2M/Sol/S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.lean`
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

public import Mathlib.GroupTheory.Transfer
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Int
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

/-!
# Hecke operators on coefficient cocycles

For a congruence subgroup `Gamma0 N`, a representation `ρ` of `Gamma0 N` on a
module `V`, and a positive integer `ℓ`, the coefficient Hecke operator sends a
cocycle `z` for `ρ` to a new cocycle by averaging, over the cosets of an
upper-triangular subgroup, the values of `z` at conjugate elements, twisted by
an intertwining endomorphism.  For a prime `ℓ` dividing neither `N` nor `ℓ'`
and `m = ℓ * ℓ'`, the composite of the operators for `ℓ'` and then `ℓ`, twisted
by intertwining endomorphisms `a'` and `a`, agrees modulo coboundaries with the
operator for `m` twisted by `a ∘ₗ a'`.

Cocycles and coboundaries are Mathlib's `groupCohomology.cocycles₁` and
`groupCohomology.coboundaries₁` of `Rep.of ρ`, and the parabolic classes form a
submodule of `groupCohomology.H1 (Rep.of ρ)`. Mathlib's low-degree group
cohomology takes the coefficient ring in the universe of the group, and `H1`
also the representation space, so for `Gamma0 N` these live in `Type`.
-/

open CongruenceSubgroup Subgroup Matrix
open scoped MatrixGroups

namespace HeckeEis


open CongruenceSubgroup Subgroup Matrix
open scoped MatrixGroups

section ConjMatrix

@[expose] public def alphaMat (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, (ℓ : ℤ)]

@[simp] public theorem alphaMat_apply_zero_zero (ℓ : ℕ) : alphaMat ℓ 0 0 = 1 := rfl
@[simp] public theorem alphaMat_apply_zero_one (ℓ : ℕ) : alphaMat ℓ 0 1 = 0 := rfl
@[simp] public theorem alphaMat_apply_one_zero (ℓ : ℕ) : alphaMat ℓ 1 0 = 0 := rfl
@[simp] public theorem alphaMat_apply_one_one (ℓ : ℕ) : alphaMat ℓ 1 1 = (ℓ : ℤ) := rfl

public theorem det_alphaMat (ℓ : ℕ) : (alphaMat ℓ).det = (ℓ : ℤ) := by
  rw [alphaMat, det_fin_two_of]; ring

theorem eq_of_mul_alphaMat_eq {ℓ : ℕ} (hℓ : (ℓ : ℤ) ≠ 0) {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (h : A * alphaMat ℓ = B * alphaMat ℓ) : A = B := by
  ext i j
  have h0 := congrFun (congrFun h i) 0
  have h1 := congrFun (congrFun h i) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, alphaMat_apply_zero_zero,
    alphaMat_apply_zero_one, alphaMat_apply_one_zero, alphaMat_apply_one_one,
    mul_one, mul_zero, add_zero, zero_add] at h0 h1
  fin_cases j
  · exact h0
  · exact mul_right_cancel₀ hℓ h1

@[expose] public def heckeConjMat (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  !![g 0 0, g 0 1 / (ℓ : ℤ); g 1 0 * (ℓ : ℤ), g 1 1]

@[simp] public theorem heckeConjMat_apply_zero_zero (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    heckeConjMat ℓ g 0 0 = g 0 0 := rfl
@[simp] public theorem heckeConjMat_apply_zero_one (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    heckeConjMat ℓ g 0 1 = g 0 1 / (ℓ : ℤ) := rfl
@[simp] public theorem heckeConjMat_apply_one_zero (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    heckeConjMat ℓ g 1 0 = g 1 0 * (ℓ : ℤ) := rfl
@[simp] public theorem heckeConjMat_apply_one_one (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    heckeConjMat ℓ g 1 1 = g 1 1 := rfl

public theorem heckeConjMat_mul_alphaMat {ℓ : ℕ} {g : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (ℓ : ℤ) ∣ g 0 1) :
    heckeConjMat ℓ g * alphaMat ℓ = alphaMat ℓ * g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, alphaMat_apply_zero_zero,
      alphaMat_apply_zero_one, alphaMat_apply_one_zero, alphaMat_apply_one_one,
      heckeConjMat_apply_zero_zero, heckeConjMat_apply_zero_one, heckeConjMat_apply_one_zero,
      heckeConjMat_apply_one_one, Fin.zero_eta, Fin.mk_one, Fin.isValue, mul_zero,
      one_mul, zero_mul, add_zero, zero_add] <;>
    first
      | exact Int.ediv_mul_cancel hg
      | ring1

theorem dvd_mul_apply_zero_one {ℓ : ℕ} {g h : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (ℓ : ℤ) ∣ g 0 1) (hh : (ℓ : ℤ) ∣ h 0 1) : (ℓ : ℤ) ∣ (g * h) 0 1 := by
  rw [(Matrix.two_mul_expl g h).2.1]
  exact dvd_add (hh.mul_left _) (hg.mul_right _)

public theorem heckeConjMat_mul {ℓ : ℕ} (hℓ : (ℓ : ℤ) ≠ 0) {g h : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (ℓ : ℤ) ∣ g 0 1) (hh : (ℓ : ℤ) ∣ h 0 1) :
    heckeConjMat ℓ (g * h) = heckeConjMat ℓ g * heckeConjMat ℓ h := by
  have key : (heckeConjMat ℓ g * heckeConjMat ℓ h) * alphaMat ℓ = alphaMat ℓ * (g * h) := by
    rw [mul_assoc, heckeConjMat_mul_alphaMat hh, ← mul_assoc, heckeConjMat_mul_alphaMat hg,
      mul_assoc]
  exact eq_of_mul_alphaMat_eq hℓ
    ((heckeConjMat_mul_alphaMat (dvd_mul_apply_zero_one hg hh)).trans key.symm)

public theorem det_heckeConjMat {ℓ : ℕ} (hℓ : (ℓ : ℤ) ≠ 0) {g : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (ℓ : ℤ) ∣ g 0 1) : (heckeConjMat ℓ g).det = g.det := by
  have h := congrArg Matrix.det (heckeConjMat_mul_alphaMat hg)
  rw [Matrix.det_mul, Matrix.det_mul, det_alphaMat] at h
  exact mul_right_cancel₀ hℓ (by linear_combination h)

public theorem heckeConjMat_one (ℓ : ℕ) : heckeConjMat ℓ (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeConjMat]

public theorem heckeConjMat_injective {ℓ : ℕ} (hℓ : (ℓ : ℤ) ≠ 0) {g h : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (ℓ : ℤ) ∣ g 0 1) (hh : (ℓ : ℤ) ∣ h 0 1)
    (e : heckeConjMat ℓ g = heckeConjMat ℓ h) : g = h := by
  have key : alphaMat ℓ * g = alphaMat ℓ * h := by
    rw [← heckeConjMat_mul_alphaMat hg, ← heckeConjMat_mul_alphaMat hh, e]
  ext i j
  have h0 := congrFun (congrFun key 0) j
  have h1 := congrFun (congrFun key 1) j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, alphaMat_apply_zero_zero,
    alphaMat_apply_zero_one, alphaMat_apply_one_zero, alphaMat_apply_one_one,
    one_mul, zero_mul, add_zero, zero_add] at h0 h1
  fin_cases i
  · exact h0
  · exact mul_left_cancel₀ hℓ h1

end ConjMatrix

section HeckeSubgroup

@[expose] public def heckeUpperSL (ℓ : ℕ) : Subgroup SL(2, ℤ) where
  carrier := {g | (ℓ : ℤ) ∣ g 0 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    have h : (ℓ : ℤ) ∣ (a.1 * b.1) 0 1 := by
      rw [(Matrix.two_mul_expl a.1 b.1).2.1]
      exact dvd_add (hb.mul_left _) (ha.mul_right _)
    exact h
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl a]
    simpa using ha

@[simp]
public theorem mem_heckeUpperSL {ℓ : ℕ} {g : SL(2, ℤ)} : g ∈ heckeUpperSL ℓ ↔ (ℓ : ℤ) ∣ g 0 1 :=
  Iff.rfl

variable (N ℓ : ℕ)

@[expose] public def heckeUpper : Subgroup (Gamma0 N) := (heckeUpperSL ℓ).subgroupOf (Gamma0 N)

public theorem mem_heckeUpper {γ : Gamma0 N} :
    γ ∈ heckeUpper N ℓ ↔ (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 :=
  Iff.rfl

def gammaZeroRed : Gamma0 N →* SL(2, ZMod ℓ) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod ℓ))).comp
    (Gamma0 N).subtype

theorem ker_gammaZeroRed_le_heckeUpper : (gammaZeroRed N ℓ).ker ≤ heckeUpper N ℓ := by
  intro γ hγ
  rw [MonoidHom.mem_ker] at hγ
  rw [mem_heckeUpper]
  have h01 : ((((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ)) = 0 := by
    have h := congrArg (fun A : SL(2, ZMod ℓ) => A 0 1) hγ
    simpa [gammaZeroRed, Matrix.one_apply] using h
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp h01

public instance instFiniteIndexHeckeUpper [NeZero ℓ] : (heckeUpper N ℓ).FiniteIndex :=
  haveI : (gammaZeroRed N ℓ).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  Subgroup.finiteIndex_of_le (ker_gammaZeroRed_le_heckeUpper N ℓ)

variable [NeZero ℓ]

@[expose] public def heckeConjSL (γ : heckeUpper N ℓ) : SL(2, ℤ) :=
  ⟨heckeConjMat ℓ ((γ : Gamma0 N) : SL(2, ℤ)), by
    rw [det_heckeConjMat (Int.natCast_ne_zero.mpr (NeZero.ne ℓ)) ((mem_heckeUpper N ℓ).mp γ.2)]
    exact ((γ : Gamma0 N) : SL(2, ℤ)).2⟩

@[simp]
public theorem coe_heckeConjSL (γ : heckeUpper N ℓ) :
    (heckeConjSL N ℓ γ : Matrix (Fin 2) (Fin 2) ℤ) =
      heckeConjMat ℓ ((γ : Gamma0 N) : SL(2, ℤ)) :=
  rfl

public theorem heckeConjSL_mem_Gamma0 (γ : heckeUpper N ℓ) : heckeConjSL N ℓ γ ∈ Gamma0 N := by
  rw [Gamma0_mem]
  show (((heckeConjMat ℓ ((γ : Gamma0 N) : SL(2, ℤ))) 1 0 : ℤ) : ZMod N) = 0
  rw [heckeConjMat_apply_one_zero, Int.cast_mul]
  have hc : ((((γ : Gamma0 N) : SL(2, ℤ)) 1 0 : ℤ) : ZMod N) = 0 :=
    Gamma0_mem.mp (γ : Gamma0 N).2
  rw [hc, zero_mul]

@[expose] public def heckeConj : heckeUpper N ℓ →* Gamma0 N where
  toFun γ := ⟨heckeConjSL N ℓ γ, heckeConjSL_mem_Gamma0 N ℓ γ⟩
  map_one' := by
    refine Subtype.ext (Subtype.ext ?_)
    show heckeConjMat ℓ (1 : Matrix (Fin 2) (Fin 2) ℤ) = (1 : Matrix (Fin 2) (Fin 2) ℤ)
    exact heckeConjMat_one ℓ
  map_mul' γ δ := by
    refine Subtype.ext (Subtype.ext ?_)
    show heckeConjMat ℓ
        ((((γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
          (((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) =
      heckeConjMat ℓ (((γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        heckeConjMat ℓ (((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    exact heckeConjMat_mul (Int.natCast_ne_zero.mpr (NeZero.ne ℓ))
      ((mem_heckeUpper N ℓ).mp γ.2) ((mem_heckeUpper N ℓ).mp δ.2)

@[simp]
public theorem coe_heckeConj (γ : heckeUpper N ℓ) :
    ((heckeConj N ℓ γ : Gamma0 N) : SL(2, ℤ)) = heckeConjSL N ℓ γ :=
  rfl

public theorem heckeConj_injective : Function.Injective (heckeConj N ℓ) := by
  intro γ δ h
  have hmat : heckeConjMat ℓ (((γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      heckeConjMat ℓ (((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) :=
    congrArg (fun x : Gamma0 N => ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) h
  exact Subtype.ext (Subtype.ext (Subtype.ext (heckeConjMat_injective
    (Int.natCast_ne_zero.mpr (NeZero.ne ℓ)) ((mem_heckeUpper N ℓ).mp γ.2)
    ((mem_heckeUpper N ℓ).mp δ.2) hmat)))

end HeckeSubgroup

section Transfer

variable {G : Type*} [Group G] (H : Subgroup G) {A : Type*} [AddCommGroup A]

@[expose] public def resHom : (Additive G →+ A) →+ (Additive H →+ A) :=
  AddMonoidHom.mk' (fun φ => φ.comp (MonoidHom.toAdditive H.subtype)) fun _ _ => rfl

@[simp]
public theorem resHom_apply (φ : Additive G →+ A) (γ : H) :
    resHom H φ (Additive.ofMul γ) = φ (Additive.ofMul (γ : G)) :=
  rfl

@[expose] public noncomputable def transferAux (g : G) (q : G ⧸ H) : H :=
  ⟨(g • q).out⁻¹ * (g * q.out), by
    refine QuotientGroup.eq.mp ?_
    rw [QuotientGroup.out_eq']
    show g • q = ((g * q.out : G) : G ⧸ H)
    rw [show ((g * q.out : G) : G ⧸ H) = g • ((q.out : G) : G ⧸ H) from rfl,
      QuotientGroup.out_eq']⟩

@[simp]
public theorem coe_transferAux (g : G) (q : G ⧸ H) :
    (transferAux H g q : G) = (g • q).out⁻¹ * (g * q.out) :=
  rfl

public theorem transferAux_mul (g₁ g₂ : G) (q : G ⧸ H) :
    transferAux H (g₁ * g₂) q = transferAux H g₁ (g₂ • q) * transferAux H g₂ q := by
  ext
  push_cast [coe_transferAux]
  rw [mul_smul]
  group

variable [H.FiniteIndex]

/-- The coset formula for Mathlib's transfer on homomorphisms to an additive group, with the
representatives `Quotient.out`. -/
theorem toAdditiveLeft_transfer_apply (φ : Additive H →+ A) (g : G) :
    letI := H.fintypeQuotientOfFiniteIndex
    MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ))
        (Additive.ofMul g) = ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g q)) := by
  let _ := H.fintypeQuotientOfFiniteIndex
  let T : H.LeftTransversal :=
    ⟨Set.range Quotient.out, Subgroup.isComplement_range_left Quotient.out_eq'⟩
  have hT : ∀ q : G ⧸ H, (T.2.leftQuotientEquiv q : G) = q.out :=
    Subgroup.IsComplement.leftQuotientEquiv_apply Quotient.out_eq'
  rw [MonoidHom.coe_toAdditiveLeft, Function.comp_apply, Function.comp_apply, toMul_ofMul,
    MonoidHom.transfer_def _ T g, Subgroup.leftTransversals.diff, toAdd_prod]
  refine (Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_).symm
  simp only [MulAction.toPerm_apply, AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd]
  congr 2
  ext
  rw [coe_transferAux, Subgroup.coe_mk, hT, ← Subgroup.smul_leftQuotientEquiv, hT, smul_eq_mul]

/-- The transfer `Additive G →+ A` of a homomorphism `Additive H →+ A`: Mathlib's
`MonoidHom.transfer` through `Multiplicative A`, additive in the homomorphism. -/
public noncomputable def coresHom : (Additive H →+ A) →+ (Additive G →+ A) :=
  AddMonoidHom.mk'
    (fun φ => MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ)))
    fun φ ψ => AddMonoidHom.ext fun g => by
      let _ := H.fintypeQuotientOfFiniteIndex
      rw [← ofMul_toMul g, AddMonoidHom.add_apply, toAdditiveLeft_transfer_apply,
        toAdditiveLeft_transfer_apply, toAdditiveLeft_transfer_apply, ← Finset.sum_add_distrib]
      rfl

public theorem coresHom_apply (φ : Additive H →+ A) (g : G) :
    letI := H.fintypeQuotientOfFiniteIndex
    coresHom H φ (Additive.ofMul g) =
      ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g q)) :=
  toAdditiveLeft_transfer_apply H φ g

/-- `coresHom` is Mathlib's transfer, through `Multiplicative A`. -/
public theorem coresHom_eq_transfer (φ : Additive H →+ A) :
    coresHom H φ =
      MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ)) :=
  AddMonoidHom.ext fun g =>
    (coresHom_apply H φ g.toMul).trans (toAdditiveLeft_transfer_apply H φ g.toMul).symm

end Transfer

section Pullback

variable {G K : Type*} [Group G] [Group K] {A : Type*} [AddCommGroup A]

@[expose] public def pullbackHom (f : G →* K) : (Additive K →+ A) →+ (Additive G →+ A) :=
  AddMonoidHom.mk' (fun φ => φ.comp (MonoidHom.toAdditive f)) fun _ _ => rfl

@[simp]
public theorem pullbackHom_apply (f : G →* K) (φ : Additive K →+ A) (g : G) :
    pullbackHom f φ (Additive.ofMul g) = φ (Additive.ofMul (f g)) :=
  rfl

end Pullback

section HeckeOperator

variable (N ℓ : ℕ) [NeZero ℓ] (A : Type*) [AddCommGroup A]

@[expose] public noncomputable def heckeOperatorHom :
    (Additive (Gamma0 N) →+ A) →+ (Additive (Gamma0 N) →+ A) :=
  (coresHom (heckeUpper N ℓ)).comp (pullbackHom (heckeConj N ℓ))

public theorem heckeOperatorHom_apply (φ : Additive (Gamma0 N) →+ A) (g : Gamma0 N) :
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    heckeOperatorHom N ℓ A φ (Additive.ofMul g) =
      ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
        φ (Additive.ofMul ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N))) :=
  coresHom_apply _ _ g

public noncomputable abbrev uOperatorHom (q : ℕ) [NeZero q] :
    (Additive (Gamma0 N) →+ A) →+ (Additive (Gamma0 N) →+ A) :=
  heckeOperatorHom N q A

@[expose] public def HeckeIndexEq : Prop := (heckeUpper N ℓ).index = ℓ + 1

end HeckeOperator


open CongruenceSubgroup
open scoped MatrixGroups

section Parabolic

variable {Γ : Subgroup SL(2, ℤ)}

@[expose] public def IsParabolicCocycle {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V]
    [Module K V]
    (ρ : Representation K Γ V) (z : Γ → V) : Prop :=
  ∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
    z γ ∈ LinearMap.range (ρ γ - 1)

open groupCohomology

section Cocycles

variable {K : Type} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] public def coeffParabolicCocycles (ρ : Representation K Γ V) : Submodule K (Γ → V) where
  carrier := {z | z ∈ cocycles₁ (Rep.of ρ) ∧ IsParabolicCocycle ρ z}
  zero_mem' := ⟨Submodule.zero_mem _, fun γ _ => by simp⟩
  add_mem' := by
    rintro z w ⟨hz, hz'⟩ ⟨hw, hw'⟩
    exact ⟨Submodule.add_mem _ hz hw, fun γ hγ => Submodule.add_mem _ (hz' γ hγ) (hw' γ hγ)⟩
  smul_mem' := by
    rintro c z ⟨hz, hz'⟩
    exact ⟨Submodule.smul_mem _ c hz, fun γ hγ => Submodule.smul_mem _ c (hz' γ hγ)⟩

public theorem mem_coeffParabolicCocycles_iff (ρ : Representation K Γ V) (z : Γ → V) :
    z ∈ coeffParabolicCocycles ρ ↔ z ∈ cocycles₁ (Rep.of ρ) ∧ IsParabolicCocycle ρ z :=
  Iff.rfl

public theorem coeffParabolicCocycles_le_cocycles₁ (ρ : Representation K Γ V) :
    coeffParabolicCocycles ρ ≤ cocycles₁ (Rep.of ρ) :=
  fun _ hz => hz.1

public theorem coboundaries₁_le_coeffParabolicCocycles (ρ : Representation K Γ V) :
    coboundaries₁ (Rep.of ρ) ≤ coeffParabolicCocycles ρ := by
  intro z hz
  refine ⟨coboundaries₁_le_cocycles₁ _ hz, fun γ _ => ?_⟩
  obtain ⟨v, rfl⟩ := hz
  exact ⟨v, rfl⟩

end Cocycles

variable {K V : Type} [CommRing K] [AddCommGroup V] [Module K V]

/-- The parabolic classes: the image in `H¹` of the parabolic cocycles. -/
@[expose] public noncomputable def coeffH1par (ρ : Representation K Γ V) :
    Submodule K (H1 (Rep.of ρ)) :=
  ((coeffParabolicCocycles ρ).comap (cocycles₁ (Rep.of ρ)).subtype).map (H1π (Rep.of ρ)).hom

/-- The class in `coeffH1par ρ` of a parabolic cocycle. -/
@[expose] public noncomputable def coeffH1parMk (ρ : Representation K Γ V) :
    ↥(coeffParabolicCocycles ρ) →ₗ[K] ↥(coeffH1par ρ) :=
  ((H1π (Rep.of ρ)).hom ∘ₗ Submodule.inclusion (coeffParabolicCocycles_le_cocycles₁ ρ)).codRestrict
    (coeffH1par ρ) fun z => ⟨_, z.2, rfl⟩

public theorem coeffH1parMk_surjective (ρ : Representation K Γ V) :
    Function.Surjective (coeffH1parMk ρ) := by
  rintro ⟨_, c, hc, rfl⟩
  exact ⟨⟨c, hc⟩, rfl⟩

public theorem coeffH1parMk_eq_zero_iff (ρ : Representation K Γ V)
    (z : ↥(coeffParabolicCocycles ρ)) :
    coeffH1parMk ρ z = 0 ↔ (z : Γ → V) ∈ coboundaries₁ (Rep.of ρ) :=
  Submodule.coe_eq_zero.symm.trans <|
    H1π_eq_zero_iff (A := Rep.of ρ) (Submodule.inclusion (coeffParabolicCocycles_le_cocycles₁ ρ) z)

end Parabolic

section Hecke

variable (N : ℕ) (ℓ : ℕ) [NeZero ℓ]
variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] public noncomputable def coeffHeckeFun (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
    (z : Gamma0 N → V) : Gamma0 N → V :=
  fun g =>
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
      ρ (g • q).out (a (z (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q))))

public theorem coeffHeckeFun_apply (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
    (z : Gamma0 N → V) (g : Gamma0 N) :
    coeffHeckeFun N ℓ ρ a z g =
      letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
      ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
        ρ (g • q).out (a (z (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q)))) :=
  rfl

public theorem coeffHeckeFun_trivial (φ : Additive (Gamma0 N) →+ K) (g : Gamma0 N) :
    coeffHeckeFun N ℓ (1 : Representation K (Gamma0 N) K) LinearMap.id
        (fun h => φ (Additive.ofMul h)) g
      = heckeOperatorHom N ℓ K φ (Additive.ofMul g) := by
  rw [coeffHeckeFun_apply, heckeOperatorHom_apply]
  simp

end Hecke


namespace Sh2
open CongruenceSubgroup groupCohomology
open scoped MatrixGroups

variable (N ℓ : ℕ) [NeZero ℓ]
  {K : Type} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
  (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)
  (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)

local notation "U" => heckeUpper N ℓ
local notation "c" => heckeConj N ℓ

include ha in
theorem ha_apply (u : ↥U) (v : V) : a (ρ (c u) v) = ρ (u : Gamma0 N) (a v) := by
  have := LinearMap.congr_fun (ha u) v
  simpa using this

theorem cocycle_map_inv {z : Gamma0 N → V} (hz : z ∈ cocycles₁ (Rep.of ρ)) (x : ↥U) :
    z (c x⁻¹) = -(ρ (c x⁻¹) (z (c x))) := by
  have h1 := (mem_cocycles₁_iff (A := Rep.of ρ) z).1 hz (c x⁻¹) (c x)
  have h0 : z 1 = 0 := cocycles₁_map_one (⟨z, hz⟩ : cocycles₁ (Rep.of ρ))
  rw [← map_mul, inv_mul_cancel, map_one, h0] at h1
  exact eq_neg_of_add_eq_zero_right h1.symm

theorem out_mul_transferAux (g : Gamma0 N) (q : Gamma0 N ⧸ U) :
    (g • q).out * (transferAux U g q : Gamma0 N) = g * q.out := by
  rw [coe_transferAux, mul_inv_cancel_left]

include ha in

theorem mem_cocycles₁ {z : Gamma0 N → V} (hz : z ∈ cocycles₁ (Rep.of ρ)) :
    coeffHeckeFun N ℓ ρ a z ∈ cocycles₁ (Rep.of ρ) := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  have hz' : ∀ g h : Gamma0 N, z (g * h) = z g + ρ g (z h) := fun g h =>
    ((mem_cocycles₁_iff (A := Rep.of ρ) z).1 hz g h).trans (add_comm _ _)
  refine (mem_cocycles₁_iff (A := Rep.of ρ) _).2 fun g h => ?_
  rw [Rep.of_ρ, add_comm]
  simp only [coeffHeckeFun_apply]
  have key : ∀ q : Gamma0 N ⧸ U,
      ρ ((g * h) • q).out (a (z (c (transferAux U (g * h) q))))
        = ρ (g • (h • q)).out (a (z (c (transferAux U g (h • q)))))
          + ρ g (ρ (h • q).out (a (z (c (transferAux U h q))))) := by
    intro q
    rw [transferAux_mul, map_mul, hz', map_add, map_add, mul_smul]
    congr 1
    rw [ha_apply N ℓ ρ a ha, ← Module.End.mul_apply, ← map_mul, out_mul_transferAux, map_mul,
      Module.End.mul_apply]
  rw [Finset.sum_congr rfl fun q _ => key q, Finset.sum_add_distrib, map_sum]
  congr 1
  exact Fintype.sum_bijective (h • ·) (MulAction.bijective h) _ _ fun q => rfl

include ha in

theorem mem_coboundaries₁ {z : Gamma0 N → V} (hz : z ∈ coboundaries₁ (Rep.of ρ)) :
    coeffHeckeFun N ℓ ρ a z ∈ coboundaries₁ (Rep.of ρ) := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  obtain ⟨v, rfl⟩ := hz
  change coeffHeckeFun N ℓ ρ a (fun g => ρ g v - v) ∈ coboundaries₁ (Rep.of ρ)
  refine ⟨∑ q : Gamma0 N ⧸ U, ρ q.out (a v), funext fun g => ?_⟩
  change ρ g (∑ q : Gamma0 N ⧸ U, ρ q.out (a v)) - ∑ q : Gamma0 N ⧸ U, ρ q.out (a v) = _
  simp only [coeffHeckeFun_apply, map_sub, map_sum, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp only [ha_apply N ℓ ρ a ha]
    rw [← Module.End.mul_apply (ρ (g • q).out) (ρ _), ← map_mul, out_mul_transferAux, map_mul,
      Module.End.mul_apply]
  · exact (Fintype.sum_bijective (g • ·) (MulAction.bijective g)
      (fun q : Gamma0 N ⧸ U => ρ (g • q).out (a v)) (fun q : Gamma0 N ⧸ U => ρ q.out (a v)) fun q
        => rfl).symm

include ha in

theorem sum_repr_sub_mem_coboundaries₁
    (s : Gamma0 N ⧸ U → Gamma0 N) (t : Gamma0 N → Gamma0 N ⧸ U → ↥U)
    (hs : ∀ q, (s q : Gamma0 N ⧸ U) = q)
    (hst : ∀ g q, s (g • q) * (t g q : Gamma0 N) = g * s q)
    {z : Gamma0 N → V} (hz : z ∈ cocycles₁ (Rep.of ρ)) :
    (fun g => letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
        ∑ q : Gamma0 N ⧸ U, ρ (s (g • q)) (a (z (c (t g q)))))
      - coeffHeckeFun N ℓ ρ a z ∈ coboundaries₁ (Rep.of ρ) := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  have hz' : ∀ g h : Gamma0 N, z (g * h) = z g + ρ g (z h) := fun g h =>
    ((mem_cocycles₁_iff (A := Rep.of ρ) z).1 hz g h).trans (add_comm _ _)
  have hu_mem : ∀ q : Gamma0 N ⧸ U, (q.out)⁻¹ * s q ∈ U := fun q =>
    QuotientGroup.eq.mp ((QuotientGroup.out_eq' q).trans (hs q).symm)
  have hex : ∀ q : Gamma0 N ⧸ U, ∃ uq : ↥U, s q = q.out * (uq : Gamma0 N) := fun q =>
    ⟨⟨_, hu_mem q⟩, by rw [Subgroup.coe_mk, mul_inv_cancel_left]⟩
  choose u hsq using hex
  have ht : ∀ g q, t g q = (u (g • q))⁻¹ * transferAux U g q * u q := by
    intro g q
    apply Subtype.ext
    have h1 := hst g q
    rw [hsq, hsq] at h1
    push_cast [coe_transferAux]
    calc ((t g q : ↥U) : Gamma0 N)
        = ((g • q).out * ↑(u (g • q)))⁻¹ * (((g • q).out * ↑(u (g • q))) * ↑(t g q)) := by group
      _ = ((g • q).out * ↑(u (g • q)))⁻¹ * (g * (q.out * ↑(u q))) := by rw [h1]
      _ = (↑(u (g • q)))⁻¹ * ((g • q).out⁻¹ * (g * q.out)) * ↑(u q) := by group

  set F : V := ∑ q : Gamma0 N ⧸ U, ρ q.out (a (z (c (u q)))) with hF
  refine ⟨F, funext fun g => ?_⟩
  change ρ g F - F = _
  simp only [Pi.sub_apply, coeffHeckeFun_apply]

  have key : ∀ q : Gamma0 N ⧸ U,
      ρ (s (g • q)) (a (z (c (t g q))))
        = -(ρ (g • q).out (a (z (c (u (g • q))))))
          + ρ (g • q).out (a (z (c (transferAux U g q))))
          + ρ g (ρ q.out (a (z (c (u q))))) := by
    intro q
    rw [hsq (g • q), ht g q, map_mul c, map_mul c,
      hz' (c (u (g • q))⁻¹ * c (transferAux U g q)) (c (u q)),
      hz' (c (u (g • q))⁻¹) (c (transferAux U g q)),
      cocycle_map_inv N ℓ ρ hz (u (g • q)), ← map_mul c]
    simp only [map_add, map_neg, ha_apply N ℓ ρ a ha]
    have e12 : ∀ v : V, ρ ((g • q).out * ((u (g • q) : ↥U) : Gamma0 N)) (ρ (((u (g • q))⁻¹ : ↥U) :
      Gamma0 N) v)
        = ρ (g • q).out v := by
      intro v
      rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel_right]
    have e3 : ∀ v : V, ρ ((g • q).out * ((u (g • q) : ↥U) : Gamma0 N))
        (ρ (((u (g • q))⁻¹ * transferAux U g q : ↥U) : Gamma0 N) v) = ρ g (ρ q.out v) := by
      intro v
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← out_mul_transferAux N ℓ g q]
      group
    rw [e12, e12, e3]
  rw [Finset.sum_congr rfl fun q _ => key q, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← map_sum]
  have hre : ∑ q : Gamma0 N ⧸ U, ρ (g • q).out (a (z (c (u (g • q))))) = F :=
    Fintype.sum_bijective (g • ·) (MulAction.bijective g) _ _ fun q => rfl
  rw [hre]
  abel

end Sh2

public theorem sum_repr_sub_coeffHeckeFun_mem_coboundaries₁ (N ℓ : ℕ) [NeZero ℓ]
    {K : Type} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    (s : CongruenceSubgroup.Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ → CongruenceSubgroup.Gamma0 N)
    (t : CongruenceSubgroup.Gamma0 N → CongruenceSubgroup.Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ →
      ↥(HeckeEis.heckeUpper N ℓ))
    (hs : ∀ q, (s q : CongruenceSubgroup.Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) = q)
    (hst : ∀ g q, s (g • q) * (t g q : CongruenceSubgroup.Gamma0 N) = g * s q)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ groupCohomology.cocycles₁ (Rep.of ρ)) :
    (fun g => letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
        ∑ q : CongruenceSubgroup.Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ,
          ρ (s (g • q)) (a (z (HeckeEis.heckeConj N ℓ (t g q)))))
      - HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ groupCohomology.coboundaries₁ (Rep.of ρ) :=
  Sh2.sum_repr_sub_mem_coboundaries₁ N ℓ ρ a ha s t hs hst hz

public theorem coeffHeckeFun_mem_coboundaries₁ (N ℓ : ℕ) [NeZero ℓ]
    {K : Type} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ groupCohomology.coboundaries₁ (Rep.of ρ)) :
    HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ groupCohomology.coboundaries₁ (Rep.of ρ) :=
  Sh2.mem_coboundaries₁ N ℓ ρ a ha hz

/-- The coefficient Hecke operator, twisted by an intertwining endomorphism, sends cocycles to
cocycles. -/
public theorem coeffHeckeFun_mem_cocycles₁ (N ℓ : ℕ) [NeZero ℓ]
    {K : Type} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ groupCohomology.cocycles₁ (Rep.of ρ)) :
    HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ groupCohomology.cocycles₁ (Rep.of ρ) :=
  Sh2.mem_cocycles₁ N ℓ ρ a ha hz


namespace R2CompTT

open CongruenceSubgroup Matrix groupCohomology
open scoped MatrixGroups

section Entries

variable (N ℓ : ℕ) [NeZero ℓ]

theorem conj_apply00 (u : ↥(heckeUpper N ℓ)) :
    ((heckeConj N ℓ u : Gamma0 N) : SL(2, ℤ)) 0 0 = ((u : Gamma0 N) : SL(2, ℤ)) 0 0 := rfl

theorem conj_apply01 (u : ↥(heckeUpper N ℓ)) :
    ((heckeConj N ℓ u : Gamma0 N) : SL(2, ℤ)) 0 1 = ((u : Gamma0 N) : SL(2, ℤ)) 0 1 / (ℓ : ℤ) := rfl

theorem conj_apply10 (u : ↥(heckeUpper N ℓ)) :
    ((heckeConj N ℓ u : Gamma0 N) : SL(2, ℤ)) 1 0 = ((u : Gamma0 N) : SL(2, ℤ)) 1 0 * (ℓ : ℤ) := rfl

theorem conj_apply11 (u : ↥(heckeUpper N ℓ)) :
    ((heckeConj N ℓ u : Gamma0 N) : SL(2, ℤ)) 1 1 = ((u : Gamma0 N) : SL(2, ℤ)) 1 1 := rfl

theorem dvd_conj_apply10 (u : ↥(heckeUpper N ℓ)) :
    (ℓ : ℤ) ∣ ((heckeConj N ℓ u : Gamma0 N) : SL(2, ℤ)) 1 0 := by
  rw [conj_apply10]; exact dvd_mul_left _ _

end Entries

section Levels

variable (N ℓ ℓ' m : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero m]

omit [NeZero ℓ] [NeZero ℓ'] [NeZero m] in
theorem heckeUpper_le_left (hm : m = ℓ * ℓ') : heckeUpper N m ≤ heckeUpper N ℓ := by
  intro w hw
  rw [mem_heckeUpper] at hw ⊢
  have h : (ℓ : ℤ) ∣ (m : ℤ) := ⟨(ℓ' : ℤ), by rw [hm]; push_cast; ring⟩
  exact h.trans hw

omit [NeZero ℓ] [NeZero ℓ'] [NeZero m] in
theorem heckeUpper_le_right (hm : m = ℓ * ℓ') : heckeUpper N m ≤ heckeUpper N ℓ' := by
  intro w hw
  rw [mem_heckeUpper] at hw ⊢
  have h : (ℓ' : ℤ) ∣ (m : ℤ) := ⟨(ℓ : ℤ), by rw [hm]; push_cast; ring⟩
  exact h.trans hw

theorem mem_heckeUpper_mul_iff (hm : m = ℓ * ℓ') (u : ↥(heckeUpper N ℓ)) :
    (u : Gamma0 N) ∈ heckeUpper N m ↔ heckeConj N ℓ u ∈ heckeUpper N ℓ' := by
  rw [mem_heckeUpper, mem_heckeUpper, conj_apply01]
  obtain ⟨b', hb'⟩ := (mem_heckeUpper N ℓ).mp u.2
  have hℓ0 : (ℓ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne ℓ)
  rw [hb', Int.mul_ediv_cancel_left _ hℓ0, hm, Nat.cast_mul]
  exact mul_dvd_mul_iff_left hℓ0

def toLeft (hm : m = ℓ * ℓ') (w : ↥(heckeUpper N m)) : ↥(heckeUpper N ℓ) :=
  ⟨w, heckeUpper_le_left N ℓ ℓ' m hm w.2⟩

@[scoped simp] theorem coe_toLeft (hm : m = ℓ * ℓ') (w : ↥(heckeUpper N m)) :
    ((toLeft N ℓ ℓ' m hm w : ↥(heckeUpper N ℓ)) : Gamma0 N) = w := rfl

theorem conj_toLeft_mem (hm : m = ℓ * ℓ') (w : ↥(heckeUpper N m)) :
    heckeConj N ℓ (toLeft N ℓ ℓ' m hm w) ∈ heckeUpper N ℓ' :=
  (mem_heckeUpper_mul_iff N ℓ ℓ' m hm _).mp w.2

theorem heckeConj_mul (hm : m = ℓ * ℓ') (w : ↥(heckeUpper N m)) :
    heckeConj N m w =
      heckeConj N ℓ' ⟨heckeConj N ℓ (toLeft N ℓ ℓ' m hm w), conj_toLeft_mem N ℓ ℓ' m hm w⟩ := by
  have hm' : ((m : ℕ) : ℤ) = (ℓ : ℤ) * (ℓ' : ℤ) := by rw [hm, Nat.cast_mul]
  refine Subtype.ext (Subtype.ext ?_)
  change heckeConjMat m (((w : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    = heckeConjMat ℓ' (heckeConjMat ℓ (((w : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
  set A : Matrix (Fin 2) (Fin 2) ℤ := (((w : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · simp only [heckeConjMat_apply_zero_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
    rw [Int.ediv_ediv_of_nonneg (by positivity), hm']
  · simp only [heckeConjMat_apply_one_zero, Fin.zero_eta, Fin.mk_one, Fin.isValue]
    rw [hm', mul_assoc]
  · rfl

theorem heckeConj_mul_eq (hm : m = ℓ * ℓ') (w : ↥(heckeUpper N m)) (u : ↥(heckeUpper N ℓ))
    (u' : ↥(heckeUpper N ℓ')) (hwu : (w : Gamma0 N) = u) (huu' : heckeConj N ℓ u = (u' : Gamma0 N))
      :
    heckeConj N m w = heckeConj N ℓ' u' := by
  rw [heckeConj_mul N ℓ ℓ' m hm w]
  congr 1
  refine Subtype.ext ?_
  rw [← huu']
  change heckeConj N ℓ (toLeft N ℓ ℓ' m hm w) = heckeConj N ℓ u
  congr 1
  exact Subtype.ext hwu

end Levels

/-- If `a` intertwines `ρ ∘ heckeConj N ℓ` with `ρ` on `heckeUpper N ℓ`, and `a'` does so at
`ℓ'`, then `a ∘ₗ a'` does so at `m = ℓ * ℓ'`. -/
public theorem _root_.HeckeEis.heckeConj_intertwines_comp {N ℓ ℓ' m : ℕ} [NeZero ℓ] [NeZero ℓ']
    [NeZero m] (hm : m = ℓ * ℓ') {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) {a a' : V →ₗ[K] V}
    (ha : ∀ u : ↥(heckeUpper N ℓ),
      a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    (ha' : ∀ u : ↥(heckeUpper N ℓ'),
      a' ∘ₗ ρ (heckeConj N ℓ' u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a')
    (w : ↥(heckeUpper N m)) :
    (a ∘ₗ a') ∘ₗ ρ (heckeConj N m w) = ρ (w : CongruenceSubgroup.Gamma0 N) ∘ₗ (a ∘ₗ a') := by
  rw [heckeConj_mul N ℓ ℓ' m hm w, LinearMap.comp_assoc, ha', ← LinearMap.comp_assoc]
  change (a ∘ₗ ρ (heckeConj N ℓ (toLeft N ℓ ℓ' m hm w))) ∘ₗ a' = _
  rw [ha, LinearMap.comp_assoc]
  rfl

section Coset

variable (N ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

theorem exists_heckeConj_eq (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (x : Gamma0 N)
    (hx : (ℓ : ℤ) ∣ (x : SL(2, ℤ)) 1 0) : ∃ u : ↥(heckeUpper N ℓ), heckeConj N ℓ u = x := by
  obtain ⟨c', hc'⟩ := hx
  have hℓ0 : (ℓ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne ℓ)
  set A : Matrix (Fin 2) (Fin 2) ℤ := ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hA
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [← Matrix.det_fin_two, hA]; exact (x : SL(2, ℤ)).2
  have hc'' : A 1 0 = (ℓ : ℤ) * c' := hc'
  let B : Matrix (Fin 2) (Fin 2) ℤ := !![A 0 0, A 0 1 * (ℓ : ℤ); c', A 1 1]
  have hB00 : B 0 0 = A 0 0 := rfl
  have hB01 : B 0 1 = A 0 1 * (ℓ : ℤ) := rfl
  have hB10 : B 1 0 = c' := rfl
  have hB11 : B 1 1 = A 1 1 := rfl
  have hBdet : B.det = 1 := by
    rw [Matrix.det_fin_two, hB00, hB01, hB10, hB11, ← hdet, hc'']; ring
  have hNc : ((A 1 0 : ℤ) : ZMod N) = 0 := by
    have := Gamma0_mem.mp x.2
    simpa [hA] using this
  have hNc' : ((c' : ℤ) : ZMod N) = 0 := by
    have hcop : IsCoprime (N : ℤ) (ℓ : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN).symm
    have hdvd : (N : ℤ) ∣ (ℓ : ℤ) * c' := by
      rw [← hc'']; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hNc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr (hcop.dvd_of_dvd_mul_left hdvd)
  let uSL : SL(2, ℤ) := ⟨B, hBdet⟩
  have huG : uSL ∈ Gamma0 N := by
    rw [Gamma0_mem]
    exact hNc'
  have huU : (⟨uSL, huG⟩ : Gamma0 N) ∈ heckeUpper N ℓ := by
    rw [mem_heckeUpper]
    exact Dvd.intro_left _ rfl
  refine ⟨⟨⟨uSL, huG⟩, huU⟩, Subtype.ext (Subtype.ext ?_)⟩
  change heckeConjMat ℓ B = A
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · simp only [heckeConjMat_apply_zero_one, Fin.zero_eta, Fin.mk_one, Fin.isValue, hB01]
    exact Int.mul_ediv_cancel _ hℓ0
  · simp only [heckeConjMat_apply_one_zero, Fin.zero_eta, Fin.mk_one, Fin.isValue, hB10, hc'']
    ring
  · rfl

theorem exists_mul_mem_dvd (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (γ : Gamma0 N) (k : ℤ)
    (he : ¬ (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 * k * (ℓ' : ℤ) + (γ : SL(2, ℤ)) 1 1) :
    ∃ u'' : ↥(heckeUpper N ℓ'), (ℓ : ℤ) ∣ ((γ : Gamma0 N) * u'' : SL(2, ℤ)) 1 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  set c : ℤ := (γ : SL(2, ℤ)) 1 0 with hc
  set d : ℤ := (γ : SL(2, ℤ)) 1 1 with hd
  set e : ℤ := c * k * (ℓ' : ℤ) + d with he_def
  have heZ : ((e : ℤ) : ZMod ℓ) ≠ 0 := fun h => he ((ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp h)
  have hNZ : ((N : ℤ) : ZMod ℓ) ≠ 0 := by
    intro h
    rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff] at h
    exact hℓN h
  set Y : ZMod ℓ := -(c : ZMod ℓ) * (((N : ℤ) : ZMod ℓ) * (e : ZMod ℓ))⁻¹ with hY
  let z₁ : ℕ := Y.val
  let zz : ℤ := (N : ℤ) * (z₁ : ℤ)
  have hz₁ : ((z₁ : ℤ) : ZMod ℓ) = Y := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val Y
  have hzz : ((zz : ℤ) : ZMod ℓ) = ((N : ℤ) : ZMod ℓ) * Y := by
    change (((N : ℤ) * (z₁ : ℤ) : ℤ) : ZMod ℓ) = _
    rw [Int.cast_mul, hz₁]
  let B : Matrix (Fin 2) (Fin 2) ℤ := !![1 + k * (ℓ' : ℤ) * zz, k * (ℓ' : ℤ); zz, 1]
  have hB00 : B 0 0 = 1 + k * (ℓ' : ℤ) * zz := rfl
  have hB01 : B 0 1 = k * (ℓ' : ℤ) := rfl
  have hB10 : B 1 0 = zz := rfl
  have hB11 : B 1 1 = 1 := rfl
  have hBdet : B.det = 1 := by rw [Matrix.det_fin_two, hB00, hB01, hB10, hB11]; ring
  let uSL : SL(2, ℤ) := ⟨B, hBdet⟩
  have huG : uSL ∈ Gamma0 N := by
    rw [Gamma0_mem]
    change ((B 1 0 : ℤ) : ZMod N) = 0
    rw [hB10]
    change (((N : ℤ) * (z₁ : ℤ) : ℤ) : ZMod N) = 0
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  have huU : (⟨uSL, huG⟩ : Gamma0 N) ∈ heckeUpper N ℓ' := by
    rw [mem_heckeUpper]
    change (ℓ' : ℤ) ∣ B 0 1
    rw [hB01]; exact dvd_mul_left _ _
  refine ⟨⟨⟨uSL, huG⟩, huU⟩, ?_⟩

  have hentry : ((γ : Gamma0 N) * (⟨⟨uSL, huG⟩, huU⟩ : ↥(heckeUpper N ℓ')) : SL(2, ℤ)) 1 0
      = c * (1 + k * (ℓ' : ℤ) * zz) + d * zz := by
    change (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * B) 1 0 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two, hB00, hB10]
  rw [hentry, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_one, hzz]
  have hNe : ((N : ℤ) : ZMod ℓ) * (e : ZMod ℓ) ≠ 0 := mul_ne_zero hNZ heZ
  have hX : (((N : ℤ) : ZMod ℓ) * (e : ZMod ℓ)) * Y = -(c : ZMod ℓ) := by
    rw [hY, mul_comm, mul_assoc, inv_mul_cancel₀ hNe, mul_one]
  have he' : ((e : ℤ) : ZMod ℓ) = (c : ZMod ℓ) * (k : ZMod ℓ) * ((ℓ' : ℤ) : ZMod ℓ) + (d : ZMod ℓ)
    := by
    rw [he_def, Int.cast_add, Int.cast_mul, Int.cast_mul]
  linear_combination hX - (((N : ℤ) : ZMod ℓ) * Y) * he'

theorem exists_conj_mul_eq (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓℓ' : ¬ ℓ ∣ ℓ') (γ : Gamma0 N) :
    ∃ (u : ↥(heckeUpper N ℓ)) (u' : ↥(heckeUpper N ℓ')),
      (heckeConj N ℓ u : Gamma0 N) * u' = γ := by
  have hk : ∃ k : ℤ, ¬ (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 * k * (ℓ' : ℤ) + (γ : SL(2, ℤ)) 1 1 := by
    by_cases hd : (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 1
    · refine ⟨1, fun h => ?_⟩
      rw [mul_one] at h
      have hc : (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 * (ℓ' : ℤ) := (dvd_add_left hd).mp h
      have hℓp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
      rcases hℓp.dvd_or_dvd hc with h1 | h1
      ·
        have hdet := Matrix.det_fin_two ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        rw [(γ : SL(2, ℤ)).2] at hdet
        have : (ℓ : ℤ) ∣ 1 := by
          rw [hdet]
          exact dvd_sub (hd.mul_left _) (h1.mul_left _)
        exact hℓ.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
      · exact hℓℓ' (by exact_mod_cast h1)
    · exact ⟨0, by simpa using hd⟩
  obtain ⟨k, hk⟩ := hk
  obtain ⟨u'', hu''⟩ := exists_mul_mem_dvd N ℓ ℓ' hℓ hℓN γ k hk
  obtain ⟨u, hu⟩ := exists_heckeConj_eq N ℓ hℓ hℓN ((γ : Gamma0 N) * u'') hu''
  refine ⟨u, u''⁻¹, ?_⟩
  rw [hu, Subgroup.coe_inv, mul_inv_cancel_right]

theorem exists_section (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓℓ' : ¬ ℓ ∣ ℓ') :
    ∃ σ : Gamma0 N ⧸ heckeUpper N ℓ' → ↥(heckeUpper N ℓ),
      ∀ q', ((heckeConj N ℓ (σ q') : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q' := by
  have h : ∀ q' : Gamma0 N ⧸ heckeUpper N ℓ', ∃ u : ↥(heckeUpper N ℓ),
      ((heckeConj N ℓ u : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q' := by
    intro q'
    obtain ⟨u, u', huu'⟩ := exists_conj_mul_eq N ℓ ℓ' hℓ hℓN hℓℓ' q'.out
    refine ⟨u, ?_⟩
    rw [← QuotientGroup.out_eq' q']
    refine QuotientGroup.eq.mpr ?_
    rw [← huu', inv_mul_cancel_left]
    exact u'.2
  choose σ hσ using h
  exact ⟨σ, hσ⟩

end Coset

section Main

variable {N ℓ ℓ' m : ℕ} [NeZero ℓ] [NeZero ℓ'] [NeZero m]
variable {K : Type} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (ρ : Representation K (Gamma0 N) V) (a a' : V →ₗ[K] V)
variable (σ : Gamma0 N ⧸ heckeUpper N ℓ' → ↥(heckeUpper N ℓ))
variable (hσ : ∀ q', ((heckeConj N ℓ (σ q') : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q')

def sP (q' : Gamma0 N ⧸ heckeUpper N ℓ') : Gamma0 N := heckeConj N ℓ (σ q')

include hσ in
theorem sP_coe (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ((sP σ q' : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q' := hσ q'

def tP (h : Gamma0 N) (q' : Gamma0 N ⧸ heckeUpper N ℓ') : ↥(heckeUpper N ℓ') :=
  ⟨(sP σ (h • q'))⁻¹ * (h * sP σ q'), by
    refine QuotientGroup.eq.mp ?_
    rw [sP_coe σ hσ]
    change h • q' = h • ((sP σ q' : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ')
    rw [sP_coe σ hσ]⟩

@[scoped simp] theorem coe_tP (h : Gamma0 N) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ((tP σ hσ h q' : ↥(heckeUpper N ℓ')) : Gamma0 N) = (sP σ (h • q'))⁻¹ * (h * sP σ q') := rfl

theorem sP_mul_tP (h : Gamma0 N) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    sP σ (h • q') * (tP σ hσ h q' : Gamma0 N) = h * sP σ q' := by
  rw [coe_tP, mul_inv_cancel_left]

noncomputable def Ty (z : Gamma0 N → V) : Gamma0 N → V := fun h =>
  letI := (heckeUpper N ℓ').fintypeQuotientOfFiniteIndex
  ∑ q' : Gamma0 N ⧸ heckeUpper N ℓ', ρ (sP σ (h • q')) (a' (z (heckeConj N ℓ' (tP σ hσ h q'))))

theorem Ty_sub_mem
    (ha' : ∀ u : ↥(heckeUpper N ℓ'), a' ∘ₗ ρ (heckeConj N ℓ' u) = ρ (u : Gamma0 N) ∘ₗ a')
    {z : Gamma0 N → V} (hz : z ∈ cocycles₁ (Rep.of ρ)) :
    Ty ρ a' σ hσ z - coeffHeckeFun N ℓ' ρ a' z ∈ coboundaries₁ (Rep.of ρ) :=
  sum_repr_sub_coeffHeckeFun_mem_coboundaries₁ N ℓ' ρ a' ha' (sP σ) (tP σ hσ)
    (sP_coe σ hσ) (sP_mul_tP σ hσ) hz

noncomputable def PsiFun (x : (Gamma0 N ⧸ heckeUpper N ℓ) × (Gamma0 N ⧸ heckeUpper N ℓ')) :
    Gamma0 N ⧸ heckeUpper N m :=
  ((x.1.out * ((σ x.2 : ↥(heckeUpper N ℓ)) : Gamma0 N) : Gamma0 N) : Gamma0 N ⧸ heckeUpper N m)

variable (hm : m = ℓ * ℓ')

include hσ hm in
theorem PsiFun_injective : Function.Injective (PsiFun (m := m) σ) := by
  rintro ⟨q₁, q₁'⟩ ⟨q₂, q₂'⟩ h
  have hW : (q₁.out * ((σ q₁' : ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹
      * (q₂.out * ((σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N)) ∈ heckeUpper N m :=
    QuotientGroup.eq.mp h
  have hU : q₁.out⁻¹ * q₂.out ∈ heckeUpper N ℓ := by
    have h1 : (q₁.out * ((σ q₁' : ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹
        * (q₂.out * ((σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N)) ∈ heckeUpper N ℓ :=
      heckeUpper_le_left N ℓ ℓ' m hm hW
    rw [_root_.mul_inv_rev, mul_assoc, ← mul_assoc (q₁.out⁻¹)] at h1
    have h2 := (Subgroup.mul_mem_cancel_left _ ((heckeUpper N ℓ).inv_mem (σ q₁').2)).mp h1
    exact (Subgroup.mul_mem_cancel_right _ (σ q₂').2).mp h2
  have hq : q₁ = q₂ := by
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
    exact QuotientGroup.eq.mpr hU
  subst hq
  have hW' : (((σ q₁')⁻¹ * σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N) ∈ heckeUpper N m := by
    have : (q₁.out * ((σ q₁' : ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹
        * (q₁.out * ((σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N))
        = (((σ q₁')⁻¹ * σ q₂' : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
      push_cast; group
    rw [← this]; exact hW
  have hU' : heckeConj N ℓ ((σ q₁')⁻¹ * σ q₂') ∈ heckeUpper N ℓ' :=
    (mem_heckeUpper_mul_iff N ℓ ℓ' m hm _).mp hW'
  rw [map_mul, map_inv] at hU'
  have hq' : ((sP σ q₁' : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = (sP σ q₂' : Gamma0 N) :=
    QuotientGroup.eq.mpr hU'
  rw [sP_coe σ hσ, sP_coe σ hσ] at hq'
  rw [hq']

include hσ hm in
theorem PsiFun_surjective : Function.Surjective (PsiFun (m := m) σ) := by
  intro Q
  induction Q using QuotientGroup.induction_on with
  | H γ =>
    set q : Gamma0 N ⧸ heckeUpper N ℓ := (γ : Gamma0 N ⧸ heckeUpper N ℓ) with hq
    have hu₀ : q.out⁻¹ * γ ∈ heckeUpper N ℓ := QuotientGroup.eq.mp (by rw [QuotientGroup.out_eq'])
    set u₀ : ↥(heckeUpper N ℓ) := ⟨q.out⁻¹ * γ, hu₀⟩ with hu₀_def
    set q' : Gamma0 N ⧸ heckeUpper N ℓ' :=
      ((heckeConj N ℓ u₀ : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') with hq'
    refine ⟨(q, q'), ?_⟩
    change ((q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N) : Gamma0 N) : Gamma0 N ⧸ heckeUpper N
      m)
      = (γ : Gamma0 N ⧸ heckeUpper N m)
    refine QuotientGroup.eq.mpr ?_
    have hmem : (((σ q')⁻¹ * u₀ : ↥(heckeUpper N ℓ)) : Gamma0 N) ∈ heckeUpper N m := by
      refine (mem_heckeUpper_mul_iff N ℓ ℓ' m hm _).mpr ?_
      rw [map_mul, map_inv]
      refine QuotientGroup.eq.mp ?_
      change ((sP σ q' : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q'
      exact sP_coe σ hσ q'
    have : (q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹ * γ
        = (((σ q')⁻¹ * u₀ : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
      rw [hu₀_def]; push_cast; group
    rw [this]; exact hmem

noncomputable def Psi : (Gamma0 N ⧸ heckeUpper N ℓ) × (Gamma0 N ⧸ heckeUpper N ℓ') ≃
    Gamma0 N ⧸ heckeUpper N m :=
  Equiv.ofBijective (PsiFun σ) ⟨PsiFun_injective σ hσ hm, PsiFun_surjective σ hσ hm⟩

theorem Psi_apply (x : (Gamma0 N ⧸ heckeUpper N ℓ) × (Gamma0 N ⧸ heckeUpper N ℓ')) :
    Psi σ hσ hm x =
      ((x.1.out * ((σ x.2 : ↥(heckeUpper N ℓ)) : Gamma0 N) : Gamma0 N) : Gamma0 N ⧸ heckeUpper N m)
        :=
  rfl

noncomputable def wU (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N
  ℓ') :
    ↥(heckeUpper N ℓ) :=
  (σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q'))⁻¹
    * transferAux (heckeUpper N ℓ) g q * σ q'

theorem heckeConj_wU (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ)
    (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    heckeConj N ℓ (wU σ g q q') =
      (tP σ hσ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) q' : Gamma0 N) := by
  rw [wU, map_mul, map_mul, map_inv, coe_tP, mul_assoc]
  rfl

include hσ hm in
theorem wU_mem (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ((wU σ g q q' : ↥(heckeUpper N ℓ)) : Gamma0 N) ∈ heckeUpper N m := by
  refine (mem_heckeUpper_mul_iff N ℓ ℓ' m hm _).mpr ?_
  rw [heckeConj_wU σ hσ]
  exact (tP σ hσ _ q').2

theorem coe_wU (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    ((wU σ g q q' : ↥(heckeUpper N ℓ)) : Gamma0 N) =
      ((σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q') :
          ↥(heckeUpper N ℓ)) : Gamma0 N)⁻¹
        * ((g • q).out⁻¹ * (g * q.out)) * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N) := rfl

theorem smul_Psi (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    g • Psi σ hσ hm (q, q') =
      Psi σ hσ hm (g • q, (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q') := by
  rw [Psi_apply, Psi_apply]
  change (((g * (q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N))) : Gamma0 N) :
      Gamma0 N ⧸ heckeUpper N m) = _
  refine QuotientGroup.eq.mpr ?_
  have key : ((g • q).out *
        ((σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q') :
          ↥(heckeUpper N ℓ)) : Gamma0 N))⁻¹ * (g * (q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0
            N)))
      = ((wU σ g q q' : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
    rw [coe_wU]; group
  have hmem := (heckeUpper N m).inv_mem (wU_mem σ hσ hm g q q')
  rw [← key, _root_.mul_inv_rev, inv_inv] at hmem
  exact hmem

noncomputable def SS (Q : Gamma0 N ⧸ heckeUpper N m) : Gamma0 N :=
  ((Psi σ hσ hm).symm Q).1.out * (((σ ((Psi σ hσ hm).symm Q).2) : ↥(heckeUpper N ℓ)) : Gamma0 N)

theorem SS_Psi (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    SS σ hσ hm (Psi σ hσ hm (q, q')) = q.out * ((σ q' : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
  rw [SS, Equiv.symm_apply_apply]

theorem SS_coe (Q : Gamma0 N ⧸ heckeUpper N m) :
    ((SS σ hσ hm Q : Gamma0 N) : Gamma0 N ⧸ heckeUpper N m) = Q := by
  conv_rhs => rw [← (Psi σ hσ hm).apply_symm_apply Q]
  unfold SS
  rw [Psi_apply]

noncomputable def TT (g : Gamma0 N) (Q : Gamma0 N ⧸ heckeUpper N m) : ↥(heckeUpper N m) :=
  ⟨(SS σ hσ hm (g • Q))⁻¹ * (g * SS σ hσ hm Q), by
    refine QuotientGroup.eq.mp ?_
    rw [SS_coe]
    change g • Q = g • ((SS σ hσ hm Q : Gamma0 N) : Gamma0 N ⧸ heckeUpper N m)
    rw [SS_coe]⟩

@[scoped simp] theorem coe_TT (g : Gamma0 N) (Q : Gamma0 N ⧸ heckeUpper N m) :
    ((TT σ hσ hm g Q : ↥(heckeUpper N m)) : Gamma0 N) = (SS σ hσ hm (g • Q))⁻¹ * (g * SS σ hσ hm Q)
      :=
  rfl

theorem SS_mul_TT (g : Gamma0 N) (Q : Gamma0 N ⧸ heckeUpper N m) :
    SS σ hσ hm (g • Q) * (TT σ hσ hm g Q : Gamma0 N) = g * SS σ hσ hm Q := by
  rw [coe_TT, mul_inv_cancel_left]

theorem coe_TT_Psi (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) (q' : Gamma0 N ⧸ heckeUpper N ℓ')
  :
    ((TT σ hσ hm g (Psi σ hσ hm (q, q')) : ↥(heckeUpper N m)) : Gamma0 N)
      = ((wU σ g q q' : ↥(heckeUpper N ℓ)) : Gamma0 N) := by
  rw [coe_TT, smul_Psi, SS_Psi, SS_Psi, coe_wU]
  group

theorem heckeConj_TT_Psi (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ)
    (q' : Gamma0 N ⧸ heckeUpper N ℓ') :
    heckeConj N m (TT σ hσ hm g (Psi σ hσ hm (q, q'))) =
      heckeConj N ℓ' (tP σ hσ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) q') :=
  heckeConj_mul_eq N ℓ ℓ' m hm _ (wU σ g q q') _ (coe_TT_Psi σ hσ hm g q q') (heckeConj_wU σ hσ g q
    q')

noncomputable def TmS (z : Gamma0 N → V) : Gamma0 N → V := fun g =>
  letI := (heckeUpper N m).fintypeQuotientOfFiniteIndex
  ∑ Q : Gamma0 N ⧸ heckeUpper N m, ρ (SS σ hσ hm (g • Q)) ((a ∘ₗ a') (z (heckeConj N m (TT σ hσ hm
    g Q))))

theorem TmS_sub_mem
    (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    (ha' : ∀ u : ↥(heckeUpper N ℓ'), a' ∘ₗ ρ (heckeConj N ℓ' u) = ρ (u : Gamma0 N) ∘ₗ a')
    {z : Gamma0 N → V} (hz : z ∈ cocycles₁ (Rep.of ρ)) :
    TmS ρ a a' σ hσ hm z - coeffHeckeFun N m ρ (a ∘ₗ a') z ∈ coboundaries₁ (Rep.of ρ) :=
  sum_repr_sub_coeffHeckeFun_mem_coboundaries₁ N m ρ (a ∘ₗ a')
    (heckeConj_intertwines_comp hm ρ ha ha')
    (SS σ hσ hm) (TT σ hσ hm) (SS_coe σ hσ hm) (SS_mul_TT σ hσ hm) hz

theorem coeffHeckeFun_Ty
    (ha : ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    (z : Gamma0 N → V) :
    coeffHeckeFun N ℓ ρ a (Ty ρ a' σ hσ z) = TmS ρ a a' σ hσ hm z := by
  letI iU := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  letI iU' := (heckeUpper N ℓ').fintypeQuotientOfFiniteIndex
  letI iW := (heckeUpper N m).fintypeQuotientOfFiniteIndex
  funext g
  rw [coeffHeckeFun_apply]
  change ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, ρ (g • q).out (a (Ty ρ a' σ hσ z _)) =
    ∑ Q : Gamma0 N ⧸ heckeUpper N m, ρ (SS σ hσ hm (g • Q)) ((a ∘ₗ a') (z (heckeConj N m (TT σ hσ
      hm g Q))))

  rw [← Fintype.sum_equiv (Psi σ hσ hm) (fun x => ρ (SS σ hσ hm (g • Psi σ hσ hm x))
      ((a ∘ₗ a') (z (heckeConj N m (TT σ hσ hm g (Psi σ hσ hm x))))))
      (fun Q => ρ (SS σ hσ hm (g • Q)) ((a ∘ₗ a') (z (heckeConj N m (TT σ hσ hm g Q)))))
      (fun x => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_

  simp only [Ty, map_sum]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have hpush : a (ρ (sP σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q'))
      (a' (z (heckeConj N ℓ' (tP σ hσ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N)
        q')))))
      = ρ ((σ ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) : Gamma0 N) • q') :
          ↥(heckeUpper N ℓ)) : Gamma0 N)
        (a (a' (z (heckeConj N ℓ' (tP σ hσ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q) :
          Gamma0 N) q'))))) :=
    LinearMap.congr_fun (ha _) _
  rw [hpush, smul_Psi, SS_Psi, heckeConj_TT_Psi, map_mul, Module.End.mul_apply,
    LinearMap.comp_apply]

theorem coeffHeckeFun_sub (ℓ₀ : ℕ) [NeZero ℓ₀] (b : V →ₗ[K] V) (z w : Gamma0 N → V) :
    coeffHeckeFun N ℓ₀ ρ b (z - w) = coeffHeckeFun N ℓ₀ ρ b z - coeffHeckeFun N ℓ₀ ρ b w := by
  letI := (heckeUpper N ℓ₀).fintypeQuotientOfFiniteIndex
  funext g
  simp only [coeffHeckeFun_apply, Pi.sub_apply, map_sub, Finset.sum_sub_distrib]

end Main

end R2CompTT

/-- Hecke composition at a prime on coefficient cocycles, modulo
coboundaries: for prime `ℓ` not dividing `N` or `ℓ'`, and `m = ℓ * ℓ'`, the
composite of the coefficient Hecke operators at `ℓ'` and then at `ℓ`, twisted
by intertwining endomorphisms `a'` and `a`, differs from the coefficient
Hecke operator at `m`, twisted by `a ∘ₗ a'`, by a coboundary. Cocycles and
coboundaries are Mathlib's `groupCohomology.cocycles₁` and
`groupCohomology.coboundaries₁` of `Rep.of ρ`. -/
public theorem coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coboundaries₁
    (N ℓ ℓ' m : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero m] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (hℓℓ' : ¬ ℓ ∣ ℓ') (hm : m = ℓ * ℓ')
    {K : Type} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a a' : V →ₗ[K] V)
    (ha : ∀ u : ↥(heckeUpper N ℓ),
      a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    (ha' : ∀ u : ↥(heckeUpper N ℓ'),
      a' ∘ₗ ρ (heckeConj N ℓ' u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a')
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ groupCohomology.cocycles₁ (Rep.of ρ)) :
    coeffHeckeFun N ℓ ρ a (coeffHeckeFun N ℓ' ρ a' z)
      - coeffHeckeFun N m ρ (a ∘ₗ a') z ∈ groupCohomology.coboundaries₁ (Rep.of ρ) := by
  obtain ⟨σ, hσ⟩ := R2CompTT.exists_section N ℓ ℓ' hℓ hℓN hℓℓ'
  have h1 : coeffHeckeFun N ℓ ρ a
      (R2CompTT.Ty ρ a' σ hσ z - coeffHeckeFun N ℓ' ρ a' z) ∈
      groupCohomology.coboundaries₁ (Rep.of ρ) :=
    coeffHeckeFun_mem_coboundaries₁ N ℓ ρ a ha
      (R2CompTT.Ty_sub_mem ρ a' σ hσ ha' hz)
  have h2 : coeffHeckeFun N ℓ ρ a (R2CompTT.Ty ρ a' σ hσ z)
      - coeffHeckeFun N m ρ (a ∘ₗ a') z ∈ groupCohomology.coboundaries₁ (Rep.of ρ) := by
    rw [R2CompTT.coeffHeckeFun_Ty ρ a a' σ hσ hm ha]
    exact R2CompTT.TmS_sub_mem ρ a a' σ hσ hm ha ha' hz
  have h3 := (groupCohomology.coboundaries₁ (Rep.of ρ)).sub_mem h2 h1
  rw [R2CompTT.coeffHeckeFun_sub] at h3
  convert h3 using 1
  abel

end HeckeEis
