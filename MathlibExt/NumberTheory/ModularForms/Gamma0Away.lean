/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Gamma0Away.lean`,
`Definitions/Def_Gamma0AwayUnitsChar.lean`,
`Definitions/Def_Gamma0UnitsChar.lean` and
`Definitions/Def_IharaAmalgamMap.lean`
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

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace Ihara

open Matrix

open scoped MatrixGroups

/-- The ring `ℤ[1/q]`, as the localization of `ℤ` away from `q`. -/
abbrev ZAway (q : ℕ) : Type := Localization.Away (q : ℤ)

variable (N q : ℕ)

/-- The subgroup `Γ₀(N)` of `SL(2, ℤ[1/q])`: matrices whose lower-left
entry is divisible by `N`. -/
def Gamma0Away : Subgroup (SL(2, ZAway q)) where
  carrier := { g | (N : ZAway q) ∣ g 1 0 }
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    change (N : ZAway q) ∣ (1 : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0
    rw [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    exact dvd_zero _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    change (N : ZAway q) ∣ (a.1 * b.1) 1 0
    rw [(Matrix.two_mul_expl a.1 b.1).2.2.1]
    exact dvd_add (ha.mul_right _) (hb.mul_left _)
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [SpecialLinearGroup.SL2_inv_expl a]
    simp only [SpecialLinearGroup.coe_mk]
    exact dvd_neg.mpr ha

theorem mem_Gamma0Away {N q : ℕ} {g : SL(2, ZAway q)} :
    g ∈ Gamma0Away N q ↔ (N : ZAway q) ∣ g 1 0 :=
  Iff.rfl

theorem mem_Gamma0Away_iff_algebraMap {N q : ℕ} {g : SL(2, ZAway q)} :
    g ∈ Gamma0Away N q ↔ algebraMap ℤ (ZAway q) (N : ℤ) ∣ g 1 0 := by
  have h : algebraMap ℤ (ZAway q) (N : ℤ) = (N : ZAway q) := by simp
  rw [mem_Gamma0Away, h]

/-- The diagonal matrix `diag(1, q)` over `ℤ[1/q]`. -/
def wMat : Matrix (Fin 2) (Fin 2) (ZAway q) := !![1, 0; 0, (q : ZAway q)]

/-- The diagonal matrix `diag(1, q⁻¹)` over `ℤ[1/q]`. -/
noncomputable def wMatInv : Matrix (Fin 2) (Fin 2) (ZAway q) :=
  !![1, 0; 0, IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ)]

theorem q_mul_invSelf :
    (q : ZAway q) * IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) = 1 := by
  simpa using IsLocalization.Away.mul_invSelf (S := ZAway q) ((q : ℕ) : ℤ)

theorem invSelf_mul_q :
    IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ) * (q : ZAway q) = 1 := by
  rw [mul_comm]; exact q_mul_invSelf q

theorem wMat_mul_wMatInv : wMat q * wMatInv q = 1 := by
  rw [wMat, wMatInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [q_mul_invSelf q]

theorem wMatInv_mul_wMat : wMatInv q * wMat q = 1 := by
  rw [wMat, wMatInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [invSelf_mul_q q]

noncomputable def wConjFun (γ : SL(2, ZAway q)) : SL(2, ZAway q) :=
  ⟨wMatInv q * γ.1 * wMat q, by
    rw [det_mul, det_mul, γ.2, mul_one, ← det_mul, wMatInv_mul_wMat, det_one]⟩

noncomputable def wConjInvFun (γ : SL(2, ZAway q)) : SL(2, ZAway q) :=
  ⟨wMat q * γ.1 * wMatInv q, by
    rw [det_mul, det_mul, γ.2, mul_one, ← det_mul, wMat_mul_wMatInv, det_one]⟩

theorem wConjFun_coe (γ : SL(2, ZAway q)) :
    (wConjFun q γ).1 = wMatInv q * γ.1 * wMat q :=
  rfl

theorem wConjInvFun_coe (γ : SL(2, ZAway q)) :
    (wConjInvFun q γ).1 = wMat q * γ.1 * wMatInv q :=
  rfl

/-- The map `A ↦ D⁻¹ * A * D` with `D = diag(1, q)`, as a multiplicative
equivalence of `SL(2, ℤ[1/q])`. -/
noncomputable def wConj : SL(2, ZAway q) ≃* SL(2, ZAway q) where
  toFun := wConjFun q
  invFun := wConjInvFun q
  left_inv γ := Subtype.ext <| by
    rw [wConjInvFun_coe, wConjFun_coe,
      show wMat q * (wMatInv q * γ.1 * wMat q) * wMatInv q
          = (wMat q * wMatInv q) * γ.1 * (wMat q * wMatInv q) by
        simp only [mul_assoc],
      wMat_mul_wMatInv, one_mul, mul_one]
  right_inv γ := Subtype.ext <| by
    rw [wConjFun_coe, wConjInvFun_coe,
      show wMatInv q * (wMat q * γ.1 * wMatInv q) * wMat q
          = (wMatInv q * wMat q) * γ.1 * (wMatInv q * wMat q) by
        simp only [mul_assoc],
      wMatInv_mul_wMat, one_mul, mul_one]
  map_mul' a b := Subtype.ext <| by
    change wMatInv q * (a.1 * b.1) * wMat q
        = wMatInv q * a.1 * wMat q * (wMatInv q * b.1 * wMat q)
    rw [show wMatInv q * a.1 * wMat q * (wMatInv q * b.1 * wMat q)
          = wMatInv q * a.1 * (wMat q * wMatInv q) * (b.1 * wMat q) by
        simp only [mul_assoc],
      wMat_mul_wMatInv, mul_one]
    simp only [mul_assoc]

@[simp]
theorem wConj_coe (γ : SL(2, ZAway q)) :
    (wConj q γ).1 = wMatInv q * γ.1 * wMat q :=
  rfl

@[simp]
theorem wConj_symm_coe (γ : SL(2, ZAway q)) :
    ((wConj q).symm γ).1 = wMat q * γ.1 * wMatInv q :=
  rfl

/-- The unit-valued lower-right-entry character of `Γ₀(N)`. -/
def gamma0UnitsHom (N : ℕ) : CongruenceSubgroup.Gamma0 N →* (ZMod N)ˣ :=
  (CongruenceSubgroup.Gamma0Map N).toHomUnits

@[simp]
theorem gamma0UnitsHom_coe (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    (gamma0UnitsHom N g : ZMod N) = CongruenceSubgroup.Gamma0Map N g :=
  rfl

/-- Base change of matrices from `SL(2, ℤ)` to `SL(2, ℤ[1/q])`. -/
def slToAway : SL(2, ℤ) →* SL(2, ZAway q) :=
  Matrix.SpecialLinearGroup.map (algebraMap ℤ (ZAway q))

@[simp]
theorem coe_slToAway (g : SL(2, ℤ)) :
    ((slToAway q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      ((g : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ (ZAway q)) :=
  rfl

/-- The first vertex map: entrywise base change of `Γ₀(N)` over `ℤ` into `SL(2, ℤ[1/q])`
(not injective when `q = 0`, where `ℤ[1/0]` is the zero ring). -/
def vertexZero : CongruenceSubgroup.Gamma0 N →* SL(2, ZAway q) :=
  (slToAway q).comp (CongruenceSubgroup.Gamma0 N).subtype

@[simp]
theorem coe_vertexZero (g : CongruenceSubgroup.Gamma0 N) :
    ((vertexZero N q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ (ZAway q)) :=
  rfl

/-- The second vertex map: entrywise base change of `Γ₀(N)` followed by
`A ↦ diag(1, q) * A * diag(1, q)⁻¹`, the inverse of `wConj`. -/
noncomputable def vertexOne : CongruenceSubgroup.Gamma0 N →* SL(2, ZAway q) :=
  (wConj q).symm.toMonoidHom.comp (vertexZero N q)

theorem coe_vertexOne (g : CongruenceSubgroup.Gamma0 N) :
    ((vertexOne N q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      wMat q * (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map
        (algebraMap ℤ (ZAway q)) * wMatInv q :=
  rfl

theorem wMat_mul_mul_wMatInv (M : Matrix (Fin 2) (Fin 2) (ZAway q)) :
    wMat q * M * wMatInv q =
      !![M 0 0, M 0 1 * IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ);
         (q : ZAway q) * M 1 0, M 1 1] := by
  conv_lhs => rw [Matrix.eta_fin_two M]
  rw [wMat, wMatInv, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [one_mul, zero_mul, mul_zero, add_zero, zero_add, mul_one]
  rw [mul_right_comm (q : ZAway q) (M 1 1), q_mul_invSelf, one_mul]

theorem coe_vertexOne_eq (g : CongruenceSubgroup.Gamma0 N) :
    ((vertexOne N q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 0 0),
         algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 0 1) *
           IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ);
         (q : ZAway q) * algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 0),
         algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 1)] := by
  rw [coe_vertexOne, wMat_mul_mul_wMatInv]
  rfl

theorem N_dvd_entry (g : CongruenceSubgroup.Gamma0 N) :
    (N : ℤ) ∣ (g : SL(2, ℤ)) 1 0 := by
  have h := g.2
  rw [CongruenceSubgroup.Gamma0_mem, CharP.intCast_eq_zero_iff (ZMod N) N] at h
  exact h

theorem vertexZero_mem (g : CongruenceSubgroup.Gamma0 N) :
    vertexZero N q g ∈ Gamma0Away N q := by
  obtain ⟨k, hk⟩ := N_dvd_entry N g
  refine ⟨algebraMap ℤ (ZAway q) k, ?_⟩
  show algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 0) = _
  rw [hk, map_mul]
  simp

theorem vertexOne_apply_one_zero (g : CongruenceSubgroup.Gamma0 N) :
    (vertexOne N q g : SL(2, ZAway q)) 1 0 =
      (q : ZAway q) * algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 0) := by
  rw [coe_vertexOne_eq]
  rfl

theorem vertexOne_mem (g : CongruenceSubgroup.Gamma0 N) :
    vertexOne N q g ∈ Gamma0Away N q := by
  rw [mem_Gamma0Away, vertexOne_apply_one_zero]
  obtain ⟨k, hk⟩ := N_dvd_entry N g
  refine ⟨(q : ZAway q) * algebraMap ℤ (ZAway q) k, ?_⟩
  rw [hk, map_mul, eq_intCast, Int.cast_natCast]
  ring

theorem isUnit_intCast_q (hNq : Nat.Coprime N q) :
    IsUnit (((q : ℤ) : ZMod N)) := by
  have h : ((ZMod.unitOfCoprime q hNq.symm : (ZMod N)ˣ) : ZMod N)
      = (((q : ℤ)) : ZMod N) := by
    rw [ZMod.coe_unitOfCoprime, Int.cast_natCast]
  exact h ▸ (ZMod.unitOfCoprime q hNq.symm).isUnit

/-- The ring map `ℤ[1/q] → ZMod N`, defined when `q` is coprime to `N`. -/
noncomputable def zAwayToZMod (hNq : Nat.Coprime N q) : ZAway q →+* ZMod N :=
  IsLocalization.Away.lift (S := ZAway q) (g := Int.castRingHom (ZMod N)) (q : ℤ)
    (by rw [eq_intCast]; exact isUnit_intCast_q N q hNq)

@[simp]
theorem zAwayToZMod_algebraMap (hNq : Nat.Coprime N q) (a : ℤ) :
    zAwayToZMod N q hNq (algebraMap ℤ (ZAway q) a) = (a : ZMod N) := by
  rw [zAwayToZMod, IsLocalization.Away.lift_eq, eq_intCast]

theorem zAwayToZMod_natCast_self (hNq : Nat.Coprime N q) :
    zAwayToZMod N q hNq (N : ZAway q) = 0 := by
  have h : ((N : ℕ) : ZAway q) = algebraMap ℤ (ZAway q) ((N : ℕ) : ℤ) := by simp
  rw [h, zAwayToZMod_algebraMap, Int.cast_natCast, ZMod.natCast_self]

theorem zAwayToZMod_apply_one_zero (hNq : Nat.Coprime N q) (g : Gamma0Away N q) :
    zAwayToZMod N q hNq ((g : SL(2, ZAway q)) 1 0) = 0 := by
  obtain ⟨r, hr⟩ := g.2
  rw [hr, map_mul, zAwayToZMod_natCast_self, zero_mul]

/-- The lower-right-entry map `Γ₀(N)` over `ℤ[1/q]` to `ZMod N`. -/
noncomputable def gamma0AwayMap (hNq : Nat.Coprime N q) :
    Gamma0Away N q →* ZMod N where
  toFun g := zAwayToZMod N q hNq ((g : SL(2, ZAway q)) 1 1)
  map_one' := by
    have h : ((1 : Gamma0Away N q) : SL(2, ZAway q)) 1 1 = 1 := rfl
    rw [h, map_one]
  map_mul' a b := by
    have h : ((a * b : Gamma0Away N q) : SL(2, ZAway q)) 1 1
        = (a : SL(2, ZAway q)) 1 0 * (b : SL(2, ZAway q)) 0 1
          + (a : SL(2, ZAway q)) 1 1 * (b : SL(2, ZAway q)) 1 1 :=
      (Matrix.two_mul_expl (a : SL(2, ZAway q)).1 (b : SL(2, ZAway q)).1).2.2.2
    rw [h, map_add, map_mul, map_mul, zAwayToZMod_apply_one_zero N q hNq a,
      zero_mul, zero_add]

/-- The unit-valued character of `Γ₀(N)` over `ℤ[1/q]` extending the
lower-right-entry character of `Γ₀(N)` over `ℤ`. -/
noncomputable def gamma0AwayUnitsChar (hNq : Nat.Coprime N q) :
    Gamma0Away N q →* (ZMod N)ˣ :=
  (gamma0AwayMap N q hNq).toHomUnits

@[simp]
theorem gamma0AwayUnitsChar_coe (hNq : Nat.Coprime N q) (g : Gamma0Away N q) :
    (gamma0AwayUnitsChar N q hNq g : ZMod N) = gamma0AwayMap N q hNq g :=
  rfl

/-- The first vertex map, landing in `Γ₀(N)` over `ℤ[1/q]`. -/
noncomputable def vertexZeroAway :
    CongruenceSubgroup.Gamma0 N →* Gamma0Away N q :=
  (vertexZero N q).codRestrict (Gamma0Away N q) (vertexZero_mem N q)

/-- The second vertex map, landing in `Γ₀(N)` over `ℤ[1/q]`. -/
noncomputable def vertexOneAway :
    CongruenceSubgroup.Gamma0 N →* Gamma0Away N q :=
  (vertexOne N q).codRestrict (Gamma0Away N q) (vertexOne_mem N q)

theorem gamma0AwayUnitsChar_comp_vertexZeroAway (hNq : Nat.Coprime N q) :
    (gamma0AwayUnitsChar N q hNq).comp (vertexZeroAway N q) = gamma0UnitsHom N := by
  ext g
  show zAwayToZMod N q hNq ((vertexZero N q g : SL(2, ZAway q)) 1 1)
      = CongruenceSubgroup.Gamma0Map N g
  have h : (vertexZero N q g : SL(2, ZAway q)) 1 1
      = algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 1) := rfl
  rw [h, zAwayToZMod_algebraMap]
  rfl

theorem gamma0AwayUnitsChar_comp_vertexOneAway (hNq : Nat.Coprime N q) :
    (gamma0AwayUnitsChar N q hNq).comp (vertexOneAway N q) = gamma0UnitsHom N := by
  ext g
  show zAwayToZMod N q hNq ((vertexOne N q g : SL(2, ZAway q)) 1 1)
      = CongruenceSubgroup.Gamma0Map N g
  have h : (vertexOne N q g : SL(2, ZAway q)) 1 1
      = algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 1) := by
    rw [coe_vertexOne_eq]
    rfl
  rw [h, zAwayToZMod_algebraMap]
  rfl

end Ihara
