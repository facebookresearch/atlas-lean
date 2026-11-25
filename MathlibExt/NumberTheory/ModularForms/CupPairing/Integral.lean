/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_CupPairing_exists_perfectPairing_intCast_eq_pair.lean`
and
`P2M/Sol/S_ModularCurve_CupPairing_exists_perfectPairing_intCast_eq_pair.lean`
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

public import MathlibExt.NumberTheory.ModularForms.CupPairing.Defs
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import MathlibExt.LinearAlgebra.Matrix.DotProductPerfectPairing
import MathlibExt.NumberTheory.ModularForms.CupPairing.FinsumFormula
import MathlibExt.NumberTheory.ModularForms.CupPairing.OrbitSum
import MathlibExt.NumberTheory.ModularForms.CupPairing.ParabolicLift

/-!
# An integral perfect pairing on parabolic homomorphisms

For a finite-index subgroup `Γ` of `SL(2, ℤ)`, there is a `ℤ`-bilinear form on the parabolic
homomorphisms `Additive Γ →+ ℤ` that is perfect (both curried maps are bijective) and agrees,
after extending scalars to `ℚ`, with the rational cup pairing `ModularCurve.CupPairing.pair`.
-/

set_option linter.unusedSectionVars false

namespace ModularCurve
namespace CupPairing
namespace PD
open ModularCurve.CupPairing ModularCurve

open Matrix.SpecialLinearGroup ModularGroup MulAction ModularCurve.PDPairing ModularCurve.Period
open ModularCurve.CupPairing.OrbitSum

open scoped MatrixGroups

private theorem U_mul_U : S * T * (S * T) = T⁻¹ * S := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem S_mul_U_mul_U (g : SL(2, ℤ)) : S * (S * T * (S * T * g)) = -(T * (S * T * g)) := by
  have : S * (S * T * (S * T * g)) = S * (S * T) * (S * T * g) := by group
  rw [this, S_mul_U, neg_mul]

section PM

variable (Γ : Subgroup SL(2, ℤ))

private abbrev pm : Subgroup SL(2, ℤ) := Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))

private theorem neg_one_mem_pm : (-1 : SL(2, ℤ)) ∈ pm Γ := Subgroup.mem_sup_right
    (Subgroup.mem_zpowers _)

private theorem le_pm : Γ ≤ pm Γ := le_sup_left

private scoped instance zpowers_neg_one_normal : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal :=
  ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute g ((-1 : SL(2, ℤ)) ^ k) := (Commute.neg_one_right g).zpow_right k
    rw [hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k⟩

private theorem mem_or_neg_mem_of_mem_pm {g : SL(2, ℤ)} (hg : g ∈ pm Γ) : g ∈ Γ ∨ -g ∈ Γ := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have h2 : ((-1 : SL(2, ℤ)) ^ (2 : ℤ)) = 1 := by rw [zpow_two]; simp
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, h2, one_zpow, mul_one]
    exact hy
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one, mul_neg_one, neg_neg]
    exact hy

private scoped instance pm_finiteIndex [Γ.FiniteIndex] : (pm Γ).FiniteIndex :=
    Subgroup.finiteIndex_of_le (le_pm Γ)

private theorem index_subgroupOf_pm [Γ.FiniteIndex] : ((Γ.subgroupOf (pm Γ)).index : ℚ) = mult Γ :=
    by
  unfold mult
  by_cases hneg : (-1 : SL(2, ℤ)) ∈ Γ
  · rw [ite_eq_left hneg]
    have : pm Γ = Γ := sup_eq_left.mpr ((Subgroup.zpowers_le).mpr hneg)
    have hidx : (Γ.subgroupOf (pm Γ)).index = 1 := by
      rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top]
      exact this.le
    rw [hidx, Nat.cast_one]
  · rw [ite_eq_right hneg]
    have hidx : (Γ.subgroupOf (pm Γ)).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨-1, neg_one_mem_pm Γ⟩, fun b => ?_⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, mul_neg_one]
      rcases mem_or_neg_mem_of_mem_pm Γ b.2 with hb | hb
      · refine Or.inr ⟨hb, fun hnb => hneg ?_⟩
        have := Γ.mul_mem (Γ.inv_mem hb) hnb
        rwa [mul_neg, inv_mul_cancel] at this
      · refine Or.inl ⟨hb, fun hb' => hneg ?_⟩
        have := Γ.mul_mem (Γ.inv_mem hb') hb
        rwa [mul_neg, inv_mul_cancel] at this
    rw [hidx, Nat.cast_ofNat]

private abbrev Qb : Type := SL(2, ℤ) ⧸ pm Γ

private noncomputable scoped instance [Γ.FiniteIndex] : Fintype (Qb Γ) := Fintype.ofFinite _

private theorem neg_one_smul (q : Qb Γ) : (-1 : SL(2, ℤ)) • q = q := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [Quotient.smul_mk, QuotientGroup.eq]
    simpa using neg_one_mem_pm Γ

private theorem neg_smul' (g : SL(2, ℤ)) (q : Qb Γ) : (-g) • q = g • q := by
  rw [show -g = g * (-1) by simp, mul_smul, neg_one_smul]

private theorem S_S_smul (q : Qb Γ) : S • S • q = q := by
  rw [smul_smul, S_mul_S_eq, neg_one_smul]

private theorem S_inv_smul (q : Qb Γ) : S⁻¹ • q = S • q := by
  rw [ModularGroup.S_inv, neg_smul']

private theorem U_U_U_smul (q : Qb Γ) : (S * T) • (S * T) • (S * T) • q = q := by
  rw [smul_smul, smul_smul, U_cube, neg_one_smul]

private theorem S_U_smul (q : Qb Γ) : S • (S * T) • q = T • q := by
  rw [smul_smul, S_mul_U, neg_smul']

private theorem mk_mul' (g₀ g : SL(2, ℤ)) : (QuotientGroup.mk (g₀ * g) : Qb Γ) = g₀ •
    QuotientGroup.mk g := rfl

private def RInv {X : Type*} (A : SL(2, ℤ) → X) : Prop := ∀ (g γ : SL(2, ℤ)), γ ∈ pm Γ → A (g * γ)
    = A g

variable {Γ}

private theorem rInv_of {X : Type*} {A : SL(2, ℤ) → X} (hΓ : ∀ (g : SL(2, ℤ)) (γ : Γ), A (g * γ) =
    A g)
    (hneg : ∀ g, A (-g) = A g) : RInv Γ A := by
  intro g γ hγ
  rcases mem_or_neg_mem_of_mem_pm Γ hγ with h | h
  · exact hΓ g ⟨γ, h⟩
  · have := hΓ g ⟨-γ, h⟩
    rw [Subgroup.coe_mk, mul_neg, hneg] at this
    exact this

private noncomputable def descend {X : Type*} (A : SL(2, ℤ) → X) : Qb Γ → X := fun q => A q.out

private theorem descend_mk {X : Type*} {A : SL(2, ℤ) → X} (hA : RInv Γ A) (g : SL(2, ℤ)) :
    descend A (QuotientGroup.mk g : Qb Γ) = A g := by
  unfold descend
  obtain ⟨⟨γ, hγ⟩, h⟩ := QuotientGroup.mk_out_eq_mul (pm Γ) g
  rw [h]
  exact hA g γ hγ

private theorem descend_smul {X : Type*} {A : SL(2, ℤ) → X} (hA : RInv Γ A) (g₀ : SL(2, ℤ)) (q : Qb
    Γ) :
    descend A (g₀ • q) = A (g₀ * q.out) := by
  conv_lhs => rw [← QuotientGroup.out_eq' q, Quotient.smul_mk, smul_eq_mul]
  exact descend_mk hA _

end PM

section Prim

variable (Γ : Subgroup SL(2, ℤ)) (H : Subgroup SL(2, ℤ))

private noncomputable def kk (g : SL(2, ℤ)) : Γ :=
  ⟨(Classical.choose (Classical.choose_spec (DoubleCoset.mk_out_eq_mul H Γ g)).2)⁻¹,
    Γ.inv_mem (Classical.choose_spec
      (Classical.choose_spec (DoubleCoset.mk_out_eq_mul H Γ g)).2).1⟩

private theorem decomp (g : SL(2, ℤ)) : ∃ h ∈ H,
    g = h * (DoubleCoset.mk H Γ g : DoubleCoset.Quotient (H : Set SL(2, ℤ)) Γ).out * (kk Γ H g) :=
        by
  have hh := Classical.choose_spec (DoubleCoset.mk_out_eq_mul H Γ g)
  set h := Classical.choose (DoubleCoset.mk_out_eq_mul H Γ g) with hh_def
  have hk := Classical.choose_spec hh.2
  set k := Classical.choose hh.2 with hk_def
  refine ⟨h⁻¹, H.inv_mem hh.1, ?_⟩
  have hkk : ((kk Γ H g : Γ) : SL(2, ℤ)) = k⁻¹ := rfl
  rw [hkk, hk.2]
  group

private noncomputable def prim (φ : Additive Γ →+ ℤ) (g : SL(2, ℤ)) : ℤ := φ (Additive.ofMul (kk Γ
    H g))

private theorem prim_add (φ ψ : Additive Γ →+ ℤ) (g : SL(2, ℤ)) :
    prim Γ H (φ + ψ) g = prim Γ H φ g + prim Γ H ψ g := rfl

private theorem prim_smul (c : ℤ) (φ : Additive Γ →+ ℤ) (g : SL(2, ℤ)) :
    prim Γ H (c • φ) g = c * prim Γ H φ g := by
  simp [prim]

variable {Γ H}
variable (φ : Additive Γ →+ ℤ)
  (hφ : ∀ (o : SL(2, ℤ)) (γ : Γ), o * γ * o⁻¹ ∈ H → φ (Additive.ofMul γ) = 0)

private theorem mk_mul_mem (g k : SL(2, ℤ)) (hk : k ∈ Γ) :
    (DoubleCoset.mk H Γ (g * k) : DoubleCoset.Quotient (H : Set SL(2, ℤ)) Γ) = DoubleCoset.mk H Γ g
        := by
  rw [DoubleCoset.eq]
  exact ⟨1, H.one_mem, k⁻¹, Γ.inv_mem hk, by rw [one_mul, mul_inv_cancel_right]⟩

private theorem mk_mem_mul (h g : SL(2, ℤ)) (hh : h ∈ H) :
    (DoubleCoset.mk H Γ (h * g) : DoubleCoset.Quotient (H : Set SL(2, ℤ)) Γ) = DoubleCoset.mk H Γ g
        := by
  rw [DoubleCoset.eq]
  exact ⟨h⁻¹, H.inv_mem hh, 1, Γ.one_mem, by rw [mul_one, inv_mul_cancel_left]⟩

include hφ in
private theorem phi_eq_of_decomp {o h₁ h₂ : SL(2, ℤ)} (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H) {k₁ k₂ : Γ} {γ
    : SL(2, ℤ)}
    (hγ : γ ∈ Γ) (heq : h₁ * o * k₁ * γ = h₂ * o * k₂) :
    φ (Additive.ofMul k₂) = φ (Additive.ofMul k₁) + φ (Additive.ofMul (⟨γ, hγ⟩ : Γ)) := by
  have hmem : o * ((k₁ : SL(2, ℤ)) * γ * (k₂ : SL(2, ℤ))⁻¹) * o⁻¹ ∈ H := by
    have : o * ((k₁ : SL(2, ℤ)) * γ * (k₂ : SL(2, ℤ))⁻¹) * o⁻¹ = h₁⁻¹ * h₂ := by
      have e : h₂ = h₁ * o * k₁ * γ * (k₂ : SL(2, ℤ))⁻¹ * o⁻¹ := by rw [heq]; group
      rw [e]; group
    rw [this]
    exact H.mul_mem (H.inv_mem hh₁) hh₂
  have h0 := hφ o (k₁ * ⟨γ, hγ⟩ * k₂⁻¹) (by simpa using hmem)
  rw [ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg] at h0
  linarith

include hφ in
private theorem prim_mul (g : SL(2, ℤ)) (γ : Γ) : prim Γ H φ (g * γ) = prim Γ H φ g + φ
    (Additive.ofMul γ) := by
  obtain ⟨h₁, hh₁, e₁⟩ := decomp Γ H g
  obtain ⟨h₂, hh₂, e₂⟩ := decomp Γ H (g * γ)
  rw [mk_mul_mem g γ γ.2] at e₂
  unfold prim
  have heq : h₁ * (DoubleCoset.mk H Γ g : DoubleCoset.Quotient (H : Set SL(2, ℤ)) Γ).out * (kk Γ H
      g) * γ =
      h₂ * (DoubleCoset.mk H Γ g : DoubleCoset.Quotient (H : Set SL(2, ℤ)) Γ).out * (kk Γ H (g *
          γ)) := by
    rw [← e₁, ← e₂]
  have := phi_eq_of_decomp φ hφ hh₁ hh₂ γ.2 heq
  simpa using this

include hφ in
private theorem prim_left (h : SL(2, ℤ)) (hh : h ∈ H) (g : SL(2, ℤ)) : prim Γ H φ (h * g) = prim Γ
    H φ g := by
  obtain ⟨h₁, hh₁, e₁⟩ := decomp Γ H g
  obtain ⟨h₂, hh₂, e₂⟩ := decomp Γ H (h * g)
  rw [mk_mem_mul h g hh] at e₂
  unfold prim
  have heq : h * h₁ * (DoubleCoset.mk H Γ g : DoubleCoset.Quotient (H : Set SL(2, ℤ)) Γ).out * (kk
      Γ H g) * 1 =
      h₂ * (DoubleCoset.mk H Γ g : DoubleCoset.Quotient (H : Set SL(2, ℤ)) Γ).out * (kk Γ H (h *
          g)) := by
    rw [mul_one, mul_assoc h h₁, mul_assoc h, ← e₁, ← e₂]
  have := phi_eq_of_decomp φ hφ (H.mul_mem hh hh₁) hh₂ Γ.one_mem heq
  have h1 : (⟨1, Γ.one_mem⟩ : Γ) = 1 := rfl
  rw [h1, ofMul_one, map_zero, add_zero] at this
  exact this

end Prim

section Stab

private def Binf : Subgroup SL(2, ℤ) where
  carrier := {g | g 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
    ring
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [ha]

private theorem mem_Binf {g : SL(2, ℤ)} : g ∈ Binf ↔ g 1 0 = 0 := Iff.rfl

private theorem T_mem_Binf : T ∈ Binf := by rw [mem_Binf]; rfl

private theorem neg_one_mem_Binf : (-1 : SL(2, ℤ)) ∈ Binf := by
  rw [mem_Binf]; simp

private theorem trace_sq_of_mem_Binf {g : SL(2, ℤ)} (hg : g ∈ Binf) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 := by
  rw [mem_Binf] at hg
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := hg
  rw [h10, mul_zero, sub_zero] at hdet
  rw [Matrix.trace_fin_two]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h
  · rw [h, one_mul] at hdet; rw [h, hdet]; norm_num
  · rw [h, neg_one_mul] at hdet
    rw [h, show (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -1 by linarith]; norm_num

private theorem trace_conj (o γ : SL(2, ℤ)) :
    ((o * γ * o⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = ((γ : SL(2, ℤ)) : Matrix (Fin 2)
        (Fin 2) ℤ).trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul]

variable {Γ : Subgroup SL(2, ℤ)}

private theorem apply_eq_zero_of_pow_eq_one (φ : Additive Γ →+ ℤ) (γ : Γ) {n : ℕ} (hn : n ≠ 0)
    (h : γ ^ n = 1) : φ (Additive.ofMul γ) = 0 := by
  have : (n : ℤ) * φ (Additive.ofMul γ) = 0 := by
    have := congrArg (fun δ : Γ => φ (Additive.ofMul δ)) h
    simpa [ofMul_pow] using this
  exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast hn)

private theorem pow_eq_one_of_conj_mem_zpowers {z γ o : SL(2, ℤ)} {n : ℕ} (hz : z ^ n = 1)
    (h : o * γ * o⁻¹ ∈ Subgroup.zpowers z) : γ ^ n = 1 := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
  have h1 : (o * γ * o⁻¹) ^ n = 1 := by
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  rw [conj_pow] at h1
  have := congrArg (fun m => o⁻¹ * m * o) h1
  simpa [mul_assoc] using this

private theorem killS (φ : Additive Γ →+ ℤ) (o : SL(2, ℤ)) (γ : Γ) (h : o * γ * o⁻¹ ∈
    Subgroup.zpowers S) :
    φ (Additive.ofMul γ) = 0 := by
  have hS4 : S ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, sq, S_mul_S_eq]; simp
  apply apply_eq_zero_of_pow_eq_one φ γ (n := 4) (by norm_num)
  exact Subtype.ext (by simpa using pow_eq_one_of_conj_mem_zpowers hS4 h)

private theorem killU (φ : Additive Γ →+ ℤ) (o : SL(2, ℤ)) (γ : Γ) (h : o * γ * o⁻¹ ∈
    Subgroup.zpowers (S * T)) :
    φ (Additive.ofMul γ) = 0 := by
  have hU6 : (S * T) ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 + 3 by rfl, pow_add, show (3 : ℕ) = 1 + 1 + 1 by rfl, pow_add, pow_add,
      pow_one, U_cube]; simp
  apply apply_eq_zero_of_pow_eq_one φ γ (n := 6) (by norm_num)
  exact Subtype.ext (by simpa using pow_eq_one_of_conj_mem_zpowers hU6 h)

private theorem killB (φ : Additive Γ →+ ℤ) (hφ : IsParabolicHom Γ φ) (o : SL(2, ℤ)) (γ : Γ)
    (h : o * γ * o⁻¹ ∈ Binf) : φ (Additive.ofMul γ) = 0 := by
  apply hφ
  rw [← trace_conj o]
  exact trace_sq_of_mem_Binf h

end Stab

section Maps

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

private abbrev L : Type := ModularCurve.Period.parabolicHoms ℤ Γ ℤ

variable {Γ}

private noncomputable def Fx (x : L Γ) : SL(2, ℤ) → ℤ := prim Γ Binf (x : Additive Γ →+ ℤ)

private noncomputable def Ga (y : L Γ) : SL(2, ℤ) → ℤ := prim Γ (Subgroup.zpowers S) (y : Additive
    Γ →+ ℤ)

private noncomputable def Gb (y : L Γ) : SL(2, ℤ) → ℤ := prim Γ (Subgroup.zpowers (S * T)) (y :
    Additive Γ →+ ℤ)

private theorem Fx_mul (x : L Γ) (g : SL(2, ℤ)) (γ : Γ) : Fx x (g * γ) = Fx x g + (x : Additive Γ
    →+ ℤ) (Additive.ofMul γ) :=
  prim_mul _ (fun o γ h => killB _ x.2 o γ h) g γ

private theorem Fx_T (x : L Γ) (g : SL(2, ℤ)) : Fx x (T * g) = Fx x g :=
  prim_left _ (fun o γ h => killB _ x.2 o γ h) T T_mem_Binf g

private theorem Fx_neg (x : L Γ) (g : SL(2, ℤ)) : Fx x (-g) = Fx x g := by
  rw [show -g = -1 * g by simp]
  exact prim_left _ (fun o γ h => killB _ x.2 o γ h) (-1) neg_one_mem_Binf g

private theorem Ga_mul (y : L Γ) (g : SL(2, ℤ)) (γ : Γ) : Ga y (g * γ) = Ga y g + (y : Additive Γ
    →+ ℤ) (Additive.ofMul γ) :=
  prim_mul _ (fun o γ h => killS _ o γ h) g γ

private theorem Ga_S (y : L Γ) (g : SL(2, ℤ)) : Ga y (S * g) = Ga y g :=
  prim_left _ (fun o γ h => killS _ o γ h) S (Subgroup.mem_zpowers S) g

private theorem Gb_mul (y : L Γ) (g : SL(2, ℤ)) (γ : Γ) : Gb y (g * γ) = Gb y g + (y : Additive Γ
    →+ ℤ) (Additive.ofMul γ) :=
  prim_mul _ (fun o γ h => killU _ o γ h) g γ

private theorem Gb_U (y : L Γ) (g : SL(2, ℤ)) : Gb y (S * T * g) = Gb y g :=
  prim_left _ (fun o γ h => killU _ o γ h) (S * T) (Subgroup.mem_zpowers _) g

private theorem Ga_neg (y : L Γ) (g : SL(2, ℤ)) : Ga y (-g) = Ga y g := neg_invariant_of_S _ (Ga_S
    y) g

private theorem Gb_neg (y : L Γ) (g : SL(2, ℤ)) : Gb y (-g) = Gb y g := by
  have h3 : -g = S * T * (S * T * (S * T * g)) := by
    rw [← mul_assoc, ← mul_assoc, U_cube, neg_one_mul]
  rw [h3, Gb_U, Gb_U, Gb_U]

private noncomputable def Xfun (x : L Γ) (g : SL(2, ℤ)) : ℤ := Fx x g - Fx x (S * g)

private noncomputable def ffun (y : L Γ) (g : SL(2, ℤ)) : ℤ := Gb y g - Ga y g

private theorem rInv_Xfun (x : L Γ) : RInv Γ (Xfun x) := by
  refine rInv_of (fun g γ => ?_) (fun g => ?_)
  · unfold Xfun; rw [← mul_assoc, Fx_mul, Fx_mul]; ring
  · unfold Xfun; rw [mul_neg, Fx_neg, Fx_neg]

private theorem rInv_ffun (y : L Γ) : RInv Γ (ffun y) := by
  refine rInv_of (fun g γ => ?_) (fun g => ?_)
  · unfold ffun; rw [Ga_mul, Gb_mul]; ring
  · unfold ffun; rw [Ga_neg, Gb_neg]

private noncomputable def Xf : L Γ →ₗ[ℤ] (Qb Γ → ℤ) where
  toFun x := descend (Xfun x)
  map_add' x x' := by
    funext q
    simp only [descend, Xfun, Fx, Pi.add_apply, Submodule.coe_add, prim_add]
    ring
  map_smul' c x := by
    funext q
    simp only [descend, Xfun, Fx, Pi.smul_apply, Submodule.coe_smul, prim_smul, RingHom.id_apply,
      smul_eq_mul]
    ring

private noncomputable def ff : L Γ →ₗ[ℤ] (Qb Γ → ℤ) where
  toFun y := descend (ffun y)
  map_add' y y' := by
    funext q
    simp only [descend, ffun, Ga, Gb, Pi.add_apply, Submodule.coe_add, prim_add]
    ring
  map_smul' c y := by
    funext q
    simp only [descend, ffun, Ga, Gb, Pi.smul_apply, Submodule.coe_smul, prim_smul,
        RingHom.id_apply,
      smul_eq_mul]
    ring

private theorem Xf_mk (x : L Γ) (g : SL(2, ℤ)) : Xf x (QuotientGroup.mk g) = Xfun x g := descend_mk
    (rInv_Xfun x) g

private theorem ff_mk (y : L Γ) (g : SL(2, ℤ)) : ff y (QuotientGroup.mk g) = ffun y g := descend_mk
    (rInv_ffun y) g

private theorem Xf_smul (x : L Γ) (g₀ : SL(2, ℤ)) (q : Qb Γ) : Xf x (g₀ • q) = Xfun x (g₀ * q.out)
    :=
  descend_smul (rInv_Xfun x) g₀ q

private theorem ff_smul (y : L Γ) (g₀ : SL(2, ℤ)) (q : Qb Γ) : ff y (g₀ • q) = ffun y (g₀ * q.out)
    :=
  descend_smul (rInv_ffun y) g₀ q

private theorem Xf_eq (x : L Γ) (q : Qb Γ) : Xf x q = Xfun x q.out := rfl

private theorem ff_eq (y : L Γ) (q : Qb Γ) : ff y q = ffun y q.out := rfl

private theorem Xf_S (x : L Γ) (q : Qb Γ) : Xf x (S • q) = -Xf x q := by
  rw [Xf_smul, Xf_eq]
  unfold Xfun
  rw [← neg_eq_S_mul_S_mul, Fx_neg]
  ring

private theorem Xf_U_rel (x : L Γ) (q : Qb Γ) : Xf x q + Xf x ((S * T) • q) + Xf x ((S * T) • (S *
    T) • q) = 0 := by
  rw [smul_smul, Xf_smul, Xf_smul, Xf_eq]
  unfold Xfun
  set m := q.out
  have h1 : Fx x (S * (S * T * m)) = Fx x m := by
    rw [← mul_assoc, S_mul_U, neg_mul, Fx_neg, Fx_T]
  have h2 : Fx x (S * (S * T * (S * T) * m)) = Fx x (S * T * m) := by
    rw [show S * (S * T * (S * T) * m) = S * (S * T) * (S * T * m) by group, S_mul_U, neg_mul,
        Fx_neg,
      Fx_T]
  have h3 : Fx x (S * T * (S * T) * m) = Fx x (S * m) := by
    rw [U_mul_U, mul_assoc, ← Fx_T x (T⁻¹ * (S * m)), mul_inv_cancel_left]
  rw [h1, h2, h3]
  ring

end Maps

section Complex

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

private def Inv (g₀ : SL(2, ℤ)) : Submodule ℤ (Qb Γ → ℤ) where
  carrier := {a | ∀ q, a (g₀ • q) = a q}
  zero_mem' := fun _ => rfl
  add_mem' := by intro a b ha hb q; simp only [Pi.add_apply, ha q, hb q]
  smul_mem' := by intro c a ha q; simp only [Pi.smul_apply, ha q]

private theorem mem_Inv {g₀ : SL(2, ℤ)} {a : Qb Γ → ℤ} : a ∈ Inv Γ g₀ ↔ ∀ q, a (g₀ • q) = a q :=
    Iff.rfl

private def Bd : Submodule ℤ (Qb Γ → ℤ) := Inv Γ S ⊔ Inv Γ (S * T)

private def dS : (Qb Γ → ℤ) →ₗ[ℤ] (Qb Γ → ℤ) where
  toFun e := fun q => e q - e (S • q)
  map_add' e e' := by funext q; simp only [Pi.add_apply]; ring
  map_smul' c e := by funext q; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private theorem dS_apply (e : Qb Γ → ℤ) (q : Qb Γ) : dS Γ e q = e q - e (S • q) := rfl

private def Ec : Submodule ℤ (Qb Γ → ℤ) := (Inv Γ T).map (dS Γ)

private theorem mem_Ec {v : Qb Γ → ℤ} : v ∈ Ec Γ ↔ ∃ e ∈ Inv Γ T, dS Γ e = v := Submodule.mem_map

variable {Γ}

private theorem const_of_S_U {X : Type*} (F : Qb Γ → X) (hS : ∀ q, F (S • q) = F q)
    (hU : ∀ q, F ((S * T) • q) = F q) (q : Qb Γ) : F q = F (QuotientGroup.mk 1) := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    have := eq_apply_one_of_S_U (fun g : SL(2, ℤ) => F (QuotientGroup.mk g))
      (fun g => by simpa [Quotient.smul_mk] using hS (QuotientGroup.mk g))
      (fun g => by simpa [Quotient.smul_mk] using hU (QuotientGroup.mk g)) g
    exact this

private theorem const_of_S_T {X : Type*} (F : Qb Γ → X) (hS : ∀ q, F (S • q) = F q)
    (hT : ∀ q, F (T • q) = F q) (q : Qb Γ) : F q = F (QuotientGroup.mk 1) := by
  refine const_of_S_U F hS (fun q => ?_) q
  rw [mul_smul, hS, hT]

private theorem sum_smul_eq (g₀ : SL(2, ℤ)) (F : Qb Γ → ℤ) : ∑ q, F (g₀ • q) = ∑ q, F q :=
  Fintype.sum_equiv (MulAction.toPerm g₀) _ _ (fun _ => rfl)

private theorem Xf_dot_InvS (x : L Γ) {a : Qb Γ → ℤ} (ha : a ∈ Inv Γ S) : Xf x ⬝ᵥ a = 0 := by
  have h : ∑ q, Xf x q * a q = ∑ q, Xf x (S • q) * a (S • q) := (sum_smul_eq S _).symm
  simp only [Xf_S, ha _, neg_mul, Finset.sum_neg_distrib] at h
  rw [dotProduct]
  linarith

private theorem Xf_dot_InvU (x : L Γ) {b : Qb Γ → ℤ} (hb : b ∈ Inv Γ (S * T)) : Xf x ⬝ᵥ b = 0 := by
  have h1 : ∑ q, Xf x ((S * T) • q) * b q = ∑ q, Xf x q * b q := by
    rw [← sum_smul_eq (S * T) (fun q => Xf x q * b q)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hb q]
  have h2 : ∑ q, Xf x ((S * T) • (S * T) • q) * b q = ∑ q, Xf x q * b q := by
    rw [← sum_smul_eq (S * T) (fun q => Xf x ((S * T) • (S * T) • q) * b q)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [U_U_U_smul, hb q]
  have h3 : ∑ q, (Xf x q + Xf x ((S * T) • q) + Xf x ((S * T) • (S * T) • q)) * b q = 0 := by
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Xf_U_rel, zero_mul]
  simp only [add_mul, Finset.sum_add_distrib, h1, h2] at h3
  rw [dotProduct]
  linarith

private theorem Xf_dot_Bd (x : L Γ) {v : Qb Γ → ℤ} (hv : v ∈ Bd Γ) : Xf x ⬝ᵥ v = 0 := by
  rw [Bd, Submodule.mem_sup] at hv
  obtain ⟨a, ha, b, hb, rfl⟩ := hv
  rw [dotProduct_add, Xf_dot_InvS x ha, Xf_dot_InvU x hb, add_zero]

private theorem InvS_dot_dS {a : Qb Γ → ℤ} (ha : a ∈ Inv Γ S) (e : Qb Γ → ℤ) : a ⬝ᵥ dS Γ e = 0 := by
  rw [dotProduct]
  simp only [dS_apply, mul_sub, Finset.sum_sub_distrib]
  have : ∑ q, a q * e (S • q) = ∑ q, a q * e q := by
    rw [← sum_smul_eq S (fun q => a q * e q)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ha q]
  linarith

private theorem InvU_dot_dS {b : Qb Γ → ℤ} (hb : b ∈ Inv Γ (S * T)) {e : Qb Γ → ℤ} (he : e ∈ Inv Γ
    T) :
    b ⬝ᵥ dS Γ e = 0 := by
  rw [dotProduct]
  simp only [dS_apply, mul_sub, Finset.sum_sub_distrib]
  have : ∑ q, b q * e (S • q) = ∑ q, b q * e q := by
    rw [← sum_smul_eq (S * T) (fun q => b q * e (S • q))]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hb q, S_U_smul, he q]
  linarith

private theorem Bd_dot_Ec {v : Qb Γ → ℤ} (hv : v ∈ Bd Γ) {w : Qb Γ → ℤ} (hw : w ∈ Ec Γ) : v ⬝ᵥ w =
    0 := by
  rw [Bd, Submodule.mem_sup] at hv
  obtain ⟨a, ha, b, hb, rfl⟩ := hv
  obtain ⟨e, he, rfl⟩ := (mem_Ec Γ).mp hw
  rw [add_dotProduct, InvS_dot_dS ha, InvU_dot_dS hb he, add_zero]

private theorem emod_const {n : ℤ} (a : Qb Γ → ℤ) (hS : ∀ q, a (S • q) % n = a q % n)
    (hU : ∀ q, a ((S * T) • q) % n = a q % n) (q : Qb Γ) : n ∣ a q - a (QuotientGroup.mk 1) := by
  have := const_of_S_U (fun q => a q % n) hS hU q
  exact Int.ModEq.dvd this.symm |> fun h => by simpa using h

private theorem Bd_saturated (n : ℤ) (v : Qb Γ → ℤ) (hn : n ≠ 0) (hv : n • v ∈ Bd Γ) : v ∈ Bd Γ :=
    by
  rw [Bd, Submodule.mem_sup] at hv ⊢
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  have hab' : ∀ q, a q + b q = n * v q := fun q => by
    have := congrFun hab q; simpa using this
  set q₁ : Qb Γ := QuotientGroup.mk 1
  have hdvd : ∀ q, n ∣ a q - a q₁ := by
    refine emod_const a (fun q => by rw [ha q]) (fun q => ?_)
    have h1 := hab' q
    have h2 := hab' ((S * T) • q)
    rw [hb q] at h2
    have : a ((S * T) • q) = a q + n * (v ((S * T) • q) - v q) := by linarith
    rw [this, Int.add_mul_emod_self_left]
  choose a₁ ha₁ using hdvd
  refine ⟨a₁, fun q => ?_, v - a₁, fun q => ?_, by abel⟩
  · apply mul_left_cancel₀ hn
    rw [← ha₁, ← ha₁, ha q]
  · simp only [Pi.sub_apply]
    apply mul_left_cancel₀ hn
    rw [mul_sub, mul_sub, ← ha₁, ← ha₁, ← hab', ← hab', hb q]
    ring

private theorem Ec_saturated (n : ℤ) (v : Qb Γ → ℤ) (hn : n ≠ 0) (hv : n • v ∈ Ec Γ) : v ∈ Ec Γ :=
    by
  rw [mem_Ec] at hv ⊢
  obtain ⟨e, he, hev⟩ := hv
  have hev' : ∀ q, e q - e (S • q) = n * v q := fun q => by
    have := congrFun hev q; simpa [dS_apply] using this
  set q₁ : Qb Γ := QuotientGroup.mk 1
  have hdvd : ∀ q, n ∣ e q - e q₁ := by
    refine emod_const e (fun q => ?_) (fun q => ?_)
    · have : e (S • q) = e q + n * (-v q) := by linarith [hev' q]
      rw [this, Int.add_mul_emod_self_left]
    · rw [mul_smul]
      have : e (S • T • q) = e (T • q) + n * (-v (T • q)) := by linarith [hev' (T • q)]
      rw [this, Int.add_mul_emod_self_left, he q]
  choose e₁ he₁ using hdvd
  refine ⟨e₁, fun q => ?_, ?_⟩
  · apply mul_left_cancel₀ hn
    rw [← he₁, ← he₁, he q]
  · funext q
    rw [dS_apply]
    apply mul_left_cancel₀ hn
    rw [mul_sub, ← he₁, ← he₁, ← hev' q]
    ring

end Complex

section Facts

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

private theorem Ga_T_mul_sub (y : L Γ) (h : SL(2, ℤ)) : Ga y (T * h) - Ga y h = ffun y h - ffun y
    (S * (T * h)) := by
  have hT : Ga y (T * h) = Ga y (S * T * h) := by
    conv_lhs => rw [T_mul_eq, Ga_neg, Ga_S]
  unfold ffun
  rw [hT, ← mul_assoc S T h, Gb_U]
  ring

private theorem Ga_T_pow_mul_sub (y : L Γ) (m : SL(2, ℤ)) (n : ℕ) :
    Ga y (T ^ n * m) - Ga y m =
      ∑ k ∈ Finset.range n, (ffun y (T ^ k * m) - ffun y (S * (T ^ (k + 1) * m))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have step := Ga_T_mul_sub y (T ^ n * m)
    rw [← mul_assoc, ← pow_succ'] at step
    linarith

private theorem y_conj_T_pow_eq (y : L Γ) (m : SL(2, ℤ)) (w : ℕ) (hmem : m⁻¹ * T ^ w * m ∈ pm Γ) :
    Ga y (T ^ w * m) = Ga y m := by
  have htr : (((m⁻¹ * T ^ w * m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 := by
    have := trace_conj m⁻¹ (T ^ w)
    rw [inv_inv] at this
    rw [this]
    exact trace_sq_of_mem_Binf (Binf.pow_mem T_mem_Binf w)
  have hTw : T ^ w * m = m * (m⁻¹ * T ^ w * m) := by group
  rcases mem_or_neg_mem_of_mem_pm Γ hmem with h | h
  · rw [hTw]
    have := Ga_mul y m ⟨_, h⟩
    rw [Subgroup.coe_mk] at this
    rw [this, y.2 ⟨_, h⟩ htr, add_zero]
  · rw [hTw, ← neg_neg (m * (m⁻¹ * T ^ w * m)), Ga_neg, ← mul_neg]
    have := Ga_mul y m ⟨_, h⟩
    rw [Subgroup.coe_mk] at this
    have htr' : (((-(m⁻¹ * T ^ w * m) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 := by
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, neg_sq, htr]
    rw [this, y.2 ⟨_, h⟩ htr', add_zero]

private theorem face_sum_ff (y : L Γ) (q₀ : Qb Γ) :
    ∑ k ∈ Finset.range (Function.minimalPeriod (T • ·) q₀), (ff y (T ^ k • q₀) - ff y (S • T ^ k •
        q₀)) = 0 := by
  set m := q₀.out with hm
  set w := Function.minimalPeriod (T • ·) q₀ with hw
  have hmem : m⁻¹ * T ^ w * m ∈ pm Γ := QuotientGroup.out_conj_pow_minimalPeriod_mem (pm Γ) T q₀
  have h1 : ∀ k, ff y (T ^ k • q₀) = ffun y (T ^ k * m) := fun k => ff_smul y _ q₀
  have h2 : ∀ k, ff y (S • T ^ k • q₀) = ffun y (S * (T ^ k * m)) := fun k => by
    rw [smul_smul, ff_smul, mul_assoc]
  have hshift := sum_period_shift_one (pm Γ) T q₀ (fun q => ff y (S • q))
  rw [← hw] at hshift
  rw [Finset.sum_sub_distrib, ← hshift]
  simp only [h1, h2]
  rw [← Finset.sum_sub_distrib, ← Ga_T_pow_mul_sub, y_conj_T_pow_eq y m w hmem, sub_self]

private theorem ff_dot_dS (y : L Γ) {e : Qb Γ → ℤ} (he : e ∈ Inv Γ T) : ff y ⬝ᵥ dS Γ e = 0 := by
  classical
  haveI : Fintype (orbitRel.Quotient (Subgroup.zpowers T) (Qb Γ)) := Fintype.ofFinite _
  rw [dotProduct]
  simp only [dS_apply, mul_sub, Finset.sum_sub_distrib]
  have hre : ∑ q, ff y q * e (S • q) = ∑ q, ff y (S • q) * e q := by
    rw [← sum_smul_eq S (fun q => ff y q * e (S • q))]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [S_S_smul]
  rw [hre, ← Finset.sum_sub_distrib]
  have : ∑ q, (ff y q * e q - ff y (S • q) * e q) = ∑ q, e q * (ff y q - ff y (S • q)) := by
    refine Finset.sum_congr rfl fun q _ => ?_; ring
  rw [this, sum_eq_sum_orbits (pm Γ) T]
  refine Finset.sum_eq_zero fun c _ => ?_
  have heT : ∀ k : ℕ, e (T ^ k • c.out) = e c.out := by
    intro k; induction k with
    | zero => rw [pow_zero, one_smul]
    | succ k ih => rw [pow_succ', mul_smul, he, ih]
  simp only [heT, ← Finset.mul_sum]
  rw [face_sum_ff, mul_zero]

private theorem ff_dot_Ec (y : L Γ) {w : Qb Γ → ℤ} (hw : w ∈ Ec Γ) : ff y ⬝ᵥ w = 0 := by
  obtain ⟨e, he, rfl⟩ := (mem_Ec Γ).mp hw
  exact ff_dot_dS y he

private theorem eq_zero_of_ff_mem_Bd (y : L Γ) (hy : ff y ∈ Bd Γ) : y = 0 := by
  rw [Bd, Submodule.mem_sup] at hy
  obtain ⟨a, ha, b, hb, hab⟩ := hy
  set D : SL(2, ℤ) → ℤ := fun g => Ga y g + a (QuotientGroup.mk g) with hD
  have hD' : ∀ g, D g = Gb y g - b (QuotientGroup.mk g) := by
    intro g
    have := congrFun hab (QuotientGroup.mk g)
    rw [Pi.add_apply, ff_mk] at this
    unfold ffun at this
    simp only [hD]
    linarith
  have hDS : ∀ g, D (S * g) = D g := by
    intro g
    simp only [hD, Ga_S]
    rw [mk_mul', ha]
  have hDU : ∀ g, D (S * T * g) = D g := by
    intro g
    rw [hD', hD', Gb_U, mk_mul', hb]
  have hconst := eq_apply_one_of_S_U D hDS hDU
  apply Subtype.ext
  ext γ
  have hγ : (QuotientGroup.mk ((Additive.toMul γ : Γ) : SL(2, ℤ)) : Qb Γ) = QuotientGroup.mk 1 := by
    rw [QuotientGroup.eq]
    simpa using le_pm Γ (Additive.toMul γ).2
  have h1 := hconst ((Additive.toMul γ : Γ) : SL(2, ℤ))
  simp only [hD, hγ] at h1
  have h2 := Ga_mul y 1 (Additive.toMul γ)
  rw [one_mul] at h2
  change (y : Additive Γ →+ ℤ) γ = 0
  have : (y : Additive Γ →+ ℤ) (Additive.ofMul (Additive.toMul γ)) = 0 := by linarith
  exact this

private theorem eq_zero_of_Xf_mem_Ec (x : L Γ) (hx : Xf x ∈ Ec Γ) : x = 0 := by
  obtain ⟨e, he, hex⟩ := (mem_Ec Γ).mp hx
  set D : SL(2, ℤ) → ℤ := fun g => Fx x g - e (QuotientGroup.mk g) with hD
  have hrel : ∀ g, Fx x g - Fx x (S * g) = e (QuotientGroup.mk g) - e (S • QuotientGroup.mk g) := by
    intro g
    have := congrFun hex (QuotientGroup.mk g)
    rw [dS_apply, Xf_mk] at this
    exact this.symm
  have hDS : ∀ g, D (S * g) = D g := by
    intro g
    simp only [hD]
    have := hrel g
    rw [Quotient.smul_mk, smul_eq_mul] at this
    linarith
  have hDT : ∀ g, D (T * g) = D g := by
    intro g
    simp only [hD, Fx_T]
    rw [mk_mul', he]
  apply Subtype.ext
  ext γ
  have hγ : (QuotientGroup.mk ((Additive.toMul γ : Γ) : SL(2, ℤ)) : Qb Γ) = QuotientGroup.mk 1 := by
    rw [QuotientGroup.eq]
    simpa using le_pm Γ (Additive.toMul γ).2
  have h1 := apply_mul_eq_of_invariant D hDS hDT ((Additive.toMul γ : Γ) : SL(2, ℤ)) 1
  rw [mul_one] at h1
  simp only [hD, hγ] at h1
  have h2 := Fx_mul x 1 (Additive.toMul γ)
  rw [one_mul] at h2
  change (x : Additive Γ →+ ℤ) γ = 0
  have : (x : Additive Γ →+ ℤ) (Additive.ofMul (Additive.toMul γ)) = 0 := by linarith
  exact this

private theorem exists_eq_smul_of_dvd (x : L Γ) (n : ℤ)
    (hdvd : ∀ γ : Γ, n ∣ (x : Additive Γ →+ ℤ) (Additive.ofMul γ)) : ∃ x' : L Γ, x = n • x' := by
  have hdvd' : ∀ γ : Additive Γ, n ∣ (x : Additive Γ →+ ℤ) γ := fun γ => hdvd (Additive.toMul γ)
  set x' : Additive Γ →+ ℤ :=
    { toFun := fun γ => (x : Additive Γ →+ ℤ) γ / n
      map_zero' := by simp
      map_add' := fun γ γ' => by
        simp only [map_add]
        rw [Int.add_ediv_of_dvd_left (hdvd' γ)] } with hx'
  have hx'par : IsParabolicHom Γ x' := by
    intro γ hγ
    simp only [hx', AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [x.2 γ hγ, Int.zero_ediv]
  refine ⟨⟨x', hx'par⟩, ?_⟩
  apply Subtype.ext
  ext γ
  change (x : Additive Γ →+ ℤ) γ = n • ((x : Additive Γ →+ ℤ) γ / n)
  rw [smul_eq_mul, Int.mul_ediv_cancel' (hdvd' γ)]

private theorem Xf_sat (n : ℤ) (v : Qb Γ → ℤ) (hn : n ≠ 0) (h : ∃ x : L Γ, n • v - Xf x ∈ Ec Γ) :
    ∃ x : L Γ, v - Xf x ∈ Ec Γ := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨e, he, hex⟩ := (mem_Ec Γ).mp hx
  set D : SL(2, ℤ) → ℤ := fun g => Fx x g + e (QuotientGroup.mk g) with hD
  have hrel : ∀ g, D g - D (S * g) = n * v (QuotientGroup.mk g) := by
    intro g
    have := congrFun hex (QuotientGroup.mk g)
    rw [dS_apply, Pi.sub_apply, Pi.smul_apply, Xf_mk, Quotient.smul_mk, smul_eq_mul, smul_eq_mul]
        at this
    simp only [hD]
    unfold Xfun at this
    linarith
  have hDS : ∀ g, D (S * g) % n = D g % n := by
    intro g
    have : D (S * g) = D g + n * (-v (QuotientGroup.mk g)) := by linarith [hrel g]
    rw [this, Int.add_mul_emod_self_left]
  have hDT : ∀ g, D (T * g) % n = D g % n := by
    intro g
    simp only [hD, Fx_T]
    rw [mk_mul', he]
  have hconst := apply_mul_eq_of_invariant (fun g => D g % n) hDS hDT
  have hdvd : ∀ γ : Γ, n ∣ (x : Additive Γ →+ ℤ) (Additive.ofMul γ) := by
    intro γ
    have hγ : (QuotientGroup.mk ((γ : Γ) : SL(2, ℤ)) : Qb Γ) = QuotientGroup.mk 1 := by
      rw [QuotientGroup.eq]
      simpa using le_pm Γ γ.2
    have h1 := hconst γ 1
    rw [mul_one] at h1
    have h2 := Fx_mul x 1 γ
    rw [one_mul] at h2
    have h3 : (x : Additive Γ →+ ℤ) (Additive.ofMul γ) = D γ - D 1 := by
      simp only [hD, hγ]; linarith
    rw [h3]
    exact Int.ModEq.dvd h1.symm
  obtain ⟨x', rfl⟩ := exists_eq_smul_of_dvd x n hdvd
  refine ⟨x', Ec_saturated n _ hn ?_⟩
  rw [map_smul, ← smul_sub] at hx
  exact hx

end Facts

section Assembly

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

private theorem exists_sub_ff_mem_Bd (v : Qb Γ → ℤ) (hv : ∀ w ∈ Ec Γ, v ⬝ᵥ w = 0) :
    ∃ y : L Γ, v - ff y ∈ Bd Γ := by
  classical
  have hf : ∀ e : Qb Γ → ℤ, (∀ q, e (T • q) = e q) → ∑ᶠ q, v q * (e q - e (S • q)) = 0 := by
    intro e he
    rw [finsum_eq_sum_of_fintype]
    have := hv (dS Γ e) (Submodule.mem_map_of_mem he)
    rw [dotProduct] at this
    simpa [dS_apply] using this
  obtain ⟨φ, hφ, a', b', ha', hb', ha'm, hb'm, hvab⟩ :=
    ModularCurve.CupPairing.exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero (pm Γ)
      (neg_one_mem_pm Γ) v hf
  set ψ : Additive Γ →+ ℤ := φ.comp (MonoidHom.toAdditive (Subgroup.inclusion (le_pm Γ))) with hψ
  have hψapp : ∀ γ : Γ, ψ (Additive.ofMul γ) = φ (Additive.ofMul (Subgroup.inclusion (le_pm Γ) γ))
      :=
    fun γ => rfl
  have hψpar : IsParabolicHom Γ ψ := fun γ hγ => hφ (Subgroup.inclusion (le_pm Γ) γ) hγ
  set y : L Γ := ⟨ψ, hψpar⟩ with hy
  set A : SL(2, ℤ) → ℤ := fun g => Ga y g - a' g with hA
  set B : SL(2, ℤ) → ℤ := fun g => Gb y g - b' g with hB
  have hAinv : RInv Γ A := by
    refine rInv_of (fun g γ => ?_) (fun g => ?_)
    · simp only [hA, Ga_mul]
      have := ha'm g (Subgroup.inclusion (le_pm Γ) γ)
      rw [Subgroup.coe_inclusion] at this
      rw [this, ← hψapp]
      change Ga y g + ψ (Additive.ofMul γ) - (a' g + ψ (Additive.ofMul γ)) = Ga y g - a' g
      ring
    · simp only [hA, Ga_neg, neg_invariant_of_S a' ha']
  have hBinv : RInv Γ B := by
    refine rInv_of (fun g γ => ?_) (fun g => ?_)
    · simp only [hB, Gb_mul]
      have := hb'm g (Subgroup.inclusion (le_pm Γ) γ)
      rw [Subgroup.coe_inclusion] at this
      rw [this, ← hψapp]
      change Gb y g + ψ (Additive.ofMul γ) - (b' g + ψ (Additive.ofMul γ)) = Gb y g - b' g
      ring
    · simp only [hB, Gb_neg]
      have h3 : -g = S * T * (S * T * (S * T * g)) := by
        rw [← mul_assoc, ← mul_assoc, U_cube, neg_one_mul]
      rw [h3, hb', hb', hb']
  refine ⟨y, ?_⟩
  rw [Bd, Submodule.mem_sup]
  refine ⟨descend A, fun q => ?_, -descend B, fun q => ?_, ?_⟩
  · rw [descend_smul hAinv]
    simp only [hA, Ga_S, ha']
    rfl
  · simp only [Pi.neg_apply, descend_smul hBinv]
    simp only [hB, Gb_U, hb']
    rfl
  · funext q
    simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, descend, ff_eq, hA, hB]
    unfold ffun
    have := hvab q.out
    rw [QuotientGroup.out_eq'] at this
    rw [this]
    ring

end Assembly

section Final

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

private theorem exists_isPerfPair :
    ∃ p : L Γ →ₗ[ℤ] L Γ →ₗ[ℤ] ℤ, (∀ x y, p x y = Xf x ⬝ᵥ ff y) ∧ p.IsPerfPair :=
  Submodule.exists_isPerfPair_dotProduct_of_saturated (Bd Γ) (Ec Γ)
    (fun n v hn hv => Bd_saturated n v hn hv) (fun n v hn hv => Ec_saturated n v hn hv)
    (fun _ hb _ he => Bd_dot_Ec hb he) ff Xf (fun y _ he => ff_dot_Ec y he)
    (fun x _ hb => Xf_dot_Bd x hb) eq_zero_of_ff_mem_Bd eq_zero_of_Xf_mem_Ec exists_sub_ff_mem_Bd
    (fun n v hn h => Xf_sat n v hn h)

variable {Γ}

private theorem sum_quotient_eq_index_mul [Fintype (SL(2, ℤ) ⧸ Γ)] (Ψ : Qb Γ → ℤ) (Φ : SL(2, ℤ) ⧸ Γ
    → ℤ)
    (hΦ : ∀ g, Φ (QuotientGroup.mk g) = Ψ (QuotientGroup.mk g)) :
    ∑ q, Φ q = ((Γ.subgroupOf (pm Γ)).index : ℤ) * ∑ q, Ψ q := by
  classical
  haveI : (Γ.subgroupOf (pm Γ)).FiniteIndex := by infer_instance
  haveI : Fintype (pm Γ ⧸ Γ.subgroupOf (pm Γ)) := Fintype.ofFinite _
  set e := Subgroup.quotientEquivProdOfLE (le_pm Γ) with he
  have h1 : ∀ q, Φ q = Ψ (e q).1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g => rw [hΦ]; rfl
  simp_rw [h1]
  rw [Fintype.sum_equiv e (fun q => Ψ (e q).1) (fun pr => Ψ pr.1) (fun _ => rfl),
      Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.index,
      Nat.card_eq_fintype_card]

private theorem pair_eq_neg_dot (x y : L Γ) :
    pair Γ ((Int.castAddHom ℚ).comp (x : Additive Γ →+ ℤ)) ((Int.castAddHom ℚ).comp (y : Additive Γ
        →+ ℤ)) =
      -((Xf x ⬝ᵥ ff y : ℤ) : ℚ) := by
  classical
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  set Φ : SL(2, ℤ) ⧸ Γ → ℤ := fun q => Xfun x q.out * ffun y q.out with hΦdef
  have hΦ' : ∀ g, Φ (QuotientGroup.mk g) = Xfun x g * ffun y g := by
    intro g
    obtain ⟨⟨γ, hγ⟩, h⟩ := QuotientGroup.mk_out_eq_mul Γ g
    simp only [hΦdef, h]
    rw [rInv_Xfun x g γ (le_pm Γ hγ), rInv_ffun y g γ (le_pm Γ hγ)]
  have hΦ : ∀ g, Φ (QuotientGroup.mk g) = (Fx x g - Fx x (S * g)) * (Gb y g - Ga y g) := hΦ'
  have hC := ModularCurve.CupPairing.mult_mul_pair_eq_neg_finsum Γ (x : Additive Γ →+ ℤ)
    (y : Additive Γ →+ ℤ) x.2 y.2 (Fx x) (Fx_T x) (Fx_neg x) (Fx_mul x) (Ga y) (Gb y) (Ga_S y)
        (Gb_U y)
    (Ga_mul y) (Gb_mul y) Φ hΦ
  rw [finsum_eq_sum_of_fintype,
    sum_quotient_eq_index_mul (fun q => Xf x q * ff y q) Φ (fun g => by
      show Φ (QuotientGroup.mk g) = Xf x (QuotientGroup.mk g) * ff y (QuotientGroup.mk g)
      rw [hΦ', Xf_mk, ff_mk])] at hC
  push_cast at hC
  rw [index_subgroupOf_pm] at hC
  have hne : (mult Γ : ℚ) ≠ 0 := mult_ne_zero Γ
  have : pair Γ ((Int.castAddHom ℚ).comp (x : Additive Γ →+ ℤ)) ((Int.castAddHom ℚ).comp (y :
      Additive Γ →+ ℤ)) =
      -((∑ q, Xf x q * ff y q : ℤ) : ℚ) := by
    apply mul_left_cancel₀ hne
    rw [hC]; push_cast; ring
  rw [this, dotProduct]

end Final

end ModularCurve.CupPairing.PD

open scoped MatrixGroups in
open ModularCurve.CupPairing.PD in
/-- On the parabolic homomorphisms `Additive Γ →+ ℤ` of a finite-index subgroup `Γ`, there is a
perfect `ℤ`-bilinear pairing whose values, cast to `ℚ`, are the rational cup pairing. -/
public theorem ModularCurve.CupPairing.exists_perfectPairing_intCast_eq_pair (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex] :
    ∃ IP : ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ] ℤ,
      Function.Bijective IP ∧ Function.Bijective IP.flip ∧
      ∀ x y : ModularCurve.Period.parabolicHoms ℤ Γ ℤ,
        (IP x y : ℚ) = ModularCurve.CupPairing.pair Γ
          ((Int.castAddHom ℚ).comp (x : Additive Γ →+ ℤ))
          ((Int.castAddHom ℚ).comp (y : Additive Γ →+ ℤ)) := by
  obtain ⟨p, hp, hperf⟩ := exists_isPerfPair Γ
  refine ⟨-p, ?_, ?_, fun x y => ?_⟩
  · have e : ⇑(-p) = (Equiv.neg _) ∘ ⇑p := by ext; simp
    rw [e]
    exact (Equiv.neg _).bijective.comp hperf.bijective_left
  · have e : ⇑((-p).flip) = (Equiv.neg _) ∘ ⇑p.flip := by ext; simp
    rw [e]
    exact (Equiv.neg _).bijective.comp hperf.bijective_right
  · rw [LinearMap.neg_apply, LinearMap.neg_apply, hp, pair_eq_neg_dot, Int.cast_neg]
