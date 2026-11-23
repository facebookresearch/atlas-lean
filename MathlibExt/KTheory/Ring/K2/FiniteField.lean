/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.K2.MatsumotoEquivalence
public import MathlibExt.KTheory.Milnor.ClassicalK2Laws
public import MathlibExt.KTheory.Milnor.ClassicalK2Extensionality
public import Mathlib.FieldTheory.Finite.Basic

/-! # K₂ of finite fields

The algebraic K₂ of every finite field is trivial. The proof reduces Milnor symbols
using the cyclic unit group, bilinearity and the Steinberg relation, then applies
Matsumoto's equivalence with the existing algebraic K₂ kernel.
-/

public section

open scoped IsMulCommutative

universe u

namespace AlgebraicKTheory.K2

private theorem exists_nonsquare_pair {F : Type u} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) : ∃ a : F, ¬IsSquare a ∧ ¬IsSquare (1 - a) := by
  classical
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare (F := F) hF
  have hc0 : c ≠ 0 := by
    intro he
    exact hc (he ▸ IsSquare.zero)
  by_contra h
  have hs : ∀ x : F, ¬IsSquare x → IsSquare (1 - x) := by
    intro x hx
    by_contra hx'
    exact h ⟨x, hx, hx'⟩
  let N := {x : F // ¬IsSquare x}
  let t : N → N := fun x => ⟨(1 - x.val) / c, by
    intro hq
    have hx1 : x.val ≠ 1 := by
      intro he
      exact x.property (he ▸ IsSquare.one)
    have hnum0 : 1 - x.val ≠ 0 := sub_ne_zero.mpr hx1.symm
    have hsq : IsSquare ((1 - x.val) / ((1 - x.val) / c)) := (hs x.val x.property).div hq
    rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ hnum0] at hsq
    exact hc hsq⟩
  have ht : Function.Injective t := by
    intro x y he
    apply Subtype.ext
    have hv : (1 - x.val) / c = (1 - y.val) / c := congrArg Subtype.val he
    have hsub : 1 - x.val = 1 - y.val := (div_left_inj' hc0).mp hv
    have hneg : -x.val = -y.val := by
      apply add_left_cancel (a := (1 : F))
      simpa only [sub_eq_add_neg] using hsub
    exact neg_injective hneg
  have hsurj : Function.Surjective t := Finite.injective_iff_surjective.mp ht
  have hcinv : ¬IsSquare c⁻¹ := fun he => hc (isSquare_inv.mp he)
  obtain ⟨x, hx⟩ := hsurj ⟨c⁻¹, hcinv⟩
  have hv : (1 - x.val) / c = c⁻¹ := congrArg Subtype.val hx
  have he : 1 - x.val = 1 := by
    have hm := congrArg (fun y : F => y * c) hv
    simpa only [div_mul_cancel₀ _ hc0, inv_mul_cancel₀ hc0] using hm
  have hx0 : x.val = 0 := sub_eq_self.mp he
  exact x.property (hx0 ▸ IsSquare.zero)

private theorem odd_zsmul_eq {M : Type*} [AddCommGroup M] {c : M} {n : ℤ}
    (hc : c + c = 0) (hn : Odd n) : n • c = c := by
  obtain ⟨k, hk⟩ := hn
  rw [hk, two_mul, add_zsmul, add_zsmul, one_zsmul, ← zsmul_add, hc, zsmul_zero, zero_add]

private theorem generator_self_symbol_zero {F : Type u} [Field F] [Finite F]
    (g : Fˣ) (hg : ∀ a : Fˣ, a ∈ Subgroup.zpowers g) : MilnorK.k2Symbol F g g = 0 := by
  classical
  have h2 := MilnorK.k2Symbol_add_swap F g g
  by_cases hF : ringChar F = 2
  · have hunit : (-1 : Fˣ) = 1 := by
      apply Units.ext
      change (-1 : F) = 1
      exact neg_one_eq_one_iff.mpr hF
    rw [MilnorK.k2Symbol_a_a, hunit, MilnorK.k2Symbol_one_right]
  · obtain ⟨a, ha, hb⟩ := exists_nonsquare_pair (F := F) hF
    have ha0 : a ≠ 0 := by
      intro he
      exact ha (he ▸ IsSquare.zero)
    have ha1 : a ≠ 1 := by
      intro he
      exact ha (he ▸ IsSquare.one)
    have hb0 : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.symm
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 a ha0))
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 (1 - a) hb0))
    have hno : Odd n := Int.not_even_iff_odd.mp (by
      intro he
      obtain ⟨z, hz⟩ := Even.isSquare_zpow he g
      apply ha
      refine ⟨(z : F), ?_⟩
      have hv := congrArg (fun w : Fˣ => (w : F)) hz
      simpa only [hn, Units.val_mk0, Units.val_mul] using hv)
    have hmo : Odd m := Int.not_even_iff_odd.mp (by
      intro he
      obtain ⟨z, hz⟩ := Even.isSquare_zpow he g
      apply hb
      refine ⟨(z : F), ?_⟩
      have hv := congrArg (fun w : Fˣ => (w : F)) hz
      simpa only [hm, Units.val_mk0, Units.val_mul] using hv)
    have hst := MilnorK.k2Symbol_steinberg F a ha0 ha1
    rw [← hn, ← hm, MilnorK.k2Symbol_zpow_zpow] at hst
    rwa [odd_zsmul_eq h2 (hno.mul hmo)] at hst

private theorem milnor_eq_zero {F : Type u} [Field F] [Finite F] (x : MilnorK F 2) : x = 0 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hg0 := generator_self_symbol_zero g hg
  have hsymbols : ∀ a b : Fˣ, MilnorK.k2Symbol F a b = 0 := by
    intro a b
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    rw [← hn, ← hm, MilnorK.k2Symbol_zpow_zpow, hg0, zsmul_zero]
  have hlinear : (LinearMap.id : MilnorK F 2 →ₗ[ℤ] MilnorK F 2) = 0 := by
    apply MilnorK.k2Symbol_ext F
    intro a b
    simpa only [LinearMap.id_apply, LinearMap.zero_apply] using hsymbols a b
  simpa only [LinearMap.id_apply, LinearMap.zero_apply] using DFunLike.congr_fun hlinear x

/-- Every element of the algebraic K₂ of a finite field is the identity. -/
theorem finiteField_eq_one {F : Type u} [Field F] [Finite F] (x : K2 F) : x = 1 := by
  change (Additive.ofMul x : Additive (K2 F)) = 0
  let e := matsumotoAddEquiv_unconditional F
  obtain ⟨y, hy⟩ := e.surjective (Additive.ofMul x)
  rw [← hy, milnor_eq_zero y, e.map_zero]

end AlgebraicKTheory.K2
