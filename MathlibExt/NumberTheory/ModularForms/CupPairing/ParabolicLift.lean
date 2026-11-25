/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero.lean`
and
`P2M/Sol/S_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero.lean`
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
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import MathlibExt.NumberTheory.ModularForms.CupPairing.OrbitSum
import MathlibExt.NumberTheory.ModularForms.ModularGroupParabolic
import MathlibExt.NumberTheory.ModularForms.ModularGroupSerreTree

/-!
# Lifting coset functions to parabolic homomorphisms

If `-1 ∈ Γ` and a function `f` on `SL(2, ℤ) ⧸ Γ` is orthogonal to every `e - e ∘ (S • ·)` with
`e` invariant under `T`, then `f` is the difference `b - a` of an `S`-invariant and an
`S * T`-invariant primitive of a parabolic homomorphism.
-/

set_option linter.unusedSectionVars false

namespace ModularCurve
namespace CupPairing
namespace Shapiro
open ModularCurve

open Matrix.SpecialLinearGroup ModularGroup MulAction
open ModularCurve.CupPairing.OrbitSum

open scoped MatrixGroups

section Main

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
variable (f : SL(2, ℤ) ⧸ Γ → ℤ)

private def cfun (g : SL(2, ℤ)) : ℤ := f (QuotientGroup.mk g)

private theorem cfun_mul_mem (g x : SL(2, ℤ)) (hx : x ∈ Γ) : cfun Γ f (g * x) = cfun Γ f g := by
  unfold cfun
  congr 1
  rw [QuotientGroup.eq]
  simpa using hx

include hneg in
private theorem cfun_neg (g : SL(2, ℤ)) : cfun Γ f (-g) = cfun Γ f g := by
  rw [show -g = g * (-1) by simp]
  exact cfun_mul_mem Γ f g _ hneg

include hneg in
private theorem neg_one_smul (q : SL(2, ℤ) ⧸ Γ) : (-1 : SL(2, ℤ)) • q = q := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [Quotient.smul_mk, QuotientGroup.eq]
    simpa using hneg

include hneg in
private theorem S_inv_smul (q : SL(2, ℤ) ⧸ Γ) : S⁻¹ • q = S • q := by
  rw [ModularGroup.S_inv, show -S = S * (-1) by simp, mul_smul, neg_one_smul Γ hneg]

private structure Potentials where
  a : SL(2, ℤ) → ℤ
  b : SL(2, ℤ) → ℤ
  ha : ∀ g, a (S * g) = a g
  hb : ∀ g, b (S * T * g) = b g
  hab : ∀ g, cfun Γ f g = b g - a g

include hneg in
private theorem nonempty_potentials : Nonempty (Potentials Γ f) := by
  obtain ⟨a, b, ha, hb, hab⟩ :=
    ModularGroup.exists_apply_eq_sub_of_apply_neg_eq (cfun Γ f) (cfun_neg Γ hneg f)
  exact ⟨⟨a, b, ha, hb, hab⟩⟩

variable {Γ f} (P : Potentials Γ f)

private theorem a_neg (g : SL(2, ℤ)) : P.a (-g) = P.a g := neg_invariant_of_S P.a P.ha g

private theorem a_mul_sub_eq (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (g : SL(2, ℤ)) :
    P.a (g * γ) - P.a g = P.a γ - P.a 1 := by
  have key : ∀ h, P.a (h * γ) - P.a h = P.b (h * γ) - P.b h := by
    intro h
    have h1 := P.hab h
    have h2 := P.hab (h * γ)
    rw [cfun_mul_mem Γ f h γ hγ] at h2
    linarith
  have := eq_apply_one_of_S_U (fun h => P.a (h * γ) - P.a h)
    (fun h => by simp only [mul_assoc, P.ha])
    (fun h => by
      show P.a (S * T * h * γ) - P.a (S * T * h) = P.a (h * γ) - P.a h
      rw [key, key, mul_assoc (S * T) h γ, P.hb, P.hb]) g
  simpa using this

private theorem b_mul_sub_eq (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (g : SL(2, ℤ)) :
    P.b (g * γ) - P.b g = P.a γ - P.a 1 := by
  have h1 := P.hab g
  have h2 := P.hab (g * γ)
  rw [cfun_mul_mem Γ f g γ hγ] at h2
  have := a_mul_sub_eq P γ hγ g
  linarith

private def phi : Additive Γ →+ ℤ where
  toFun γ := P.a ((Additive.toMul γ : Γ) : SL(2, ℤ)) - P.a 1
  map_zero' := by simp
  map_add' γ γ' := by
    have := a_mul_sub_eq P ((Additive.toMul γ' : Γ) : SL(2, ℤ)) (Additive.toMul γ').2
      ((Additive.toMul γ : Γ) : SL(2, ℤ))
    simp only [toMul_add, Subgroup.coe_mul] at this ⊢
    linarith

private theorem phi_apply (γ : Γ) : phi P (Additive.ofMul γ) = P.a γ - P.a 1 := rfl

private theorem a_mul (g : SL(2, ℤ)) (γ : Γ) : P.a (g * γ) = P.a g + phi P (Additive.ofMul γ) := by
  rw [phi_apply, ← a_mul_sub_eq P γ γ.2 g]; ring

private theorem b_mul (g : SL(2, ℤ)) (γ : Γ) : P.b (g * γ) = P.b g + phi P (Additive.ofMul γ) := by
  rw [phi_apply, ← b_mul_sub_eq P γ γ.2 g]; ring

private theorem a_T_mul_sub (g : SL(2, ℤ)) : P.a (T * g) - P.a g = cfun Γ f g - cfun Γ f (S * T *
    g) := by
  rw [T_mul_eq, a_neg, P.ha]
  have h1 := P.hab g
  have h2 := P.hab (S * T * g)
  rw [P.hb] at h2
  linarith

private theorem a_T_pow_mul_sub (g : SL(2, ℤ)) (n : ℕ) :
    P.a (T ^ n * g) - P.a g =
      ∑ k ∈ Finset.range n, (cfun Γ f (T ^ k * g) - cfun Γ f (S * T * (T ^ k * g))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, pow_succ', mul_assoc]
    have := a_T_mul_sub P (T ^ n * g)
    linarith

variable (hf : ∀ e : SL(2, ℤ) ⧸ Γ → ℤ, (∀ q, e (T • q) = e q) → ∑ᶠ q, f q * (e q - e (S • q)) = 0)

include hneg hf in
private theorem sum_period_eq_zero (g : SL(2, ℤ)) :
    ∑ k ∈ Finset.range (Function.minimalPeriod (T • ·) (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ)),
      (cfun Γ f (T ^ k * g) - cfun Γ f (S * T * (T ^ k * g))) = 0 := by
  classical
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  set q₀ : SL(2, ℤ) ⧸ Γ := QuotientGroup.mk g with hq₀
  set e : SL(2, ℤ) ⧸ Γ → ℤ := fun x =>
    if (Quotient.mk (orbitRel (Subgroup.zpowers T) (SL(2, ℤ) ⧸ Γ)) x :
        orbitRel.Quotient (Subgroup.zpowers T) (SL(2, ℤ) ⧸ Γ)) =
      Quotient.mk (orbitRel (Subgroup.zpowers T) (SL(2, ℤ) ⧸ Γ)) q₀ then 1 else 0 with he
  have heT : ∀ q, e (T • q) = e q := by
    intro q
    have : (Quotient.mk (orbitRel (Subgroup.zpowers T) (SL(2, ℤ) ⧸ Γ)) (T • q) :
        orbitRel.Quotient (Subgroup.zpowers T) (SL(2, ℤ) ⧸ Γ)) =
        Quotient.mk (orbitRel (Subgroup.zpowers T) (SL(2, ℤ) ⧸ Γ)) q :=
      Quotient.sound ⟨⟨T, Subgroup.mem_zpowers T⟩, rfl⟩
    simp only [he, this]
  have h0 := hf e heT
  rw [finsum_eq_sum_of_fintype] at h0
  simp only [mul_sub, Finset.sum_sub_distrib] at h0
  have hA : ∑ x, f x * e x = ∑ k ∈ Finset.range (Function.minimalPeriod (T • ·) q₀), f (T ^ k • q₀)
      := by
    rw [← sum_mul_indicator_class Γ T f q₀]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [he, mul_ite, mul_one, mul_zero]
  have hB : ∑ x, f x * e (S • x) =
      ∑ k ∈ Finset.range (Function.minimalPeriod (T • ·) q₀), f (S • T ^ k • q₀) := by
    rw [← sum_mul_indicator_class Γ T (fun x => f (S • x)) q₀]
    rw [← Fintype.sum_equiv (MulAction.toPerm (S : SL(2, ℤ))) (fun x => f (S • x) * e (S • S • x))
      (fun x => f x * e (S • x)) (fun x => rfl)]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hSS : S • S • x = x := by
      rw [smul_smul, S_mul_S_eq, neg_one_smul Γ hneg]
    simp only [he, hSS, mul_ite, mul_one, mul_zero]
  rw [hA, hB] at h0
  rw [Finset.sum_sub_distrib]
  have h1 : ∀ k, cfun Γ f (T ^ k * g) = f (T ^ k • q₀) := fun k => rfl
  have h2 : ∀ k, cfun Γ f (S * T * (T ^ k * g)) = f (S • T ^ (k + 1) • q₀) := by
    intro k; rw [U_mul_T_pow]; rfl
  simp only [h1, h2]
  rw [sum_period_shift_one Γ T q₀ (fun q => f (S • q))]
  linarith

include hneg hf in
private theorem phi_eq_zero_of_eq_conj (γ : Γ) (ε δ : SL(2, ℤ)) (n : ℕ) (hε : ε = 1 ∨ ε = -1)
    (hγ : (γ : SL(2, ℤ)) = ε * (δ * T ^ n * δ⁻¹)) : phi P (Additive.ofMul γ) = 0 := by
  classical
  set g := δ⁻¹ with hg
  have hgγ : g * γ = ε * (T ^ n * g) := by
    rw [hγ, hg]
    rcases hε with rfl | rfl <;> simp [mul_assoc]
  have hεa : ∀ m, P.a (ε * m) = P.a m := by
    intro m; rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, a_neg]
  have hφ : phi P (Additive.ofMul γ) = P.a (T ^ n * g) - P.a g := by
    rw [← hεa, ← hgγ, a_mul]; ring
  rw [hφ, a_T_pow_mul_sub]
  set q₀ : SL(2, ℤ) ⧸ Γ := QuotientGroup.mk g with hq₀
  set w := Function.minimalPeriod (T • ·) q₀ with hw
  have hTn : T ^ n * g = ε⁻¹ * (g * γ) := by rw [hgγ]; simp
  have hfix : T ^ n • q₀ = q₀ := by
    rw [hq₀, Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, hTn]
    rcases hε with rfl | rfl
    · simpa using Γ.inv_mem γ.2
    · have := Γ.mul_mem (Γ.inv_mem γ.2) hneg
      simpa using this
  obtain ⟨m, hm⟩ := (pow_smul_eq_iff_minimalPeriod_dvd).mp hfix
  rw [hm]
  rw [sum_range_mul_of_periodic _ w ?_ m, sum_period_eq_zero hneg hf g, smul_zero]
  intro k
  have hper : T ^ (k + w) * g = T ^ k * (T ^ w * g) := by rw [pow_add]; group
  have hTw : ∃ x ∈ Γ, T ^ w * g = g * x := by
    have := pow_minimalPeriod_smul Γ T q₀
    rw [← hw, hq₀, Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at this
    exact ⟨g⁻¹ * (T ^ w * g), by simpa [mul_assoc] using Γ.inv_mem this, by group⟩
  obtain ⟨x, hx, hxe⟩ := hTw
  simp only [hper, hxe, ← mul_assoc, cfun_mul_mem Γ f _ x hx]

include hneg hf in
private theorem isParabolicHom_phi : ModularCurve.Period.IsParabolicHom Γ (phi P) := by
  intro γ hγ
  obtain ⟨ε, δ, n, hε, hn⟩ := ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four γ hγ
  rcases le_or_gt 0 n with h0 | h0
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    exact phi_eq_zero_of_eq_conj hneg P hf γ ε δ k hε (by rw [hn, zpow_natCast])
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr h0.le)
    have hinv : ((γ⁻¹ : Γ) : SL(2, ℤ)) = ε⁻¹ * (δ * T ^ k * δ⁻¹) := by
      rw [Subgroup.coe_inv, hn, mul_inv_rev]
      rw [show (δ * T ^ n * δ⁻¹)⁻¹ = δ * T ^ k * δ⁻¹ by
        rw [mul_inv_rev, mul_inv_rev, inv_inv, ← zpow_neg, hk, zpow_natCast, mul_assoc]]
      rcases hε with rfl | rfl <;> simp
    have hε' : ε⁻¹ = 1 ∨ ε⁻¹ = -1 := by rcases hε with rfl | rfl <;> simp
    have := phi_eq_zero_of_eq_conj hneg P hf γ⁻¹ ε⁻¹ δ k hε' hinv
    rwa [ofMul_inv, map_neg, neg_eq_zero] at this

end Main

end ModularCurve.CupPairing.Shapiro

open scoped MatrixGroups in
open ModularCurve.CupPairing.Shapiro in
/-- If `-1 ∈ Γ` and `f` is orthogonal to `e - e ∘ (S • ·)` for every `T`-invariant `e`, then
`f` is `b - a` for an `S`-invariant primitive `a` and an `S * T`-invariant primitive `b` of
the same parabolic homomorphism. -/
public theorem ModularCurve.CupPairing.exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (f : SL(2, ℤ) ⧸ Γ → ℤ)
    (hf : ∀ e : SL(2, ℤ) ⧸ Γ → ℤ, (∀ q, e (ModularGroup.T • q) = e q) →
      ∑ᶠ q, f q * (e q - e (ModularGroup.S • q)) = 0) :
    ∃ φ : Additive Γ →+ ℤ, ModularCurve.Period.IsParabolicHom Γ φ ∧
      ∃ a b : SL(2, ℤ) → ℤ, (∀ g, a (ModularGroup.S * g) = a g) ∧
        (∀ g, b (ModularGroup.S * ModularGroup.T * g) = b g) ∧
        (∀ (g : SL(2, ℤ)) (γ : Γ), a (g * γ) = a g + φ (Additive.ofMul γ)) ∧
        (∀ (g : SL(2, ℤ)) (γ : Γ), b (g * γ) = b g + φ (Additive.ofMul γ)) ∧
        ∀ g, f (QuotientGroup.mk g) = b g - a g := by
  obtain ⟨P⟩ := nonempty_potentials Γ hneg f
  exact ⟨phi P, isParabolicHom_phi hneg P hf, P.a, P.b, P.ha, P.hb, a_mul P, b_mul P, P.hab⟩
