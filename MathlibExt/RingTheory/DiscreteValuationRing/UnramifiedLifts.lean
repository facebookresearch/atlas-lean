/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CerednikDrinfeld_FormalOmega_charP_residue_and_forall_exists_pow_eq.lean`,
`P2M/Sol/S_CerednikDrinfeld_FormalOmega_charP_residue_and_forall_exists_pow_eq.lean`,
`Theorems/Thm_CerednikDrinfeld_FormalOmega_ringHom_ext_of_isNilpotent_natCast.lean`,
`P2M/Sol/S_CerednikDrinfeld_FormalOmega_ringHom_ext_of_isNilpotent_natCast.lean`,
`Theorems/Thm_CerednikDrinfeld_FormalOmega_exists_ringHom_wittVector_surjective_and_ker_eq_of_ker_
eq_span.lean`,
`P2M/Sol/S_CerednikDrinfeld_FormalOmega_exists_ringHom_wittVector_surjective_and_ker_eq_of_ker_eq_
span.lean`,
`Theorems/Thm_CerednikDrinfeld_FormalOmega_existsUnique_algHom_comp_eq_of_surjective_of_
isNilpotent.lean` and
`P2M/Sol/S_CerednikDrinfeld_FormalOmega_existsUnique_algHom_comp_eq_of_surjective_of_
isNilpotent.lean`
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

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.WittVector.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.Tactic.LinearCombination
import MathlibExt.RingTheory.WittVector.Lift

@[expose] public section

universe u

/-- If a proper ideal `I` of a commutative ring `R` contains the prime `r`, and every monic
polynomial of positive degree over `R` has a root modulo `I`, then `R ⧸ I` has characteristic `r`
and every element of `R ⧸ I` is an `r`-th power: a root of `X ^ r - C x` modulo `I` is an `r`-th
root of the class of `x`. -/
public theorem Ideal.charP_quotient_and_forall_exists_pow_eq {R : Type*} [CommRing R]
    {I : Ideal R} {r : ℕ} [Fact r.Prime] (hI : I ≠ ⊤) (hr : (r : R) ∈ I)
    (hroot : ∀ p : Polynomial R, p.Monic → 0 < p.natDegree → ∃ x : R, p.eval x ∈ I) :
    CharP (R ⧸ I) r ∧ ∀ a : R ⧸ I, ∃ b : R ⧸ I, b ^ r = a := by
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : Nontrivial R := (Ideal.Quotient.mk_surjective (I := I)).nontrivial
  refine ⟨(CharP.charP_iff_prime_eq_zero Fact.out).mpr ?_, fun a => ?_⟩
  · rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact hr
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, hy⟩ := hroot _ (Polynomial.monic_X_pow_sub_C x (Fact.out : r.Prime).ne_zero)
      (by rw [Polynomial.natDegree_X_pow_sub_C]; exact (Fact.out : r.Prime).pos)
    refine ⟨Ideal.Quotient.mk I y, ?_⟩
    rw [← map_pow, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      using hy

namespace IsDiscreteValuationRing

set_option autoImplicit false

/-- The residue ring of `Onr` at the prime above `π` has characteristic
`r`, and every residue class is an `r`-th power. -/
public theorem charP_residue_and_forall_exists_pow_eq
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type u) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span
      {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p
      ∈ Ideal.span {algebraMap 𝒪 Onr π}) :
    CharP (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r ∧
      ∀ a : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}, ∃ b : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}, b ^
        r = a := by
  refine Ideal.charP_quotient_and_forall_exists_pow_eq hOnr_max.ne_top ?_ hOnr_closed
  have hr : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr
  rw [← map_natCast (algebraMap 𝒪 Onr), ← hc, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

set_option autoImplicit false

/-- Two ring homomorphisms out of `𝒪` agree when `r` is nilpotent in
the target: `𝒪` is generated over `ℕ` modulo powers of `r`. -/
public theorem ringHom_ext_of_isNilpotent_natCast
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (C : Type u) [CommRing C] (hC : IsNilpotent ((r : ℕ) : C)) (f g : 𝒪 →+* C) : f = g := by
  classical
  have hr : (r : ℕ).Prime := Fact.out

  have hrI : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by rw [← hunr]; exact Ideal.mem_span_singleton_self _
  have hI_ne_top : Ideal.span {π} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hπ.not_isUnit

  haveI : Nontrivial (𝒪 ⧸ Ideal.span {π}) := ⟨⟨0, 1, Ideal.Quotient.zero_ne_one_iff.2 hI_ne_top⟩⟩
  haveI hchar : CharP (𝒪 ⧸ Ideal.span {π}) r := by
    refine (CharP.charP_iff_prime_eq_zero hr).2 ?_
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {π})), Ideal.Quotient.eq_zero_iff_mem]; exact
      hrI
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by rw [hres]; exact hr.ne_zero)
  letI : Fintype (𝒪 ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hbij : Function.Bijective (ZMod.castHom (dvd_refl r) (𝒪 ⧸ Ideal.span {π})) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨ZMod.castHom_injective (𝒪 ⧸ Ideal.span {π}), ?_⟩
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hres]
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have digit : ∀ x : 𝒪, ∃ (a : ℕ) (y : 𝒪), x = a + (r : 𝒪) * y := by
    intro x
    obtain ⟨z, hz⟩ := hbij.2 (Ideal.Quotient.mk (Ideal.span {π}) x)
    refine ⟨z.val, ?_⟩
    have hx : x - (z.val : 𝒪) ∈ Ideal.span {π} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_natCast, ← hz, ZMod.natCast_val,
        ZMod.castHom_apply, sub_self]
    rw [← hunr, Ideal.mem_span_singleton'] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, by rw [mul_comm] at hy; rw [hy]; ring⟩

  have digits : ∀ (N : ℕ) (x : 𝒪), ∃ (n : ℕ) (y : 𝒪), x = n + (r : 𝒪) ^ N * y := by
    intro N
    induction N with
    | zero => intro x; exact ⟨0, x, by simp⟩
    | succ N ih =>
      intro x
      obtain ⟨a, y, hx⟩ := digit x
      obtain ⟨n, z, hy⟩ := ih y
      refine ⟨a + r * n, z, ?_⟩
      rw [hx, hy]; push_cast; ring

  obtain ⟨N, hN⟩ := hC
  apply RingHom.ext
  intro x
  obtain ⟨n, y, rfl⟩ := digits N x
  simp only [map_add, map_natCast, map_mul, map_pow, hN, zero_mul, add_zero]

set_option autoImplicit false

namespace P8W2

private theorem surjective_of_forall_sub_mem_span {A B : Type*} [CommRing A] [CommRing B] (f : A
  →+* B) (ϖ : B)
    (hϖ : ϖ ∈ Set.range f) (N : ℕ) (hN : ϖ ^ N = 0)
    (h : ∀ b : B, ∃ a : A, b - f a ∈ Ideal.span {ϖ}) : Function.Surjective f := by
  obtain ⟨p, hp⟩ := hϖ

  have step : ∀ n : ℕ, ∀ b : B, ∃ a : A, b - f a ∈ Ideal.span {ϖ ^ n} := by
    intro n
    induction n with
    | zero => intro b; exact ⟨0, by simp⟩
    | succ n ih =>
      intro b
      obtain ⟨a₀, ha₀⟩ := h b
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha₀
      obtain ⟨a₁, ha₁⟩ := ih c
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 ha₁
      refine ⟨a₀ + p * a₁, Ideal.mem_span_singleton'.2 ⟨d, ?_⟩⟩
      rw [map_add, map_mul, hp]

      have e1 : b - (f a₀ + ϖ * f a₁) = ϖ * (c - f a₁) := by rw [← sub_sub, ← hc]; ring
      rw [e1, ← hd]; ring
  intro b
  obtain ⟨a, ha⟩ := step N b
  rw [hN, Ideal.span_singleton_zero, Ideal.mem_bot, sub_eq_zero] at ha
  exact ⟨a, ha.symm⟩

private theorem surjective_of_comp_eq_of_ker_le {W B K : Type*} [CommRing W] [CommRing B] [CommRing
  K]
    (f : W →+* B) (ρ : B →+* K) (c : W →+* K) (hc : Function.Surjective c) (hcomp : ρ.comp f = c)
    (ϖ : B) (hker : RingHom.ker ρ ≤ Ideal.span {ϖ}) (hϖ : ϖ ∈ Set.range f) (N : ℕ) (hN : ϖ ^ N = 0)
      :
    Function.Surjective f := by
  refine surjective_of_forall_sub_mem_span f ϖ hϖ N hN (fun b => ?_)
  obtain ⟨w, hw⟩ := hc (ρ b)
  refine ⟨w, hker ?_⟩
  rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply, hcomp, hw, sub_self]

private theorem surjective_quotient_pow_of_comp_eq {𝒪 Onr : Type*} [CommRing 𝒪] [CommRing Onr]
  [Algebra 𝒪 Onr]
    (r : ℕ) (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (N : ℕ)
    {W K : Type*} [CommRing W] [CommRing K]
    (f : W →+* Onr ⧸ (Ideal.span {algebraMap 𝒪 Onr π}) ^ (N + 1))
    (ρ : Onr ⧸ (Ideal.span {algebraMap 𝒪 Onr π}) ^ (N + 1) →+* K)
    (hρ : ∀ y : Onr, ρ (Ideal.Quotient.mk _ y) = 0 → y ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (c : W →+* K) (hc : Function.Surjective c) (hcomp : ρ.comp f = c) :
    Function.Surjective f := by

  have hπr : algebraMap 𝒪 Onr π ∈ Ideal.span {((r : ℕ) : Onr)} := by
    have : π ∈ Ideal.span {((r : ℕ) : 𝒪)} := by rw [hunr]; exact Ideal.mem_span_singleton_self π
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 this
    refine Ideal.mem_span_singleton'.2 ⟨algebraMap 𝒪 Onr s, ?_⟩
    rw [← hs, map_mul, map_natCast]
  have hrπ : ((r : ℕ) : Onr) ∈ Ideal.span {algebraMap 𝒪 Onr π} := by
    have : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by rw [← hunr]; exact Ideal.mem_span_singleton_self _
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 this
    refine Ideal.mem_span_singleton'.2 ⟨algebraMap 𝒪 Onr s, ?_⟩
    rw [← map_mul, hs, map_natCast]
  have hrange : ((r : ℕ) : Onr ⧸ (Ideal.span {algebraMap 𝒪 Onr π}) ^ (N + 1)) ∈ Set.range f :=
    ⟨(r : W), map_natCast f r⟩
  refine surjective_of_comp_eq_of_ker_le f ρ c hc hcomp
    ((r : ℕ) : Onr ⧸ (Ideal.span {algebraMap 𝒪 Onr π}) ^ (N + 1)) ?_ hrange (N + 1) ?_
  · intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hy : y ∈ Ideal.span {algebraMap 𝒪 Onr π} := hρ y hx
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hπr
    refine Ideal.mem_span_singleton'.2 ⟨Ideal.Quotient.mk _ (s * t), ?_⟩
    rw [← map_natCast (Ideal.Quotient.mk ((Ideal.span {algebraMap 𝒪 Onr π}) ^ (N + 1))) r, ←
      map_mul, mul_assoc, ht, hs]
  · rw [← map_natCast (Ideal.Quotient.mk ((Ideal.span {algebraMap 𝒪 Onr π}) ^ (N + 1))) r, ←
      map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hrπ (N + 1)

end P8W2

namespace OnrWitt

open WittVector

variable {r : ℕ} [Fact r.Prime]
variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] {π : 𝒪}
variable {Onr : Type u} [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
variable {k : Type u} [Field k] [CharP k r] [PerfectRing k r] {ρ₁ : Onr →+* k}

private abbrev I (π : 𝒪) (Onr : Type u) [CommRing Onr] [Algebra 𝒪 Onr] (N : ℕ) : Ideal Onr :=
  Ideal.span {algebraMap 𝒪 Onr π ^ N}

private theorem I_le (N : ℕ) : I π Onr (N + 1) ≤ I π Onr N := by
  refine Ideal.span_le.2 ?_
  rintro _ rfl
  exact Ideal.mem_span_singleton'.2 ⟨algebraMap 𝒪 Onr π, by ring⟩

private theorem I_le_one : I π Onr 1 ≤ Ideal.span {algebraMap 𝒪 Onr π} := by
  rw [I, pow_one]

section residue

private theorem pi_mem_ker (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) : algebraMap 𝒪
  Onr π ∈ RingHom.ker ρ₁ := by
  rw [hker]; exact Ideal.mem_span_singleton_self _

private theorem I_le_ker (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (N : ℕ) : I π
  Onr (N + 1) ≤ RingHom.ker ρ₁ := by
  refine Ideal.span_le.2 ?_
  rintro _ rfl
  rw [SetLike.mem_coe, pow_succ]
  exact Ideal.mul_mem_left _ _ (pi_mem_ker hker)

private def rhoBar (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (N : ℕ) : Onr ⧸ I π
  Onr (N + 1) →+* k :=
  Ideal.Quotient.lift (I π Onr (N + 1)) ρ₁ (fun a ha => I_le_ker hker N ha)

@[scoped simp] private theorem rhoBar_mk (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π})
    (N : ℕ)
  (x : Onr) : rhoBar hker N (Ideal.Quotient.mk _ x) = ρ₁ x :=
  Ideal.Quotient.lift_mk _ _ _

private theorem rhoBar_surjective (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ :
  Function.Surjective ρ₁) (N : ℕ) : Function.Surjective (rhoBar hker N) := by
  intro a
  obtain ⟨x, rfl⟩ := hρ₁ a
  exact ⟨Ideal.Quotient.mk _ x, rhoBar_mk hker N x⟩

private theorem ker_rhoBar (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (N : ℕ) :
    RingHom.ker (rhoBar hker N) = Ideal.span {Ideal.Quotient.mk (I π Onr (N + 1)) (algebraMap 𝒪 Onr
      π)} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.mem_ker, rhoBar_mk] at hz
    have hx : x ∈ Ideal.span {algebraMap 𝒪 Onr π} := by rw [← hker]; exact hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hx
    exact Ideal.mem_span_singleton'.2 ⟨Ideal.Quotient.mk _ c, by rw [← map_mul, hc]⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, rhoBar_mk]
    exact pi_mem_ker hker

private theorem isNilpotent_ker_rhoBar (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (N
  : ℕ) : IsNilpotent (RingHom.ker (rhoBar hker N)) := by
  refine ⟨N + 1, ?_⟩
  rw [ker_rhoBar, Ideal.span_singleton_pow, ← map_pow, Ideal.zero_eq_bot,
    Ideal.span_singleton_eq_bot]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

private noncomputable def fN (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ :
  Function.Surjective ρ₁) (N : ℕ) : WittVector r k →+* Onr ⧸ I π Onr (N + 1) :=
  (WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker r k (Onr ⧸ I π Onr (N +
    1))
    (rhoBar hker N) (rhoBar_surjective hker hρ₁ N) (isNilpotent_ker_rhoBar hker N)).exists.choose

private theorem rhoBar_comp_fN (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ :
  Function.Surjective ρ₁) (N : ℕ) :
    (rhoBar hker N).comp (fN hker hρ₁ N) = WittVector.constantCoeff :=
  (WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker r k (Onr ⧸ I π Onr (N +
    1))
    (rhoBar hker N) (rhoBar_surjective hker hρ₁ N) (isNilpotent_ker_rhoBar hker
      N)).exists.choose_spec

private theorem fN_unique (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ :
  Function.Surjective ρ₁) (N : ℕ) (g : WittVector r k →+* Onr ⧸ I π Onr (N + 1))
    (hg : (rhoBar hker N).comp g = WittVector.constantCoeff) : g = fN hker hρ₁ N :=
  (WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker r k (Onr ⧸ I π Onr (N +
    1))
    (rhoBar hker N) (rhoBar_surjective hker hρ₁ N) (isNilpotent_ker_rhoBar hker N)).unique hg
      (rhoBar_comp_fN hker hρ₁ N)

private theorem factor_comp_fN (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ :
  Function.Surjective ρ₁) (N : ℕ) :
    (Ideal.Quotient.factor (I_le (π := π) (Onr := Onr) (N + 1))).comp (fN hker hρ₁ (N + 1)) = fN
      hker hρ₁ N := by
  apply fN_unique
  rw [← RingHom.comp_assoc]
  have h : (rhoBar hker N).comp (Ideal.Quotient.factor (I_le (π := π) (Onr := Onr) (N + 1))) =
    rhoBar hker (N + 1) := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, Ideal.Quotient.factor_mk, rhoBar_mk]
  rw [h, rhoBar_comp_fN]

private theorem rho_eq_constantCoeff (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁
  : Function.Surjective ρ₁) (N : ℕ) (x : Onr) (w : WittVector r k)
    (h : Ideal.Quotient.mk (I π Onr (N + 1)) x = fN hker hρ₁ N w) : ρ₁ x = WittVector.constantCoeff
      w := by
  rw [← rhoBar_mk hker N x, h, ← RingHom.comp_apply, rhoBar_comp_fN]

end residue

section kernel

private theorem exists_r_eq_mul (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) : ∃ u : 𝒪, ((r
  : ℕ) : 𝒪) = u * π := by
  have : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by rw [← hunr]; exact Ideal.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨u, hu.symm⟩

private theorem exists_pi_eq_mul (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) : ∃ v : 𝒪, π
  = v * ((r : ℕ) : 𝒪) := by
  have : π ∈ Ideal.span {((r : ℕ) : 𝒪)} := by rw [hunr]; exact Ideal.mem_span_singleton_self _
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨v, hv.symm⟩

private theorem algebraMap_pi_ne_zero (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) :
  algebraMap 𝒪 Onr π ≠ 0 := by
  intro h0
  obtain ⟨u, hu⟩ := exists_r_eq_mul hunr
  have : ((r : ℕ) : Onr) = 0 := by
    rw [← map_natCast (algebraMap 𝒪 Onr) r, hu, map_mul, h0, mul_zero]
  exact (Nat.cast_ne_zero.2 (Fact.out : r.Prime).ne_zero) this

private theorem fN_surjective (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ : Function.Surjective ρ₁) (N :
      ℕ) : Function.Surjective (fN hker hρ₁ N) := by
  obtain ⟨u, hu⟩ := exists_r_eq_mul hunr
  obtain ⟨v, hv⟩ := exists_pi_eq_mul hunr
  have hrπ : ((r : ℕ) : Onr) ∈ Ideal.span {algebraMap 𝒪 Onr π} :=
    Ideal.mem_span_singleton'.2 ⟨algebraMap 𝒪 Onr u, by rw [← map_natCast (algebraMap 𝒪 Onr) r, hu,
      map_mul]⟩
  refine P8W2.surjective_of_comp_eq_of_ker_le (fN hker hρ₁ N) (rhoBar hker N)
    WittVector.constantCoeff
    (WittVector.constantCoeff_surjective r) (rhoBar_comp_fN hker hρ₁ N)
    ((r : ℕ) : Onr ⧸ I π Onr (N + 1)) ?_ ⟨(r : WittVector r k), map_natCast _ r⟩ (N + 1) ?_
  · rw [ker_rhoBar hker N, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    refine Ideal.mem_span_singleton'.2 ⟨Ideal.Quotient.mk _ (algebraMap 𝒪 Onr v), ?_⟩
    rw [← map_natCast (Ideal.Quotient.mk (I π Onr (N + 1))) r, ← map_mul, ← map_natCast (algebraMap
      𝒪 Onr) r,
      ← map_mul, ← hv]
  · rw [← map_natCast (Ideal.Quotient.mk (I π Onr (N + 1))) r, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
    rw [show I π Onr (N + 1) = Ideal.span {algebraMap 𝒪 Onr π} ^ (N + 1) from
      (Ideal.span_singleton_pow _ _).symm]
    exact Ideal.pow_mem_pow hrπ (N + 1)

private theorem fN_apply_eq_zero_of_mem (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ : Function.Surjective ρ₁) (N :
      ℕ) (w : WittVector r k)
    (hw : w ∈ Ideal.span {((r : ℕ) : WittVector r k) ^ (N + 1)}) : fN hker hρ₁ N w = 0 := by
  obtain ⟨u, hu⟩ := exists_r_eq_mul hunr
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hw
  rw [map_mul, map_pow, map_natCast]
  have hr : ((r : ℕ) : Onr ⧸ I π Onr (N + 1)) ^ (N + 1) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (I π Onr (N + 1))) r, ← map_natCast (algebraMap 𝒪 Onr) r,
      hu, map_mul,
      ← map_pow, mul_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  rw [hr, mul_zero]

private theorem mem_of_fN_apply_eq_zero (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ : Function.Surjective ρ₁) : ∀ (N
      : ℕ) (w : WittVector r k), fN hker hρ₁ N w = 0 →
    w ∈ Ideal.span {((r : ℕ) : WittVector r k) ^ (N + 1)} := by
  obtain ⟨u, hu⟩ := exists_r_eq_mul hunr
  obtain ⟨v, hv⟩ := exists_pi_eq_mul hunr
  have hvu : v * u = 1 := by
    have h1 : π = (v * u) * π := by
      conv_lhs => rw [hv, hu]
      ring
    have hπ0 : π ≠ 0 := by
      intro h; apply algebraMap_pi_ne_zero (Onr := Onr) hunr; rw [h, map_zero]
    have := mul_right_cancel₀ hπ0 (h1.symm.trans (one_mul π).symm)
    exact this

  have digit : ∀ (N : ℕ) (w : WittVector r k), fN hker hρ₁ N w = 0 → ∃ w', w = (r : WittVector r k)
    * w' := by
    intro N w hw
    have h0 : WittVector.constantCoeff w = 0 := by
      rw [← rho_eq_constantCoeff hker hρ₁ N 0 w (by rw [map_zero, hw]), map_zero]
    have hmem : w ∈ Ideal.span {((r : ℕ) : WittVector r k)} := by
      rw [← WittVector.ker_constantCoeff]; exact h0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    exact ⟨c, by rw [← hc, mul_comm]⟩
  intro N
  induction N with
  | zero =>
    intro w hw
    obtain ⟨w', rfl⟩ := digit 0 w hw
    rw [zero_add, pow_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  | succ N ih =>
    intro w hw
    obtain ⟨w', rfl⟩ := digit (N + 1) _ hw

    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (fN hker hρ₁ (N + 1) w')
    rw [map_mul, map_natCast, ← hy, ← map_natCast (Ideal.Quotient.mk (I π Onr (N + 1 + 1))) r, ←
      map_mul,
      Ideal.Quotient.eq_zero_iff_mem] at hw
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hw

    have hy' : y ∈ I π Onr (N + 1) := by
      have e1 : (algebraMap 𝒪 Onr u * y - c * algebraMap 𝒪 Onr π ^ (N + 1)) * algebraMap 𝒪 Onr π =
        0 := by
        have : ((r : ℕ) : Onr) = algebraMap 𝒪 Onr u * algebraMap 𝒪 Onr π := by
          rw [← map_natCast (algebraMap 𝒪 Onr) r, hu, map_mul]
        rw [this] at hc
        rw [sub_mul, pow_succ] at *
        linear_combination (-1 : Onr) * hc
      have e2 : algebraMap 𝒪 Onr u * y = c * algebraMap 𝒪 Onr π ^ (N + 1) := by
        have := (mul_eq_zero.1 e1).resolve_right (algebraMap_pi_ne_zero hunr)
        exact sub_eq_zero.1 this
      have e3 : y = algebraMap 𝒪 Onr v * (algebraMap 𝒪 Onr u * y) := by
        rw [← mul_assoc, ← map_mul, hvu, map_one, one_mul]
      rw [e3, e2]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton'.2 ⟨c, rfl⟩)

    have hN : fN hker hρ₁ N w' = 0 := by
      rw [← factor_comp_fN hker hρ₁ N, RingHom.comp_apply, ← hy, Ideal.Quotient.factor_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hy'
    have := ih w' hN
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 this
    refine Ideal.mem_span_singleton'.2 ⟨d, ?_⟩
    rw [← hd]; ring

private theorem fN_apply_eq_zero_iff (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) (hρ₁ : Function.Surjective ρ₁) (N :
      ℕ) (w : WittVector r k) :
    fN hker hρ₁ N w = 0 ↔ w ∈ Ideal.span {((r : ℕ) : WittVector r k) ^ (N + 1)} :=
  ⟨mem_of_fN_apply_eq_zero hunr hker hρ₁ N w, fN_apply_eq_zero_of_mem hunr hker hρ₁ N w⟩

end kernel

end OnrWitt

/-- Witt vectors over the residue field map surjectively onto each
`Onr ⧸ (π ^ N)`, with kernel exactly the ideal generated by `r ^ N`. -/
public theorem exists_ringHom_wittVector_surjective_and_ker_eq_of_ker_eq_span
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type u) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span
      {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p
      ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (k : Type u) [Field k] [CharP k r] [PerfectRing k r]
    (ρ₁ : Onr →+* k) (hρ₁ : Function.Surjective ρ₁)
    (hker : RingHom.ker ρ₁ = Ideal.span {algebraMap 𝒪 Onr π}) :
    ∀ N : ℕ, ∃ f : WittVector r k →+* Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N},
      (0 < N → ∀ (x : Onr) (w : WittVector r k),
          Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x = f w → ρ₁ x =
            WittVector.constantCoeff w) ∧
      Function.Surjective f ∧
      (∀ w : WittVector r k, f w = 0 ↔ w ∈ Ideal.span {((r : ℕ) : WittVector r k) ^ N}) := by
  intro N
  cases N with
  | zero =>

    have htop : Ideal.span {algebraMap 𝒪 Onr π ^ 0} = ⊤ := by rw [pow_zero,
      Ideal.span_singleton_one]
    haveI : Subsingleton (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ 0}) :=
      Ideal.Quotient.subsingleton_iff.2 htop
    refine ⟨(Ideal.Quotient.factor (by rw [htop]; exact le_top)).comp (OnrWitt.fN hker hρ₁ 0), fun
      h => absurd h (lt_irrefl 0),
      fun y => ⟨0, Subsingleton.elim _ _⟩, fun w => ⟨fun _ => ?_, fun _ => Subsingleton.elim _ _⟩⟩
    rw [pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top
  | succ N =>
    exact ⟨OnrWitt.fN hker hρ₁ N, fun _ x w h => OnrWitt.rho_eq_constantCoeff hker hρ₁ N x w h,
      OnrWitt.fN_surjective hunr hker hρ₁ N, fun w => OnrWitt.fN_apply_eq_zero_iff hunr hker hρ₁ N
        w⟩

set_option autoImplicit false

namespace LegLiftAsm

open Function

variable {𝒪 : Type u} [CommRing 𝒪] {Onr : Type u} [CommRing Onr] [Algebra 𝒪 Onr]
  {W : Type u} [CommRing W]
  {B : Type u} [CommRing B] [Algebra 𝒪 B] {B₀ : Type u} [CommRing B₀] [Algebra 𝒪 B₀]

private theorem ringHom_ext_of_surjective {R S T : Type*} [CommRing R] [CommRing S] [Semiring T] (f
  : R →+* S) (hf : Surjective f)
    (g₁ g₂ : S →+* T) (h : g₁.comp f = g₂.comp f) : g₁ = g₂ :=
  RingHom.ext fun s => by obtain ⟨x, rfl⟩ := hf s; exact congrArg (fun φ : R →+* T => φ x) h

private theorem core (r : ℕ) (π : 𝒪) (hrπ : (r : 𝒪) ∈ Ideal.span {π})

    (hW1 : ∀ (C : Type u) [CommRing C], IsNilpotent ((r : ℕ) : C) → ∀ f g : 𝒪 →+* C, f = g)

    (N : ℕ) (fN : W →+* Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N}) (hfN : Surjective fN)
    (hker : ∀ w : W, fN w = 0 → ∃ w' : W, w = (r : W) ^ N * w')

    (p : B →ₐ[𝒪] B₀)
    (hW3 : ∀ g₀ : W →+* B₀, ∃! g : W →+* B, p.toRingHom.comp g = g₀)

    (hB : algebraMap 𝒪 B π ^ N = 0) (ψ₀ : Onr →ₐ[𝒪] B₀) :
    ∃! ψ : Onr →ₐ[𝒪] B, p.comp ψ = ψ₀ := by
  classical

  have hrB : IsNilpotent ((r : ℕ) : B) := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hrπ
    refine ⟨N, ?_⟩
    rw [← map_natCast (algebraMap 𝒪 B), ← ha, map_mul, mul_pow, hB, mul_zero]
  have hrNB : ((r : ℕ) : B) ^ N = 0 := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hrπ
    rw [← map_natCast (algebraMap 𝒪 B), ← ha, map_mul, mul_pow, hB, mul_zero]
  have hB₀ : algebraMap 𝒪 B₀ π ^ N = 0 := by
    rw [← p.commutes, ← map_pow, hB, map_zero]

  have hψ₀I : ∀ a ∈ Ideal.span {algebraMap 𝒪 Onr π ^ N}, ψ₀ a = 0 := by
    intro a ha
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, map_pow, ψ₀.commutes, hB₀, mul_zero]
  let ψ₀' : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N} →ₐ[𝒪] B₀ := Ideal.Quotient.liftₐ (Ideal.span
    {algebraMap 𝒪 Onr π ^ N}) ψ₀ hψ₀I

  let g₀ : W →+* B₀ := ψ₀'.toRingHom.comp fN
  obtain ⟨g, hg, hguniq⟩ := hW3 g₀

  have hgker : ∀ w ∈ RingHom.ker fN, g w = 0 := by
    intro w hw
    obtain ⟨w', rfl⟩ := hker w ((RingHom.mem_ker).1 hw)
    rw [map_mul, map_pow, map_natCast, hrNB, zero_mul]

  let e : W ⧸ RingHom.ker fN ≃+* Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N} :=
    RingHom.quotientKerEquivOfSurjective hfN
  let gbar : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N} →+* B := (Ideal.Quotient.lift (RingHom.ker
    fN) g hgker).comp e.symm.toRingHom
  have hgbar : gbar.comp fN = g := by
    apply RingHom.ext; intro w
    show (Ideal.Quotient.lift (RingHom.ker fN) g hgker) (e.symm (fN w)) = g w
    rw [← RingHom.quotientKerEquivOfSurjective_apply_mk hfN w]
    show (Ideal.Quotient.lift (RingHom.ker fN) g hgker) (e.symm (e (Ideal.Quotient.mk _ w))) = g w
    rw [RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]

  let ψr : Onr →+* B := gbar.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}))
  have hlin : ψr.comp (algebraMap 𝒪 Onr) = algebraMap 𝒪 B := hW1 B hrB _ _
  let ψ : Onr →ₐ[𝒪] B :=
    { toRingHom := ψr
      commutes' := fun c => congrArg (fun φ : 𝒪 →+* B => φ c) hlin }

  have hpgbar : p.toRingHom.comp gbar = ψ₀'.toRingHom := by
    apply ringHom_ext_of_surjective fN hfN
    rw [RingHom.comp_assoc, hgbar, hg]
  have hpψ : p.comp ψ = ψ₀ := by
    apply AlgHom.ext; intro x
    have h1 := congrArg (fun φ : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N} →+* B₀ => φ
      (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x)) hpgbar
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] at h1
    rw [AlgHom.comp_apply]
    refine h1.trans ?_
    show (Ideal.Quotient.liftₐ (Ideal.span {algebraMap 𝒪 Onr π ^ N}) ψ₀ hψ₀I) (Ideal.Quotient.mk
      (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x) = ψ₀ x
    rw [Ideal.Quotient.liftₐ_apply]; rfl
  refine ⟨ψ, hpψ, ?_⟩

  intro ψ' hψ'
  have hψ'I : ∀ a ∈ Ideal.span {algebraMap 𝒪 Onr π ^ N}, ψ' a = 0 := by
    intro a ha
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, map_pow, ψ'.commutes, hB, mul_zero]
  let ψ'' : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N} →ₐ[𝒪] B := Ideal.Quotient.liftₐ (Ideal.span
    {algebraMap 𝒪 Onr π ^ N}) ψ' hψ'I
  have hψ''mk : ψ''.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N})) =
    ψ'.toRingHom := by
    apply RingHom.ext; intro x
    show (Ideal.Quotient.liftₐ (Ideal.span {algebraMap 𝒪 Onr π ^ N}) ψ' hψ'I) (Ideal.Quotient.mk
      (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x) = ψ' x
    rw [Ideal.Quotient.liftₐ_apply]; rfl

  have hg' : p.toRingHom.comp (ψ''.toRingHom.comp fN) = g₀ := by
    apply RingHom.ext; intro w
    obtain ⟨x, hx⟩ : ∃ x : Onr, Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x = fN w :=
      Ideal.Quotient.mk_surjective (fN w)
    show p (ψ'' (fN w)) = ψ₀' (fN w)
    rw [← hx]
    show p ((Ideal.Quotient.liftₐ (Ideal.span {algebraMap 𝒪 Onr π ^ N}) ψ' hψ'I) (Ideal.Quotient.mk
      (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x)) =
      (Ideal.Quotient.liftₐ (Ideal.span {algebraMap 𝒪 Onr π ^ N}) ψ₀ hψ₀I) (Ideal.Quotient.mk
        (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x)
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.liftₐ_apply]
    show p (ψ' x) = ψ₀ x
    exact congrArg (fun φ : Onr →ₐ[𝒪] B₀ => φ x) hψ'
  have hgg : ψ''.toRingHom.comp fN = g := hguniq _ hg'
  have hψ''gbar : ψ''.toRingHom = gbar := by
    apply ringHom_ext_of_surjective fN hfN
    rw [hgg, hgbar]
  apply AlgHom.ext; intro x
  have := congrArg (fun φ : Onr →+* B => φ x) (hψ''mk.symm.trans (congrArg (fun φ => RingHom.comp φ
    (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}))) hψ''gbar))
  exact this

end LegLiftAsm

open LegLiftAsm in
/-- An `𝒪`-algebra map out of `Onr` lifts uniquely through a surjection
whose kernel has square zero, when `π` is nilpotent on both sides. -/
public theorem existsUnique_algHom_comp_eq_of_surjective_of_isNilpotent
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type u) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span
      {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p
      ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (B : Type u) [CommRing B] [Algebra 𝒪 B] (B₀ : Type u) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪]
      B₀)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π))
    (hp : Function.Surjective p) (hsq : ∀ s t : B, p s = 0 → p t = 0 → s * t = 0)
    (ψ₀ : Onr →ₐ[𝒪] B₀) :
    ∃! ψ : Onr →ₐ[𝒪] B, p.comp ψ = ψ₀ := by
  classical

  obtain ⟨N, hN⟩ := hB

  have hrπ : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by rw [← hunr]; exact Ideal.mem_span_singleton_self _
  have hrB : IsNilpotent ((r : ℕ) : B) := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hrπ
    refine ⟨N, ?_⟩
    rw [← map_natCast (algebraMap 𝒪 B), ← ha, map_mul, mul_pow, hN, mul_zero]

  haveI hmax : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal := hOnr_max
  letI : Field (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) := Ideal.Quotient.field _
  obtain ⟨hchar, hroot⟩ := IsDiscreteValuationRing.charP_residue_and_forall_exists_pow_eq 𝒪
    hdvr π hπ hcomplete hres hunr Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed
  haveI := hchar
  haveI : PerfectRing (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r :=
    PerfectRing.ofSurjective _ r (fun a => by
      obtain ⟨b, hb⟩ := hroot a; exact ⟨b, by rw [frobenius_def]; exact hb⟩)

  obtain ⟨fN, -, hfN, hker⟩ :=
    IsDiscreteValuationRing.exists_ringHom_wittVector_surjective_and_ker_eq_of_ker_eq_span
      𝒪 hdvr π hπ hcomplete hres hunr Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed
    (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      Ideal.mk_ker N

  exact core r π hrπ
    (fun C _ hC f g => IsDiscreteValuationRing.ringHom_ext_of_isNilpotent_natCast 𝒪 hdvr π hπ
      hcomplete hres hunr C hC f g)
    N fN hfN
    (fun w hw => by
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 ((hker w).1 hw)
      exact ⟨a, by rw [mul_comm]; exact ha.symm⟩)
    p
    (fun g₀ => WittVector.existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent
      r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B B₀ p.toRingHom hp hsq hrB g₀)
    hN ψ₀

end IsDiscreteValuationRing
