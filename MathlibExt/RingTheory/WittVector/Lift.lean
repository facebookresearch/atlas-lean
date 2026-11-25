/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WittVector_existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker.lean`,
`P2M/Sol/S_WittVector_existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker.lean`,
`Theorems/Thm_WittVector_existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_
isNilpotent.lean` and
`P2M/Sol/S_WittVector_existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent.lean`
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

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.WittVector.Basic

import Mathlib.LinearAlgebra.SModEq.Pow
import Mathlib.RingTheory.Perfection
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.Frobenius
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.RingTheory.WittVector.TeichmullerSeries
import Mathlib.RingTheory.Perfectoid.FontaineTheta

@[expose] public section

universe u

set_option autoImplicit false

namespace WittLift

open WittVector

variable {p : ℕ} [hp : Fact p.Prime]

private theorem isAdicComplete_span_of_pow_eq_zero {B : Type u} [CommRing B] (x : B) {N : ℕ} (hN :
  x ^ N = 0) :
    IsAdicComplete (Ideal.span {x}) B := by
  have hbot : ∀ n, N ≤ n → (Ideal.span {x} ^ n • ⊤ : Submodule B B) = ⊥ := by
    intro n hn
    rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_eq_bot]
    exact pow_eq_zero_of_le hn hN
  haveI : IsHausdorff (Ideal.span {x}) B := ⟨fun y hy => by
    have := hy N
    rw [hbot N le_rfl, SModEq.bot] at this
    exact this⟩
  haveI : IsPrecomplete (Ideal.span {x}) B := ⟨fun f hf => by
    refine ⟨f N, fun n => ?_⟩
    rcases le_or_gt n N with h | h
    · exact hf h
    · have := hf h.le
      rw [hbot N le_rfl, SModEq.bot] at this
      rw [this]⟩
  exact ⟨⟩

end WittLift

namespace WittVector

/-- There is a unique Witt-vector lift over a perfect residue field
through a surjection whose kernel is nilpotent. -/
public theorem existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (B : Type u) [CommRing B] (ρ : B →+* k) (hρ : Function.Surjective ρ) (hnil : IsNilpotent
      (RingHom.ker ρ)) :
    ∃! f : WittVector p k →+* B, ρ.comp f = WittVector.constantCoeff := by
  classical
  obtain ⟨N, hN⟩ := hnil
  set I : Ideal B := RingHom.ker ρ with hIdef
  have hIN : I ^ N = ⊥ := by simpa using hN
  have hIN1 : I ^ (N + 1) = ⊥ := by rw [pow_succ, hIN, Ideal.bot_mul]

  have hpI : ((p : ℕ) : B) ∈ I := by
    rw [hIdef, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hpN : ((p : ℕ) : B) ^ N = 0 := by
    have : ((p : ℕ) : B) ^ N ∈ I ^ N := Ideal.pow_mem_pow hpI N
    rwa [hIN, Ideal.mem_bot] at this

  haveI hpu : Fact (¬ IsUnit ((p : ℕ) : B)) := ⟨fun h => by
    have := h.map ρ
    rw [map_natCast, CharP.cast_eq_zero] at this
    exact not_isUnit_zero this⟩
  haveI : IsAdicComplete (Ideal.span {((p : ℕ) : B)}) B :=
    WittLift.isAdicComplete_span_of_pow_eq_zero _ hpN

  have huniq : ∀ f g : WittVector p k →+* B, ρ.comp f = WittVector.constantCoeff → ρ.comp g =
    WittVector.constantCoeff → f = g := by
    intro f g hf hg
    apply WittVector.eq_of_apply_teichmuller_eq f g ⟨N, hpN⟩
    intro x

    set y : k := (iterateFrobeniusEquiv k p N).symm x with hy
    have hx : x = y ^ p ^ N := by
      rw [hy, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply, RingEquiv.apply_symm_apply]
    have hmod : f (teichmuller p y) ≡ g (teichmuller p y) [SMOD I] := by
      rw [SModEq.sub_mem, hIdef, RingHom.mem_ker, map_sub, sub_eq_zero]
      have h1 := congrArg (fun φ : WittVector p k →+* k => φ (teichmuller p y)) hf
      have h2 := congrArg (fun φ : WittVector p k →+* k => φ (teichmuller p y)) hg
      simp only [RingHom.comp_apply] at h1 h2
      rw [h1, h2]
    have := SModEq.pow_pow_add_one hpI hmod N
    rw [hIN1, SModEq.bot] at this
    rw [hx, map_pow, map_pow, map_pow, this]

  set ρbar : ModP B p →+* k := Ideal.Quotient.lift (Ideal.span {((p : ℕ) : B)}) ρ (fun b hb => by
      rw [Ideal.mem_span_singleton] at hb
      obtain ⟨c, rfl⟩ := hb
      rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]) with hρbar
  have hρbar_mk : ∀ b : B, ρbar (Ideal.Quotient.mk _ b) = ρ b := fun b => Ideal.Quotient.lift_mk _
    _ _
  have hρbar_surj : Function.Surjective ρbar := by
    intro a; obtain ⟨b, rfl⟩ := hρ a; exact ⟨Ideal.Quotient.mk _ b, hρbar_mk b⟩

  set ψ : ModP B p →+* ModP B p := iterateFrobenius (ModP B p) p N with hψ
  have hψker : ∀ z : ModP B p, z ∈ RingHom.ker ρbar → ψ z = 0 := by
    intro z hz
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [RingHom.mem_ker, hρbar_mk] at hz
    have hb : b ^ N = 0 := by
      have : b ^ N ∈ I ^ N := Ideal.pow_mem_pow (by rw [hIdef, RingHom.mem_ker]; exact hz) N
      rwa [hIN, Ideal.mem_bot] at this
    rw [hψ, iterateFrobenius_def, ← map_pow]
    rw [pow_eq_zero_of_le (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le hb, map_zero]

  set ψ' : k →+* ModP B p :=
    (Ideal.Quotient.lift (RingHom.ker ρbar) ψ hψker).comp (RingHom.quotientKerEquivOfSurjective
      hρbar_surj).symm.toRingHom with hψ'
  have hψ'_apply : ∀ z : ModP B p, ψ' (ρbar z) = z ^ p ^ N := by
    intro z
    rw [hψ', RingHom.comp_apply]
    have : (RingHom.quotientKerEquivOfSurjective hρbar_surj).symm.toRingHom (ρbar z) =
      Ideal.Quotient.mk _ z := by
      apply (RingHom.quotientKerEquivOfSurjective hρbar_surj).injective
      rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
      rfl
    rw [this, Ideal.Quotient.lift_mk, hψ, iterateFrobenius_def]

  set sbar : k →+* ModP B p := ψ'.comp (iterateFrobeniusEquiv k p N).symm.toRingHom with hsbar
  have hsbar : ∀ a : k, ρbar (sbar a) = a := by
    intro a
    set a' : k := (iterateFrobeniusEquiv k p N).symm a with ha'
    obtain ⟨z, hz⟩ := hρbar_surj a'
    have : sbar a = ψ' a' := by rw [hsbar, RingHom.comp_apply]; rfl
    rw [this, ← hz, hψ'_apply, map_pow, hz, ha', ← iterateFrobenius_def, ←
      iterateFrobeniusEquiv_apply, RingEquiv.apply_symm_apply]

  let e : k →+* PreTilt B p := Perfection.lift p k (ModP B p) sbar
  have he0 : ∀ a : k, PreTilt.coeff 0 (e a) = sbar a := by
    intro a
    rw [PreTilt.coeff_def]
    show Perfection.coeff (ModP B p) p 0 (Perfection.lift p k (ModP B p) sbar a) = sbar a
    rfl
  let F : WittVector p k →+* B := (WittVector.fontaineTheta B p).comp (WittVector.map e)
  have hF : ρ.comp F = WittVector.constantCoeff := by
    apply WittVector.eq_of_apply_teichmuller_eq _ _ (⟨1, by rw [pow_one, CharP.cast_eq_zero]⟩ :
      IsNilpotent ((p : ℕ) : k))
    intro x
    rw [RingHom.comp_apply]
    show ρ (WittVector.fontaineTheta B p (WittVector.map e (teichmuller p x))) =
      WittVector.constantCoeff (teichmuller p x)
    rw [WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]
    have : ρ (PreTilt.untilt (e x)) = ρbar (Ideal.Quotient.mk _ (PreTilt.untilt (e x))) :=
      (hρbar_mk _).symm
    rw [this, PreTilt.mk_untilt_eq_coeff_zero, he0, hsbar]
    show x = (teichmuller p x).coeff 0
    rw [WittVector.teichmuller_coeff_zero]
  exact ⟨F, hF, fun g hg => huniq g F hg hF⟩

end WittVector


namespace WittVector

/-- A Witt-vector map lifts uniquely through a surjection whose kernel
has square zero, when `p` is nilpotent in the source. -/
public theorem existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (B B₀ : Type u) [CommRing B] [CommRing B₀] (q : B →+* B₀) (hq : Function.Surjective q)
    (hsq : ∀ s t : B, q s = 0 → q t = 0 → s * t = 0) (hpB : IsNilpotent (p : B))
    (ψ₀ : WittVector p k →+* B₀) :
    ∃! ψ : WittVector p k →+* B, q.comp ψ = ψ₀ := by
  classical
  obtain ⟨M₀, hM₀⟩ := hpB
  set M := M₀ + 1 with hMdef
  have hM : (p : B) ^ M = 0 := by rw [hMdef, pow_succ, hM₀, zero_mul]
  have hM' : (p : B₀) ^ M = 0 := by
    have := congrArg q hM
    rwa [map_pow, map_natCast, map_zero] at this
  have hMk : (p : k) ^ M = 0 := by
    rw [hMdef, pow_succ, CharP.cast_eq_zero, mul_zero]

  let J : Ideal (WittVector p k) := Ideal.span {((p : WittVector p k) ^ M)}
  have hJ : ∀ {C : Type u} [CommRing C] (g : WittVector p k →+* C), (p : C) ^ M = 0 → ∀ a ∈ J, g a
    = 0 := by
    intro C _ g hg a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_pow, map_natCast, hg, mul_zero]
  let ψ₀' : WittVector p k ⧸ J →+* B₀ := Ideal.Quotient.lift J ψ₀ (hJ ψ₀ hM')
  let cc' : WittVector p k ⧸ J →+* k := Ideal.Quotient.lift J (constantCoeff : WittVector p k →+*
    k) (hJ _ hMk)
  have hψ₀' : ψ₀'.comp (Ideal.Quotient.mk J) = ψ₀ := Ideal.Quotient.lift_comp_mk _ _ _
  have hcc' : cc'.comp (Ideal.Quotient.mk J) = constantCoeff := Ideal.Quotient.lift_comp_mk _ _ _

  have hker_cc' : ∀ w : WittVector p k ⧸ J, cc' w = 0 → ∃ v : WittVector p k ⧸ J, w = (p :
    WittVector p k ⧸ J) * v := by
    intro w hw
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    have hw' : constantCoeff w = 0 := by
      have : (cc'.comp (Ideal.Quotient.mk J)) w = 0 := hw
      rwa [hcc'] at this
    have : w ∈ RingHom.ker (constantCoeff : WittVector p k →+* k) := hw'
    rw [ker_constantCoeff, Ideal.mem_span_singleton'] at this
    obtain ⟨v, rfl⟩ := this
    exact ⟨Ideal.Quotient.mk J v, by rw [map_mul, map_natCast, mul_comm]⟩
  have hpM_WM : (p : WittVector p k ⧸ J) ^ M = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk J), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl

  let P : Subring (B × (WittVector p k ⧸ J)) :=
    RingHom.eqLocus (q.comp (RingHom.fst B (WittVector p k ⧸ J))) (ψ₀'.comp (RingHom.snd B
      (WittVector p k ⧸ J)))
  have hPmem : ∀ x : B × (WittVector p k ⧸ J), x ∈ P ↔ q x.1 = ψ₀' x.2 := fun x => Iff.rfl
  let prB : P →+* B := (RingHom.fst B (WittVector p k ⧸ J)).comp P.subtype
  let prW : P →+* WittVector p k ⧸ J := (RingHom.snd B (WittVector p k ⧸ J)).comp P.subtype
  have hPcomm : q.comp prB = ψ₀'.comp prW := by
    ext x
    exact (hPmem x.1).mp x.2
  let ρ : P →+* k := cc'.comp prW

  have hρs : Function.Surjective ρ := by
    intro a
    obtain ⟨w, hw⟩ := constantCoeff_surjective (p := p) (R := k) a
    obtain ⟨b, hb⟩ := hq (ψ₀ w)
    refine ⟨⟨(b, Ideal.Quotient.mk J w), ?_⟩, ?_⟩
    · show q b = ψ₀' (Ideal.Quotient.mk J w)
      rw [hb, ← hψ₀']
      rfl
    · show cc' (Ideal.Quotient.mk J w) = a
      rw [← hw, ← hcc']
      rfl

  have hρn : IsNilpotent (RingHom.ker ρ) := by

    have h1 : RingHom.ker ρ ≤ (Ideal.span {(p : WittVector p k ⧸ J)}).comap prW := by
      intro x hx
      obtain ⟨v, hv⟩ := hker_cc' (prW x) hx
      rw [Ideal.mem_comap, hv]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    have h2 : (RingHom.ker ρ) ^ M ≤ RingHom.ker prW := by
      refine (Ideal.pow_right_mono h1 M).trans ?_
      refine (Ideal.le_comap_pow _ M).trans ?_
      rw [Ideal.span_singleton_pow, hpM_WM, Ideal.span_singleton_zero]
      intro x hx
      exact hx
    have h3 : (RingHom.ker prW) ^ 2 = ⊥ := by
      rw [pow_two, ← le_bot_iff, Ideal.mul_le]
      intro x hx y hy
      rw [Ideal.mem_bot]
      have hx1 : q (prB x) = 0 := by
        have := congrArg (fun φ : P →+* B₀ => φ x) hPcomm
        simp only [RingHom.comp_apply] at this
        rw [this, RingHom.mem_ker.mp hx, map_zero]
      have hy1 : q (prB y) = 0 := by
        have := congrArg (fun φ : P →+* B₀ => φ y) hPcomm
        simp only [RingHom.comp_apply] at this
        rw [this, RingHom.mem_ker.mp hy, map_zero]
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · exact hsq _ _ hx1 hy1
      · show prW (x * y) = 0
        rw [map_mul, RingHom.mem_ker.mp hx, zero_mul]
    refine ⟨2 * M, ?_⟩
    rw [mul_comm, pow_mul]
    exact le_bot_iff.mp ((Ideal.pow_right_mono h2 2).trans h3.le)

  obtain ⟨F, hF, hFu⟩ := WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker p
    k P ρ hρs hρn
  have hWMu : ∀ G : WittVector p k →+* WittVector p k ⧸ J, cc'.comp G = constantCoeff → G =
    Ideal.Quotient.mk J := by
    have hs : Function.Surjective cc' := fun a => by
      obtain ⟨w, hw⟩ := constantCoeff_surjective (p := p) (R := k) a
      exact ⟨Ideal.Quotient.mk J w, by rw [← hw, ← hcc']; rfl⟩
    have hn : IsNilpotent (RingHom.ker cc') := by
      refine ⟨M, ?_⟩
      have h1 : RingHom.ker cc' ≤ Ideal.span {(p : WittVector p k ⧸ J)} := by
        intro w hw
        obtain ⟨v, hv⟩ := hker_cc' w hw
        rw [hv]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
      apply le_bot_iff.mp
      refine (Ideal.pow_right_mono h1 M).trans ?_
      rw [Ideal.span_singleton_pow, hpM_WM, Ideal.span_singleton_zero]
    obtain ⟨G₀, -, hG₀u⟩ :=
      WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker p k
        (WittVector p k ⧸ J) cc' hs hn
    intro G hG
    rw [hG₀u G hG, hG₀u (Ideal.Quotient.mk J) hcc']
  have hFW : prW.comp F = Ideal.Quotient.mk J := by
    apply hWMu
    rw [← RingHom.comp_assoc]
    exact hF

  refine ⟨prB.comp F, ?_, ?_⟩
  · show q.comp (prB.comp F) = ψ₀
    rw [← RingHom.comp_assoc, hPcomm, RingHom.comp_assoc, hFW, hψ₀']
  · intro ψ hψ

    let F' : WittVector p k →+* P := (RingHom.prod ψ (Ideal.Quotient.mk J)).codRestrict P (fun w =>
      by
      show q (ψ w) = ψ₀' (Ideal.Quotient.mk J w)
      rw [← RingHom.comp_apply, hψ, ← hψ₀']
      rfl)
    have hF' : ρ.comp F' = constantCoeff := by
      ext w
      show cc' (Ideal.Quotient.mk J w) = constantCoeff w
      rw [← hcc']
      rfl
    have : F' = F := hFu F' hF'
    rw [← this]
    rfl

end WittVector
