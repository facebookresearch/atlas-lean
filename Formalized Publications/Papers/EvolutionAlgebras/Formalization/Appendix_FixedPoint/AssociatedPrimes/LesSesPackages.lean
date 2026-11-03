/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.RingTheory.Regular.Category
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

/-!
# LES wrappers + SES packages for the GapBase finite-dimensional close (D3)

Two contravariant-`Ext` long-exact-sequence wrappers over mathlib's
`Ext.contravariant_sequence_exact₁/₂`, plus the two short-exact-sequence
packages consumed downstream: the `x`-multiplication SES (on the Rees
`ModuleCat.smulShortComplex` pattern) and the submodule SES
`0 → ↧K → ↧M → ↧(M ⧸ K) → 0`.

Consumers: PrimeFiltrationDevissage takes wrapper A (devissage-exact) + the submodule SES;
IschebeckAssembly takes wrapper B (`x`-surjectivity) + the `x`-SES.

`[IsAlgClosed]`: not required and not used — nothing in this file needs
algebraic closedness (wrapper A is over a general abelian category and
the SES packages over a general commutative ring).

Wall-1: `N ⧸ xN` / `M ⧸ K` appear only as objects of short complexes and
the first variable of `Ext`; no prime is descended through a quotient.
Wall-2: zero height/grade content — only LES exactness + SES packaging.
-/

namespace AssociatedPrimes.LesSesPackages

open CategoryTheory Abelian

universe w v u

/-! ## Wrapper A — devissage-exact (for PrimeFiltrationDevissage) -/

/-- Wrapper A (devissage-exact): in a short exact sequence `S`, vanishing
    of `Ext` at both ends forces vanishing in the middle. Uses
    `Ext.contravariant_sequence_exact₂` only. -/
theorem subsingleton_ext_middle_of_subsingleton_ends
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C) (n : ℕ)
    (h₃ : Subsingleton (Ext S.X₃ Y n))
    (h₁ : Subsingleton (Ext S.X₁ Y n)) :
    Subsingleton (Ext S.X₂ Y n) := by
  suffices h0 : ∀ z : Ext S.X₂ Y n, z = 0 from
    ⟨fun x y => (h0 x).trans (h0 y).symm⟩
  intro z
  have hfz : (Ext.mk₀ S.f).comp z (zero_add n) = 0 := h₁.elim _ _
  obtain ⟨w, hw⟩ := Ext.contravariant_sequence_exact₂ hS Y z hfz
  have hw0 : w = 0 := h₃.elim _ _
  rw [hw0, Ext.comp_zero] at hw
  exact hw.symm

/-! ## Wrapper B — x-surjectivity (for IschebeckAssembly) -/

variable {R : Type v} [CommRing R]

/-- Wrapper B (`x`-surjectivity, specialized to the `x`-SES where
    `S.f = x • 𝟙 N` holds by `rfl`): both vanishings of the quotient
    `N ⧸ xN` (at degrees `n₀` and `n₁ = 1 + n₀`) make precomposition
    with `x • 𝟙 N` bijective on `Ext N Y n₀`. Surjectivity via
    `Ext.contravariant_sequence_exact₁`, injectivity via
    `Ext.contravariant_sequence_exact₂`. -/
theorem bijective_x_precomp_of_subsingleton_quot
    [Small.{v} R] {N : ModuleCat.{v} R} {x : R}
    (reg : IsSMulRegular (N : Type v) x)
    (Y : ModuleCat.{v} R) {n₀ n₁ : ℕ} (h : 1 + n₀ = n₁)
    (h₃ : Subsingleton (Ext (ModuleCat.smulShortComplex N x).X₃ Y n₀))
    (h₃' : Subsingleton (Ext (ModuleCat.smulShortComplex N x).X₃ Y n₁)) :
    Function.Bijective
      (fun e : Ext N Y n₀ => (Ext.mk₀ (x • 𝟙 N)).comp e (zero_add n₀)) := by
  have hS : (ModuleCat.smulShortComplex N x).ShortExact :=
    reg.smulShortComplex_shortExact
  have hker : ∀ z : Ext N Y n₀,
      (Ext.mk₀ (x • 𝟙 N)).comp z (zero_add n₀) = 0 → z = 0 := by
    intro z hz
    have hz' : (Ext.mk₀ (ModuleCat.smulShortComplex N x).f).comp z
        (zero_add n₀) = 0 := by
      rw [ModuleCat.smulShortComplex_f_eq_smul_id]
      exact hz
    obtain ⟨w, hw⟩ := Ext.contravariant_sequence_exact₂ hS Y z hz'
    have hw0 : w = 0 := h₃.elim _ _
    rw [hw0, Ext.comp_zero] at hw
    exact hw.symm
  constructor
  · intro a b hab
    have hab' : (Ext.mk₀ (x • 𝟙 N)).comp a (zero_add n₀)
        = (Ext.mk₀ (x • 𝟙 N)).comp b (zero_add n₀) := hab
    have hsub : a - b = 0 := by
      apply hker
      show (Ext.mk₀ (x • 𝟙 N)).comp (a - b) (zero_add n₀) = 0
      rw [sub_eq_add_neg, Ext.comp_add, Ext.comp_neg, hab', add_neg_cancel]
    exact sub_eq_zero.mp hsub
  · intro y
    have hδ : hS.extClass.comp y h = 0 := h₃'.elim _ _
    obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁ hS Y y h hδ
    refine ⟨x₂, ?_⟩
    change (Ext.mk₀ (x • 𝟙 N)).comp x₂ (zero_add n₀) = y
    rw [← ModuleCat.smulShortComplex_f_eq_smul_id]
    exact hx₂

/-! ## SES packages -/

/-- The submodule SES `0 → ↧K → ↧M → ↧(M ⧸ K) → 0`. -/
noncomputable abbrev submoduleSES {M : Type v} [AddCommGroup M] [Module R M]
    (K : Submodule R M) : ShortComplex (ModuleCat.{v} R) :=
  ModuleCat.shortComplexOfCompEqZero K.subtype (Submodule.mkQ K) (by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero K).mpr x.2)

/-- Exactness of the submodule SES. -/
theorem submoduleSES_shortExact {M : Type v} [AddCommGroup M] [Module R M]
    (K : Submodule R M) : (submoduleSES K).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · change Function.Exact ⇑K.subtype ⇑(Submodule.mkQ K)
    intro x
    constructor
    · intro hx
      rw [Submodule.mkQ_apply] at hx
      have hxmem : x ∈ K := (Submodule.Quotient.mk_eq_zero K).mp hx
      exact ⟨⟨x, hxmem⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero K).mpr a.2
  · change Function.Injective ⇑K.subtype
    exact K.injective_subtype
  · change Function.Surjective ⇑(Submodule.mkQ K)
    exact Submodule.mkQ_surjective K

end AssociatedPrimes.LesSesPackages
