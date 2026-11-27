/-
Portions of this file are adapted from:

`Theorems/Thm_Subring_isMaximal_of_liesOver_adjoin_of_forall_not_isMaximal_valuationSubring.lean`,
`P2M/Sol/S_Subring_isMaximal_of_liesOver_adjoin_of_forall_not_isMaximal_valuationSubring.lean`,
`Theorems/Thm_ValuationSubring_eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing.lean`
and
`P2M/Sol/S_ValuationSubring_eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing.lean`
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

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.LocalSubring
import Mathlib.RingTheory.Localization.Submodule
import MathlibExt.RingTheory.Valuation.ValuationSubringNotField

@[expose] public section

open IsLocalRing

private theorem eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing
    {K : Type*} [Field K] (A : ValuationSubring K) [IsDiscreteValuationRing ↥A]
    (B : Subring K) (h : A.toSubring ≤ B) : B = A.toSubring ∨ B = ⊤ := by
  classical
  let B' : ValuationSubring K := ValuationSubring.ofLE A B h
  have hB' : (B' : ValuationSubring K).toSubring = B := rfl
  have hAB' : A ≤ B' := fun x hx => h hx
  set P : Ideal ↥A := A.idealOfLE B' hAB' with hP
  have hPB' : A.ofPrime P = B' := ValuationSubring.ofPrime_idealOfLE A B' hAB'
  by_cases hbot : P = ⊥
  · right
    rw [← hB', ← hPB']
    have : A.ofPrime P = ⊤ := by
      have : (⊥ : Ideal ↥A).IsPrime := Ideal.isPrime_bot
      have e : A.ofPrime P = A.ofPrime ⊥ := by congr 1
      rw [e]; exact ValuationSubring.ofPrime_bot A
    rw [this]; rfl
  · left
    rw [← hB', ← hPB']
    have hmax : P.IsMaximal := IsPrime.to_maximal_ideal hbot
    have hPm : P = IsLocalRing.maximalIdeal ↥A := IsLocalRing.eq_maximalIdeal hmax
    have : A.ofPrime P = A := by
      have e : A.ofPrime P = A.ofPrime (IsLocalRing.maximalIdeal ↥A) := by congr 1
      rw [e]; exact ValuationSubring.ofPrime_top A
    rw [this]



private theorem mem_ofPrime_of_mul_eq {F : Type*} [Field F] (A : Subring F) (P : Ideal A)
    [P.IsPrime] {x : F} (s t : A) (ht : t ∉ P) (h : x * (t : F) = (s : F)) :
    x ∈ (LocalSubring.ofPrime A P).toSubring := by
  simp only [LocalSubring.ofPrime, LocalSubring.range_toSubring]
  refine ⟨IsLocalization.mk' (Localization.AtPrime P) s (⟨t, ht⟩ : P.primeCompl), ?_⟩
  rw [IsLocalization.lift_mk'_spec]
  simp only [Subring.coe_subtype]
  rw [← h, mul_comm]

private theorem exists_mul_eq_of_mem_ofPrime {F : Type*} [Field F] (A : Subring F)
    (P : Ideal A) [P.IsPrime] {x : F} (hx : x ∈ (LocalSubring.ofPrime A P).toSubring) :
    ∃ s t : A, t ∉ P ∧ x * (t : F) = (s : F) := by
  simp only [LocalSubring.ofPrime, LocalSubring.range_toSubring] at hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
  refine ⟨s, t, t.2, ?_⟩
  have h := (IsLocalization.lift_mk'_spec (M := P.primeCompl) (S := Localization.AtPrime P)
    (g := A.subtype) (by simp [Ideal.primeCompl, not_imp_not]) s _ t).mp rfl
  simp only [Subring.coe_subtype] at h
  rw [h, mul_comm]

private theorem inv_notMem_ofPrime {F : Type*} [Field F] (A : Subring F) (P : Ideal A)
    [P.IsPrime] (p : A) (hp : p ∈ P) (hp0 : (p : F) ≠ 0) :
    (p : F)⁻¹ ∉ (LocalSubring.ofPrime A P).toSubring := fun hinv =>
  (IsLocalization.AtPrime.isUnit_to_map_iff (LocalSubring.ofPrime A P).toSubring P p).mp
    (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hp0))) hp

private theorem eq_bot_of_ofPrime_eq_top {F : Type*} [Field F] (A : Subring F) (P : Ideal A)
    [P.IsPrime] (h : (LocalSubring.ofPrime A P).toSubring = ⊤) : P = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  by_contra hp0
  have hp0' : (p : F) ≠ 0 := fun h0 => hp0 (by rw [Submodule.mem_bot]; exact Subtype.ext h0)
  exact inv_notMem_ofPrime A P p hp hp0' (h.symm ▸ Subring.mem_top ((p : F)⁻¹))

private theorem isNoetherianRing_of_presentation {F : Type*} [Field F] (A : Subring F)
    [IsNoetherianRing A] (P : Ideal A) [P.IsPrime] (V : ValuationSubring F)
    (hV : ∀ f : F, f ∈ V ↔ ∃ b c : A, c ∉ P ∧ f * (c : F) = (b : F)) : IsNoetherianRing ↥V := by
  have hVR : V.toSubring = (LocalSubring.ofPrime A P).toSubring := by
    ext f
    exact (hV f).trans ⟨fun ⟨b, c, hc, h⟩ => mem_ofPrime_of_mul_eq A P b c hc h,
      exists_mul_eq_of_mem_ofPrime A P⟩
  have : IsNoetherianRing (LocalSubring.ofPrime A P).toSubring :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  exact isNoetherianRing_of_ringEquiv _ (RingEquiv.subringCongr hVR).symm

private theorem isDVR_or_eq_top_of_presentation {F : Type*} [Field F] (A : Subring F)
    [IsNoetherianRing A] (P : Ideal A) [P.IsPrime] (V : ValuationSubring F)
    (hV : ∀ f : F, f ∈ V ↔ ∃ b c : A, c ∉ P ∧ f * (c : F) = (b : F)) :
    IsDiscreteValuationRing ↥V ∨ V = ⊤ := by
  by_cases hf : IsField ↥V
  · exact Or.inr (not_ne_iff.mp fun hV => ValuationSubring.not_isField_of_ne_top F hV hf)
  · have hN : IsNoetherianRing ↥V := isNoetherianRing_of_presentation A P V hV
    have : ValuationRing ↥V := inferInstance
    have htf := IsDiscreteValuationRing.TFAE (R := ↥V) hf
    exact Or.inl ((htf.out 1 2).mpr (inferInstance : ValuationRing ↥V))

private def inclB {F : Type*} [Field F] {A₀ : Type*} [CommRing A₀] [Algebra A₀ F] (O : Subring F) (B
  : Subalgebra A₀ F) :
    ↥B →+* ↥(Algebra.adjoin ↥O (B : Set F)) where
  toFun b := ⟨b, Algebra.subset_adjoin b.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] private theorem coe_inclB {F : Type*} [Field F] {A₀ : Type*} [CommRing A₀] [Algebra
  A₀ F] (O : Subring F) (B : Subalgebra A₀ F) (b : ↥B) :
    ((inclB O B b : ↥(Algebra.adjoin ↥O (B : Set F))) : F) = b := rfl

private theorem blockB
    {F : Type*} [Field F]
    (A₀ : Type*) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [Algebra A₀ F]
    (O : Subring F) [IsLocalRing ↥O] [IsNoetherianRing ↥O]
    (hAO : ∀ a : A₀, algebraMap A₀ F a ∈ O)
    (hAOloc : ∀ a : A₀, a ∈ maximalIdeal A₀ → (⟨algebraMap A₀ F a, hAO a⟩ : ↥O) ∈ maximalIdeal ↥O)
    (B : Subalgebra A₀ F) (hBfg : B.FG)
    (hcomp : ∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬
      𝔮.IsMaximal →
      ∃ V : ValuationSubring F,
        (∀ f : F, f ∈ V ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ f * (c : F) = (b : F)) ∧
        ¬ (O ≤ V.toSubring ∧ ∀ g : ↥O, g ∈ maximalIdeal ↥O → (g : F) ∈ V.nonunits))
    (ℜ : Ideal ↥(Algebra.adjoin ↥O (B : Set F))) [ℜ.IsPrime]
    (hℜ : ∀ g : ↥O, g ∈ maximalIdeal ↥O ↔ algebraMap ↥O ↥(Algebra.adjoin ↥O (B : Set F)) g ∈ ℜ)
    (h𝔮 : ¬ (ℜ.comap (inclB O B)).IsMaximal) : False := by
  classical
  have : Algebra.FiniteType A₀ ↥B := (Subalgebra.fg_iff_finiteType B).mp hBfg
  have : IsNoetherianRing ↥B := Algebra.FiniteType.isNoetherianRing A₀ ↥B
  set 𝔮 : Ideal ↥B := ℜ.comap (inclB O B) with h𝔮def
  have h𝔮p : 𝔮.IsPrime := Ideal.comap_isPrime _ ℜ
  have hle : Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, h𝔮def, Ideal.mem_comap]
    have h1 := (hℜ ⟨algebraMap A₀ F a, hAO a⟩).mp (hAOloc a ha)
    convert h1 using 1
    rfl
  obtain ⟨V, hV, hndom⟩ := hcomp 𝔮 h𝔮p hle h𝔮
  let R := (LocalSubring.ofPrime (Algebra.adjoin ↥O (B : Set F)).toSubring ℜ).toSubring
  have hVR : V.toSubring ≤ R := by
    intro f hf
    obtain ⟨b, c, hc, h⟩ := (hV f).mp hf
    exact mem_ofPrime_of_mul_eq (Algebra.adjoin ↥O (B : Set F)).toSubring ℜ (inclB O B b)
      (inclB O B c) hc (by simpa using h)
  have hOS : ∀ x : F, x ∈ O → x ∈ (Algebra.adjoin ↥O (B : Set F)) := fun x hx => by
    have := Subalgebra.algebraMap_mem (Algebra.adjoin ↥O (B : Set F)) (⟨x, hx⟩ : ↥O); exact this
  have hOR : O ≤ R := fun x hx =>
    LocalSubring.le_ofPrime (Algebra.adjoin ↥O (B : Set F)).toSubring ℜ (hOS x hx)
  have hmR : ∀ g : ↥O, g ∈ maximalIdeal ↥O → (⟨(g : F), hOS g g.2⟩ : ↥(Algebra.adjoin ↥O (B : Set
    F))) ∈ ℜ := by
    intro g hg
    exact (hℜ g).mp hg
  rcases @isDVR_or_eq_top_of_presentation F _ B.toSubring ‹IsNoetherianRing ↥B› 𝔮 h𝔮p V hV with
    hDVR | hVtop
  · have := hDVR
    rcases eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing V R hVR with hRV | hRtop
    · apply hndom
      refine ⟨fun x hx => hRV ▸ hOR hx, fun g hg => ?_⟩
      rw [ValuationSubring.mem_nonunits_iff]
      have hgV : (g : F) ∈ V := by have := hOR g.2; rw [hRV] at this; exact this
      rcases eq_or_ne (g : F) 0 with h0 | h0
      · rw [h0, map_zero]; exact zero_lt_one
      · apply lt_of_le_of_ne ((V.valuation_le_one_iff _).mpr hgV)
        intro h1
        have hinv : (g : F)⁻¹ ∈ V := by apply V.mem_of_valuation_le_one; rw [map_inv₀, h1, inv_one]
        have hinvR : (g : F)⁻¹ ∈ R := hVR hinv
        exact inv_notMem_ofPrime (Algebra.adjoin ↥O (B : Set F)).toSubring ℜ ⟨(g : F), hOS g g.2⟩
          (hmR g hg) h0 hinvR
    · have hℜbot : ℜ = ⊥ :=
        eq_bot_of_ofPrime_eq_top (Algebra.adjoin ↥O (B : Set F)).toSubring ℜ hRtop
      have h𝔮bot : 𝔮 = ⊥ := by
        rw [h𝔮def, hℜbot, Ideal.comap_bot_of_injective]
        intro x y hxy; exact Subtype.ext (congrArg (fun w : ↥(Algebra.adjoin ↥O (B : Set F)) => (w :
          F)) hxy)
      have hVtop : V = ⊤ := by
        ext f
        refine ⟨fun _ => ValuationSubring.mem_top f, fun _ => ?_⟩
        rcases V.mem_or_inv_mem f with hf | hf
        · exact hf
        rcases eq_or_ne f 0 with h0 | h0
        · rw [h0]; exact zero_mem V
        obtain ⟨b, c, hc, h⟩ := (hV _).mp hf
        have hb : b ∉ 𝔮 := by
          rw [h𝔮bot]; intro hb0
          rw [Submodule.mem_bot] at hb0
          rw [hb0] at h; push_cast at h
          exact hc (by rw [h𝔮bot, Submodule.mem_bot]; exact Subtype.ext (by
            have := mul_eq_zero.mp h; rcases this with h1 | h1
            · exact absurd h1 (inv_ne_zero h0)
            · exact h1))
        exact (hV f).mpr ⟨c, b, hb, by rw [← h]; field_simp⟩
      apply hndom
      refine ⟨fun x _ => hVtop ▸ ValuationSubring.mem_top x, fun g hg => ?_⟩
      have : (⟨(g : F), hOS g g.2⟩ : ↥(Algebra.adjoin ↥O (B : Set F))) ∈ ℜ := hmR g hg
      rw [hℜbot, Submodule.mem_bot] at this
      have hg0 : (g : F) = 0 := congrArg (fun w : ↥(Algebra.adjoin ↥O (B : Set F)) => (w : F)) this
      rw [hg0, ValuationSubring.mem_nonunits_iff, map_zero]; exact zero_lt_one
  · apply hndom
    refine ⟨fun x _ => hVtop ▸ ValuationSubring.mem_top x, fun g hg => ?_⟩
    by_contra hgn
    have h0 : (g : F) ≠ 0 := by
      intro h0; apply hgn; rw [h0, ValuationSubring.mem_nonunits_iff, map_zero]; exact zero_lt_one
    have hinvR : (g : F)⁻¹ ∈ R := hVR (hVtop ▸ ValuationSubring.mem_top _)
    exact inv_notMem_ofPrime (Algebra.adjoin ↥O (B : Set F)).toSubring ℜ ⟨(g : F), hOS g g.2⟩
      (hmR g hg) h0 hinvR


/-- Maximality of a prime of `O[B]` lying over the maximal ideal of `O`.

Let `A₀` be a discrete valuation ring and `F` a field with an `A₀`-algebra structure. The
structure map `A₀ → F` need not be injective (it may factor through the residue field of `A₀`),
so `F` need not be the fraction field of `A₀`. Let `O` be a local Noetherian subring of `F` that
contains the image of `A₀`, with the induced map `A₀ → O` sending the maximal ideal of `A₀` into
the maximal ideal of `O`. Let `B` be a finitely generated `A₀`-subalgebra of `F`. Suppose that
every prime `𝔮` of `B` that contains the image of the maximal ideal of `A₀` and is not maximal
has its localization, the set of `f ∈ F` with `f * c = b` for some `b, c ∈ B` with `c ∉ 𝔮`, equal
to a valuation subring of `F` that does not dominate `O`. Then every prime of `O[B]`, the
`O`-subalgebra of `F` generated by `B`, whose contraction to `O` is the maximal ideal of `O` is
maximal. -/
public theorem Subring.isMaximal_of_liesOver_adjoin_of_forall_not_isMaximal_valuationSubring
    {F : Type*} [Field F]
    (A₀ : Type*) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [Algebra A₀ F]
    (O : Subring F) [IsLocalRing ↥O] [IsNoetherianRing ↥O]
    (hAO : ∀ a : A₀, algebraMap A₀ F a ∈ O)
    (hAOloc : ∀ a : A₀, a ∈ maximalIdeal A₀ → (⟨algebraMap A₀ F a, hAO a⟩ : ↥O) ∈ maximalIdeal ↥O)
    (B : Subalgebra A₀ F) (hBfg : B.FG)
    (hcomp : ∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬
      𝔮.IsMaximal →
      ∃ V : ValuationSubring F,
        (∀ f : F, f ∈ V ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ f * (c : F) = (b : F)) ∧
        ¬ (O ≤ V.toSubring ∧ ∀ g : ↥O, g ∈ maximalIdeal ↥O → (g : F) ∈ V.nonunits))
    (ℜ : Ideal ↥(Algebra.adjoin ↥O (B : Set F))) [ℜ.IsPrime]
    (hℜ : ∀ g : ↥O, g ∈ maximalIdeal ↥O ↔ algebraMap ↥O ↥(Algebra.adjoin ↥O (B : Set F)) g ∈ ℜ) :
    ℜ.IsMaximal := by
  classical
  have hBS : ∀ b : ↥B, (b : F) ∈ Algebra.adjoin ↥O (B : Set F) := fun b => Algebra.subset_adjoin b.2
  let iB : ↥B →+* ↥(Algebra.adjoin ↥O (B : Set F)) :=
    { toFun := fun b => ⟨b, hBS b⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hiB : ∀ b : ↥B, ((iB b : ↥(Algebra.adjoin ↥O (B : Set F))) : F) = b := fun b => rfl
  set 𝔮 : Ideal ↥B := ℜ.comap iB with h𝔮
  have h𝔮p : 𝔮.IsPrime := Ideal.comap_isPrime iB ℜ
  let c : A₀ →+* ↥O := (algebraMap A₀ F).codRestrict O hAO
  have hc : ∀ a : A₀, ((c a : ↥O) : F) = algebraMap A₀ F a := fun a => rfl
  have hconst : ∀ a : A₀, iB (algebraMap A₀ ↥B a) = algebraMap ↥O ↥(Algebra.adjoin ↥O (B : Set F))
    (c a) := by
    intro a; apply Subtype.ext
    rw [hiB, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]
    rfl
  have h𝔪𝔮 : Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change iB (algebraMap A₀ ↥B a) ∈ ℜ
    rw [hconst]
    exact (hℜ _).mp (hAOloc a ha)
  by_cases hmax : 𝔮.IsMaximal
  · have : Algebra.FiniteType A₀ ↥B := (Subalgebra.fg_iff_finiteType B).mp hBfg
    let : Field (↥B ⧸ 𝔮) := Ideal.Quotient.field 𝔮
    let θ : A₀ ⧸ maximalIdeal A₀ →+* ↥B ⧸ 𝔮 :=
      Ideal.Quotient.lift (maximalIdeal A₀) ((Ideal.Quotient.mk 𝔮).comp (algebraMap A₀ ↥B)) (by
        intro a ha
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact h𝔪𝔮 (Ideal.mem_map_of_mem _ ha))
    let algκ₀ : Algebra (A₀ ⧸ maximalIdeal A₀) (↥B ⧸ 𝔮) := θ.toAlgebra
    let : Field (A₀ ⧸ maximalIdeal A₀) := Ideal.Quotient.field _
    have : IsScalarTower A₀ (A₀ ⧸ maximalIdeal A₀) (↥B ⧸ 𝔮) :=
      IsScalarTower.of_algebraMap_eq fun a => rfl
    have : Algebra.FiniteType (A₀ ⧸ maximalIdeal A₀) (↥B ⧸ 𝔮) :=
      Algebra.FiniteType.of_restrictScalars_finiteType A₀ (A₀ ⧸ maximalIdeal A₀) (↥B ⧸ 𝔮)
    have : Module.Finite (A₀ ⧸ maximalIdeal A₀) (↥B ⧸ 𝔮) := finite_of_finite_type_of_isJacobsonRing
      _ _
    have : Algebra.IsIntegral (A₀ ⧸ maximalIdeal A₀) (↥B ⧸ 𝔮) := Algebra.IsIntegral.of_finite _ _
    have : Algebra.IsIntegral A₀ (A₀ ⧸ maximalIdeal A₀) :=
      Algebra.IsIntegral.of_surjective (Algebra.ofId A₀ (A₀ ⧸ maximalIdeal A₀))
        Ideal.Quotient.mk_surjective
    have hintB : Algebra.IsIntegral A₀ (↥B ⧸ 𝔮) := Algebra.IsIntegral.trans (A₀ ⧸ maximalIdeal A₀)
    let mkℜ := Ideal.Quotient.mk ℜ
    let φ : ↥O →+* ↥(Algebra.adjoin ↥O (B : Set F)) ⧸ ℜ := mkℜ.comp (algebraMap ↥O ↥(Algebra.adjoin
      ↥O (B : Set F)))
    have hφker : ∀ g : ↥O, g ∈ maximalIdeal ↥O → φ g = 0 := fun g hg => by
      change mkℜ _ = 0; rw [Ideal.Quotient.eq_zero_iff_mem]; exact (hℜ g).mp hg
    let ψ : ResidueField ↥O →+* ↥(Algebra.adjoin ↥O (B : Set F)) ⧸ ℜ :=
      Ideal.Quotient.lift (maximalIdeal ↥O) φ hφker
    let algκ : Algebra (ResidueField ↥O) (↥(Algebra.adjoin ↥O (B : Set F)) ⧸ ℜ) :=
      @RingHom.toAlgebra (ResidueField ↥O) (↥(Algebra.adjoin ↥O (B : Set F)) ⧸ ℜ) _
        (Ideal.Quotient.commRing ℜ).toCommSemiring ψ
    have hint : ∀ z : ↥(Algebra.adjoin ↥O (B : Set F)) ⧸ ℜ, IsIntegral (ResidueField ↥O) z := by
      intro z
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨s, hs⟩ := s
      induction hs using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨P, hPm, hP⟩ := hintB.isIntegral (Ideal.Quotient.mk 𝔮 ⟨x, hx⟩)
        have hP𝔮 : Polynomial.eval₂ (algebraMap A₀ ↥B) ⟨x, hx⟩ P ∈ 𝔮 := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]
          exact hP
        refine ⟨P.map ((IsLocalRing.residue ↥O).comp c), hPm.map _, ?_⟩
        rw [Polynomial.eval₂_map]
        have hcomp : (algebraMap (ResidueField ↥O) (↥(Algebra.adjoin ↥O (B : Set F)) ⧸ ℜ)).comp
            ((IsLocalRing.residue ↥O).comp c) = mkℜ.comp (iB.comp (algebraMap A₀ ↥B)) := by
          ext a
          change ψ (IsLocalRing.residue ↥O (c a)) = mkℜ (iB (algebraMap A₀ ↥B a))
          rw [hconst]; rfl
        rw [hcomp]
        have : mkℜ (iB ⟨x, hx⟩) = Ideal.Quotient.mk ℜ ⟨x, Algebra.subset_adjoin hx⟩ := rfl
        rw [← this, ← Polynomial.hom_eval₂, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
        exact hP𝔮
      | algebraMap r =>
        have : Ideal.Quotient.mk ℜ ⟨algebraMap ↥O F r, Subalgebra.algebraMap_mem _ r⟩ =
            algebraMap (ResidueField ↥O) _ (IsLocalRing.residue ↥O r) := rfl
        rw [this]; exact isIntegral_algebraMap
      | add x y hx hy ihx ihy =>
        have : Ideal.Quotient.mk ℜ ⟨x + y, Subalgebra.add_mem _ hx hy⟩ =
            Ideal.Quotient.mk ℜ ⟨x, hx⟩ + Ideal.Quotient.mk ℜ ⟨y, hy⟩ := rfl
        rw [this]; exact ihx.add ihy
      | mul x y hx hy ihx ihy =>
        have : Ideal.Quotient.mk ℜ ⟨x * y, Subalgebra.mul_mem _ hx hy⟩ =
            Ideal.Quotient.mk ℜ ⟨x, hx⟩ * Ideal.Quotient.mk ℜ ⟨y, hy⟩ := rfl
        rw [this]; exact ihx.mul ihy
    have : Algebra.IsIntegral (ResidueField ↥O) (↥(Algebra.adjoin ↥O (B : Set F)) ⧸ ℜ) := ⟨hint⟩
    have : IsDomain (↥(Algebra.adjoin ↥O (B : Set F)) ⧸ ℜ) := Ideal.Quotient.isDomain ℜ
    have hF := isField_of_isIntegral_of_isField' (R := ResidueField ↥O)
      (S := ↥(Algebra.adjoin ↥O (B : Set F)) ⧸ ℜ) (Field.toIsField (ResidueField ↥O))
    exact Ideal.Quotient.maximal_of_isField ℜ ⟨hF.exists_pair_ne, hF.mul_comm, hF.mul_inv_cancel⟩
  · exfalso
    exact blockB A₀ O hAO hAOloc B hBfg hcomp ℜ hℜ (by exact hmax)
