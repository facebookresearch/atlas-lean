/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_finite_integralClosure_adjoin_singleton_of_isAlgClosed.lean`
and
`P2M/Sol/S_Algebra_finite_integralClosure_adjoin_singleton_of_isAlgClosed.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.RingTheory.Adjoin.Polynomial.Transcendental
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

@[expose] public section

open Polynomial IntermediateField

open scoped IntermediateField.algebraAdjoinAdjoin Pointwise

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

private theorem isNoetherianRing_adjoin (y : F) :
    IsNoetherianRing (Algebra.adjoin k ({y} : Set F)) :=
  isNoetherianRing_of_fg ⟨{y}, by rw [Finset.coe_singleton]⟩

private theorem fg_of_image_le {A A' : Subalgebra k F} (φ : F →+* F)
    (hφ : Function.Injective φ)
    (hlift : ∀ a' ∈ A', ∃ a ∈ A, φ a = a') [IsNoetherianRing A']
    (M' : Submodule A' F) (hM' : M'.FG) (B : Submodule A F)
    (hB : ∀ b ∈ B, φ b ∈ M') :
    B.FG := by
  classical
  have : IsNoetherian A' M' := isNoetherian_of_fg_of_noetherian M' hM'
  let P : Submodule A' F :=
    { carrier := φ '' (B : Set F)
      add_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
        exact ⟨b + c, add_mem hb hc, map_add φ b c⟩
      zero_mem' := ⟨0, zero_mem _, map_zero φ⟩
      smul_mem' := by
        rintro a' _ ⟨b, hb, rfl⟩
        obtain ⟨a, ha, hφa⟩ := hlift a' a'.2
        refine ⟨(⟨a, ha⟩ : A) • b, B.smul_mem _ hb, ?_⟩
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        change φ a * φ b = (a' : F) * φ b
        rw [hφa] }
  have hPM' : P ≤ M' := by
    rintro _ ⟨b, hb, rfl⟩
    exact hB b hb
  have hPfg : P.FG := (isNoetherian_submodule.mp inferInstance) P hPM'
  obtain ⟨G, hG⟩ := hPfg
  have hGP : ∀ g ∈ G, ∃ b ∈ B, φ b = g := by
    intro g hg
    have : g ∈ P := hG ▸ Submodule.subset_span hg
    exact this
  choose t ht htφ using hGP
  let T : Finset F := G.attach.image fun g => t g.1 g.2
  have hTB : (T : Set F) ⊆ B := by
    intro y hy
    rw [Finset.coe_image] at hy
    obtain ⟨g, _, rfl⟩ := hy
    exact ht g.1 g.2
  have hkey : ∀ y ∈ P, ∃ c ∈ Submodule.span A (T : Set F), φ c = y := by
    intro y hy
    rw [← hG] at hy
    induction hy using Submodule.span_induction with
    | mem g hg =>
      refine ⟨t g hg, Submodule.subset_span ?_, htφ g hg⟩
      rw [Finset.mem_coe]
      exact Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩
    | zero => exact ⟨0, zero_mem _, map_zero φ⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨d, hd, rfl⟩ := hz
      exact ⟨c + d, add_mem hc hd, map_add φ c d⟩
    | smul a' y _ hy =>
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨a, ha, hφa⟩ := hlift a' a'.2
      refine ⟨(⟨a, ha⟩ : A) • c, Submodule.smul_mem _ _ hc, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      change φ a * φ c = (a' : F) * φ c
      rw [hφa]
  refine ⟨T, le_antisymm (Submodule.span_le.mpr hTB) ?_⟩
  intro b hb
  obtain ⟨c, hc, hφc⟩ := hkey (φ b) ⟨b, hb, rfl⟩
  rw [← hφ hφc]
  exact hc

section WithX

variable (x : F)

local notation3 "𝓐" => Algebra.adjoin k ({x} : Set F)
local notation3 "𝓚" => IntermediateField.adjoin k ({x} : Set F)

private theorem fg_toSubmodule_integralClosure_of_isSeparable
    (hx : Transcendental k x)
    (E : IntermediateField 𝓚 F) [FiniteDimensional 𝓚 E]
    [Algebra.IsSeparable 𝓚 E] :
    (Subalgebra.toSubmodule (integralClosure 𝓐 E)).FG := by
  have : UniqueFactorizationMonoid 𝓐 := hx.uniqueFactorizationMonoid_adjoin
  have : IsIntegrallyClosed 𝓐 := inferInstance
  have : IsNoetherianRing 𝓐 := isNoetherianRing_adjoin x
  let : Algebra 𝓐 (integralClosure 𝓐 E) := Subalgebra.algebra (integralClosure 𝓐 E)
  let : SMul 𝓐 (integralClosure 𝓐 E) := Algebra.toSMul
  have : IsScalarTower 𝓐 (integralClosure 𝓐 E) E :=
    IsScalarTower.subalgebra' 𝓐 E E (integralClosure 𝓐 E)
  exact Module.Finite.iff_fg.mp (IsIntegralClosure.finite 𝓐 𝓚 E (integralClosure 𝓐 E))

private theorem exists_fg_of_isSeparable (hx : Transcendental k x)
    (E : IntermediateField 𝓚 F) [FiniteDimensional 𝓚 E]
    [Algebra.IsSeparable 𝓚 E] :
    ∃ N : Submodule 𝓐 F, N.FG ∧ ∀ f : F, f ∈ E → IsIntegral 𝓐 f → f ∈ N := by
  have h1 := fg_toSubmodule_integralClosure_of_isSeparable x hx E
  let ψ : E →ₗ[𝓐] F := ((IntermediateField.val E).restrictScalars 𝓐).toLinearMap
  refine ⟨(Subalgebra.toSubmodule (integralClosure 𝓐 E)).map ψ, h1.map _, ?_⟩
  intro f hf hint
  refine ⟨⟨f, hf⟩, ?_, rfl⟩
  change IsIntegral 𝓐 (⟨f, hf⟩ : E)
  have : ((IntermediateField.val E).restrictScalars 𝓐) ⟨f, hf⟩ = f := rfl
  rw [← this] at hint
  exact (isIntegral_algHom_iff _ Subtype.val_injective).mp hint

private theorem exists_pow_mem_separableClosure [FiniteDimensional 𝓚 F] :
    ∃ p e : ℕ, ExpChar F p ∧ ∀ f : F, f ^ p ^ e ∈ separableClosure 𝓚 F := by
  refine ⟨ringExpChar F,
    IsPurelyInseparable.exponent (↥(separableClosure 𝓚 F)) (L := F),
    inferInstance, fun f => ?_⟩
  obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def'
    (K := ↥(separableClosure 𝓚 F)) (L := F) (ringExpChar F) f
  rw [← hy]
  exact y.2

private theorem exists_pow_eq_of_mem_adjoin_pow [IsAlgClosed k] (p e : ℕ)
    [ExpChar F p] {a' : F}
    (ha' : a' ∈ Algebra.adjoin k ({x ^ p ^ e} : Set F)) :
    ∃ a ∈ 𝓐, a ^ p ^ e = a' := by
  induction ha' using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨x, Algebra.self_mem_adjoin_singleton k x, hy.symm⟩
  | algebraMap c =>
    obtain ⟨d, rfl⟩ := IsAlgClosed.exists_pow_nat_eq c (pow_pos (expChar_pos F p) e)
    exact ⟨algebraMap k F d, Subalgebra.algebraMap_mem _ d, by rw [map_pow]⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, rfl⟩ := hz
    exact ⟨a + b, add_mem ha hb, add_pow_expChar_pow a b p e⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, rfl⟩ := hz
    exact ⟨a * b, mul_mem ha hb, mul_pow a b _⟩

private theorem exists_fg_adjoin_pow_of_fg (q : ℕ) (hq : 0 < q)
    (N : Submodule 𝓐 F) (hN : N.FG) :
    ∃ M' : Submodule (Algebra.adjoin k ({x ^ q} : Set F)) F,
      M'.FG ∧ ∀ f ∈ N, f ∈ M' := by
  have hxq : x ^ q ∈ Algebra.adjoin k ({x ^ q} : Set F) :=
    Algebra.self_mem_adjoin_singleton k _
  have hxint : IsIntegral (Algebra.adjoin k ({x ^ q} : Set F)) x :=
    IsIntegral.of_pow hq
      (isIntegral_algebraMap (A := F)
        (x := (⟨x ^ q, hxq⟩ : Algebra.adjoin k ({x ^ q} : Set F))))
  obtain ⟨t, ht⟩ := hxint.fg_adjoin_singleton
  have hAA₁ : ∀ a ∈ 𝓐, a ∈ Algebra.adjoin
      (Algebra.adjoin k ({x ^ q} : Set F)) ({x} : Set F) := by
    intro a ha
    have h1 : Algebra.adjoin k ({x} : Set F) ≤
        Algebra.adjoin k ({x ^ q} ∪ {x} : Set F) :=
      Algebra.adjoin_mono Set.subset_union_right
    have h2 := Algebra.adjoin_union_eq_adjoin_adjoin k ({x ^ q} : Set F) ({x} : Set F)
    have := h1 ha
    rw [h2] at this
    exact this
  obtain ⟨S, hS⟩ := hN
  refine ⟨Submodule.span _ ((t : Set F) • (S : Set F)),
    Submodule.fg_span (Set.Finite.smul t.finite_toSet S.finite_toSet), ?_⟩
  have hstable : ∀ a ∈ Algebra.adjoin (Algebra.adjoin k ({x ^ q} : Set F))
        ({x} : Set F),
      ∀ m ∈ Submodule.span (Algebra.adjoin k ({x ^ q} : Set F))
        ((t : Set F) • (S : Set F)),
      a * m ∈ Submodule.span (Algebra.adjoin k ({x ^ q} : Set F))
        ((t : Set F) • (S : Set F)) := by
    intro a ha m hm
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨ti, hti, sj, hsj, rfl⟩ := Set.mem_smul.mp hy
      have hti' : ti ∈ Algebra.adjoin (Algebra.adjoin k ({x ^ q} : Set F))
          ({x} : Set F) := by
        rw [← Subalgebra.mem_toSubmodule, ← ht]
        exact Submodule.subset_span hti
      have hat : a * ti ∈ Submodule.span (Algebra.adjoin k ({x ^ q} : Set F))
          (t : Set F) := by
        rw [ht, Subalgebra.mem_toSubmodule]
        exact mul_mem ha hti'
      have hassoc : a * ti • sj = (a * ti) • sj := by
        simp only [smul_eq_mul, mul_assoc]
      rw [hassoc]
      exact Submodule.smul_mem_span_smul_of_mem hat hsj
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul a' y _ hy =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ hy
  intro f hf
  rw [← hS] at hf
  induction hf using Submodule.span_induction with
  | mem s hs =>
    have h1 : (1 : F) ∈ Submodule.span (Algebra.adjoin k ({x ^ q} : Set F))
        (t : Set F) := by
      rw [ht, Subalgebra.mem_toSubmodule]; exact one_mem _
    have := Submodule.smul_mem_span_smul_of_mem h1 hs
    rwa [one_smul] at this
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul a y _ hy =>
    rw [Algebra.smul_def]
    exact hstable _ (hAA₁ _ a.2) _ hy

private theorem fg_toSubmodule_integralClosure [IsAlgClosed k]
    (hx : Transcendental k x) (hfd : FiniteDimensional 𝓚 F) :
    (Subalgebra.toSubmodule (integralClosure 𝓐 F)).FG := by
  obtain ⟨N, hNfg, hN⟩ := exists_fg_of_isSeparable x hx (separableClosure 𝓚 F)
  obtain ⟨p, e, hp, hpe⟩ := exists_pow_mem_separableClosure (k := k) x
  have := hp
  have hq0 : 0 < p ^ e := pow_pos (expChar_pos F p) e
  let φ : F →+* F := iterateFrobenius F p e
  have hφ : ∀ f : F, φ f = f ^ p ^ e := fun f => iterateFrobenius_def p e f
  obtain ⟨M', hM'fg, hNM'⟩ := exists_fg_adjoin_pow_of_fg x (p ^ e) hq0 N hNfg
  have : IsNoetherianRing (Algebra.adjoin k ({x ^ p ^ e} : Set F)) :=
    isNoetherianRing_adjoin (x ^ p ^ e)
  refine fg_of_image_le φ φ.injective ?_ M' hM'fg _ ?_
  · intro a' ha'
    obtain ⟨a, ha, h⟩ := exists_pow_eq_of_mem_adjoin_pow x p e ha'
    exact ⟨a, ha, by rw [hφ, h]⟩
  · intro b hb
    refine hNM' _ (hN _ ?_ ?_)
    · rw [hφ]; exact hpe b
    · rw [hφ]; exact IsIntegral.pow hb _

end WithX

/-- The integral closure of `k[x]` in a finite extension of `k(x)` is finite
over `k[x]`, for an algebraically closed field `k` and a transcendental
element `x`. -/
public theorem Algebra.finite_integralClosure_adjoin_singleton_of_isAlgClosed
    [IsAlgClosed k] (x : F) (hx : Transcendental k x)
    (hfd : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    Module.Finite (Algebra.adjoin k ({x} : Set F))
      (integralClosure (Algebra.adjoin k ({x} : Set F)) F) :=
  Module.Finite.iff_fg.mpr (fg_toSubmodule_integralClosure x hx hfd)
