/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.lean` and
`P2M/Sol/S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.lean`
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

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Noetherian.Orzech
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# The Krull–Akizuki theorem

Let `A` be a Noetherian domain of Krull dimension at most one, `K` its
fraction field, and `L` a finite extension of `K`. Then every
`A`-subalgebra `B` of `L` is Noetherian of Krull dimension at most one,
and every nonzero quotient `B ⧸ J` has finite length as an `A`-module.
The proof bounds lengths of quotients of finite modules by powers of a
nonzero element, using the Artinianity of `A ⧸ (d)`.
-/

@[expose] public section

namespace KrullAkizukiAux

open Module

private def smulRange {A : Type*} [CommRing A] (a : A) (M : Type*) [AddCommGroup M] [Module A M] :
    Submodule A M :=
  LinearMap.range (DistribSMul.toLinearMap A M a)

private theorem mem_smulRange_iff {A : Type*} [CommRing A] {a : A} {M : Type*} [AddCommGroup M]
    [Module A M] (x : M) : x ∈ smulRange a M ↔ ∃ y : M, a • y = x := by
  simp [smulRange, DistribSMul.toLinearMap_apply]

private theorem smul_mem_smulRange {A : Type*} [CommRing A] (a : A) {M : Type*} [AddCommGroup M]
    [Module A M] (x : M) : a • x ∈ smulRange a M :=
  (mem_smulRange_iff (a := a) (a • x)).mpr ⟨x, rfl⟩

private theorem le_of_forall_mul_le {x y c : ℕ∞} (hy : y ≠ ⊤) (hc : c ≠ ⊤)
    (h : ∀ k : ℕ, (k : ℕ∞) * x ≤ (k : ℕ∞) * y + c) : x ≤ y := by
  have hx : x ≠ ⊤ := by
    intro hx
    have h1 := h 1
    rw [hx, Nat.cast_one, one_mul, one_mul] at h1
    exact (WithTop.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hy, lt_top_iff_ne_top.mpr hc⟩).ne
      (top_le_iff.mp h1)
  lift x to ℕ using hx
  lift y to ℕ using hy
  lift c to ℕ using hc
  by_contra hxy
  have hxy' : y + 1 ≤ x := by
    have : ¬ (x ≤ y) := fun h' => hxy (by exact_mod_cast h')
    omega
  have h2 := h (c + 1)
  have h3 : ((c + 1 : ℕ) : ℕ∞) * (x : ℕ∞) ≤ ((c + 1 : ℕ) : ℕ∞) * (y : ℕ∞) + (c : ℕ∞) := h2
  have h4 : (c + 1) * x ≤ (c + 1) * y + c := by exact_mod_cast h3
  have h5 : (c + 1) * (y + 1) ≤ (c + 1) * x := Nat.mul_le_mul_left _ hxy'
  nlinarith

section Domain

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

private theorem isArtinianRing_quotient_span_singleton {d : A} (hd : d ≠ 0) :
    IsArtinianRing (A ⧸ Ideal.span {d}) := by
  rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  refine ⟨inferInstance, ?_⟩
  rw [Ring.krullDimLE_zero_iff]
  intro P hP
  set Q : Ideal A := P.comap (Ideal.Quotient.mk (Ideal.span {d})) with hQdef
  have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
  have hdQ : d ∈ Q := by
    have h0 : (Ideal.Quotient.mk (Ideal.span {d})) d = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton d))
    rw [hQdef, Ideal.mem_comap, h0]
    exact P.zero_mem
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h] at hdQ
    exact hd ((Submodule.mem_bot A).mp hdQ)
  have hQmax : Q.IsMaximal := hQ.isMaximal_of_ne_bot hQne
  have hPQ : P = Q.map (Ideal.Quotient.mk (Ideal.span {d})) := by
    rw [hQdef, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span {d}))
      Ideal.Quotient.mk_surjective hQmax with h | h
  · exact absurd (hPQ ▸ h) hP.ne_top
  · exact hPQ ▸ h

private theorem length_ne_top_of_isTorsionBy {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] {d : A} (hd : d ≠ 0) (hM : ∀ m : M, d • m = 0) :
    Module.length A M ≠ ⊤ := by
  have hI : Module.IsTorsionBySet A M (Ideal.span {d} : Set A) := by
    rw [Module.isTorsionBySet_span_singleton_iff]
    intro m
    exact hM m
  letI : Module (A ⧸ Ideal.span {d}) M := hI.module
  haveI : IsScalarTower A (A ⧸ Ideal.span {d}) M :=
    hI.isScalarTower (S := A)
  haveI := isArtinianRing_quotient_span_singleton hd
  haveI : Module.Finite (A ⧸ Ideal.span {d}) M := Module.Finite.of_restrictScalars_finite A _ _
  haveI : IsArtinian (A ⧸ Ideal.span {d}) M := inferInstance
  haveI : IsNoetherian (A ⧸ Ideal.span {d}) M := inferInstance
  rw [Module.length_eq_of_surjective (S := A) (R := A ⧸ Ideal.span {d})
    Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

end Domain

section Filtration

variable {A : Type*} [CommRing A]

private theorem pow_smul_injective {M : Type*} [AddCommGroup M] [Module A M] {a : A}
    (hinj : ∀ m : M, a • m = 0 → m = 0) (k : ℕ) (m : M) (h : a ^ k • m = 0) : m = 0 := by
  induction k generalizing m with
  | zero => simpa using h
  | succ k ih =>
      rw [pow_succ, mul_smul] at h
      exact hinj m (ih (a • m) h)

private theorem smulRange_pow_succ_le {M : Type*} [AddCommGroup M] [Module A M] (a : A) (k : ℕ) :
    smulRange (a ^ (k + 1)) M ≤ smulRange (a ^ k) M := by
  rintro x hx
  obtain ⟨y, rfl⟩ := (mem_smulRange_iff x).mp hx
  exact (mem_smulRange_iff _).mpr ⟨a • y, by rw [pow_succ, mul_smul]⟩

private theorem length_quot_pow {M : Type*} [AddCommGroup M] [Module A M] (a : A)
    (hinj : ∀ m : M, a • m = 0 → m = 0) (k : ℕ) :
    Module.length A (M ⧸ smulRange (a ^ k) M) = k * Module.length A (M ⧸ smulRange a M) := by
  induction k with
  | zero =>
      have htop : smulRange ((a : A) ^ 0) M = ⊤ := by
        rw [eq_top_iff]
        rintro x -
        exact (mem_smulRange_iff x).mpr ⟨x, by simp⟩
      rw [htop, Nat.cast_zero, zero_mul]
      exact Module.length_eq_zero
  | succ k ih =>
      set q1 : Submodule A M := smulRange a M
      set qk : Submodule A M := smulRange (a ^ k) M
      set qk1 : Submodule A M := smulRange (a ^ (k + 1)) M
      have hf_wd : q1 ≤ LinearMap.ker (qk1.mkQ ∘ₗ DistribSMul.toLinearMap A M (a ^ k)) := by
        rintro x hx
        obtain ⟨y, rfl⟩ := (mem_smulRange_iff x).mp hx
        rw [LinearMap.mem_ker, LinearMap.comp_apply, DistribSMul.toLinearMap_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact (mem_smulRange_iff _).mpr ⟨y, by rw [← mul_smul, ← pow_succ]⟩
      set f : (M ⧸ q1) →ₗ[A] (M ⧸ qk1) :=
        q1.liftQ (qk1.mkQ ∘ₗ DistribSMul.toLinearMap A M (a ^ k)) hf_wd
      have hf_apply : ∀ m : M, f (Submodule.Quotient.mk m) = Submodule.Quotient.mk (a ^ k • m) := by
        intro m
        rfl
      have hg_wd : qk1 ≤ qk.comap (LinearMap.id : M →ₗ[A] M) := by
        rw [Submodule.comap_id]
        exact smulRange_pow_succ_le a k
      set g : (M ⧸ qk1) →ₗ[A] (M ⧸ qk) := qk1.mapQ qk LinearMap.id hg_wd
      have hg_apply : ∀ m : M, g (Submodule.Quotient.mk m) = Submodule.Quotient.mk m := by
        intro m
        rfl
      have hf_inj : Function.Injective f := by
        rw [← LinearMap.ker_eq_bot, eq_bot_iff]
        intro x hx
        induction x using Submodule.Quotient.induction_on with
        | H m =>
          rw [LinearMap.mem_ker, hf_apply, Submodule.Quotient.mk_eq_zero] at hx
          obtain ⟨y, hy⟩ := (mem_smulRange_iff _).mp hx
          rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
          have h0 : a ^ k • (m - a • y) = 0 := by
            rw [smul_sub, ← hy, ← mul_smul, ← pow_succ, sub_self]
          have := pow_smul_injective hinj k _ h0
          rw [sub_eq_zero] at this
          rw [this]
          exact smul_mem_smulRange a y
      have hg_surj : Function.Surjective g := by
        intro x
        induction x using Submodule.Quotient.induction_on with
        | H m => exact ⟨Submodule.Quotient.mk m, hg_apply m⟩
      have hexact : Function.Exact f g := by
        intro x
        induction x using Submodule.Quotient.induction_on with
        | H m =>
          rw [hg_apply, Submodule.Quotient.mk_eq_zero]
          constructor
          · intro hm
            obtain ⟨y, rfl⟩ := (mem_smulRange_iff _).mp hm
            exact ⟨Submodule.Quotient.mk y, hf_apply y⟩
          · rintro ⟨z, hz⟩
            induction z using Submodule.Quotient.induction_on with
            | H y =>
              rw [hf_apply, Submodule.Quotient.eq] at hz
              have h1 : a ^ k • y - m ∈ qk := smulRange_pow_succ_le a k hz
              have h2 : a ^ k • y ∈ qk := smul_mem_smulRange _ y
              have := qk.sub_mem h2 h1
              rwa [sub_sub_cancel] at this
      rw [Module.length_eq_add_of_exact f g hf_inj hg_surj hexact, ih, Nat.cast_succ,
        add_mul, one_mul, add_comm]

private theorem length_quot_le {M : Type*} [AddCommGroup M] [Module A M] (E : Submodule A M)
    (b : A) :
    Module.length A (M ⧸ smulRange b M) ≤
      Module.length A (E ⧸ smulRange b E) + Module.length A (M ⧸ E) := by
  set q : Submodule A M := smulRange b M
  set N' : Submodule A (M ⧸ q) := E.map q.mkQ
  have hsplit : Module.length A (M ⧸ q) = Module.length A N' + Module.length A ((M ⧸ q) ⧸ N') :=
    Module.length_eq_add_of_exact N'.subtype N'.mkQ (Submodule.injective_subtype N')
      (Submodule.mkQ_surjective N') (LinearMap.exact_subtype_mkQ N')
  rw [hsplit]
  refine add_le_add ?_ ?_
  · have hcod : ∀ e : E, (q.mkQ ∘ₗ E.subtype) e ∈ N' := fun e => ⟨e, e.2, rfl⟩
    set g₀ : E →ₗ[A] N' := LinearMap.codRestrict N' (q.mkQ ∘ₗ E.subtype) hcod
    have hwd : smulRange b E ≤ LinearMap.ker g₀ := by
      rintro x hx
      obtain ⟨y, rfl⟩ := (mem_smulRange_iff x).mp hx
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      change (q.mkQ ∘ₗ E.subtype) (b • y) = 0
      rw [LinearMap.comp_apply, map_smul, Submodule.subtype_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact smul_mem_smulRange b (y : M)
    refine Module.length_le_of_surjective ((smulRange b E).liftQ g₀ hwd) ?_
    rintro ⟨x, hx⟩
    obtain ⟨e, he, rfl⟩ := hx
    exact ⟨Submodule.Quotient.mk ⟨e, he⟩, rfl⟩
  · have hwd : E ≤ LinearMap.ker (N'.mkQ ∘ₗ q.mkQ) := by
      intro e he
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact ⟨e, he, rfl⟩
    refine Module.length_le_of_surjective (E.liftQ (N'.mkQ ∘ₗ q.mkQ) hwd) ?_
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      induction y using Submodule.Quotient.induction_on with
      | H m => exact ⟨Submodule.Quotient.mk m, rfl⟩

private theorem length_quot_smulRange_eq_of_equiv {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) (a : A) :
    Module.length A (M ⧸ smulRange a M) = Module.length A (N ⧸ smulRange a N) := by
  refine (Submodule.Quotient.equiv (smulRange a M) (smulRange a N) e ?_).length_eq
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := (mem_smulRange_iff x).mp hx
    exact (mem_smulRange_iff _).mpr ⟨e y, by simp⟩
  · rintro x hx
    obtain ⟨y, rfl⟩ := (mem_smulRange_iff x).mp hx
    exact ⟨a • e.symm y, smul_mem_smulRange a _, by simp⟩

end Filtration

section Core

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

private theorem length_quot_le_of_fg {P : Type*} [AddCommGroup P] [Module A P]
    (htf : ∀ a : A, a ≠ 0 → ∀ p : P, a • p = 0 → p = 0)
    (E : Submodule A P) (hEd : ∀ p : P, ∃ d : A, d ≠ 0 ∧ d • p ∈ E)
    {a : A} (ha : a ≠ 0) (M₁ : Submodule A P) (hM₁ : M₁.FG) (hEM₁ : E ≤ M₁) :
    Module.length A (M₁ ⧸ smulRange a M₁) ≤ Module.length A (E ⧸ smulRange a E) := by
  classical
  set E' : Submodule A M₁ := E.comap M₁.subtype
  have eE : E' ≃ₗ[A] E := Submodule.comapSubtypeEquivOfLe hEM₁
  haveI : Module.Finite A M₁ := Module.Finite.iff_fg.mpr hM₁
  obtain ⟨s, hs⟩ := hM₁
  have hgen : ∀ g : P, ∃ d : A, d ≠ 0 ∧ d • g ∈ E := hEd
  choose dg hdg0 hdgE using hgen
  set d : A := ∏ g ∈ s, dg g with hd_def
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun g _ => hdg0 g
  have hdmem : ∀ m ∈ M₁, d • m ∈ E := by
    intro m hm
    rw [← hs] at hm
    induction hm using Submodule.span_induction with
    | mem g hg =>
        have : d = (∏ g' ∈ s.erase g, dg g') * dg g := by
          rw [hd_def, ← Finset.prod_erase_mul _ _ hg]
        rw [this, mul_smul]
        exact E.smul_mem _ (hdgE g)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact E.add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact E.smul_mem c hx
  have hc : Module.length A (M₁ ⧸ E') ≠ ⊤ := by
    apply length_ne_top_of_isTorsionBy hd0
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      change (M₁.subtype (d • m)) ∈ E
      rw [map_smul]
      exact hdmem _ m.2
  haveI : Module.Finite A E := Module.Finite.of_injective eE.symm.toLinearMap eE.symm.injective
  have hy : Module.length A (E ⧸ smulRange a E) ≠ ⊤ := by
    apply length_ne_top_of_isTorsionBy ha
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H e =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact smul_mem_smulRange a e
  have hinjM : ∀ m : M₁, a • m = 0 → m = 0 := by
    intro m hm
    apply Subtype.ext
    exact htf a ha m (by exact_mod_cast congrArg Subtype.val hm)
  have hinjE : ∀ e : E', a • e = 0 → e = 0 := by
    intro e he
    apply Subtype.ext
    exact hinjM e (by exact_mod_cast congrArg Subtype.val he)
  refine le_of_forall_mul_le hy hc fun k => ?_
  have hak : a ^ k ≠ 0 := pow_ne_zero k ha
  calc (k : ℕ∞) * Module.length A (M₁ ⧸ smulRange a M₁)
        = Module.length A (M₁ ⧸ smulRange (a ^ k) M₁) := (length_quot_pow a hinjM k).symm
    _ ≤ Module.length A (E' ⧸ smulRange (a ^ k) E') + Module.length A (M₁ ⧸ E') :=
        length_quot_le E' (a ^ k)
    _ = (k : ℕ∞) * Module.length A (E' ⧸ smulRange a E') + Module.length A (M₁ ⧸ E') := by
          rw [length_quot_pow a hinjE k]
    _ = (k : ℕ∞) * Module.length A (E ⧸ smulRange a E) + Module.length A (M₁ ⧸ E') := by
          rw [length_quot_smulRange_eq_of_equiv eE a]

private theorem length_le_of_fg_quot {P : Type*} [AddCommGroup P] [Module A P]
    (htf : ∀ a : A, a ≠ 0 → ∀ p : P, a • p = 0 → p = 0)
    (E : Submodule A P) (hE : E.FG) (hEd : ∀ p : P, ∃ d : A, d ≠ 0 ∧ d • p ∈ E)
    {a : A} (ha : a ≠ 0) (N' : Submodule A (P ⧸ smulRange a P)) (hN' : N'.FG) :
    Module.length A N' ≤ Module.length A (E ⧸ smulRange a E) := by
  classical
  obtain ⟨s, hs⟩ := hN'
  have hlift : ∀ x : P ⧸ smulRange a P, ∃ p : P, Submodule.Quotient.mk p = x :=
    fun x => Submodule.mkQ_surjective (smulRange a P) x
  choose lift hlift using hlift
  set M₁ : Submodule A P := E ⊔ Submodule.span A (lift '' (s : Set (P ⧸ smulRange a P)))
  have hM₁fg : M₁.FG := hE.sup (Submodule.fg_span ((s.finite_toSet).image lift))
  have hEM₁ : E ≤ M₁ := le_sup_left
  have hN'le : N' ≤ M₁.map (smulRange a P).mkQ := by
    rw [← hs, Submodule.span_le]
    intro x hx
    refine ⟨lift x, ?_, hlift x⟩
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨x, hx, rfl⟩)
  have hcod : ∀ m : M₁, ((smulRange a P).mkQ ∘ₗ M₁.subtype) m ∈ M₁.map (smulRange a P).mkQ :=
    fun m => ⟨m, m.2, rfl⟩
  set g₀ : M₁ →ₗ[A] (M₁.map (smulRange a P).mkQ) :=
    LinearMap.codRestrict (M₁.map (smulRange a P).mkQ) ((smulRange a P).mkQ ∘ₗ M₁.subtype) hcod
  have hwd : smulRange a M₁ ≤ LinearMap.ker g₀ := by
    rintro x hx
    obtain ⟨y, rfl⟩ := (mem_smulRange_iff x).mp hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change ((smulRange a P).mkQ ∘ₗ M₁.subtype) (a • y) = 0
    rw [LinearMap.comp_apply, map_smul, Submodule.subtype_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact smul_mem_smulRange a (y : P)
  have hsurj : Function.Surjective ((smulRange a M₁).liftQ g₀ hwd) := by
    rintro ⟨x, hx⟩
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨Submodule.Quotient.mk ⟨m, hm⟩, rfl⟩
  calc Module.length A N'
        ≤ Module.length A (M₁.map (smulRange a P).mkQ) :=
          Module.length_le_of_injective (Submodule.inclusion hN'le)
            (Submodule.inclusion_injective hN'le)
    _ ≤ Module.length A (M₁ ⧸ smulRange a M₁) := Module.length_le_of_surjective _ hsurj
    _ ≤ Module.length A (E ⧸ smulRange a E) := length_quot_le_of_fg htf E hEd ha M₁ hM₁fg hEM₁

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
private theorem length_ne_top_of_forall_fg_le {Q : Type*} [AddCommGroup Q] [Module A Q]
    {y : ℕ∞} (hy : y ≠ ⊤) (h : ∀ N : Submodule A Q, N.FG → Module.length A N ≤ y) :
    Module.length A Q ≠ ⊤ := by
  classical
  set S : Set ℕ := {n : ℕ | ∃ N : Submodule A Q, N.FG ∧ Module.length A N = n} with hS
  have hS0 : (0 : ℕ) ∈ S := ⟨⊥, Submodule.fg_bot, by rw [Module.length_bot]; rfl⟩
  have hSne : S.Nonempty := ⟨0, hS0⟩
  have hbdd : BddAbove S := by
    refine ⟨y.toNat, ?_⟩
    rintro n ⟨N, hN, hn⟩
    have h1 : (n : ℕ∞) ≤ y := hn ▸ h N hN
    rw [← ENat.natCast_toNat hy] at h1
    exact_mod_cast h1
  obtain ⟨N₀, hN₀fg, hN₀⟩ := Nat.sSup_mem hSne hbdd
  set m : ℕ := sSup S
  have hmax : ∀ N : Submodule A Q, N.FG → Module.length A N ≤ m := by
    intro N hN
    have hne : Module.length A N ≠ ⊤ := ne_top_of_le_ne_top hy (h N hN)
    have hmem : (Module.length A N).toNat ∈ S := ⟨N, hN, (ENat.natCast_toNat hne).symm⟩
    have := le_csSup hbdd hmem
    rw [← ENat.natCast_toNat hne]
    exact_mod_cast this
  have htop : N₀ = ⊤ := by
    rw [eq_top_iff]
    intro q _
    by_contra hq
    set N₁ : Submodule A Q := N₀ ⊔ Submodule.span A {q}
    have hN₁fg : N₁.FG := hN₀fg.sup (Submodule.fg_span (Set.finite_singleton q))
    have h01 : N₀ ≤ N₁ := le_sup_left
    have hlen1 : Module.length A N₁ = m := by
      apply le_antisymm (hmax N₁ hN₁fg)
      rw [← hN₀]
      exact Module.length_le_of_injective (Submodule.inclusion h01)
        (Submodule.inclusion_injective h01)
    have hfl : IsFiniteLength A N₁ := by
      rw [← Module.length_ne_top_iff, hlen1]
      exact ENat.natCast_ne_top m
    obtain ⟨hnoeth, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
    set N₀' : Submodule A N₁ := N₀.comap N₁.subtype
    have hne : N₀' ≠ ⊤ := by
      intro h'
      have hq1 : q ∈ N₁ := Submodule.mem_sup_right (Submodule.mem_span_singleton_self q)
      have : (⟨q, hq1⟩ : N₁) ∈ N₀' := by rw [h']; trivial
      exact hq this
    have hlt := Submodule.length_lt (R := A) (M := N₁) hne
    rw [(Submodule.comapSubtypeEquivOfLe h01).length_eq, hN₀, hlen1] at hlt
    exact lt_irrefl _ hlt
  rw [← Submodule.topEquiv.length_eq, ← htop, hN₀]
  exact ENat.natCast_ne_top m

private theorem core {P : Type*} [AddCommGroup P] [Module A P]
    (htf : ∀ a : A, a ≠ 0 → ∀ p : P, a • p = 0 → p = 0)
    (E : Submodule A P) (hE : E.FG) (hEd : ∀ p : P, ∃ d : A, d ≠ 0 ∧ d • p ∈ E)
    {a : A} (ha : a ≠ 0) :
    Module.length A (P ⧸ smulRange a P) ≠ ⊤ := by
  haveI : Module.Finite A E := Module.Finite.iff_fg.mpr hE
  have hy : Module.length A (E ⧸ smulRange a E) ≠ ⊤ := by
    apply length_ne_top_of_isTorsionBy ha
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H e =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact smul_mem_smulRange a e
  exact length_ne_top_of_forall_fg_le hy fun N hN => length_le_of_fg_quot htf E hE hEd ha N hN

end Core

section Lattice

variable {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

private theorem exists_smul_mem_span {V : Type*} [AddCommGroup V] [Module K V] [Module A V]
    [IsScalarTower A K V] (S : Set V) {x : V} (hx : x ∈ Submodule.span K S) :
    ∃ d : A, d ≠ 0 ∧ d • x ∈ Submodule.span A S := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
      obtain ⟨d₁, hd₁, h₁⟩ := hx
      obtain ⟨d₂, hd₂, h₂⟩ := hy
      refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
      rw [smul_add, mul_comm d₁ d₂, mul_smul, mul_comm d₂ d₁, mul_smul]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  | smul c x _ hx =>
      obtain ⟨d, hd, h⟩ := hx
      obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := A) c
      have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
      have hmK : algebraMap A K m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
      refine ⟨m * d, mul_ne_zero hm0 hd, ?_⟩
      have : (m * d) • ((algebraMap A K n / algebraMap A K m) • x) = n • (d • x) := by
        rw [← IsScalarTower.algebraMap_smul K (m * d), smul_smul, map_mul, mul_assoc,
          mul_comm (algebraMap A K d), ← mul_assoc, mul_div_cancel₀ _ hmK, ← map_mul,
          IsScalarTower.algebraMap_smul, mul_smul]
      rw [this]
      exact Submodule.smul_mem _ _ h

private theorem exists_lattice {V P : Type*} [AddCommGroup V] [Module K V] [Module A V]
    [IsScalarTower A K V] [FiniteDimensional K V] [AddCommGroup P] [Module A P] (f : P →ₗ[A] V)
    (hf : Function.Injective f) :
    ∃ E : Submodule A P, E.FG ∧ ∀ p : P, ∃ d : A, d ≠ 0 ∧ d • p ∈ E := by
  classical
  set W : Submodule K V := Submodule.span K (Set.range f)
  let b := Module.finBasis K W
  have h1 : ∀ i, ∃ p : P, ∃ d : A, d ≠ 0 ∧ f p = d • ((b i : W) : V) := by
    intro i
    obtain ⟨d, hd, hmem⟩ := exists_smul_mem_span (A := A) (K := K) (Set.range f) (b i).2
    have hrange : Submodule.span A (Set.range f) = LinearMap.range f := by
      rw [← LinearMap.coe_range, Submodule.span_eq]
    rw [hrange] at hmem
    obtain ⟨p, hp⟩ := hmem
    exact ⟨p, d, hd, hp⟩
  choose p d hd hp using h1
  refine ⟨Submodule.span A (Set.range p), Submodule.fg_span (Set.finite_range p), fun x => ?_⟩
  have hW : W ≤ Submodule.span K (Set.range fun i => f (p i)) := by
    have hb : ∀ i, ((b i : W) : V) ∈ Submodule.span K (Set.range fun i => f (p i)) := by
      intro i
      have : ((b i : W) : V) = (algebraMap A K (d i))⁻¹ • f (p i) := by
        rw [hp i, ← IsScalarTower.algebraMap_smul K (d i), smul_smul,
          inv_mul_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
            (mem_nonZeroDivisors_of_ne_zero (hd i))), one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    intro w hw
    have hw' : (⟨w, hw⟩ : W) ∈ Submodule.span K (Set.range b) := b.mem_span _
    have hwmap : W.subtype ⟨w, hw⟩ ∈ (Submodule.span K (Set.range b)).map W.subtype :=
      Submodule.mem_map_of_mem hw'
    have hmap : (Submodule.span K (Set.range b)).map W.subtype ≤
        Submodule.span K (Set.range fun i => f (p i)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact hb i
    exact hmap hwmap
  have hx : f x ∈ Submodule.span K (Set.range fun i => f (p i)) :=
    hW (Submodule.subset_span ⟨x, rfl⟩)
  obtain ⟨d', hd', hmem'⟩ := exists_smul_mem_span (A := A) (K := K) _ hx
  have hspan : Submodule.span A (Set.range fun i => f (p i)) =
      (Submodule.span A (Set.range p)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hspan] at hmem'
  obtain ⟨e, he, hfe⟩ := hmem'
  refine ⟨d', hd', ?_⟩
  have : f (d' • x) = f e := by rw [map_smul, hfe]
  rw [hf this]
  exact he

end Lattice

section Main

private theorem main {A K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L]
    (B : Subalgebra A L) :
    IsNoetherianRing B ∧ Ring.KrullDimLE 1 B ∧
      ∀ J : Ideal B, J ≠ ⊥ → IsFiniteLength A (B ⧸ J) := by
  classical
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp hAK
  have hAB : Function.Injective (algebraMap A B) := by
    intro x y hxy
    apply hAL
    have := congrArg (fun b : B => (b : L)) hxy
    simpa using this
  have htf : ∀ a : A, a ≠ 0 → ∀ b : B, a • b = 0 → b = 0 := by
    intro a ha b hb
    rw [Algebra.smul_def] at hb
    exact (mul_eq_zero.mp hb).resolve_left ((map_ne_zero_iff _ hAB).mpr ha)
  obtain ⟨E, hEfg, hEd⟩ := exists_lattice (A := A) (K := K) (V := L) (B.val.toLinearMap)
    (fun x y h => Subtype.ext h)
  have hcore : ∀ a : A, a ≠ 0 → Module.length A (B ⧸ smulRange a B) ≠ ⊤ :=
    fun a ha => core htf E hEfg hEd ha
  have halgL : Algebra.IsAlgebraic A L := by
    haveI : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
    haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    exact Algebra.IsAlgebraic.trans A K L
  have hJ : ∀ J : Ideal B, J ≠ ⊥ → ∃ a : A, a ≠ 0 ∧ algebraMap A B a ∈ J := by
    intro J hJne
    obtain ⟨b, hbJ, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJne
    have hb : IsAlgebraic A b :=
      (isAlgebraic_algHom_iff B.val (fun x y h => Subtype.ext h)).mp (halgL.isAlgebraic (b : L))
    have hne := Ideal.under_ne_bot_of_algebraic_mem hb0 hbJ hb
    obtain ⟨a, haJ, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨a, ha0, haJ⟩
  have h3 : ∀ J : Ideal B, J ≠ ⊥ → IsFiniteLength A (B ⧸ J) := by
    intro J hJne
    obtain ⟨a, ha, haJ⟩ := hJ J hJne
    have hle : smulRange a B ≤ (J.restrictScalars A).comap (LinearMap.id : B →ₗ[A] B) := by
      rintro x hx
      obtain ⟨b, rfl⟩ := (mem_smulRange_iff x).mp hx
      change a • b ∈ J
      rw [Algebra.smul_def]
      exact J.mul_mem_right _ haJ
    set φ : (B ⧸ smulRange a B) →ₗ[A] (B ⧸ J) :=
      (Submodule.Quotient.restrictScalarsEquiv A J).toLinearMap ∘ₗ
        (smulRange a B).mapQ (J.restrictScalars A) LinearMap.id hle
    have hφ : Function.Surjective φ := by
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H b => exact ⟨Submodule.Quotient.mk b, rfl⟩
    rw [← Module.length_ne_top_iff]
    exact ne_top_of_le_ne_top (hcore a ha) (Module.length_le_of_surjective φ hφ)
  have hI : ∀ {a : A}, a ≠ 0 → (Ideal.span {algebraMap A B a} : Ideal B) ≠ ⊥ := by
    intro a ha h
    rw [Ideal.span_singleton_eq_bot] at h
    exact (map_ne_zero_iff _ hAB).mpr ha h
  refine ⟨?_, ?_, h3⟩
  · rw [isNoetherianRing_iff, isNoetherian_def]
    intro J
    by_cases hJ0 : J = ⊥
    · rw [hJ0]; exact Submodule.fg_bot
    obtain ⟨a, ha, haJ⟩ := hJ J hJ0
    set I : Ideal B := Ideal.span {algebraMap A B a}
    have hIJ : I ≤ J := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact haJ
    haveI : IsNoetherian A (B ⧸ I) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp (h3 I (hI ha))).1
    haveI : IsNoetherian B (B ⧸ I) := isNoetherian_of_tower A inferInstance
    apply Submodule.fg_of_fg_map_of_fg_inf_ker I.mkQ
    · exact IsNoetherian.noetherian _
    · rw [Submodule.ker_mkQ, inf_eq_right.mpr hIJ]
      exact ⟨{algebraMap A B a}, by simp [I]⟩
  · rw [Ring.krullDimLE_one_iff_of_noZeroDivisors]
    intro p hp0 hp
    obtain ⟨a, ha, hap⟩ := hJ p hp0
    set I : Ideal B := Ideal.span {algebraMap A B a}
    have hIp : I ≤ p := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hap
    haveI : IsArtinian A (B ⧸ I) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp (h3 I (hI ha))).2
    haveI : IsArtinianRing (B ⧸ I) := isArtinian_of_tower A inferInstance
    have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ p := by
      rw [Ideal.mk_ker]
      exact hIp
    haveI hp' : (p.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    have hmax : (p.map (Ideal.Quotient.mk I)).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
    have hcomap := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective (K := p.map (Ideal.Quotient.mk I))
    have heq : (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = p := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, sup_eq_left]
      rw [← RingHom.ker_eq_comap_bot]
      exact hker
    rwa [heq] at hcomap

end Main

end KrullAkizukiAux

/-- The Krull–Akizuki theorem: a subalgebra of a finite extension of the
fraction field of a Noetherian domain of Krull dimension at most one is
Noetherian of Krull dimension at most one, and every nonzero quotient has
finite length over the base. -/
theorem Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
    {A K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L]
    (B : Subalgebra A L) :
    IsNoetherianRing B ∧ Ring.KrullDimLE 1 B ∧
      ∀ J : Ideal B, J ≠ ⊥ → IsFiniteLength A (B ⧸ J) :=
  KrullAkizukiAux.main (K := K) B
