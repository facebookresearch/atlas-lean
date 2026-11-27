/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
the theorem files `Theorems/Thm_<Y>.lean` and solution files `P2M/Sol/S_<Y>.lean`
for `<Y>` in the list below:
`Module_isClosed_setOf_range_le_smul_top`
`Module_Invertible_bijective_localizedModule_map_of_not_range_le`
`Module_Invertible_range_le_smul_top_or_of_comp_eq_smul`
`IsLocalizedModule_exists_forall_isLocalizedModule_comp_eq_of_span_eq_top`
`Module_Invertible_of_isLocalizedModule_of_span_eq_top`
`Module_Invertible_of_isLocalizedModule_of_span_range_eq_top`
`IsLocalizedModule_existsUnique_forall_comp_eq_of_span_eq_top`
`LinearMap_exists_forall_localizedModule_mk_eq_of_forall_exists_chart`
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

noncomputable section

universe u v w

open scoped TensorProduct

/-- If `Q` is finite projective, the set of primes `x` with `range f ≤ x • ⊤` is closed. -/
theorem Module.isClosed_setOf_range_le_smul_top
    {R : Type*} [CommRing R] {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q]
    [Module R Q] [Module.Finite R Q] [Module.Projective R Q] (f : P →ₗ[R] Q) :
    IsClosed {x : PrimeSpectrum R | LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q)} := by
  classical
  let s : Set R := {r | ∃ (φ : Q →ₗ[R] R) (p : P), r = φ (f p)}
  suffices h : {x : PrimeSpectrum R | LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q)} =
      PrimeSpectrum.zeroLocus s by
    rw [h]; exact PrimeSpectrum.isClosed_zeroLocus s
  obtain ⟨sec, hsec⟩ := (inferInstance : Module.Projective R Q).out
  ext x
  simp only [Set.mem_ofPred_eq, PrimeSpectrum.mem_zeroLocus]
  constructor
  · intro hx
    rintro r ⟨φ, p, rfl⟩
    have hfp : f p ∈ x.asIdeal • (⊤ : Submodule R Q) := hx ⟨p, rfl⟩
    change φ (f p) ∈ x.asIdeal
    refine Submodule.smul_induction_on (p := fun q => φ q ∈ x.asIdeal) hfp ?_ ?_
    · intro a ha q _
      rw [map_smul, smul_eq_mul]; exact Ideal.mul_mem_right _ _ ha
    · intro u v hu hv
      rw [map_add]; exact Ideal.add_mem _ hu hv
  · intro hx
    rintro _ ⟨p, rfl⟩
    rw [← hsec (f p), Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun q _ => ?_
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    exact hx ⟨(Finsupp.lapply q).comp sec, p, rfl⟩

private theorem invLoc_mem_smul_top_of_smul_mem {R : Type*} [CommRing R] {Q : Type*}
    [AddCommGroup Q] [Module R Q] [Module.Flat R Q] (I : Ideal R) [hI : I.IsPrime] (u : R)
    (hu : u ∉ I) (q : Q) (h : u • q ∈ I • (⊤ : Submodule R Q)) :
    q ∈ I • (⊤ : Submodule R Q) := by
  have : IsDomain (R ⧸ I) := Ideal.Quotient.isDomain I
  have hu0 : (Ideal.Quotient.mk I u) ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hreg : IsSMulRegular ((R ⧸ I) ⊗[R] Q) (Ideal.Quotient.mk I u) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (M := (R ⧸ I) ⊗[R] Q)
      (mem_nonZeroDivisors_of_ne_zero hu0)
  let e := TensorProduct.quotTensorEquivQuotSMul Q I
  have h1 : e.symm (Submodule.Quotient.mk (u • q)) = 0 := by
    rw [(Submodule.Quotient.mk_eq_zero _).2 h, map_zero]
  rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk] at h1
  have h2 : (Ideal.Quotient.mk I u) • ((1 : R ⧸ I) ⊗ₜ[R] q) =
      (Ideal.Quotient.mk I u) • (0 : (R ⧸ I) ⊗[R] Q) := by
    rw [smul_zero, TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← h1, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  have h3 : (1 : R ⧸ I) ⊗ₜ[R] q = 0 := hreg h2
  have h4 : e.symm (Submodule.Quotient.mk q) = 0 := by
    rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk, h3]
  rw [← Submodule.Quotient.mk_eq_zero, ← e.symm.map_eq_zero_iff]
  exact h4

private theorem invLoc_exists_smul_mem_of_mk_mem {R : Type*} [CommRing R] (S : Submonoid R)
    {Q : Type*} [AddCommGroup Q] [Module R Q] (N : Submodule R Q) (q : Q)
    (h : LocalizedModule.mk q (1 : S) ∈
      N.localized' (Localization S) S (LocalizedModule.mkLinearMap S Q)) :
    ∃ u : S, (u : R) • q ∈ N := by
  obtain ⟨m, hm, s, hms⟩ :=
    (Submodule.mem_localized' (Localization S) S (LocalizedModule.mkLinearMap S Q) N _).1 h
  rw [IsLocalizedModule.mk'_eq_iff, LocalizedModule.mkLinearMap_apply, Submonoid.smul_def,
    LocalizedModule.smul'_mk, ← LocalizedModule.mkLinearMap_apply] at hms
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists S (LocalizedModule.mkLinearMap S Q)).1 hms
  refine ⟨c * s, ?_⟩
  have hc' : (c : R) • m = (c : R) • ((s : R) • q) := hc
  rw [Submonoid.coe_mul, mul_smul, ← hc']
  exact N.smul_mem _ hm

/-- A map of invertible modules whose range is not contained in `x • ⊤` is bijective after
localizing at `x`. -/
theorem Module.Invertible.bijective_localizedModule_map_of_not_range_le
    {R : Type*} [CommRing R] {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q]
    [Module R Q] [Module.Invertible R P] [Module.Invertible R Q] (f : P →ₗ[R] Q)
    (x : PrimeSpectrum R) (hx : ¬ LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q)) :
    Function.Bijective (LocalizedModule.map x.asIdeal.primeCompl f) := by
  classical
  set S := x.asIdeal.primeCompl with hS
  let Rp := Localization S
  let fp : LocalizedModule S P →ₗ[Rp] LocalizedModule S Q := LocalizedModule.map S f
  apply Module.Invertible.bijective_of_surjective (R := Rp) (f := fp)
  obtain ⟨e⟩ :=
    (Module.Invertible.free_iff_linearEquiv (R := Rp) (M := LocalizedModule S Q)).1 inferInstance
  let J : Ideal Rp := (LinearMap.range fp).map e.toLinearMap
  by_cases hJ : J = ⊤
  · intro y
    have : e y ∈ J := by rw [hJ]; trivial
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 this
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hz
    exact ⟨w, e.injective hzy⟩
  · exfalso
    apply hx
    have hJle : J ≤ IsLocalRing.maximalIdeal Rp := IsLocalRing.le_maximalIdeal hJ
    rintro _ ⟨p, rfl⟩
    have h1 : e (LocalizedModule.mk (f p) 1) ∈ IsLocalRing.maximalIdeal Rp := by
      apply hJle
      refine Submodule.mem_map.2 ⟨_, ⟨LocalizedModule.mk p 1, ?_⟩, rfl⟩
      exact LocalizedModule.map_mk S f p 1
    have h2 : LocalizedModule.mk (f p) (1 : S) ∈
        (x.asIdeal • (⊤ : Submodule R Q)).localized' Rp S (LocalizedModule.mkLinearMap S Q) := by
      rw [Submodule.localized'_smul, Submodule.localized'_top]
      have : LocalizedModule.mk (f p) (1 : S) = (e (LocalizedModule.mk (f p) 1)) • e.symm 1 := by
        rw [← LinearEquiv.map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
      rw [this]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [← Localization.AtPrime.map_eq_maximalIdeal] at h1
      refine (Ideal.map_le_iff_le_comap.2 ?_) h1
      intro r hr
      exact (Submodule.mem_localized' Rp S (Algebra.linearMap R Rp) _ _).2 ⟨r, hr, 1, by
        rw [IsLocalizedModule.mk'_one]; rfl⟩
    obtain ⟨u, hu⟩ := invLoc_exists_smul_mem_of_mk_mem S _ _ h2
    exact invLoc_mem_smul_top_of_smul_mem x.asIdeal (u : R) u.2 (f p) hu

/-- If `g ∘ f = a • id` for invertible modules and `a ∈ x`, then the range of `f` or of `g`
lies in `x • ⊤`. -/
theorem Module.Invertible.range_le_smul_top_or_of_comp_eq_smul
    {R : Type*} [CommRing R] {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q]
    [Module R Q] [Module.Invertible R P] [Module.Invertible R Q] (f : P →ₗ[R] Q)
    (g : Q →ₗ[R] P) (a : R) (hfg : g ∘ₗ f = a • LinearMap.id) (x : PrimeSpectrum R)
    (ha : a ∈ x.asIdeal) :
    LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q) ∨
      LinearMap.range g ≤ x.asIdeal • (⊤ : Submodule R P) := by
  classical
  by_contra h
  rw [not_or] at h
  obtain ⟨hf, hg⟩ := h
  set S := x.asIdeal.primeCompl with hS
  let Rp := Localization S
  have hbf := Module.Invertible.bijective_localizedModule_map_of_not_range_le f x hf
  have hbg := Module.Invertible.bijective_localizedModule_map_of_not_range_le g x hg
  have hcomp : ∀ z : LocalizedModule S P,
      LocalizedModule.map S g (LocalizedModule.map S f z) = algebraMap R Rp a • z := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h p s =>
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk, ← LinearMap.comp_apply, hfg,
        LinearMap.smul_apply, LinearMap.id_apply, algebraMap_smul, LocalizedModule.smul'_mk]
  have hbij : Function.Bijective fun z : LocalizedModule S P => algebraMap R Rp a • z := by
    have := hbg.comp hbf
    convert this using 1
    funext z; exact (hcomp z).symm
  obtain ⟨e⟩ :=
    (Module.Invertible.free_iff_linearEquiv (R := Rp) (M := LocalizedModule S P)).1 inferInstance
  obtain ⟨z, hz⟩ := hbij.2 (e.symm 1)
  have hz' : algebraMap R Rp a * e z = 1 := by
    have := congrArg e hz
    rwa [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul] at this
  have hunit : IsUnit (algebraMap R Rp a) := IsUnit.of_mul_eq_one _ hz'
  have hmem : algebraMap R Rp a ∈ IsLocalRing.maximalIdeal Rp := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ ha
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem hunit

private theorem zarGlue_pow_sup_eq {B : Type*} [CommRing B] {ι : Type*} [Fintype ι] (b : B)
    (n : ι → ℕ) (i : ι) :
    b ^ (Finset.univ.sup n) = b ^ (Finset.univ.sup n - n i) * b ^ (n i) := by
  rw [← pow_add, Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ i))]

private theorem zarGlue_eq_of_pow_smul_eq {B : Type*} [CommRing B] {M : Type*} [AddCommGroup M]
    [Module B M] (b : B)
    (h : IsLocalizedModule (Submonoid.powers b) (LinearMap.id : M →ₗ[B] M)) (n : ℕ) (x y : M)
    (hxy : b ^ n • x = b ^ n • y) : x = y := by
  have hu := h.map_units ⟨b ^ n, n, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have this : (u : Module.End B M) x = (u : Module.End B M) y := by
    rw [hu]; exact hxy
  have key : ∀ z : M,
      ((u⁻¹ : (Module.End B M)ˣ) : Module.End B M) ((u : Module.End B M) z) = z := fun z => by
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
  rw [← key x, ← key y, this]

/-- Zariski gluing of modules along a finite cover `D(f i)` given cocycle data. -/
theorem IsLocalizedModule.exists_forall_isLocalizedModule_comp_eq_of_span_eq_top
    {B : Type u} [CommRing B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (M : Fin k → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)]
    (hM : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (LinearMap.id : M i →ₗ[B] M i))
    (M₂ : Fin k → Fin k → Type u) [∀ i j, AddCommGroup (M₂ i j)] [∀ i j, Module B (M₂ i j)]
    (ρl : ∀ i j, M i →ₗ[B] M₂ i j) (ρr : ∀ i j, M j →ₗ[B] M₂ i j)
    (hρr : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr i j))
    (hdiag : ∀ i, ρl i i = ρr i i)
    (M₃ : Fin k → Fin k → Fin k → Type u) [∀ i j l, AddCommGroup (M₃ i j l)]
    [∀ i j l, Module B (M₃ i j l)]
    (σ₁ : ∀ i j l, M₂ i j →ₗ[B] M₃ i j l) (σ₂ : ∀ i j l, M₂ i l →ₗ[B] M₃ i j l)
    (σ₃ : ∀ i j l, M₂ j l →ₗ[B] M₃ i j l)
    (hσ₃ : ∀ i j l, IsLocalizedModule (Submonoid.powers (f i)) (σ₃ i j l))
    (hcoc₁ : ∀ i j l, σ₁ i j l ∘ₗ ρl i j = σ₂ i j l ∘ₗ ρl i l)
    (hcoc₂ : ∀ i j l, σ₁ i j l ∘ₗ ρr i j = σ₃ i j l ∘ₗ ρl j l)
    (hcoc₃ : ∀ i j l, σ₂ i j l ∘ₗ ρr i l = σ₃ i j l ∘ₗ ρr j l) :
    ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module B N) (π : ∀ i, N →ₗ[B] M i),
      (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (π i)) ∧
      (∀ i j, ρl i j ∘ₗ π i = ρr i j ∘ₗ π j) := by
  classical
  let N : Submodule B (∀ i, M i) :=
    ⨅ i, ⨅ j, LinearMap.ker (ρl i j ∘ₗ LinearMap.proj i - ρr i j ∘ₗ LinearMap.proj j)
  have hN : ∀ m : ∀ i, M i, m ∈ N ↔ ∀ i j, ρl i j (m i) = ρr i j (m j) := by
    intro m
    simp only [N, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, sub_eq_zero]
  let π : ∀ i, N →ₗ[B] M i := fun i => (LinearMap.proj i).comp N.subtype
  have hπ : ∀ i (n : N), π i n = (n : ∀ i, M i) i := fun i n => rfl
  refine ⟨N, inferInstance, inferInstance, π, fun i => ?_, fun i j => ?_⟩
  swap
  · ext n
    simp only [LinearMap.comp_apply, hπ]
    exact (hN n).1 n.2 i j
  refine ⟨fun s => ?_, fun y => ?_, fun {n n'} h => ?_⟩
  · exact (hM i).map_units s
  · have h1 : ∀ j, ∃ (nz : ℕ × M j), f i ^ nz.1 • ρl i j y = ρr i j nz.2 := by
      intro j
      obtain ⟨⟨z, s⟩, hs⟩ := (hρr i j).surj (ρl i j y)
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
      exact ⟨(n, z), by rw [← hs, Submonoid.smul_def, ← hn]⟩
    choose nz hnz using h1
    let N₁ : ℕ := Finset.univ.sup fun j => (nz j).1
    obtain ⟨z', hz'⟩ : ∃ z' : ∀ j, M j, ∀ j, f i ^ N₁ • ρl i j y = ρr i j (z' j) := by
      refine ⟨fun j => f i ^ (N₁ - (nz j).1) • (nz j).2, fun j => ?_⟩
      rw [map_smul, ← hnz j, ← mul_smul, ← zarGlue_pow_sup_eq (f i) (fun j => (nz j).1) j]
    have h2 : ∀ j l, ∃ a : ℕ, f i ^ a • (ρl j l (z' j) - ρr j l (z' l)) = 0 := by
      intro j l
      have hzero : σ₃ i j l (ρl j l (z' j) - ρr j l (z' l)) = 0 := by
        rw [map_sub, sub_eq_zero, ← LinearMap.comp_apply, ← hcoc₂, LinearMap.comp_apply, ← hz' j,
          map_smul, ← LinearMap.comp_apply (σ₁ i j l), hcoc₁, LinearMap.comp_apply,
          ← LinearMap.comp_apply (σ₃ i j l), ← hcoc₃, LinearMap.comp_apply, ← hz' l, map_smul]
      obtain ⟨c, hc⟩ :=
        (IsLocalizedModule.eq_zero_iff (Submonoid.powers (f i)) (σ₃ i j l)).1 hzero
      obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).1 c.2
      exact ⟨a, by rw [Submonoid.smul_def, ← ha] at hc; exact hc⟩
    choose a ha using h2
    let A : ℕ := Finset.univ.sup fun p : Fin k × Fin k => a p.1 p.2
    obtain ⟨w, hwdef⟩ : ∃ w : ∀ j, M j, ∀ j, w j = f i ^ A • z' j :=
      ⟨fun j => f i ^ A • z' j, fun j => rfl⟩
    have hw : w ∈ N := by
      rw [hN]
      intro j l
      rw [hwdef, hwdef, map_smul, map_smul, ← sub_eq_zero, ← smul_sub,
        zarGlue_pow_sup_eq (f i) (fun p : Fin k × Fin k => a p.1 p.2) (j, l), mul_smul, ha j l,
        smul_zero]
    have hwi : w i = f i ^ (A + N₁) • y := by
      rw [hwdef, pow_add, mul_smul]
      congr 1
      have : ρr i i (z' i) = ρr i i (f i ^ N₁ • y) := by rw [← hz' i, map_smul, hdiag]
      obtain ⟨c, hc⟩ := (hρr i i).exists_of_eq this
      obtain ⟨b, hb⟩ := (Submonoid.mem_powers_iff _ _).1 c.2
      rw [Submonoid.smul_def, Submonoid.smul_def, ← hb] at hc
      exact zarGlue_eq_of_pow_smul_eq (f i) (hM i) b _ _ hc
    refine ⟨(⟨w, hw⟩, ⟨f i ^ (A + N₁), _, rfl⟩), ?_⟩
    change f i ^ (A + N₁) • y = w i
    rw [hwi]
  · have h3 : ∀ j, ∃ e : ℕ, f i ^ e • (n : ∀ i, M i) j = f i ^ e • (n' : ∀ i, M i) j := by
      intro j
      have : ρr i j ((n : ∀ i, M i) j) = ρr i j ((n' : ∀ i, M i) j) := by
        rw [← (hN n).1 n.2 i j, ← (hN n').1 n'.2 i j]
        exact congrArg (ρl i j) h
      obtain ⟨c, hc⟩ := (hρr i j).exists_of_eq this
      obtain ⟨e, he⟩ := (Submonoid.mem_powers_iff _ _).1 c.2
      exact ⟨e, by rw [Submonoid.smul_def, Submonoid.smul_def, ← he] at hc; exact hc⟩
    choose e he using h3
    refine ⟨⟨f i ^ (Finset.univ.sup e), _, rfl⟩, ?_⟩
    apply Subtype.ext
    funext j
    change f i ^ (Finset.univ.sup e) • (n : ∀ i, M i) j =
      f i ^ (Finset.univ.sup e) • (n' : ∀ i, M i) j
    rw [zarGlue_pow_sup_eq (f i) e j, mul_smul, mul_smul, he j]

private theorem invLocal_bijective_map_contractLeft {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization S A] {M' : Type*} [AddCommGroup M'] [Module R M'] [Module A M']
    [IsScalarTower R A M'] (φ : M →ₗ[R] M') [IsLocalizedModule S φ]
    [Module.FinitePresentation R M] [Module.Invertible A M'] :
    Function.Bijective
      (IsLocalizedModule.map S (TensorProduct.mk R A (Module.Dual R M ⊗[R] M) 1)
        (Algebra.linearMap R A) (contractLeft R M)) := by
  let d : Module.Dual R M →ₗ[R] Module.Dual A M' :=
    IsLocalizedModule.mapExtendScalars S φ (Algebra.linearMap R A) A
  have : IsLocalizedModule S d :=
    Module.FinitePresentation.isLocalizedModule_mapExtendScalars S φ (Algebra.linearMap R A) A
  have hd : ∀ (x : Module.Dual R M) (m : M), d x (φ m) = algebraMap R A (x m) := by
    intro x m
    rw [IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply,
      Algebra.linearMap_apply]
  let eD : A ⊗[R] Module.Dual R M ≃ₗ[A] Module.Dual A M' :=
    (IsLocalizedModule.isBaseChange S A d).equiv
  let eM : A ⊗[R] M ≃ₗ[A] M' := (IsLocalizedModule.isBaseChange S A φ).equiv
  let e : A ⊗[R] (Module.Dual R M ⊗[R] M) ≃ₗ[A] Module.Dual A M' ⊗[A] M' :=
    TensorProduct.AlgebraTensorModule.distribBaseChange R A _ _ ≪≫ₗ TensorProduct.congr eD eM
  have key : IsLocalizedModule.map S (TensorProduct.mk R A (Module.Dual R M ⊗[R] M) 1)
      (Algebra.linearMap R A) (contractLeft R M) =
      ((contractLeft A M') ∘ₗ e.toLinearMap).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext S (TensorProduct.mk R A (Module.Dual R M ⊗[R] M) 1)
      (Algebra.linearMap R A)
    rw [IsLocalizedModule.map_comp]
    refine TensorProduct.ext' fun x m => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
      contractLeft_apply, LinearMap.coe_restrictScalars, TensorProduct.mk_apply,
      LinearEquiv.coe_coe, e, LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul, eD, eM,
      IsBaseChange.equiv_tmul, one_smul, hd]
  rw [key]
  exact Module.Invertible.bijective.comp e.bijective

/-- A module that is invertible after localizing at each element of a spanning set is
invertible. -/
theorem Module.Invertible.of_isLocalizedModule_of_span_eq_top
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (s : Set R) (hs : Ideal.span s = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ (g : s), AddCommGroup (Mₚ g)] [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type*} [∀ (g : s), CommRing (Rₚ g)] [∀ (g : s), Algebra R (Rₚ g)]
    [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (ϕ : ∀ (g : s), M →ₗ[R] Mₚ g)
    [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (h : ∀ (g : s), Module.Invertible (Rₚ g) (Mₚ g)) :
    Module.Invertible R M := by
  have hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Rₚ := Rₚ) ϕ
      (fun g => by have := h g; exact Module.finitePresentation_of_projective (Rₚ g) (Mₚ g))
  refine ⟨bijective_of_isLocalized_span s hs (fun g => Rₚ g ⊗[R] (Module.Dual R M ⊗[R] M))
    (fun g => TensorProduct.mk R (Rₚ g) (Module.Dual R M ⊗[R] M) 1) (fun g => Rₚ g)
    (fun g => Algebra.linearMap R (Rₚ g)) (contractLeft R M) (fun g => ?_)⟩
  have := h g
  exact invLocal_bijective_map_contractLeft (Submonoid.powers g.val) (Rₚ g) (ϕ g)

/-- `Fin k`-indexed version of `Module.Invertible.of_isLocalizedModule_of_span_eq_top`. -/
theorem Module.Invertible.of_isLocalizedModule_of_span_range_eq_top
    {B : Type u} [CommRing B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (N : Type u) [AddCommGroup N] [Module B N]
    (M : Fin k → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)]
    (R : Fin k → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra B (R i)]
    [∀ i, IsLocalization.Away (f i) (R i)]
    [∀ i, Module (R i) (M i)] [∀ i, IsScalarTower B (R i) (M i)]
    (π : ∀ i, N →ₗ[B] M i) (hπ : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (π i))
    (h : ∀ i, Module.Invertible (R i) (M i)) :
    Module.Invertible B N := by
  classical
  have hpre : ∀ g : ↥(Set.range f), ∃ i : Fin k, f i = g := fun g => g.2
  choose idx hidx using hpre
  have : ∀ g : ↥(Set.range f), IsLocalization.Away (g : B) (R (idx g)) := fun g => by
    rw [← hidx g]; infer_instance
  have : ∀ g : ↥(Set.range f), IsLocalizedModule (Submonoid.powers (g : B)) (π (idx g)) :=
    fun g => by rw [← hidx g]; exact hπ (idx g)
  exact Module.Invertible.of_isLocalizedModule_of_span_eq_top (Set.range f) hf
    (Mₚ := fun g => M (idx g)) (Rₚ := fun g => R (idx g)) (fun g => π (idx g))
    (fun g => h (idx g))

private theorem morDesc_exists_sum_mul_pow_eq_one {B : Type*} [CommRing B] {k : ℕ}
    (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤) (n : Fin k → ℕ) :
    ∃ c : Fin k → B, ∑ i, c i * f i ^ n i = 1 := by
  classical
  let m : ℕ := Finset.univ.sup n
  have htop : Ideal.span (Set.range fun i => f i ^ m) = ⊤ := by
    have := Ideal.span_pow_eq_top (Set.range f) hf m
    rwa [← Set.range_comp] at this
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1
    (htop.symm ▸ Submodule.mem_top : (1 : B) ∈ Ideal.span (Set.range fun i => f i ^ m))
  refine ⟨fun i => c i * f i ^ (m - n i), ?_⟩
  rw [← hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← zarGlue_pow_sup_eq (f i) n i]

/-- Morphisms into a glued module are determined by compatible morphisms to the charts. -/
theorem IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top
    {B : Type u} [CommRing B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (M : Fin k → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)]
    (M₂ : Fin k → Fin k → Type u) [∀ i j, AddCommGroup (M₂ i j)] [∀ i j, Module B (M₂ i j)]
    (ρl : ∀ i j, M i →ₗ[B] M₂ i j) (ρr : ∀ i j, M j →ₗ[B] M₂ i j)
    (hρr : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr i j))
    (N : Type u) [AddCommGroup N] [Module B N] (π : ∀ i, N →ₗ[B] M i)
    (hπ : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (π i))
    (hπc : ∀ i j, ρl i j ∘ₗ π i = ρr i j ∘ₗ π j)
    (T : Type u) [AddCommGroup T] [Module B T] (g : ∀ i, T →ₗ[B] M i)
    (hg : ∀ i j, ρl i j ∘ₗ g i = ρr i j ∘ₗ g j) :
    ∃! G : T →ₗ[B] N, ∀ i, π i ∘ₗ G = g i := by
  classical
  have hinj : ∀ n : N, (∀ i, π i n = 0) → n = 0 := by
    intro n hn
    have h1 : ∀ i, ∃ a : ℕ, f i ^ a • n = 0 := by
      intro i
      have : π i n = π i 0 := by rw [hn i, map_zero]
      obtain ⟨c, hc⟩ := (hπ i).exists_of_eq this
      obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).1 c.2
      exact ⟨a, by rw [Submonoid.smul_def, Submonoid.smul_def, ← ha, smul_zero] at hc; exact hc⟩
    choose a ha using h1
    obtain ⟨c, hc⟩ := morDesc_exists_sum_mul_pow_eq_one f hf a
    calc n = (∑ i, c i * f i ^ a i) • n := by rw [hc, one_smul]
      _ = ∑ i, c i • (f i ^ a i • n) := by rw [Finset.sum_smul]; simp only [mul_smul]
      _ = 0 := by simp only [ha, smul_zero, Finset.sum_const_zero]
  have hexists : ∀ m : ∀ i, M i, (∀ i j, ρl i j (m i) = ρr i j (m j)) →
      ∃ n : N, ∀ i, π i n = m i := by
    intro m hm
    have h1 : ∀ i, ∃ (p : N × ℕ), ∀ j, π j p.1 = f i ^ p.2 • m j := by
      intro i
      obtain ⟨⟨n₀, s⟩, hs⟩ := (hπ i).surj (m i)
      obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
      have hs' : π i n₀ = f i ^ a • m i := by rw [← hs, Submonoid.smul_def, ← ha]
      have h2 : ∀ j, ∃ b : ℕ, f i ^ b • π j n₀ = f i ^ b • (f i ^ a • m j) := by
        intro j
        have : ρr i j (π j n₀) = ρr i j (f i ^ a • m j) := by
          rw [← LinearMap.comp_apply, ← hπc, LinearMap.comp_apply, hs', map_smul, map_smul,
            hm i j]
        obtain ⟨c, hc⟩ := (hρr i j).exists_of_eq this
        obtain ⟨b, hb⟩ := (Submonoid.mem_powers_iff _ _).1 c.2
        exact ⟨b, by rw [Submonoid.smul_def, Submonoid.smul_def, ← hb] at hc; exact hc⟩
      choose b hb using h2
      let bm : ℕ := Finset.univ.sup b
      refine ⟨(f i ^ bm • n₀, bm + a), fun j => ?_⟩
      rw [map_smul, zarGlue_pow_sup_eq (f i) b j, mul_smul, hb j, ← mul_smul, ← mul_smul,
        ← zarGlue_pow_sup_eq (f i) b j, ← pow_add]
    choose p hp using h1
    obtain ⟨c, hc⟩ := morDesc_exists_sum_mul_pow_eq_one f hf (fun i => (p i).2)
    refine ⟨∑ i, c i • (p i).1, fun j => ?_⟩
    rw [map_sum]
    simp only [map_smul, hp]
    calc ∑ i, c i • (f i ^ (p i).2 • m j) = (∑ i, c i * f i ^ (p i).2) • m j := by
          rw [Finset.sum_smul]; simp only [mul_smul]
      _ = m j := by rw [hc, one_smul]
  choose lift hlift using hexists
  have hgc : ∀ (t : T) i j, ρl i j (g i t) = ρr i j (g j t) := fun t i j => by
    rw [← LinearMap.comp_apply, hg, LinearMap.comp_apply]
  let Gfun : T → N := fun t => lift (fun i => g i t) (hgc t)
  have hG : ∀ t i, π i (Gfun t) = g i t := fun t i => hlift _ _ i
  have hadd : ∀ t t', Gfun (t + t') = Gfun t + Gfun t' := by
    intro t t'
    rw [← sub_eq_zero]
    apply hinj
    intro i
    rw [map_sub, map_add, hG, hG, hG, map_add, sub_self]
  have hsmul : ∀ (r : B) t, Gfun (r • t) = r • Gfun t := by
    intro r t
    rw [← sub_eq_zero]
    apply hinj
    intro i
    rw [map_sub, map_smul, hG, hG, map_smul, sub_self]
  let G : T →ₗ[B] N := { toFun := Gfun, map_add' := hadd, map_smul' := hsmul }
  refine ⟨G, fun i => LinearMap.ext fun t => hG t i, fun G' hG' => ?_⟩
  apply LinearMap.ext
  intro t
  rw [← sub_eq_zero]
  apply hinj
  intro i
  rw [map_sub, sub_eq_zero, ← LinearMap.comp_apply, hG' i]
  exact (hG t i).symm

private theorem glueStalk_mk_mk_eq_of_forall_prime {B : Type*} [CommRing B] {T : Type*}
    [AddCommGroup T] [Module B T] (f g : B) (t t' : T) (n m : ℕ)
    (h : ∀ y : PrimeSpectrum B, f ∉ y.asIdeal → g ∉ y.asIdeal →
      ∃ u : B, u ∉ y.asIdeal ∧ u • (g ^ m • t) = u • (f ^ n • t')) :
    (LocalizedModule.mk (LocalizedModule.mk t (1 : Submonoid.powers g)) ⟨f ^ n, n, rfl⟩ :
        LocalizedModule (Submonoid.powers f) (LocalizedModule (Submonoid.powers g) T)) =
      LocalizedModule.mk (LocalizedModule.mk t' (⟨g ^ m, m, rfl⟩ : Submonoid.powers g)) 1 := by
  classical
  let δ : T := g ^ m • t - f ^ n • t'
  let I : Ideal B := (Submodule.span B {δ}).annihilator
  have hI : ∀ b : B, b ∈ I ↔ b • δ = 0 := fun b => Submodule.mem_annihilator_span_singleton δ b
  have hrad : f * g ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hIJ, hJ⟩
    by_contra hfg
    have hf : f ∉ J := fun hf => hfg (Ideal.mul_mem_right g J hf)
    have hg : g ∉ J := fun hg => hfg (Ideal.mul_mem_left J f hg)
    obtain ⟨u, hu, hut⟩ := h ⟨J, hJ⟩ hf hg
    exact hu (hIJ ((hI u).2 (by rw [smul_sub, sub_eq_zero]; exact hut)))
  obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.1 hrad
  have hkill : ((f * g) ^ N) • (g ^ m • t - f ^ n • t') = 0 := (hI _).1 hN
  have hkill' : (g ^ N * (g ^ m * f ^ N)) • t = (g ^ N * (f ^ N * f ^ n)) • t' := by
    rw [smul_sub, sub_eq_zero, mul_pow, smul_smul, smul_smul] at hkill
    rw [show g ^ N * (g ^ m * f ^ N) = f ^ N * g ^ N * g ^ m by ring,
      show g ^ N * (f ^ N * f ^ n) = f ^ N * g ^ N * f ^ n by ring]
    exact hkill
  rw [LocalizedModule.mk_eq]
  refine ⟨⟨f ^ N, N, rfl⟩, ?_⟩
  rw [one_smul, Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def,
    LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk,
    LocalizedModule.mk_eq]
  refine ⟨⟨g ^ N, N, rfl⟩, ?_⟩
  simp only [Submonoid.smul_def, one_smul, smul_smul]
  exact hkill'

private theorem glueStalk_exists_rep {B : Type*} [CommRing B] {T : Type*} [AddCommGroup T]
    [Module B T] (f : B) (q : LocalizedModule (Submonoid.powers f) T) :
    ∃ (t : T) (n : ℕ),
      q = LocalizedModule.mk t (⟨f ^ n, n, rfl⟩ : Submonoid.powers f) := by
  induction q using LocalizedModule.induction_on with
  | h t s =>
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
    exact ⟨t, n, by congr 1; exact Subtype.ext hn.symm⟩

/-- Stalkwise maps that are locally induced by charts glue to a global linear map. -/
theorem LinearMap.exists_forall_localizedModule_mk_eq_of_forall_exists_chart
    {B : Type u} [CommRing B] {T T' : Type u} [AddCommGroup T] [Module B T] [AddCommGroup T']
    [Module B T']
    (φ : ∀ x : PrimeSpectrum B,
      LocalizedModule x.asIdeal.primeCompl T' →ₗ[B] LocalizedModule x.asIdeal.primeCompl T)
    (hφ : ∀ x : PrimeSpectrum B, ∃ (f : B) (_ : f ∉ x.asIdeal)
        (Φ : T' →ₗ[B] LocalizedModule (Submonoid.powers f) T),
        ∀ (y : PrimeSpectrum B), f ∉ y.asIdeal → ∀ (a : T') (t : T) (n : ℕ),
          Φ a = LocalizedModule.mk t ⟨f ^ n, Submonoid.mem_powers_iff _ _ |>.mpr ⟨n, rfl⟩⟩ →
            ∀ s : y.asIdeal.primeCompl, (s : B) = f ^ n →
              φ y (LocalizedModule.mk a 1) = LocalizedModule.mk t s) :
    ∃ τ : T' →ₗ[B] T, ∀ (x : PrimeSpectrum B) (a : T'),
      LocalizedModule.mk (τ a) 1 = φ x (LocalizedModule.mk a 1) := by
  classical
  choose f hf Φ hΦ using hφ
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    by_contra h1
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h1
    exact hf ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  have h1 : (1 : B) ∈ Ideal.span (Set.range f) := by rw [hspan]; trivial
  obtain ⟨S0, hS0sub, h1S0⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hpre : ∀ s : S0, ∃ x : PrimeSpectrum B, f x = s := fun s => hS0sub s.2
  choose idx hidx using hpre
  let k := S0.card
  let e : Fin k → PrimeSpectrum B := fun i => idx (S0.equivFin.symm i)
  let fe : Fin k → B := fun i => f (e i)
  have he : Ideal.span (Set.range fe) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have hrange : Set.range fe = (S0 : Set B) := by
      ext b
      constructor
      · rintro ⟨i, rfl⟩
        change f (idx (S0.equivFin.symm i)) ∈ (S0 : Set B)
        rw [hidx]; exact (S0.equivFin.symm i).2
      · intro hb; exact ⟨S0.equivFin ⟨b, hb⟩, by simp [fe, e, hidx]⟩
    rw [hrange]; exact h1S0
  let M : Fin k → Type u := fun i => LocalizedModule (Submonoid.powers (fe i)) T
  let M₂ : Fin k → Fin k → Type u := fun i j =>
    LocalizedModule (Submonoid.powers (fe i)) (LocalizedModule (Submonoid.powers (fe j)) T)
  let π : ∀ i, T →ₗ[B] M i := fun i => LocalizedModule.mkLinearMap (Submonoid.powers (fe i)) T
  let ρr : ∀ i j, M j →ₗ[B] M₂ i j := fun i j =>
    LocalizedModule.mkLinearMap (Submonoid.powers (fe i))
      (LocalizedModule (Submonoid.powers (fe j)) T)
  let ρl : ∀ i j, M i →ₗ[B] M₂ i j := fun i j =>
    ((LocalizedModule.map (Submonoid.powers (fe i)))
      (LocalizedModule.mkLinearMap (Submonoid.powers (fe j)) T)).restrictScalars B
  have hρl : ∀ i j (t : T) (s : Submonoid.powers (fe i)),
      ρl i j (LocalizedModule.mk t s) = LocalizedModule.mk (LocalizedModule.mk t 1) s := by
    intro i j t s
    change ((LocalizedModule.map (Submonoid.powers (fe i)))
      (LocalizedModule.mkLinearMap (Submonoid.powers (fe j)) T)) (LocalizedModule.mk t s) = _
    rw [LocalizedModule.map_mk]; rfl
  have hπc : ∀ i j, ρl i j ∘ₗ π i = ρr i j ∘ₗ π j := by
    intro i j; ext t
    change ρl i j (LocalizedModule.mk t 1) = LocalizedModule.mk (LocalizedModule.mk t 1) 1
    rw [hρl]
  let g : ∀ i, T' →ₗ[B] M i := fun i => Φ (e i)
  have hg : ∀ i j, ρl i j ∘ₗ g i = ρr i j ∘ₗ g j := by
    intro i j; ext a
    obtain ⟨t, n, ht⟩ := glueStalk_exists_rep (fe i) (Φ (e i) a)
    obtain ⟨t', m, ht'⟩ := glueStalk_exists_rep (fe j) (Φ (e j) a)
    change ρl i j (Φ (e i) a) = LocalizedModule.mk (Φ (e j) a) 1
    rw [ht, ht', hρl]
    apply glueStalk_mk_mk_eq_of_forall_prime
    intro y hyi hyj
    have hsi : fe i ^ n ∈ y.asIdeal.primeCompl := fun hh => hyi (y.isPrime.mem_of_pow_mem n hh)
    have hsj : fe j ^ m ∈ y.asIdeal.primeCompl := fun hh => hyj (y.isPrime.mem_of_pow_mem m hh)
    have e1 := hΦ (e i) y hyi a t n ht ⟨fe i ^ n, hsi⟩ rfl
    have e2 := hΦ (e j) y hyj a t' m ht' ⟨fe j ^ m, hsj⟩ rfl
    rw [e1, LocalizedModule.mk_eq] at e2
    obtain ⟨u, hu⟩ := e2
    refine ⟨u, u.2, ?_⟩
    simpa only [Submonoid.smul_def] using hu
  obtain ⟨G, hG, -⟩ := IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top fe he M M₂
    ρl ρr (fun i j => inferInstance) T π (fun i => inferInstance) hπc T' g hg
  refine ⟨G, fun x a => ?_⟩
  have hex : ∃ i, fe i ∉ x.asIdeal := by
    by_contra hne
    push Not at hne
    have : Ideal.span (Set.range fe) ≤ x.asIdeal := Ideal.span_le.2 (Set.range_subset_iff.2 hne)
    rw [he, top_le_iff] at this
    exact x.isPrime.ne_top this
  obtain ⟨i, hi⟩ := hex
  have hGi : Φ (e i) a =
      LocalizedModule.mk (G a) (⟨fe i ^ 0, 0, rfl⟩ : Submonoid.powers (fe i)) := by
    have := LinearMap.congr_fun (hG i) a
    rw [LinearMap.comp_apply] at this
    change LocalizedModule.mk (G a) 1 = Φ (e i) a at this
    rw [← this]; congr 1; exact Subtype.ext (pow_zero _).symm
  have := hΦ (e i) x hi a (G a) 0 hGi 1 (by simp)
  exact this.symm

end
