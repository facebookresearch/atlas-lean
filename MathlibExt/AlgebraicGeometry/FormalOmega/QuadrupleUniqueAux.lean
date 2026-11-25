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
for `<Y>` in the list below, where `CF_` abbreviates `CerednikDrinfeld_FormalOmega_`:
`CF_DrinfeldDatum_IsQuadrupleOf_N_eq_of_isQuadrupleOf`
`CF_DrinfeldDatum_IsQuadrupleOf_isIsomorphic_of_N_eq`
`CF_DrinfeldDatum_IsQuadrupleOf_of_isIsomorphic`
`CF_DrinfeldDatum_IsQuadrupleOf_isQuadrupleOf_iff_isIsomorphic`
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

public import MathlibExt.AlgebraicGeometry.FormalOmega.DrinfeldDatum
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.LocalRing.Module
import MathlibExt.AlgebraicGeometry.FormalOmega.InvertibleModule

/-!
# Gluing stalkwise isomorphisms of invertible modules

Auxiliary results for `QuadrupleUnique`: two families of surjections from the stalkwise base
changes of a family of lattices onto the stalks of two invertible modules, with equal kernels and
continuous (locally constant on basic opens) values, come from a global isomorphism of the
invertible modules.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace CerednikDrinfeld.FormalOmega.QuadrupleUniqueAux

section QuotIso

variable {R M N N' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup N'] [Module R N']

private def quotIso (u : M →ₗ[R] N) (u' : M →ₗ[R] N') (hu : Function.Surjective u)
    (hu' : Function.Surjective u') (hker : LinearMap.ker u = LinearMap.ker u') : N ≃ₗ[R] N' :=
  (u.quotKerEquivOfSurjective hu).symm ≪≫ₗ (Submodule.quotEquivOfEq _ _ hker) ≪≫ₗ
    (u'.quotKerEquivOfSurjective hu')

private theorem quotIso_apply (u : M →ₗ[R] N) (u' : M →ₗ[R] N') (hu : Function.Surjective u)
    (hu' : Function.Surjective u') (hker : LinearMap.ker u = LinearMap.ker u') (m : M) :
    quotIso u u' hu hu' hker (u m) = u' m := by
  simp only [quotIso, LinearEquiv.trans_apply]
  have h1 : (u.quotKerEquivOfSurjective hu).symm (u m) = Submodule.Quotient.mk m := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  rw [h1]
  rfl

end QuotIso

section Generic

variable {B : Type*} [CommRing B]

private theorem exists_notMem_forall_exists_pow_smul_eq {T : Type*} [AddCommGroup T] [Module B T]
    [Module.Finite B T] (x : PrimeSpectrum B) (t : T)
    (ht : ∀ m : T, ∃ (b : B) (s : B), s ∉ x.asIdeal ∧ s • m = b • t) :
    ∃ g : B, g ∉ x.asIdeal ∧ ∀ m : T, ∃ (b : B) (n : ℕ), g ^ n • m = b • t := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := B) (M := T)
  choose b s hs hsm using ht
  refine ⟨∏ m ∈ S, s m, ?_, ?_⟩
  · have : (∏ m ∈ S, s m) ∈ x.asIdeal.primeCompl :=
      Submonoid.prod_mem _ fun m _ => show s m ∈ x.asIdeal.primeCompl from hs m
    exact this
  · intro m
    have hm : m ∈ Submodule.span B (S : Set T) := by rw [hS]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
    · intro m' hm'
      refine ⟨(∏ m'' ∈ S.erase m', s m'') * b m', 1, ?_⟩
      rw [pow_one, ← Finset.prod_erase_mul S (fun m'' => s m'') hm', mul_smul, hsm m',
        ← mul_smul]
    · exact ⟨0, 0, by simp⟩
    · rintro m₁ m₂ _ _ ⟨b₁, n₁, h₁⟩ ⟨b₂, n₂, h₂⟩
      refine ⟨(∏ m ∈ S, s m) ^ n₂ * b₁ + (∏ m ∈ S, s m) ^ n₁ * b₂, n₁ + n₂, ?_⟩
      rw [smul_add, pow_add, mul_smul, mul_smul,
        smul_comm ((∏ m ∈ S, s m) ^ n₁) ((∏ m ∈ S, s m) ^ n₂) m₁, h₁, h₂, smul_smul, smul_smul,
        ← add_smul]
    · rintro c m' _ ⟨b₁, n₁, h₁⟩
      exact ⟨c * b₁, n₁, by rw [smul_comm, h₁, mul_smul]⟩

private theorem exists_isUnit_of_span_eq_top {R : Type*} [CommRing R] [IsLocalRing R] {ι : Type*}
    (a : ι → R) (h : Ideal.span (Set.range a) = ⊤) : ∃ i, IsUnit (a i) := by
  by_contra hne
  push Not at hne
  have : Ideal.span (Set.range a) ≤ IsLocalRing.maximalIdeal R := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).mpr (hne i)
  rw [h] at this
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp this)

private theorem notMem_left {y : PrimeSpectrum B} {a b : B} (h : a * b ∉ y.asIdeal) :
    a ∉ y.asIdeal :=
  fun ha => h (y.asIdeal.mul_mem_right b ha)

private theorem notMem_right {y : PrimeSpectrum B} {a b : B} (h : a * b ∉ y.asIdeal) :
    b ∉ y.asIdeal :=
  fun hb => h (y.asIdeal.mul_mem_left a hb)

private theorem mul_notMem {y : PrimeSpectrum B} {a b : B} (ha : a ∉ y.asIdeal)
    (hb : b ∉ y.asIdeal) : a * b ∉ y.asIdeal := fun h => (y.isPrime.mem_or_mem h).elim ha hb

private theorem pow_notMem {y : PrimeSpectrum B} {a : B} (h : a ∉ y.asIdeal) (n : ℕ) :
    a ^ n ∉ y.asIdeal :=
  fun ha => h (y.isPrime.mem_of_pow_mem n ha)

private theorem exists_eq_mk_pow (h : B) (r : Localization (Submonoid.powers h)) :
    ∃ (b : B) (k : ℕ),
      r = Localization.mk b ⟨h ^ k, Submonoid.mem_powers_iff _ _ |>.mpr ⟨k, rfl⟩⟩ := by
  induction r using Localization.induction_on with
  | H p =>
    obtain ⟨b, s⟩ := p
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    exact ⟨b, k, by congr 1; exact Subtype.ext hk.symm⟩

end Generic

section Core

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  {B : Type} [CommRing B] [Algebra 𝒪 B]

private theorem mem_span_image_tmul {L : FullLattice 𝒪 K} (x : PrimeSpectrum B) {T : Type}
    [AddCommGroup T] [Module B T]
    (u : latticeBaseChange 𝒪 K (locRing B x) L →ₗ[locRing B x] stalk B x T)
    (w : latticeBaseChange 𝒪 K (locRing B x) L) :
    u w ∈ Submodule.span (locRing B x)
      (Set.range fun v : ↥L.1 => u ((1 : locRing B x) ⊗ₜ[𝒪] v)) := by
  induction w using TensorProduct.inductionOn with
  | tmul b v =>
    have : b ⊗ₜ[𝒪] v = b • ((1 : locRing B x) ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
  | add w₁ w₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂

private theorem exists_generator {L : FullLattice 𝒪 K} (x : PrimeSpectrum B) {T : Type}
    [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (u : latticeBaseChange 𝒪 K (locRing B x) L →ₗ[locRing B x] stalk B x T)
    (hu : Function.Surjective u) :
    ∃ v₀ : ↥L.1, ∀ m : stalk B x T, ∃ r : locRing B x,
      m = r • u ((1 : locRing B x) ⊗ₜ[𝒪] v₀) := by
  have : Module.Free (locRing B x) (stalk B x T) := Module.free_of_flat_of_isLocalRing
  obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := locRing B x)
    (M := stalk B x T)).mp this
  have hspan :
      Ideal.span (Set.range fun v : ↥L.1 => e (u ((1 : locRing B x) ⊗ₜ[𝒪] v))) = ⊤ := by
    rw [eq_top_iff]
    rintro r -
    obtain ⟨w, hw⟩ := hu (e.symm r)
    have hmem := mem_span_image_tmul x u w
    rw [hw] at hmem
    have := Submodule.mem_map_of_mem (f := e.toLinearMap) hmem
    rw [Submodule.map_span, ← Set.range_comp] at this
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    exact this
  obtain ⟨v₀, hv₀⟩ := exists_isUnit_of_span_eq_top _ hspan
  refine ⟨v₀, fun m => ⟨e m * (hv₀.unit⁻¹ : (locRing B x)ˣ), ?_⟩⟩
  apply e.injective
  rw [map_smul, smul_eq_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]

omit [Algebra 𝒪 K] in
private theorem gen_of_stalk {M : Type} [AddCommGroup M] [Module B M] (x : PrimeSpectrum B)
    (a : M) (e : B) (he : e ∉ x.asIdeal)
    (hgen : ∀ m' : stalk B x M, ∃ r : locRing B x, m' = r • LocalizedModule.mk a ⟨e, he⟩) :
    ∀ m : M, ∃ (b : B) (s : B), s ∉ x.asIdeal ∧ s • m = b • a := by
  intro m
  obtain ⟨r, hr⟩ := hgen (LocalizedModule.mk m 1)
  revert hr
  induction r using Localization.induction_on with
  | H p =>
    obtain ⟨c, s₁⟩ := p
    intro hr
    rw [LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq] at hr
    obtain ⟨w, hw⟩ := hr
    refine ⟨(w : B) * c, (w : B) * (s₁ : B) * e, ?_, ?_⟩
    · exact mul_notMem (mul_notMem w.2 s₁.2) he
    · simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, smul_smul] at hw
      rw [mul_assoc]
      exact hw

omit [Algebra 𝒪 K] in
private theorem pow_smul_of_mul {M : Type} [AddCommGroup M] [Module B M] {g c : B} {m a : M}
    {b : B} {n : ℕ} (h : g ^ n • m = b • a) : (g * c) ^ n • m = (c ^ n * b) • a := by
  rw [mul_pow, mul_comm, mul_smul, h, smul_smul]

omit [Algebra 𝒪 K] in
private theorem toSpanSingleton_surjective {M : Type} [AddCommGroup M] [Module B M] (h : B)
    (a : M) (H : ∀ m : M, ∃ (b : B) (n : ℕ), h ^ n • m = b • a) :
    Function.Surjective (LinearMap.toSpanSingleton (Localization (Submonoid.powers h))
      (LocalizedModule (Submonoid.powers h) M) (LocalizedModule.mk a 1)) := by
  intro w
  induction w using LocalizedModule.induction_on with
  | h m s =>
    obtain ⟨b, n, hb⟩ := H m
    have hn : h ^ n ∈ Submonoid.powers h := (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩
    refine ⟨Localization.mk b (s * ⟨h ^ n, hn⟩), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, mul_one, ← hb,
      ← Submonoid.smul_def (⟨h ^ n, hn⟩ : Submonoid.powers h), mul_comm,
      LocalizedModule.mk_cancel_common_left]

private theorem exists_chart
    (N : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K)) (full : ∀ x, Submodule.IsFullLattice K (N x))
    (T T' : Type) [AddCommGroup T] [Module B T] [AddCommGroup T'] [Module B T']
    [Module.Invertible B T] [Module.Invertible B T']
    (u : ∀ x : PrimeSpectrum B,
      latticeBaseChange 𝒪 K (locRing B x) ⟨N x, full x⟩ →ₗ[locRing B x] stalk B x T)
    (u' : ∀ x : PrimeSpectrum B,
      latticeBaseChange 𝒪 K (locRing B x) ⟨N x, full x⟩ →ₗ[locRing B x] stalk B x T')
    (hu' : ∀ x, Function.Surjective (u' x))
    (φ : ∀ x : PrimeSpectrum B, stalk B x T' ≃ₗ[locRing B x] stalk B x T)
    (hφ : ∀ x w, φ x (u' x w) = u x w)
    (hc : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K), v ∈ N x → ∃ (f : B) (t : T), f ∉ x.asIdeal ∧
      ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal), ∃ hv : v ∈ N y,
        u y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(N y))) = LocalizedModule.mk t ⟨f, hy⟩)
    (hc' : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K), v ∈ N x → ∃ (f : B) (t : T'),
      f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal), ∃ hv : v ∈ N y,
        u' y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(N y))) = LocalizedModule.mk t ⟨f, hy⟩)
    (x : PrimeSpectrum B) :
    ∃ (f : B) (_ : f ∉ x.asIdeal) (Φ : T' →ₗ[B] LocalizedModule (Submonoid.powers f) T),
      ∀ (y : PrimeSpectrum B), f ∉ y.asIdeal → ∀ (a : T') (t : T) (n : ℕ),
        Φ a = LocalizedModule.mk t ⟨f ^ n, Submonoid.mem_powers_iff _ _ |>.mpr ⟨n, rfl⟩⟩ →
          ∀ s : y.asIdeal.primeCompl, (s : B) = f ^ n →
            ((φ y).toLinearMap.restrictScalars B) (LocalizedModule.mk a 1) =
              LocalizedModule.mk t s := by
  classical
  obtain ⟨v₀, hv₀⟩ := exists_generator x (u' x) (hu' x)
  obtain ⟨f, t, hf, H⟩ := hc x v₀ v₀.2
  obtain ⟨f', t', hf', H'⟩ := hc' x v₀ v₀.2
  have Ha : ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal) (hy' : f' ∉ y.asIdeal),
      u y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨(v₀ : Fin 2 → K), (H y hy).1⟩ : ↥(N y))) =
        LocalizedModule.mk (f' • t) ⟨f * f', mul_notMem hy hy'⟩ := by
    intro y hy hy'
    rw [(H y hy).2, LocalizedModule.mk_eq]
    exact ⟨1, by simp only [one_smul, Submonoid.smul_def, smul_smul]⟩
  have Ha' : ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal) (hy' : f' ∉ y.asIdeal),
      u' y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨(v₀ : Fin 2 → K), (H y hy).1⟩ : ↥(N y))) =
        LocalizedModule.mk (f • t') ⟨f * f', mul_notMem hy hy'⟩ := by
    intro y hy hy'
    have := (H' y hy').2
    rw [show (⟨(v₀ : Fin 2 → K), (H' y hy').1⟩ : ↥(N y)) =
      ⟨(v₀ : Fin 2 → K), (H y hy).1⟩ from rfl] at this
    rw [this, LocalizedModule.mk_eq]
    exact ⟨1, by simp only [one_smul, Submonoid.smul_def, smul_smul]; ring_nf⟩
  have Hφa : ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal) (hy' : f' ∉ y.asIdeal),
      φ y (LocalizedModule.mk (f • t') 1) = LocalizedModule.mk (f' • t) 1 := by
    intro y hy hy'
    have hs : f * f' ∉ y.asIdeal := mul_notMem hy hy'
    have k1 : (LocalizedModule.mk (f • t') 1 : stalk B y T') =
        ((f * f' : B)) • LocalizedModule.mk (f • t') ⟨f * f', hs⟩ := by
      rw [LocalizedModule.smul'_mk, ← Submonoid.smul_def (⟨f * f', hs⟩ : y.asIdeal.primeCompl),
        LocalizedModule.mk_cancel]
    have k2 : (LocalizedModule.mk (f' • t) 1 : stalk B y T) =
        ((f * f' : B)) • LocalizedModule.mk (f' • t) ⟨f * f', hs⟩ := by
      rw [LocalizedModule.smul'_mk, ← Submonoid.smul_def (⟨f * f', hs⟩ : y.asIdeal.primeCompl),
        LocalizedModule.mk_cancel]
    rw [k1, ← algebraMap_smul (locRing B y) (f * f'), map_smul, algebraMap_smul,
      ← Ha' y hy hy', hφ, Ha y hy hy', ← k2]
  have hx : f * f' ∉ x.asIdeal := mul_notMem hf hf'
  have hvx : u' x ((1 : locRing B x) ⊗ₜ[𝒪] v₀) =
      LocalizedModule.mk (f • t') ⟨f * f', hx⟩ := Ha' x hf hf'
  have gen' : ∀ m : T', ∃ (b : B) (s : B), s ∉ x.asIdeal ∧ s • m = b • (f • t') :=
    gen_of_stalk x (f • t') (f * f') hx fun m' => by
      obtain ⟨r, hr⟩ := hv₀ m'; exact ⟨r, by rw [hr, hvx]⟩
  have gen : ∀ m : T, ∃ (b : B) (s : B), s ∉ x.asIdeal ∧ s • m = b • (f' • t) :=
    gen_of_stalk x (f' • t) (f * f') hx fun m' => by
      obtain ⟨r, hr⟩ := hv₀ ((φ x).symm m')
      refine ⟨r, ?_⟩
      have hux : u x ((1 : locRing B x) ⊗ₜ[𝒪] v₀) =
          LocalizedModule.mk (f' • t) ⟨f * f', hx⟩ := Ha x hf hf'
      have := congrArg (φ x) hr
      rw [LinearEquiv.apply_symm_apply, map_smul, hφ, hux] at this
      exact this
  obtain ⟨g, hg, HG⟩ := exists_notMem_forall_exists_pow_smul_eq x (f' • t) gen
  obtain ⟨g', hg', HG'⟩ := exists_notMem_forall_exists_pow_smul_eq x (f • t') gen'
  set h : B := f * f' * g * g' with hh_def
  have hh : h ∉ x.asIdeal := mul_notMem (mul_notMem hx hg) hg'
  have HH' : ∀ m : T', ∃ (b : B) (n : ℕ), h ^ n • m = b • (f • t') := fun m => by
    obtain ⟨b, n, hb⟩ := HG' m
    refine ⟨(f * f' * g) ^ n * b, n, ?_⟩
    rw [show h = g' * (f * f' * g) from by rw [hh_def]; ring]
    exact pow_smul_of_mul hb
  let S := Submonoid.powers h
  let ψ := LinearMap.toSpanSingleton (Localization S) (LocalizedModule S T)
    (LocalizedModule.mk (f' • t) 1)
  let ψ' := LinearMap.toSpanSingleton (Localization S) (LocalizedModule S T')
    (LocalizedModule.mk (f • t') 1)
  have hbij' : Function.Bijective ψ' :=
    Module.Invertible.bijective_of_surjective (toSpanSingleton_surjective h _ HH')
  let e' := LinearEquiv.ofBijective ψ' hbij'
  refine ⟨h, hh, (ψ.restrictScalars B) ∘ₗ (e'.symm.toLinearMap.restrictScalars B) ∘ₗ
    LocalizedModule.mkLinearMap S T', ?_⟩
  intro y hy a₁ t₁ n hΦ s hs
  have hfy : f ∉ y.asIdeal := notMem_left (notMem_left (notMem_left hy))
  have hf'y : f' ∉ y.asIdeal := notMem_right (notMem_left (notMem_left hy))
  obtain ⟨b, k, hr⟩ := exists_eq_mk_pow h (e'.symm (LocalizedModule.mk a₁ 1))
  have e1 : ψ' (e'.symm (LocalizedModule.mk a₁ 1)) = LocalizedModule.mk a₁ 1 := by
    have := e'.apply_symm_apply (LocalizedModule.mk a₁ 1)
    rwa [LinearEquiv.ofBijective_apply] at this
  rw [hr, LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, mul_one,
    LocalizedModule.mk_eq] at e1
  obtain ⟨w₁, hw₁⟩ := e1
  have e2 : ψ (e'.symm (LocalizedModule.mk a₁ 1)) =
      LocalizedModule.mk t₁ ⟨h ^ n, Submonoid.mem_powers_iff _ _ |>.mpr ⟨n, rfl⟩⟩ := hΦ
  rw [hr, LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, mul_one,
    LocalizedModule.mk_eq] at e2
  obtain ⟨w₂, hw₂⟩ := e2
  obtain ⟨j₁, hj₁⟩ := (Submonoid.mem_powers_iff _ _).mp w₁.2
  obtain ⟨j₂, hj₂⟩ := (Submonoid.mem_powers_iff _ _).mp w₂.2
  simp only [Submonoid.smul_def, one_smul, ← hj₁] at hw₁
  simp only [Submonoid.smul_def, ← hj₂] at hw₂
  have hhk' : h ^ k ∈ y.asIdeal.primeCompl := pow_notMem hy k
  have step1 : (LocalizedModule.mk a₁ 1 : stalk B y T') =
      (Localization.mk b ⟨h ^ k, hhk'⟩ : locRing B y) • LocalizedModule.mk (f • t') 1 := by
    rw [LocalizedModule.mk_smul_mk, mul_one, LocalizedModule.mk_eq]
    refine ⟨⟨h ^ j₁, pow_notMem hy j₁⟩, ?_⟩
    simp only [Submonoid.smul_def, one_smul]
    exact hw₁.symm
  rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, step1, map_smul, Hφa y hfy hf'y,
    LocalizedModule.mk_smul_mk, mul_one, LocalizedModule.mk_eq]
  refine ⟨⟨h ^ j₂, pow_notMem hy j₂⟩, ?_⟩
  simp only [Submonoid.smul_def, hs]
  exact hw₂

/-- Two families of stalkwise surjections `u x`, `u' x` from the base changes of a family of full
lattices `N x` onto the stalks of invertible modules `T` and `T'`, with equal kernels and values
given locally on basic opens by global sections, are related by a global isomorphism
`τ : T' ≃ₗ[B] T`: `τ` localized at `x` carries `u' x` to `u x` for every point `x`. -/
theorem exists_linearEquiv_map_comp_eq
    (N : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K)) (full : ∀ x, Submodule.IsFullLattice K (N x))
    (T T' : Type) [AddCommGroup T] [Module B T] [AddCommGroup T'] [Module B T']
    [Module.Invertible B T] [Module.Invertible B T']
    (u : ∀ x : PrimeSpectrum B,
      latticeBaseChange 𝒪 K (locRing B x) ⟨N x, full x⟩ →ₗ[locRing B x] stalk B x T)
    (u' : ∀ x : PrimeSpectrum B,
      latticeBaseChange 𝒪 K (locRing B x) ⟨N x, full x⟩ →ₗ[locRing B x] stalk B x T')
    (hu : ∀ x, Function.Surjective (u x)) (hu' : ∀ x, Function.Surjective (u' x))
    (hker : ∀ x, LinearMap.ker (u' x) = LinearMap.ker (u x))
    (hc : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K), v ∈ N x → ∃ (f : B) (t : T), f ∉ x.asIdeal ∧
      ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal), ∃ hv : v ∈ N y,
        u y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(N y))) = LocalizedModule.mk t ⟨f, hy⟩)
    (hc' : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K), v ∈ N x → ∃ (f : B) (t : T'),
      f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal), ∃ hv : v ∈ N y,
        u' y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(N y))) = LocalizedModule.mk t ⟨f, hy⟩) :
    ∃ τ : T' ≃ₗ[B] T, ∀ (x : PrimeSpectrum B)
      (w : latticeBaseChange 𝒪 K (locRing B x) ⟨N x, full x⟩),
      LocalizedModule.map x.asIdeal.primeCompl τ.toLinearMap (u' x w) = u x w := by
  classical
  let φ : ∀ x : PrimeSpectrum B, stalk B x T' ≃ₗ[locRing B x] stalk B x T :=
    fun x => quotIso (u' x) (u x) (hu' x) (hu x) (hker x)
  have hφ : ∀ x w, φ x (u' x w) = u x w := fun x w => quotIso_apply _ _ _ _ _ w
  obtain ⟨τ₀, hτ₀⟩ := LinearMap.exists_forall_localizedModule_mk_eq_of_forall_exists_chart
    (fun x => (φ x).toLinearMap.restrictScalars B)
    (fun x => exists_chart N full T T' u u' hu' φ hφ hc hc' x)
  have hmap : ∀ (x : PrimeSpectrum B) (w' : stalk B x T'),
      LocalizedModule.map x.asIdeal.primeCompl τ₀ w' = φ x w' := by
    intro x w'
    induction w' using LocalizedModule.induction_on with
    | h a s =>
      have h1 : (LocalizedModule.mk a s : stalk B x T') =
          (Localization.mk 1 s) • LocalizedModule.mk a 1 := by
        rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
      rw [h1, map_smul, map_smul, LocalizedModule.map_mk]
      exact congrArg _ (hτ₀ x a)
  have hbij : Function.Bijective τ₀ := by
    refine bijective_of_localized_maximal τ₀ fun J hJ => ?_
    have := hmap ⟨J, hJ.isPrime⟩
    have heq : ⇑(LocalizedModule.map J.primeCompl τ₀) = ⇑(φ ⟨J, hJ.isPrime⟩) := funext this
    rw [heq]
    exact (φ ⟨J, hJ.isPrime⟩).bijective
  refine ⟨LinearEquiv.ofBijective τ₀ hbij, fun x w => ?_⟩
  have hτ : (LinearEquiv.ofBijective τ₀ hbij).toLinearMap = τ₀ := LinearMap.ext fun _ => rfl
  rw [hτ, hmap, hφ]

end Core

end CerednikDrinfeld.FormalOmega.QuadrupleUniqueAux

end
