/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_NumberField_PlaceTransport.lean`,
`Theorems/Thm_M4aHerbrand_subsingleton_ideleGaloisDescent.lean`,
`P2M/Sol/S_M4aHerbrand_subsingleton_ideleGaloisDescent.lean`
and
`P2M/Sol/S_AutomorphicForm_adelicHeight_sigmaAdelicAct.lean`
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

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-!
# Bicontinuous ring automorphisms of the adele ring

Let `L` be a number field and `φ` a ring automorphism of the adele ring of `L` such that `φ`
and `φ⁻¹` are continuous and `φ` restricts to a field automorphism `τ` on the diagonal copy
of `L`. Then `φ` moves the component at a place `v` to the component at the transported
place, and preserves the normalized absolute values of components:

* `NumberField.AdeleRing.norm_fst_map_comap`: `‖(φ a)_{v ∘ τ⁻¹}‖ = ‖a_v‖` at infinite places;
* `NumberField.AdeleRing.norm_snd_map_equivOfRingEquiv`: `‖(φ a)_{τ(w)}‖ = ‖a_w‖` at finite
  places.

The proof identifies the place components through the minimal idempotents of the adele ring,
whose images under `φ` are again minimal idempotents, and recognizes the place carrying the
image through the elements of `L` whose powers tend to zero there.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField Filter Topology

namespace NumberField.AdeleRing

section MinIdempotent

variable {A : Type*} [CommRing A]

private def IsMinIdempotent (e : A) : Prop :=
  IsIdempotentElem e ∧ e ≠ 0 ∧ ∀ f : A, IsIdempotentElem f → f * e = f → f ≠ 0 → f = e

private theorem IsMinIdempotent.map_ringEquiv {B : Type*} [CommRing B] (φ : A ≃+* B) {e : A}
    (he : IsMinIdempotent e) : IsMinIdempotent (φ e) := by
  obtain ⟨hid, hne, hmin⟩ := he
  refine ⟨?_, ?_, ?_⟩
  · change φ e * φ e = φ e
    rw [← map_mul, hid.eq]
  · intro h
    exact hne (by simpa using congrArg φ.symm h)
  · intro f hf hfe hfne
    have hf' : IsIdempotentElem (φ.symm f) := by
      change φ.symm f * φ.symm f = φ.symm f
      rw [← map_mul, hf.eq]
    have hfe' : φ.symm f * e = φ.symm f := by
      have := congrArg φ.symm hfe
      rwa [map_mul, RingEquiv.symm_apply_apply] at this
    have hfne' : φ.symm f ≠ 0 := fun h => hfne (by simpa using congrArg φ h)
    have := hmin _ hf' hfe' hfne'
    rw [← this, RingEquiv.apply_symm_apply]

variable {ι : Type*} (δ : ι → A)

private theorem exists_eq_of_isMinIdempotent (hid : ∀ i, IsIdempotentElem (δ i))
    (hfaith : ∀ a : A, (∀ i, a * δ i = 0) → a = 0)
    (hcorner : ∀ e : A, IsIdempotentElem e → ∀ i, e * δ i = 0 ∨ e * δ i = δ i)
    {e : A} (he : IsMinIdempotent e) : ∃ i, e = δ i := by
  obtain ⟨heid, hene, hmin⟩ := he
  have : ∃ i, e * δ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hene (hfaith e h)
  obtain ⟨i, hi⟩ := this
  have h1 : e * δ i = δ i := (hcorner e heid i).resolve_left hi
  have hne' : δ i ≠ 0 := fun h => hi (by rw [h, mul_zero])
  refine ⟨i, (hmin (δ i) (hid i) ?_ hne').symm⟩
  rw [mul_comm]
  exact h1

end MinIdempotent

section Indicator

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F]

private abbrev PlaceIndex := InfinitePlace F ⊕ HeightOneSpectrum R

private theorem adele_ext {x y : AdeleRing R F} (h₁ : ∀ v : InfinitePlace F, x.1 v = y.1 v)
    (h₂ : ∀ w : HeightOneSpectrum R, x.2 w = y.2 w) : x = y :=
  Prod.ext (funext h₁) (FiniteAdeleRing.ext F h₂)

private theorem fst_mul_apply (x y : AdeleRing R F) (v : InfinitePlace F) :
    (x * y).1 v = x.1 v * y.1 v := rfl

private theorem snd_mul_apply (x y : AdeleRing R F) (w : HeightOneSpectrum R) :
    (x * y).2 w = x.2 w * y.2 w := rfl

private theorem fst_zero_apply (v : InfinitePlace F) : (0 : AdeleRing R F).1 v = 0 := rfl

private theorem snd_zero_apply (w : HeightOneSpectrum R) : (0 : AdeleRing R F).2 w = 0 := rfl

private theorem finiteAdele_zero_apply (w : HeightOneSpectrum R) :
    (0 : FiniteAdeleRing R F) w = 0 := rfl

open Classical in
private def indicator : PlaceIndex R F → AdeleRing R F
  | Sum.inl v => (Pi.single v 1, 0)
  | Sum.inr w =>
    (0, RestrictedProduct.single (fun u : HeightOneSpectrum R => u.adicCompletionIntegers F) w 1)

open Classical in
private theorem indicator_inl_fst (v : InfinitePlace F) :
    (indicator R F (Sum.inl v)).1 = Pi.single v 1 := rfl

private theorem indicator_inl_snd (v : InfinitePlace F) : (indicator R F (Sum.inl v)).2 = 0 :=
  rfl

private theorem indicator_inr_fst (w : HeightOneSpectrum R) :
    (indicator R F (Sum.inr w)).1 = 0 := rfl

open Classical in
private theorem indicator_inr_snd_same (w : HeightOneSpectrum R) :
    (indicator R F (Sum.inr w)).2 w = 1 :=
  RestrictedProduct.single_eq_same _ w 1

open Classical in
private theorem indicator_inr_snd_ne {w u : HeightOneSpectrum R} (h : u ≠ w) :
    (indicator R F (Sum.inr w)).2 u = 0 :=
  RestrictedProduct.single_eq_of_ne _ 1 h

open Classical in
private theorem indicator_inl_fst_same (v : InfinitePlace F) :
    (indicator R F (Sum.inl v)).1 v = 1 := by
  rw [indicator_inl_fst, Pi.single_eq_same]

open Classical in
private theorem indicator_inl_fst_ne {v u : InfinitePlace F} (h : u ≠ v) :
    (indicator R F (Sum.inl v)).1 u = 0 := by
  rw [indicator_inl_fst, Pi.single_eq_of_ne h]

private theorem isIdempotentElem_indicator (P : PlaceIndex R F) :
    IsIdempotentElem (indicator R F P) := by
  rcases P with v | w
  · refine adele_ext R F (fun u => ?_) (fun u => ?_)
    · rw [fst_mul_apply]
      by_cases h : u = v
      · subst h; rw [indicator_inl_fst_same, mul_one]
      · rw [indicator_inl_fst_ne R F h, mul_zero]
    · rw [snd_mul_apply, indicator_inl_snd, finiteAdele_zero_apply, mul_zero]
  · refine adele_ext R F (fun u => ?_) (fun u => ?_)
    · rw [fst_mul_apply, indicator_inr_fst, Pi.zero_apply, mul_zero]
    · rw [snd_mul_apply]
      by_cases h : u = w
      · subst h; rw [indicator_inr_snd_same, mul_one]
      · rw [indicator_inr_snd_ne R F h, mul_zero]

private theorem indicator_ne_zero (P : PlaceIndex R F) : indicator R F P ≠ 0 := by
  rcases P with v | w
  · intro h
    have h1 := congrArg (fun x : AdeleRing R F => x.1 v) h
    simp only [indicator_inl_fst_same, fst_zero_apply] at h1
    exact one_ne_zero h1
  · intro h
    have h1 := congrArg (fun x : AdeleRing R F => x.2 w) h
    simp only [indicator_inr_snd_same, snd_zero_apply] at h1
    exact one_ne_zero h1

private theorem faithful_indicator (a : AdeleRing R F) (h : ∀ P, a * indicator R F P = 0) :
    a = 0 := by
  refine adele_ext R F (fun v => ?_) (fun w => ?_)
  · have h1 := congrArg (fun x : AdeleRing R F => x.1 v) (h (Sum.inl v))
    simp only [fst_mul_apply, indicator_inl_fst_same, mul_one, fst_zero_apply] at h1
    rw [h1, fst_zero_apply]
  · have h1 := congrArg (fun x : AdeleRing R F => x.2 w) (h (Sum.inr w))
    simp only [snd_mul_apply, indicator_inr_snd_same, mul_one, snd_zero_apply] at h1
    rw [h1, snd_zero_apply]

private theorem corner_indicator (e : AdeleRing R F) (he : IsIdempotentElem e)
    (P : PlaceIndex R F) : e * indicator R F P = 0 ∨ e * indicator R F P = indicator R F P := by
  rcases P with v | w
  · have hev : e.1 v * e.1 v = e.1 v := by
      have h1 := congrArg (fun x : AdeleRing R F => x.1 v) he.eq
      rwa [fst_mul_apply] at h1
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hev with h0 | h1
    · left
      refine adele_ext R F (fun u => ?_) (fun u => ?_)
      · rw [fst_mul_apply, fst_zero_apply]
        by_cases hu : u = v
        · subst hu; rw [h0, zero_mul]
        · rw [indicator_inl_fst_ne R F hu, mul_zero]
      · rw [snd_mul_apply, indicator_inl_snd, finiteAdele_zero_apply, mul_zero, snd_zero_apply]
    · right
      refine adele_ext R F (fun u => ?_) (fun u => ?_)
      · rw [fst_mul_apply]
        by_cases hu : u = v
        · subst hu; rw [h1, one_mul]
        · rw [indicator_inl_fst_ne R F hu, mul_zero]
      · rw [snd_mul_apply, indicator_inl_snd, finiteAdele_zero_apply, mul_zero]
  · have hev : e.2 w * e.2 w = e.2 w := by
      have h1 := congrArg (fun x : AdeleRing R F => x.2 w) he.eq
      rwa [snd_mul_apply] at h1
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hev with h0 | h1
    · left
      refine adele_ext R F (fun u => ?_) (fun u => ?_)
      · rw [fst_mul_apply, indicator_inr_fst, Pi.zero_apply, mul_zero, fst_zero_apply]
      · rw [snd_mul_apply, snd_zero_apply]
        by_cases hu : u = w
        · subst hu; rw [h0, zero_mul]
        · rw [indicator_inr_snd_ne R F hu, mul_zero]
    · right
      refine adele_ext R F (fun u => ?_) (fun u => ?_)
      · rw [fst_mul_apply, indicator_inr_fst, Pi.zero_apply, mul_zero]
      · rw [snd_mul_apply]
        by_cases hu : u = w
        · subst hu; rw [h1, one_mul]
        · rw [indicator_inr_snd_ne R F hu, mul_zero]

private theorem exists_map_indicator_eq (φ : AdeleRing R F ≃+* AdeleRing R F)
    (P : PlaceIndex R F) : ∃ Q, φ (indicator R F P) = indicator R F Q := by
  have hmin : IsMinIdempotent (indicator R F P) :=
    ⟨isIdempotentElem_indicator R F P, indicator_ne_zero R F P, fun f hf hfe hfne => by
      rcases corner_indicator R F f hf P with h0 | h1
      · exact absurd (hfe ▸ h0) hfne
      · exact hfe ▸ h1⟩
  exact exists_eq_of_isMinIdempotent (indicator R F) (isIdempotentElem_indicator R F)
    (faithful_indicator R F) (corner_indicator R F) (hmin.map_ringEquiv φ)

end Indicator

section Corners

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F]

private theorem continuous_fst_apply (v : InfinitePlace F) :
    Continuous (fun a : AdeleRing R F => a.1 v) :=
  (continuous_apply (A := fun u : InfinitePlace F => u.Completion) v).comp continuous_fst

private theorem continuous_snd_apply (w : HeightOneSpectrum R) :
    Continuous (fun a : AdeleRing R F => a.2 w) :=
  (RestrictedProduct.continuous_eval (R := fun u : HeightOneSpectrum R => u.adicCompletion F)
    (A := fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) w).comp
    continuous_snd

open Classical in
private def singleInf (v : InfinitePlace F) (t : v.Completion) : AdeleRing R F :=
  (Pi.single v t, 0)

omit [IsDedekindDomain R] in
private theorem cofinite_le_principal_compl (w : HeightOneSpectrum R) :
    (Filter.cofinite : Filter (HeightOneSpectrum R)) ≤ Filter.principal ({w}ᶜ) :=
  Filter.le_principal_iff.mpr (Set.finite_singleton w).compl_mem_cofinite

open Classical in
private def singleFin (w : HeightOneSpectrum R) (t : w.adicCompletion F) : AdeleRing R F :=
  (0, RestrictedProduct.single (fun u : HeightOneSpectrum R => u.adicCompletionIntegers F) w t)

open Classical in
private theorem singleInf_fst (v : InfinitePlace F) (t : v.Completion) :
    (singleInf R F v t).1 = Pi.single v t := rfl

private theorem singleInf_snd (v : InfinitePlace F) (t : v.Completion) :
    (singleInf R F v t).2 = 0 := rfl

open Classical in
private theorem continuous_singleInf (v : InfinitePlace F) :
    Continuous (singleInf R F v) :=
  (continuous_single (A := fun u : InfinitePlace F => u.Completion) v).prodMk continuous_const

open Classical in
private theorem continuous_singleFin (w : HeightOneSpectrum R) :
    Continuous (singleFin R F w) := by
  -- `RestrictedProduct.single` at `w` factors through the restricted product over the
  -- principal filter of `{w}ᶜ`, where its continuity is that of `Pi.single`.
  let stratum (t : w.adicCompletion F) :
      RestrictedProduct (fun u : HeightOneSpectrum R => u.adicCompletion F)
        (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F)))
        (Filter.principal ({w}ᶜ)) :=
    ⟨Pi.single w t, by
      rw [Filter.eventually_principal]
      intro u hu
      rw [Pi.single_eq_of_ne (by simpa using hu)]
      exact zero_mem _⟩
  have h0 : Continuous stratum := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_single w
  exact continuous_const.prodMk
    ((RestrictedProduct.continuous_inclusion (cofinite_le_principal_compl R w)).comp h0)

open Classical in
private theorem mul_indicator_inl (a : AdeleRing R F) (v : InfinitePlace F) :
    a * indicator R F (Sum.inl v) = singleInf R F v (a.1 v) := by
  refine adele_ext R F (fun u => ?_) (fun u => ?_)
  · rw [fst_mul_apply, singleInf_fst]
    by_cases hu : u = v
    · subst hu; rw [indicator_inl_fst_same, mul_one, Pi.single_eq_same]
    · rw [indicator_inl_fst_ne R F hu, mul_zero, Pi.single_eq_of_ne hu]
  · rw [snd_mul_apply, indicator_inl_snd, finiteAdele_zero_apply, mul_zero, singleInf_snd,
      finiteAdele_zero_apply]

open Classical in
private theorem mul_indicator_inr (a : AdeleRing R F) (w : HeightOneSpectrum R) :
    a * indicator R F (Sum.inr w) = singleFin R F w (a.2 w) := by
  refine Prod.ext (mul_zero a.1) ?_
  have h :=
    RestrictedProduct.mul_single (fun u : HeightOneSpectrum R => u.adicCompletionIntegers F) w 1 a.2
  rw [mul_one] at h
  exact h.symm

open Classical in
private theorem singleInf_fst_same (v : InfinitePlace F) (t : v.Completion) :
    (singleInf R F v t).1 v = t := by
  rw [singleInf_fst, Pi.single_eq_same]

open Classical in
private theorem singleFin_snd_same (w : HeightOneSpectrum R) (t : w.adicCompletion F) :
    (singleFin R F w t).2 w = t :=
  RestrictedProduct.single_eq_same _ w t

private theorem singleInf_zero (v : InfinitePlace F) : singleInf R F v 0 = 0 := by
  have h := mul_indicator_inl R F 0 v
  rw [zero_mul] at h
  exact h.symm

private theorem singleFin_zero (w : HeightOneSpectrum R) : singleFin R F w 0 = 0 := by
  have h := mul_indicator_inr R F 0 w
  rw [zero_mul] at h
  exact h.symm

end Corners

section Separation

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F]

/-- `x` is nil at `P` when the powers of `x` times the indicator of `P` tend to zero. -/
private def IsNilAt (P : PlaceIndex R F) (x : F) : Prop :=
  Tendsto (fun n : ℕ => (algebraMap F (AdeleRing R F) x * indicator R F P) ^ (n + 1)) atTop
    (𝓝 0)

private theorem corner_pow_succ (P : PlaceIndex R F) (x : F) (n : ℕ) :
    (algebraMap F (AdeleRing R F) x * indicator R F P) ^ (n + 1)
      = algebraMap F (AdeleRing R F) (x ^ (n + 1)) * indicator R F P := by
  rw [mul_pow, (isIdempotentElem_indicator R F P).pow_succ_eq, map_pow]

variable {R F} in
private theorem IsNilAt.map (φ : AdeleRing R F →+* AdeleRing R F) (hφ : Continuous φ)
    (τ : F →+* F)
    (hτ : ∀ x : F, φ (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) (τ x))
    {P Q : PlaceIndex R F} (hPQ : φ (indicator R F P) = indicator R F Q) {x : F}
    (hx : IsNilAt R F P x) : IsNilAt R F Q (τ x) := by
  have h0 : Tendsto φ (𝓝 0) (𝓝 0) := by
    have := hφ.tendsto 0
    rwa [map_zero] at this
  refine (h0.comp hx).congr (fun n => ?_)
  change φ ((algebraMap F (AdeleRing R F) x * indicator R F P) ^ (n + 1)) = _
  rw [map_pow, map_mul, hτ, hPQ]

private theorem v_lt_one_of_tendsto_pow {K Γ₀ : Type*} [Ring K]
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] {x : K}
    (h : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0)) : Valued.v x < 1 := by
  by_contra hx
  rw [not_lt] at hx
  have hmem : {y : K | hv.v.restrict y
      < ((1 : (MonoidWithZeroHom.ValueGroup₀ (.ofClass hv.v))ˣ) :
        MonoidWithZeroHom.ValueGroup₀ (.ofClass hv.v))} ∈ 𝓝 (0 : K) :=
    Valued.mem_nhds_zero.mpr ⟨1, fun _ hy => hy⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h.eventually_mem hmem)
  have hN' := hN N le_rfl
  rw [Set.mem_ofPred_eq, Units.val_one] at hN'
  have h2 : hv.v (x ^ N) < 1 := (Valuation.restrict_lt_one_iff _).mp hN'
  rw [map_pow] at h2
  exact absurd h2 (not_lt.mpr (one_le_pow_of_one_le' hx N))

private theorem norm_coe_infinitePlace (v : InfinitePlace F) (x : F) :
    ‖(x : v.Completion)‖ = v x := by
  exact AbsoluteValue.Completion.norm_coe _

private theorem isNilAt_inl_iff (v : InfinitePlace F) (x : F) :
    IsNilAt R F (Sum.inl v) x ↔ v x < 1 := by
  unfold IsNilAt
  have hseq : (fun n : ℕ => (algebraMap F (AdeleRing R F) x * indicator R F (Sum.inl v))
      ^ (n + 1)) = fun n => singleInf R F v ((x : v.Completion) ^ (n + 1)) := by
    funext n
    rw [corner_pow_succ, mul_indicator_inl, map_pow]
    congr 1
    change ((algebraMap F (AdeleRing R F) x).1 v) ^ (n + 1) = _
    rw [algebraMap_fst_apply]
  rw [hseq, ← norm_coe_infinitePlace F v x, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one,
    ← Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => (x : v.Completion) ^ n) 1]
  constructor
  · intro h
    have h2 := ((continuous_fst_apply R F v).tendsto 0).comp h
    refine h2.congr (fun n => ?_)
    exact singleInf_fst_same R F v _
  · intro h
    have h2 := ((continuous_singleInf R F v).tendsto 0).comp h
    rwa [singleInf_zero] at h2

private theorem isNilAt_inr_iff (w : HeightOneSpectrum R) (x : F) :
    IsNilAt R F (Sum.inr w) x ↔ w.valuation F x < 1 := by
  unfold IsNilAt
  have hseq : (fun n : ℕ => (algebraMap F (AdeleRing R F) x * indicator R F (Sum.inr w))
      ^ (n + 1)) = fun n => singleFin R F w ((x : w.adicCompletion F) ^ (n + 1)) := by
    funext n
    rw [corner_pow_succ, mul_indicator_inr, map_pow]
    rfl
  rw [hseq, ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x]
  constructor
  · intro h
    have h2 := ((continuous_snd_apply R F w).tendsto 0).comp h
    have h1 : Tendsto (fun n : ℕ => (x : w.adicCompletion F) ^ (n + 1)) atTop (𝓝 0) :=
      h2.congr (fun n => singleFin_snd_same R F w _)
    exact v_lt_one_of_tendsto_pow
      ((Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => (x : w.adicCompletion F) ^ n)
        1).mp h1)
  · intro hx
    have h1 : Tendsto (fun n : ℕ => (x : w.adicCompletion F) ^ (n + 1)) atTop (𝓝 0) :=
      (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => (x : w.adicCompletion F) ^ n)
        1).mpr (Valued.tendsto_zero_pow_of_v_lt_one hx)
    have h2 := ((continuous_singleFin R F w).tendsto 0).comp h1
    rwa [singleFin_zero] at h2

private theorem infinitePlace_two_inv_lt_one (v : InfinitePlace F) : v (2⁻¹ : F) < 1 := by
  have h2 : v (2 : F) = 2 := by
    have := NumberField.InfinitePlace.map_natCast v 2
    simpa using this
  rw [map_inv₀, h2]
  norm_num

private theorem not_valuation_two_inv_lt_one (w : HeightOneSpectrum R) (h2 : (2 : F) ≠ 0) :
    ¬ w.valuation F (2⁻¹ : F) < 1 := by
  rw [Valuation.val_lt_one_iff _ (inv_ne_zero h2), inv_inv, not_lt]
  have : w.valuation F (algebraMap R F 2) ≤ 1 := HeightOneSpectrum.valuation_le_one w 2
  rwa [map_ofNat] at this

end Separation

section Transport

variable {L : Type*} [Field L] [NumberField L]

/-- The finite place of `L` transported along a field automorphism `τ`. -/
private abbrev finEquiv (τ : L ≃+* L) : HeightOneSpectrum (𝓞 L) ≃ HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ)

omit [NumberField L] in
private theorem mem_finEquiv_asIdeal_pow_iff (τ : L ≃+* L) (w : HeightOneSpectrum (𝓞 L))
    (r : 𝓞 L) (n : ℕ) :
    RingOfIntegers.mapRingEquiv τ r ∈ (finEquiv τ w).asIdeal ^ n ↔ r ∈ w.asIdeal ^ n := by
  change _ ∈ (w.asIdeal.comap (RingOfIntegers.mapRingEquiv τ).symm) ^ n ↔ _
  rw [Ideal.comap_symm, ← Ideal.map_pow, ← Ideal.comap_symm, Ideal.mem_comap]
  rw [RingEquiv.symm_apply_apply]

private theorem intValuation_finEquiv (τ : L ≃+* L) (w : HeightOneSpectrum (𝓞 L)) (r : 𝓞 L) :
    (finEquiv τ w).intValuation (RingOfIntegers.mapRingEquiv τ r) = w.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [map_zero, Valuation.map_zero, Valuation.map_zero]
  · have hτr : RingOfIntegers.mapRingEquiv τ r ≠ 0 :=
      (map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv τ).injective).mpr hr
    apply le_antisymm
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, w.intValuation r = WithZero.exp (-(n : ℤ)) :=
        ⟨_, w.intValuation_if_neg hr⟩
      rw [hn, HeightOneSpectrum.intValuation_le_pow_iff_mem, mem_finEquiv_asIdeal_pow_iff,
        ← HeightOneSpectrum.intValuation_le_pow_iff_mem, hn]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (finEquiv τ w).intValuation (RingOfIntegers.mapRingEquiv τ r)
          = WithZero.exp (-(n : ℤ)) := ⟨_, (finEquiv τ w).intValuation_if_neg hτr⟩
      rw [hn, HeightOneSpectrum.intValuation_le_pow_iff_mem,
        ← mem_finEquiv_asIdeal_pow_iff τ w, ← HeightOneSpectrum.intValuation_le_pow_iff_mem, hn]

private theorem valuation_finEquiv (τ : L ≃+* L) (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    (finEquiv τ w).valuation L (τ x) = w.valuation L x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have h1 : ∀ c : 𝓞 L, τ (algebraMap (𝓞 L) L c)
      = algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv τ c) := fun c => rfl
  rw [map_div₀, map_div₀, map_div₀, h1, h1, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_finEquiv, intValuation_finEquiv]

private theorem absNorm_finEquiv (τ : L ≃+* L) (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm (finEquiv τ w).asIdeal = Ideal.absNorm w.asIdeal := by
  have hmap : (finEquiv τ w).asIdeal = w.asIdeal.map (RingOfIntegers.mapRingEquiv τ) :=
    Ideal.comap_symm _
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv w.asIdeal _ (RingOfIntegers.mapRingEquiv τ)
    hmap).toEquiv).symm

private theorem toNNReal_congr {a b : NNReal} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a = b)
    (x : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal ha x = WithZeroMulInt.toNNReal hb x := by
  subst hab
  rfl

private theorem norm_coe_finEquiv (τ : L ≃+* L) (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    ‖(τ x : (finEquiv τ w).adicCompletion L)‖ = ‖(x : w.adicCompletion L)‖ := by
  rw [← FinitePlace.embedding_apply, ← FinitePlace.embedding_apply,
    FinitePlace.norm_embedding', FinitePlace.norm_embedding', valuation_finEquiv]
  congr 1
  refine toNNReal_congr _ _ ?_ _
  exact_mod_cast absNorm_finEquiv τ w

omit [NumberField L] in
private theorem norm_coe_comap (τ : L ≃+* L) (v : InfinitePlace L) (x : L) :
    ‖(τ x : (v.comap (τ.symm : L →+* L)).Completion)‖ = ‖(x : v.Completion)‖ := by
  rw [norm_coe_infinitePlace, norm_coe_infinitePlace, InfinitePlace.comap_apply]
  change v (τ.symm (τ x)) = v x
  rw [RingEquiv.symm_apply_apply]

end Transport

section Main

variable {L : Type*} [Field L] [NumberField L]
  (φ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) (hφ : Continuous φ)
  (hφ' : Continuous φ.symm) (τ : L ≃+* L)
  (hτ : ∀ x : L, φ (algebraMap L (AdeleRing (𝓞 L) L) x) = algebraMap L (AdeleRing (𝓞 L) L) (τ x))

private def placeMap : PlaceIndex (𝓞 L) L → PlaceIndex (𝓞 L) L
  | Sum.inl v => Sum.inl (v.comap (τ.symm : L →+* L))
  | Sum.inr w => Sum.inr (finEquiv τ w)

include hφ hφ' hτ in
private theorem map_indicator (P : PlaceIndex (𝓞 L) L) :
    φ (indicator (𝓞 L) L P) = indicator (𝓞 L) L (placeMap τ P) := by
  obtain ⟨Q, hQ⟩ := exists_map_indicator_eq (𝓞 L) L φ P
  have hQ' : φ.symm (indicator (𝓞 L) L Q) = indicator (𝓞 L) L P := by
    rw [← hQ, RingEquiv.symm_apply_apply]
  have hτ' : ∀ x : L, φ.symm (algebraMap L (AdeleRing (𝓞 L) L) x)
      = algebraMap L (AdeleRing (𝓞 L) L) (τ.symm x) := by
    intro x
    rw [RingEquiv.symm_apply_eq, hτ, RingEquiv.apply_symm_apply]
  have hnil : ∀ x : L, IsNilAt (𝓞 L) L P x ↔ IsNilAt (𝓞 L) L Q (τ x) := fun x =>
    ⟨fun hx => hx.map φ.toRingHom hφ τ hτ hQ, fun hx => by
      have := hx.map φ.symm.toRingHom hφ' τ.symm hτ' hQ'
      simpa using this⟩
  have h2 : τ (2⁻¹ : L) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  rw [hQ]
  congr 1
  rcases P with v | w <;> rcases Q with v' | w'
  · refine congrArg Sum.inl (NumberField.InfinitePlace.eq_iff_isEquiv.mpr
      (AbsoluteValue.isEquiv_iff_lt_one_iff.mpr fun y => ?_)).symm
    have := hnil (τ.symm y)
    rw [isNilAt_inl_iff, isNilAt_inl_iff, RingEquiv.apply_symm_apply] at this
    exact this
  · exfalso
    have h' := (hnil 2⁻¹).mp ((isNilAt_inl_iff (𝓞 L) L v _).mpr
      (infinitePlace_two_inv_lt_one L v))
    rw [h2, isNilAt_inr_iff] at h'
    exact not_valuation_two_inv_lt_one (𝓞 L) L w' two_ne_zero h'
  · exfalso
    have h' := (hnil 2⁻¹).mpr (by
      rw [h2]; exact (isNilAt_inl_iff (𝓞 L) L v' _).mpr (infinitePlace_two_inv_lt_one L v'))
    rw [isNilAt_inr_iff] at h'
    exact not_valuation_two_inv_lt_one (𝓞 L) L w two_ne_zero h'
  · refine congrArg Sum.inr (HeightOneSpectrum.ext (le_antisymm (fun r hr => ?_)
      (fun r hr => ?_))).symm
    · have := hnil (τ.symm (algebraMap (𝓞 L) L r))
      rw [isNilAt_inr_iff, isNilAt_inr_iff, RingEquiv.apply_symm_apply,
        ← valuation_finEquiv τ w, RingEquiv.apply_symm_apply] at this
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem w' r).mp
        (this.mp ((HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mpr hr))
    · have := hnil (τ.symm (algebraMap (𝓞 L) L r))
      rw [isNilAt_inr_iff, isNilAt_inr_iff, RingEquiv.apply_symm_apply,
        ← valuation_finEquiv τ w, RingEquiv.apply_symm_apply] at this
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mp
        (this.mpr ((HeightOneSpectrum.valuation_lt_one_iff_mem w' r).mpr hr))

include hφ hφ' hτ in
/-- A bicontinuous ring automorphism `φ` of the adeles of a number field `L` (both `φ` and `φ⁻¹`
continuous) that restricts to `τ` on `L` preserves the norm of the component at an infinite
place `v`, read off at the place `v ∘ τ⁻¹`. -/
theorem norm_fst_map_comap (v : InfinitePlace L) (a : AdeleRing (𝓞 L) L) :
    ‖(φ a).1 (v.comap (τ.symm : L →+* L))‖ = ‖a.1 v‖ := by
  set v' := v.comap (τ.symm : L →+* L)
  have hind : φ (indicator (𝓞 L) L (Sum.inl v)) = indicator (𝓞 L) L (Sum.inl v') :=
    map_indicator φ hφ hφ' τ hτ (Sum.inl v)
  let ψ : v.Completion → v'.Completion := fun t => (φ (singleInf (𝓞 L) L v t)).1 v'
  have hψ : ∀ b : AdeleRing (𝓞 L) L, (φ b).1 v' = ψ (b.1 v) := by
    intro b
    have h1 : (φ b * indicator (𝓞 L) L (Sum.inl v')).1 v' = (φ b).1 v' := by
      rw [mul_indicator_inl, singleInf_fst_same]
    rw [← h1, ← hind, ← map_mul, mul_indicator_inl]
  have hcont : Continuous ψ :=
    (continuous_fst_apply (𝓞 L) L v').comp (hφ.comp (continuous_singleInf (𝓞 L) L v))
  have hcoe : ∀ x : L, ψ (x : v.Completion) = (τ x : v'.Completion) := by
    intro x
    have h1 := hψ (algebraMap L (AdeleRing (𝓞 L) L) x)
    rw [hτ, algebraMap_fst_apply, algebraMap_fst_apply] at h1
    exact h1.symm
  have hdense : DenseRange (fun x : L => (x : v.Completion)) :=
    (AbsoluteValue.Completion.denseRange_coe v.1).comp
      (Function.Surjective.denseRange (f := WithAbs.toAbs v.1) fun y => ⟨y.ofAbs, rfl⟩)
      (AbsoluteValue.Completion.continuous_coe v.1)
  have heq := hdense.equalizer (continuous_norm.comp hcont) continuous_norm
    (funext fun x => by
      change ‖ψ (x : v.Completion)‖ = ‖(x : v.Completion)‖
      rw [hcoe]
      exact norm_coe_comap τ v x)
  rw [hψ]
  exact congrFun heq (a.1 v)

include hφ hφ' hτ in
/-- A bicontinuous ring automorphism `φ` of the adeles of a number field `L` (both `φ` and `φ⁻¹`
continuous) that restricts to `τ` on `L` preserves the norm of the component at a finite place
`w`, read off at the transported place. -/
theorem norm_snd_map_equivOfRingEquiv (w : HeightOneSpectrum (𝓞 L)) (a : AdeleRing (𝓞 L) L) :
    ‖(φ a).2 (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ) w)‖
      = ‖a.2 w‖ := by
  set w' := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ) w
  have hind : φ (indicator (𝓞 L) L (Sum.inr w)) = indicator (𝓞 L) L (Sum.inr w') :=
    map_indicator φ hφ hφ' τ hτ (Sum.inr w)
  let ψ : w.adicCompletion L → w'.adicCompletion L := fun t =>
    (φ (singleFin (𝓞 L) L w t)).2 w'
  have hψ : ∀ b : AdeleRing (𝓞 L) L, (φ b).2 w' = ψ (b.2 w) := by
    intro b
    have h1 : (φ b * indicator (𝓞 L) L (Sum.inr w')).2 w' = (φ b).2 w' := by
      rw [mul_indicator_inr, singleFin_snd_same]
    rw [← h1, ← hind, ← map_mul, mul_indicator_inr]
  have hcont : Continuous ψ :=
    (continuous_snd_apply (𝓞 L) L w').comp (hφ.comp (continuous_singleFin (𝓞 L) L w))
  have hcoe : ∀ x : L, ψ (x : w.adicCompletion L) = (τ x : w'.adicCompletion L) := by
    intro x
    have h1 := hψ (algebraMap L (AdeleRing (𝓞 L) L) x)
    rw [hτ] at h1
    exact h1.symm
  have heq := (HeightOneSpectrum.denseRange_algebraMap L w).equalizer
    (continuous_norm.comp hcont) continuous_norm
    (funext fun x => by
      change ‖ψ (x : w.adicCompletion L)‖ = ‖(x : w.adicCompletion L)‖
      rw [hcoe]
      exact norm_coe_finEquiv τ w x)
  rw [hψ]
  exact congrFun heq (a.2 w)

end Main

end NumberField.AdeleRing
