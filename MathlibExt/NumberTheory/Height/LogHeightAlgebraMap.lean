/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Height_logHeight_algebraMap.lean`
and
`P2M/Sol/S_Height_logHeight_algebraMap.lean`
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

public import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section


open Height NumberField

section helpers

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

open NumberField.InfinitePlace in
open scoped Classical in

private lemma mwabs_sum_mult_comap [Algebra K L] (v : InfinitePlace K) :
    ∑ w ∈ Finset.univ.filter
        (fun w : InfinitePlace L => w.comap (algebraMap K L) = v), w.mult
      = v.mult * Module.finrank K L := by
  have hmem : ∀ w : InfinitePlace L,
      w ∈ placesOver L v ↔ w.comap (algebraMap K L) = v := by
    intro w
    constructor
    · intro h
      have : w.1.LiesOver v.1 := h
      exact LiesOver.comap_eq w v
    · intro h
      exact ⟨congrArg Subtype.val h⟩
  have hset : Finset.univ.filter (fun w : InfinitePlace L => w.comap (algebraMap K L) = v)
      = (placesOver L v).toFinset := by
    ext w
    simp [hmem w]
  have hPU : (placesOver L v).toFinset
      = (ramifiedPlacesOver L v).toFinset ∪ (unramifiedPlacesOver L v).toFinset := by
    rw [← Set.toFinset_union, Set.toFinset_inj]
    exact (union_ramifiedPlacesOver_unramifiedPlacesOver L v).symm
  have hdisj : Disjoint ((ramifiedPlacesOver L v).toFinset)
      ((unramifiedPlacesOver L v).toFinset) := by
    rw [Set.disjoint_toFinset]
    exact disjoint_ramifiedPlacesOver_unramifiedPlacesOver L v
  have hU : ∀ w ∈ (unramifiedPlacesOver L v).toFinset, w.mult = v.mult := by
    intro w hw
    have hw' := Set.mem_toFinset.mp hw
    have hlies : w.1.LiesOver v.1 := hw'.1
    rw [← hw'.2.eq, LiesOver.comap_eq w v]
  have hR : ∀ w ∈ (ramifiedPlacesOver L v).toFinset, w.mult = 2 := by
    intro w hw
    have hw' := Set.mem_toFinset.mp hw
    exact mult_isComplex ⟨w, hw'.2.isComplex⟩
  rw [hset, hPU, Finset.sum_union hdisj, Finset.sum_congr rfl hR, Finset.sum_congr rfl hU,
    Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
    ← Set.ncard_eq_toFinset_card', ← Set.ncard_eq_toFinset_card']
  have hcard := unramifedPlacesOver_ncard_add_eq_finrank (K := K) (L := L) (v := v)
  rcases (ramifiedPlacesOver L v).eq_empty_or_nonempty with hE | ⟨w₀, hw₀⟩
  · rw [hE] at hcard ⊢
    simp only [Set.ncard_empty, mul_zero, zero_add, zero_mul, add_zero] at hcard ⊢
    rw [hcard]
    ring
  · haveI hlies : w₀.1.LiesOver v.1 := hw₀.1
    have hreal : v.IsReal := hw₀.2.liesOver_isReal_under (v := v)
    have hmv : v.mult = 1 := mult_isReal ⟨v, hreal⟩
    rw [hmv]
    omega

private lemma mwabs_ciSup_inv_pow {b : ℝ} (hb : 1 < b) {ι : Type*} [Finite ι] [Nonempty ι]
    (m : ι → ℕ) : ⨆ i, ((b ^ m i)⁻¹) = (b ^ (⨅ i, m i))⁻¹ := by
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  refine le_antisymm (ciSup_le fun i ↦ ?_) ?_
  · exact inv_anti₀ (pow_pos hb0 _) (pow_le_pow_right₀ hb.le (ciInf_le (OrderBot.bddBelow _) i))
  · obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := m)
    rw [← hj]
    exact le_ciSup (f := fun i ↦ (b ^ m i)⁻¹) ((Set.finite_range _).bddAbove) j

private lemma mwabs_content_formula {F : Type*} [Field F] [NumberField F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (y : ι → NumberField.RingOfIntegers F)
    (hy : ∀ i, y i ≠ 0) :
    (∏ᶠ v : NumberField.FinitePlace F, ⨆ i, v (y i : F))
      = ((Ideal.absNorm (⨆ i, Ideal.span {y i}) : ℝ))⁻¹ := by
  classical
  have hspan : ∀ i, Ideal.span {y i} ≠ (⊥ : Ideal (NumberField.RingOfIntegers F)) :=
    fun i ↦ mt Ideal.span_singleton_eq_bot.mp (hy i)
  have hJ_ne : (⨆ i, Ideal.span {y i} : Ideal (NumberField.RingOfIntegers F)) ≠ ⊥ := by
    intro h
    have hle := le_iSup (fun i ↦ Ideal.span {y i}) (Classical.arbitrary ι)
    rw [h, le_bot_iff] at hle
    exact hspan _ hle
  have h1 : ∀ v : NumberField.FinitePlace F, (⨆ i, v (y i : F))
      = ((Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)
          ^ multiplicity v.maximalIdeal.asIdeal (⨆ i, Ideal.span {y i}))⁻¹ := by
    intro v
    have hb : (1 : ℝ) < (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.maximalIdeal
    have hstep : ∀ i, v (y i : F)
        = ((Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)
            ^ multiplicity v.maximalIdeal.asIdeal (Ideal.span {y i}))⁻¹ := fun i ↦
      eq_inv_of_mul_eq_one_left (NumberField.FinitePlace.apply_mul_absNorm_pow_eq_one v (hy i))
    rw [iSup_congr hstep, mwabs_ciSup_inv_pow hb,
      ← IsDedekindDomain.HeightOneSpectrum.multiplicity_iSup v.maximalIdeal hspan]
  rw [finprod_congr h1, finprod_inv_distrib]
  congr 1
  have hker : ∀ I : Ideal (NumberField.RingOfIntegers F), Ideal.absNorm I = 1 → I = 1 := by
    simp
  have h1' := MonoidHom.map_finprod_of_preimage_one (f := Ideal.absNorm.toMonoidHom) hker
    (fun v : NumberField.FinitePlace F =>
      v.maximalIdeal.asIdeal ^ multiplicity v.maximalIdeal.asIdeal (⨆ i, Ideal.span {y i}))
  have h1'' : Ideal.absNorm (∏ᶠ v : NumberField.FinitePlace F,
        v.maximalIdeal.asIdeal ^ multiplicity v.maximalIdeal.asIdeal (⨆ i, Ideal.span {y i}))
      = ∏ᶠ v : NumberField.FinitePlace F,
          Ideal.absNorm (v.maximalIdeal.asIdeal
            ^ multiplicity v.maximalIdeal.asIdeal (⨆ i, Ideal.span {y i})) := h1'
  have h_prod : (Ideal.absNorm (∏ᶠ v : NumberField.FinitePlace F,
        v.maximalIdeal.asIdeal ^ multiplicity v.maximalIdeal.asIdeal
          (⨆ i, Ideal.span {y i})) : ℝ)
      = ∏ᶠ v : NumberField.FinitePlace F,
          (Ideal.absNorm (v.maximalIdeal.asIdeal
            ^ multiplicity v.maximalIdeal.asIdeal (⨆ i, Ideal.span {y i})) : ℝ) := by
    rw [h1'', Nat.cast_finprod']
  calc ∏ᶠ v : NumberField.FinitePlace F, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)
        ^ multiplicity v.maximalIdeal.asIdeal (⨆ i, Ideal.span {y i})
      = ∏ᶠ v : NumberField.FinitePlace F, (Ideal.absNorm (v.maximalIdeal.asIdeal
          ^ multiplicity v.maximalIdeal.asIdeal (⨆ i, Ideal.span {y i})) : ℝ) :=
        finprod_congr fun v ↦ by rw [map_pow, Nat.cast_pow]
    _ = (Ideal.absNorm (∏ᶠ v : NumberField.FinitePlace F, v.maximalIdeal.asIdeal
          ^ multiplicity v.maximalIdeal.asIdeal (⨆ i, Ideal.span {y i})) : ℝ) := h_prod.symm
    _ = (Ideal.absNorm (⨆ i, Ideal.span {y i}) : ℝ) := by
        rw [NumberField.FinitePlace.finprod_finitePlace_pow_multiplicity hJ_ne]

omit [NumberField K] [NumberField L] in

private lemma mwabs_content_map [Algebra K L] {ι : Type*} (y : ι → 𝓞 K) :
    (⨆ i, Ideal.span {algebraMap (𝓞 K) (𝓞 L) (y i)})
      = (⨆ i, Ideal.span {y i}).map (algebraMap (𝓞 K) (𝓞 L)) := by
  rw [Ideal.map_iSup]
  exact iSup_congr fun i => by rw [Ideal.map_span, Set.image_singleton]

omit [NumberField K] [NumberField L] in

private lemma mwabs_coe_algebraMap [Algebra K L] (y : 𝓞 K) :
    ((algebraMap (𝓞 K) (𝓞 L) y : 𝓞 L) : L) = algebraMap K L (y : K) := rfl

private lemma mwabs_finprod_int [Algebra K L] {ι : Type*} [Fintype ι] [Nonempty ι]
    (y : ι → 𝓞 K) (hy : ∀ i, y i ≠ 0) :
    (∏ᶠ w : NumberField.FinitePlace L, ⨆ i, w (algebraMap K L (y i : K)))
      = (∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((y i : K))) ^ Module.finrank K L := by
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ _ _
  have hy' : ∀ i, algebraMap (𝓞 K) (𝓞 L) (y i) ≠ 0 := fun i h =>
    hy i (NumberField.RingOfIntegers.algebraMap.injective K L (h.trans (map_zero _).symm))
  have hent : ∀ w : NumberField.FinitePlace L, (⨆ i, w (algebraMap K L (y i : K)))
      = ⨆ i, w ((algebraMap (𝓞 K) (𝓞 L) (y i) : 𝓞 L) : L) := fun w =>
    iSup_congr fun i => by rw [mwabs_coe_algebraMap]
  calc (∏ᶠ w : NumberField.FinitePlace L, ⨆ i, w (algebraMap K L (y i : K)))
      = ∏ᶠ w : NumberField.FinitePlace L, ⨆ i, w ((algebraMap (𝓞 K) (𝓞 L) (y i) : 𝓞 L) : L) :=
        finprod_congr hent
    _ = ((Ideal.absNorm (⨆ i, Ideal.span {algebraMap (𝓞 K) (𝓞 L) (y i)}) : ℝ))⁻¹ :=
        mwabs_content_formula _ hy'
    _ = ((Ideal.absNorm ((⨆ i, Ideal.span {y i}).map (algebraMap (𝓞 K) (𝓞 L))) : ℝ))⁻¹ := by
        rw [mwabs_content_map]
    _ = (((Ideal.absNorm (⨆ i, Ideal.span {y i}) : ℝ))⁻¹) ^ Module.finrank K L := by
        rw [Ideal.absNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]
        push_cast
        rw [inv_pow]
    _ = (∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((y i : K))) ^ Module.finrank K L := by
        rw [mwabs_content_formula y hy]

private lemma mwabs_iSup_restrict {M : Type*} [Field M] [NumberField M] {ι : Type*}
    [Finite ι] (v : NumberField.FinitePlace M) {p : ι → Prop} {z : ι → M}
    (hz : ∀ j, ¬ p j → z j = 0) (hne : ∃ j, p j) :
    (⨆ i, v (z i)) = ⨆ i : {j // p j}, v (z i.val) := by
  haveI : Nonempty ι := ⟨hne.choose⟩
  haveI : Nonempty {j // p j} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  refine le_antisymm (ciSup_le fun j => ?_) (ciSup_le fun i => Finite.le_ciSup_of_le i.val le_rfl)
  by_cases hj : p j
  · exact Finite.le_ciSup_of_le ⟨j, hj⟩ le_rfl
  · rw [hz j hj, map_zero]
    exact Real.iSup_nonneg fun i => apply_nonneg v _

private lemma mwabs_hasFiniteMulSupport_iSup {M : Type*} [Field M] [NumberField M]
    {ι : Type*} [Finite ι] [Nonempty ι] {z : ι → M} (hz : ∀ i, z i ≠ 0) :
    (fun w : NumberField.FinitePlace M ↦ ⨆ i, w (z i)).HasFiniteMulSupport :=
  Function.HasFiniteMulSupport.iSup fun i => NumberField.FinitePlace.hasFiniteMulSupport (hz i)

private lemma mwabs_finprod_single [Algebra K L] {c : K} (hc : c ≠ 0) :
    (∏ᶠ w : NumberField.FinitePlace L, w (algebraMap K L c))
      = (∏ᶠ v : NumberField.FinitePlace K, v c) ^ Module.finrank K L := by
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (by apply RingHom.ext_rat)
  have hLc : algebraMap K L c ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hc
  rw [NumberField.FinitePlace.prod_eq_inv_abs_norm hLc,
    NumberField.FinitePlace.prod_eq_inv_abs_norm hc]
  have key : |(Algebra.norm ℚ) ((algebraMap K L) c)|
      = |(Algebra.norm ℚ) c| ^ Module.finrank K L := by
    rw [← Algebra.norm_norm (R := ℚ) (S := K) (a := algebraMap K L c),
      Algebra.norm_algebraMap, map_pow, abs_pow]
  rw [key]
  push_cast
  rw [inv_pow]

private lemma mwabs_finprod_finitePlace [Algebra K L] {ι : Type*} [Finite ι] {x : ι → K}
    (hx : x ≠ 0) :
    (∏ᶠ w : NumberField.FinitePlace L, ⨆ i, w (algebraMap K L (x i)))
      = (∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v (x i)) ^ Module.finrank K L := by
  classical
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  haveI : Nonempty {j // x j ≠ 0} := ⟨⟨j₀, hj₀⟩⟩
  haveI : Fintype {j // x j ≠ 0} := Fintype.ofFinite _

  have hKr : ∀ v : NumberField.FinitePlace K, (⨆ i, v (x i))
      = ⨆ i : {j // x j ≠ 0}, v (x i.val) := fun v =>
    mwabs_iSup_restrict v (fun j hj => not_not.mp hj) ⟨j₀, hj₀⟩
  have hLr : ∀ w : NumberField.FinitePlace L, (⨆ i, w (algebraMap K L (x i)))
      = ⨆ i : {j // x j ≠ 0}, w (algebraMap K L (x i.val)) := fun w =>
    mwabs_iSup_restrict w (fun j hj => by rw [not_not.mp hj, map_zero]) ⟨j₀, hj₀⟩
  rw [finprod_congr hLr, finprod_congr hKr]

  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (𝓞 K)) (fun i : {j // x j ≠ 0} => x i.val)
  choose y hy using hb
  have hbK : ((b : 𝓞 K) : K) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have hyx : ∀ i : {j // x j ≠ 0}, (y i : K) = ((b : 𝓞 K) : K) * x i.val := by
    intro i
    have h := hy i
    rw [Algebra.smul_def] at h
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, h,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap]
  have hy0 : ∀ i : {j // x j ≠ 0}, y i ≠ 0 := by
    intro i h0
    have : (y i : K) = 0 := by rw [h0]; exact map_zero _
    rw [hyx i] at this
    exact i.prop (by
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hbK
      · exact h)
  have hint := mwabs_finprod_int (L := L) y hy0

  have hLs : ∀ w : NumberField.FinitePlace L, (⨆ i, w (algebraMap K L (y i : K)))
      = w (algebraMap K L ((b : 𝓞 K) : K))
        * ⨆ i : {j // x j ≠ 0}, w (algebraMap K L (x i.val)) := by
    intro w
    rw [Real.mul_iSup_of_nonneg (apply_nonneg w _)]
    exact iSup_congr fun i => by rw [hyx i, map_mul, map_mul]
  have hKs : ∀ v : NumberField.FinitePlace K, (⨆ i, v (y i : K))
      = v ((b : 𝓞 K) : K) * ⨆ i : {j // x j ≠ 0}, v (x i.val) := by
    intro v
    rw [Real.mul_iSup_of_nonneg (apply_nonneg v _)]
    exact iSup_congr fun i => by rw [hyx i, map_mul]
  have hbL : algebraMap K L ((b : 𝓞 K) : K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr hbK
  have hx0 : ∀ i : {j // x j ≠ 0}, x i.val ≠ 0 := fun i => i.prop
  have hxL0 : ∀ i : {j // x j ≠ 0}, algebraMap K L (x i.val) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr (hx0 i)
  rw [finprod_congr hLs, finprod_congr hKs,
    finprod_mul_distrib (NumberField.FinitePlace.hasFiniteMulSupport hbL)
      (mwabs_hasFiniteMulSupport_iSup hxL0),
    finprod_mul_distrib (NumberField.FinitePlace.hasFiniteMulSupport hbK)
      (mwabs_hasFiniteMulSupport_iSup hx0),
    mul_pow, mwabs_finprod_single (L := L) hbK] at hint
  have hPne : (∏ᶠ v : NumberField.FinitePlace K, v ((b : 𝓞 K) : K)) ^ Module.finrank K L
      ≠ 0 := by
    rw [NumberField.FinitePlace.prod_eq_inv_abs_norm hbK]
    have : Algebra.norm ℚ ((b : 𝓞 K) : K) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hbK
    positivity
  exact mul_left_cancel₀ hPne hint

open scoped Classical in

private lemma mwabs_arch [Algebra K L] {ι : Type*} [Finite ι] (x : ι → K) :
    (∏ w : InfinitePlace L, (⨆ i, w (algebraMap K L (x i))) ^ w.mult)
      = (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) ^ Module.finrank K L := by
  rw [← Finset.prod_fiberwise Finset.univ
    (fun w : InfinitePlace L => w.comap (algebraMap K L))
    (fun w => (⨆ i, w (algebraMap K L (x i))) ^ w.mult), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hfib : ∀ w ∈ Finset.univ.filter
      (fun w : InfinitePlace L => w.comap (algebraMap K L) = v),
      (⨆ i, w (algebraMap K L (x i))) ^ w.mult = (⨆ i, v (x i)) ^ w.mult := by
    intro w hw
    have hcom : w.comap (algebraMap K L) = v := (Finset.mem_filter.mp hw).2
    have hsup : (⨆ i, w (algebraMap K L (x i))) = ⨆ i, v (x i) := by
      refine iSup_congr fun i => ?_
      rw [← hcom, NumberField.InfinitePlace.comap_apply]
    rw [hsup]
  rw [Finset.prod_congr rfl hfib, Finset.prod_pow_eq_pow_sum, mwabs_sum_mult_comap v, pow_mul]

private lemma mwabs_core [Algebra K L] {ι : Type*} [Finite ι] (x : ι → K) :
    Height.mulHeight (fun i => algebraMap K L (x i))
      = Height.mulHeight x ^ Module.finrank K L := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : (fun i => algebraMap K L ((0 : ι → K) i)) = (0 : ι → L) := by
      funext i; simp
    rw [h0, Height.mulHeight_zero, Height.mulHeight_zero, one_pow]
  · have hx' : (fun i => algebraMap K L (x i)) ≠ 0 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
      refine Function.ne_iff.mpr ⟨j, fun hcontra => hj ?_⟩
      have : algebraMap K L (x j) = 0 := by simpa using hcontra
      exact (map_eq_zero (algebraMap K L)).mp this
    rw [NumberField.mulHeight_eq hx', NumberField.mulHeight_eq hx, mul_pow,
      mwabs_arch x, mwabs_finprod_finitePlace hx]

end helpers

/-- The logarithmic height of a tuple pushed forward along an extension of
number fields is the degree of the extension times the original height. -/
theorem Height.logHeight_algebraMap {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {ι : Type*} [Finite ι] (x : ι → K) :
    logHeight (fun i => algebraMap K L (x i))
      = (Module.finrank K L : ℝ) * logHeight x := by
  rw [Height.logHeight_eq_log_mulHeight, Height.logHeight_eq_log_mulHeight, mwabs_core,
    Real.log_pow]
