/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsIntegral_mem_span_of_adjoin_simple_constants_transcendental.lean`
and
`P2M/Sol/S_IsIntegral_mem_span_of_adjoin_simple_constants_transcendental.lean`
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

public import Mathlib.Data.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.GaussLemma

@[expose] public section



set_option autoImplicit false

noncomputable section

open Polynomial
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin

namespace WLightR8a

variable {K : Type*} [Field K] [Algebra ℂ K]

omit [Algebra ℂ K] in

private theorem isIntegral_subring_iff (T : Subring K) (y : K) :
    IsIntegral ↥T y ↔ ∃ p : K[X], p.Monic ∧ (∀ n, p.coeff n ∈ T) ∧ p.eval y = 0 := by
  constructor
  · rintro ⟨p, hm, hp⟩
    refine ⟨p.map (algebraMap ↥T K), hm.map _, fun n ↦ ?_, ?_⟩
    · rw [Polynomial.coeff_map]; exact (p.coeff n).2
    · rwa [Polynomial.eval_map]
  · rintro ⟨p, hm, hc, hp⟩
    have hl : p ∈ Polynomial.lifts (algebraMap ↥T K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n; exact ⟨⟨p.coeff n, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hm
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, hp]

omit [Algebra ℂ K] in

private theorem isIntegral_subalgebra_iff {R₀ : Type*} [CommRing R₀] [Algebra R₀ K]
    (T : Subalgebra R₀ K) (y : K) :
    IsIntegral ↥T y ↔ ∃ p : K[X], p.Monic ∧ (∀ n, p.coeff n ∈ T) ∧ p.eval y = 0 := by
  constructor
  · rintro ⟨p, hm, hp⟩
    refine ⟨p.map (algebraMap ↥T K), hm.map _, fun n ↦ ?_, ?_⟩
    · rw [Polynomial.coeff_map]; exact (p.coeff n).2
    · rwa [Polynomial.eval_map]
  · rintro ⟨p, hm, hc, hp⟩
    have hl : p ∈ Polynomial.lifts (algebraMap ↥T K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n; exact ⟨⟨p.coeff n, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hm
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, hp]

omit [Algebra ℂ K] in

private theorem isIntegral_adjoin_iff_closure {R₀ : Type*} [CommRing R₀] [Algebra R₀ K]
    (B : Set K) (y : K) :
    IsIntegral ↥(Algebra.adjoin R₀ B) y ↔
      IsIntegral ↥(Subring.closure (Set.range (algebraMap R₀ K) ∪ B)) y := by
  rw [isIntegral_subalgebra_iff, isIntegral_subring_iff]
  simp only [Algebra.mem_adjoin_iff]

omit [Algebra ℂ K] in

private theorem isIntegral_of_isIntegral_adjoin_singleton {A : Type*} [CommRing A] [Algebra A K]
    {r z : K}
    (hr : IsIntegral A r) (hz : IsIntegral ↥(Algebra.adjoin A {r}) z) : IsIntegral A z := by
  haveI : Algebra.IsIntegral A ↥(Algebra.adjoin A {r}) :=
    Algebra.IsIntegral.adjoin fun _ h ↦ by rw [Set.mem_singleton_iff] at h; rw [h]; exact hr
  exact isIntegral_trans z hz

private theorem algebraMap_subfield_apply (F : IntermediateField ℚ ℂ) (c : ↥F) :
    algebraMap ↥F K c = algebraMap ℂ K (c : ℂ) := rfl

private theorem range_algebraMap_subfield (F : IntermediateField ℚ ℂ) :
    Set.range (algebraMap ↥F K) = ⇑(algebraMap ℂ K) '' (F : Set ℂ) := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, c.2, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨⟨c, hc⟩, rfl⟩

private theorem algebraMap_subfield_apply' (F : IntermediateField ℚ ℂ) (E₀ : IntermediateField ↥F ℂ)
    (c : ↥E₀) : algebraMap ↥E₀ K c = algebraMap ℂ K (c : ℂ) := rfl

private theorem range_algebraMap_subfield' (F : IntermediateField ℚ ℂ)
    (E₀ : IntermediateField ↥F ℂ) :
    Set.range (algebraMap ↥E₀ K) = ⇑(algebraMap ℂ K) '' (E₀ : Set ℂ) := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, c.2, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨⟨c, hc⟩, rfl⟩

private theorem charZero_K : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℂ K).injective

private theorem charZero_KFld (F : IntermediateField ℚ ℂ) (L₀ : IntermediateField ↥F K) :
    CharZero ↥L₀ :=
  haveI : CharZero ↥F := charZero_of_injective_algebraMap (algebraMap ℚ ↥F).injective
  charZero_of_injective_algebraMap (algebraMap ↥F ↥L₀).injective

variable (F : IntermediateField ℚ ℂ) (t : K) (S : Set K)

private abbrev KFld : IntermediateField ↥F K := IntermediateField.adjoin ↥F S

private abbrev TRng : Subalgebra ↥F K := Algebra.adjoin ↥F {t}

private def RSet : Set K := {y | y ∈ KFld F S ∧ IsIntegral ↥(TRng F t) y}

private abbrev RFld : IntermediateField ↥F K := (↥F)⟮t⟯

private abbrev KFldT : IntermediateField ↥(RFld F t) K := IntermediateField.adjoin ↥(RFld F t) S

private noncomputable instance algebraTRng_KFldT : Algebra ↥(TRng F t) ↥(KFldT F t S) :=
  ((algebraMap ↥(RFld F t) ↥(KFldT F t S)).comp (algebraMap ↥(TRng F t) ↥(RFld F t))).toAlgebra

private noncomputable instance smulTRng_KFldT : SMul ↥(TRng F t) ↥(KFldT F t S) := Algebra.toSMul

private noncomputable instance moduleTRng_KFldT : Module ↥(TRng F t) ↥(KFldT F t S) :=
  Algebra.toModule

private instance : IsScalarTower ↥(TRng F t) ↥(RFld F t) ↥(KFldT F t S) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

private instance : IsScalarTower ↥(TRng F t) ↥(KFldT F t S) K :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

set_option synthInstance.maxHeartbeats 1600000 in
private instance : FaithfulSMul ↥(TRng F t) ↥(KFldT F t S) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact (FaithfulSMul.algebraMap_injective ↥(RFld F t) ↥(KFldT F t S)).comp
    (FaithfulSMul.algebraMap_injective ↥(TRng F t) ↥(RFld F t))

private abbrev RFa : Subalgebra ↥(TRng F t) ↥(KFldT F t S) :=
  integralClosure ↥(TRng F t) ↥(KFldT F t S)

set_option synthInstance.maxHeartbeats 800000 in
private instance commRing_RFa : CommRing ↥(RFa F t S) := inferInstance

private theorem KFldT_restrictScalars (htS : t ∈ S) :
    (KFldT F t S).restrictScalars ↥F = KFld F S := by
  rw [show KFldT F t S = IntermediateField.adjoin ↥(RFld F t) S from rfl,
    IntermediateField.adjoin_adjoin_left]
  congr 1
  simp [Set.insert_eq_self.mpr htS]

private theorem mem_KFldT_iff (htS : t ∈ S) (z : K) : z ∈ KFldT F t S ↔ z ∈ KFld F S := by
  rw [← KFldT_restrictScalars F t S htS, IntermediateField.mem_restrictScalars]

section instances

private instance : IsDomain ↥(TRng F t) := Subalgebra.isDomain _

private def TRngEquiv (ht : Transcendental ℂ t) : (↥F)[X] ≃ₐ[↥F] ↥(TRng F t) :=
  Polynomial.algEquivOfTranscendental ↥F t
    (ht.restrictScalars (FaithfulSMul.algebraMap_injective ↥F ℂ))

private theorem isPrincipalIdealRing_TRng (ht : Transcendental ℂ t) :
    IsPrincipalIdealRing ↥(TRng F t) :=
  IsPrincipalIdealRing.of_surjective (TRngEquiv F t ht).toRingEquiv.toRingHom
    (TRngEquiv F t ht).surjective

private theorem finiteDimensional_KFldT (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral ↥(TRng F t) s) :
    FiniteDimensional ↥(RFld F t) ↥(KFldT F t S) := by
  haveI : Finite ↥S := hSfin.to_subtype
  refine IntermediateField.finiteDimensional_adjoin (fun s hs => ?_)
  exact (hSint s hs).tower_top

private instance charZero_KFldT : CharZero ↥(KFldT F t S) :=
  haveI : CharZero ↥(RFld F t) := charZero_KFld F (RFld F t)
  charZero_of_injective_algebraMap (algebraMap ↥(RFld F t) ↥(KFldT F t S)).injective

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isDedekindDomain_RFa (ht : Transcendental ℂ t) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral ↥(TRng F t) s) : IsDedekindDomain ↥(RFa F t S) := by
  haveI := isPrincipalIdealRing_TRng F t ht
  haveI := finiteDimensional_KFldT F t S hSfin hSint
  exact integralClosure.isDedekindDomain ↥(TRng F t) ↥(RFld F t) ↥(KFldT F t S)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isFractionRing_RFa (ht : Transcendental ℂ t) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral ↥(TRng F t) s) :
    IsFractionRing ↥(RFa F t S) ↥(KFldT F t S) := by
  have hPID := isPrincipalIdealRing_TRng F t ht
  haveI : IsDedekindDomain ↥(TRng F t) := @IsPrincipalIdealRing.isDedekindDomain _ _ _ hPID
  haveI := finiteDimensional_KFldT F t S hSfin hSint
  exact integralClosure.isFractionRing_of_finite_extension ↥(RFld F t) ↥(KFldT F t S)

end instances

set_option synthInstance.maxHeartbeats 3200000 in
set_option maxHeartbeats 6400000 in

private theorem isIntegrallyClosed_RFa_polynomial (ht : Transcendental ℂ t) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral ↥(TRng F t) s) :
    IsIntegrallyClosed (Polynomial ↥(RFa F t S)) := by
  haveI : IsDedekindDomain ↥(RFa F t S) := isDedekindDomain_RFa F t S ht hSfin hSint
  infer_instance

private theorem algebraMap_adjoinF_mem {c : ℂ} {z : ℂ} (hz : z ∈ IntermediateField.adjoin ↥F {c}) :
    algebraMap ℂ K z ∈
      IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c} := by
  set f := IsScalarTower.toAlgHom ↥F ℂ K
  have h1 : algebraMap ℂ K z ∈ (IntermediateField.adjoin ↥F {c}).map f := by
    rw [← SetLike.mem_coe, IntermediateField.coe_map]
    exact ⟨z, hz, rfl⟩
  rw [IntermediateField.adjoin_map, Set.image_singleton] at h1
  have h2 : IntermediateField.adjoin ↥F {f c} ≤
      (IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}).restrictScalars ↥F :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (IntermediateField.mem_adjoin_simple_self ↥(KFld F S) _))
  exact h2 h1

private theorem closure_adjoin_le {c : ℂ} :
    Subfield.closure
        (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S) ≤
      (IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}).toSubfield := by
  refine Subfield.closure_le.mpr ?_
  rintro y (⟨z, hz, rfl⟩ | hy)
  · exact algebraMap_adjoinF_mem F S hz
  · exact (IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}).algebraMap_mem
      ⟨y, IntermediateField.subset_adjoin ↥F S hy⟩

private theorem t_mem_RSet (htS : t ∈ S) : t ∈ RSet F t S :=
  ⟨IntermediateField.subset_adjoin ↥F S htS, isIntegral_algebraMap
    (x := (⟨t, Algebra.self_mem_adjoin_singleton ↥F t⟩ : ↥(TRng F t)))⟩

private theorem algebraMap_mem_RSet (z : ↥F) : algebraMap ↥F K z ∈ RSet F t S :=
  ⟨(KFld F S).algebraMap_mem z, isIntegral_algebraMap (x := algebraMap ↥F ↥(TRng F t) z)⟩

variable (c : ℂ)

set_option synthInstance.maxHeartbeats 1600000 in

private def rfPolyEval : (↥(RFa F t S))[X] →+* K :=
  Polynomial.eval₂RingHom ((algebraMap ↥(KFldT F t S) K).comp (RFa F t S).val.toRingHom)
    (algebraMap ℂ K c)

variable {c}

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem rfPolyEval_injective
    (htc : Transcendental ↥(KFldT F t S) (algebraMap ℂ K c)) :
    Function.Injective (rfPolyEval F t S c) := by
  have h1 : Function.Injective
      (Polynomial.aeval (R := ↥(KFldT F t S)) (algebraMap ℂ K c)) :=
    transcendental_iff_injective.mp htc
  have h2 : Function.Injective (Polynomial.map (RFa F t S).val.toRingHom) :=
    Polynomial.map_injective _ Subtype.val_injective
  have hcomp : ⇑(rfPolyEval F t S c) =
      ⇑(Polynomial.aeval (R := ↥(KFldT F t S)) (algebraMap ℂ K c)) ∘
        Polynomial.map (RFa F t S).val.toRingHom := by
    funext q
    simp only [rfPolyEval, Polynomial.coe_eval₂RingHom, Function.comp_apply,
      Polynomial.aeval_def, Polynomial.eval₂_map]
  rw [hcomp]; exact h1.comp h2

set_option synthInstance.maxHeartbeats 1600000 in

private theorem isIntegral_KFldT_of (htS : t ∈ S) {y : K} (hyK : y ∈ KFld F S)
    (hyI : IsIntegral ↥(TRng F t) y) :
    IsIntegral ↥(TRng F t) (⟨y, (mem_KFldT_iff F t S htS y).mpr hyK⟩ : ↥(KFldT F t S)) := by
  obtain ⟨P, hPm, hPe⟩ := hyI
  refine ⟨P, hPm, ?_⟩
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero, ← hPe, Polynomial.eval₂_def, Polynomial.eval₂_def,
    Polynomial.sum_def, Polynomial.sum_def, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul]
  rfl

private theorem mem_range_rfPolyEval_of_mem_RSet (htS : t ∈ S) {y : K} (hy : y ∈ RSet F t S) :
    y ∈ Set.range ⇑(rfPolyEval F t S c) := by
  obtain ⟨hyK, hyI⟩ := hy
  exact ⟨Polynomial.C ⟨_, isIntegral_KFldT_of F t S htS hyK hyI⟩, by simp [rfPolyEval]⟩

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem evalF_mem_range_rfPolyEval (htS : t ∈ S) (q : (↥F)[X]) :
    Polynomial.aeval (algebraMap ℂ K c) q ∈ Set.range ⇑(rfPolyEval F t S c) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p₁, h₁⟩ := hp; obtain ⟨p₂, h₂⟩ := hq
    exact ⟨p₁ + p₂, by rw [map_add, map_add, h₁, h₂]⟩
  | monomial n z =>
    have hz := algebraMap_mem_RSet F t S z
    obtain ⟨w, hw⟩ := mem_range_rfPolyEval_of_mem_RSet F t S htS (c := c) hz
    refine ⟨w * Polynomial.X ^ n, ?_⟩
    rw [Polynomial.aeval_monomial, map_mul, map_pow, hw]
    simp only [rfPolyEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      algebraMap_subfield_apply]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem evalF_ne_zero (hc : Transcendental ↥F c) {q : (↥F)[X]} (hq : q ≠ 0) :
    Polynomial.aeval (algebraMap ℂ K c) q ≠ 0 := by
  intro h0
  rw [Polynomial.aeval_algebraMap_apply] at h0
  have h1 : Polynomial.aeval c q = 0 :=
    (map_eq_zero_iff _ (algebraMap ℂ K).injective).mp h0
  exact hq ((transcendental_iff.mp hc) q h1)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem range_rfPolyEval_subset_span (htS : t ∈ S) :
    Set.range ⇑(rfPolyEval F t S c) ⊆
      (Submodule.span ℂ (RSet F t S) : Set K) := by
  rintro _ ⟨p, rfl⟩
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n z =>
    have hshape : rfPolyEval F t S c (Polynomial.monomial n z) =
        (c ^ n) • ((z : ↥(KFldT F t S)) : K) := by
      rw [Algebra.smul_def, map_pow, rfPolyEval]
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
      exact mul_comm _ _
    rw [hshape]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨?_, ?_⟩)
    · exact (mem_KFldT_iff F t S htS _).mp (z : ↥(KFldT F t S)).2
    · have hzK : ((z : ↥(KFldT F t S)) : K) =
          algebraMap ↥(KFldT F t S) K (z : ↥(KFldT F t S)) := rfl
      rw [hzK]
      exact (z.2 : IsIntegral ↥(TRng F t) (z : ↥(KFldT F t S))).algebraMap

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_clear_denominator (htS : t ∈ S) {a : K}
    (ha : a ∈ Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) ({t} : Set K)) :
    ∃ q : (↥F)[X], q ≠ 0 ∧
      Polynomial.aeval (algebraMap ℂ K c) q * a ∈ Set.range ⇑(rfPolyEval F t S c) := by
  induction ha using Algebra.adjoin_induction with
  | mem w hw =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [map_one, one_mul, Set.mem_singleton_iff.mp hw]
    exact mem_range_rfPolyEval_of_mem_RSet F t S htS (t_mem_RSet F t S htS)
  | algebraMap z =>
    obtain ⟨r, s, hz⟩ := (IntermediateField.mem_adjoin_simple_iff ↥F ((z : ℂ))).mp z.2
    by_cases hs : Polynomial.aeval c s = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      have hz0 : (z : ℂ) = 0 := by rw [hz, hs, div_zero]
      have hmap0 : algebraMap ↥(IntermediateField.adjoin ↥F {c}) K z = 0 := by
        rw [algebraMap_subfield_apply', hz0, map_zero]
      rw [map_one, one_mul, hmap0]
      exact ⟨0, map_zero _⟩
    · refine ⟨s, fun h0 => hs (by rw [h0, map_zero]), ?_⟩
      have hid : Polynomial.aeval (algebraMap ℂ K c) s *
          algebraMap ↥(IntermediateField.adjoin ↥F {c}) K z =
          Polynomial.aeval (algebraMap ℂ K c) r := by
        rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_algebraMap_apply,
          algebraMap_subfield_apply', ← map_mul]
        congr 1; rw [hz]; field_simp
      rw [hid]; exact evalF_mem_range_rfPolyEval F t S htS r
  | add u v _ _ ihu ihv =>
    obtain ⟨q₁, h₁0, A₁, hA₁⟩ := ihu; obtain ⟨q₂, h₂0, A₂, hA₂⟩ := ihv
    obtain ⟨B₁, hB₁⟩ := evalF_mem_range_rfPolyEval F t S htS (c := c) q₁
    obtain ⟨B₂, hB₂⟩ := evalF_mem_range_rfPolyEval F t S htS (c := c) q₂
    refine ⟨q₁ * q₂, mul_ne_zero h₁0 h₂0, B₂ * A₁ + B₁ * A₂, ?_⟩
    rw [map_add, map_mul, map_mul, hB₁, hB₂, hA₁, hA₂, map_mul]; ring
  | mul u v _ _ ihu ihv =>
    obtain ⟨q₁, h₁0, A₁, hA₁⟩ := ihu; obtain ⟨q₂, h₂0, A₂, hA₂⟩ := ihv
    refine ⟨q₁ * q₂, mul_ne_zero h₁0 h₂0, A₁ * A₂, ?_⟩
    rw [map_mul, map_mul, hA₁, hA₂]; ring

variable {F t}

set_option maxHeartbeats 51200000 in
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxSynthPendingDepth 3 in

private theorem mem_span_RSet_of_adjoin_simple_transcendental
    (ht : Transcendental ℂ t) (htS : t ∈ S) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral ↥(TRng F t) s)
    {c : ℂ} (hc : Transcendental ↥F c)
    (htc : Transcendental ↥(KFldT F t S) (algebraMap ℂ K c))
    {x : K}
    (hxK : x ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    (hxint : IsIntegral ↥(Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) ({t} : Set K)) x) :
    x ∈ Submodule.span ℂ (RSet F t S) := by
  classical
  set c' : K := algebraMap ℂ K c with hc'

  set ψ : FractionRing ((↥(RFa F t S))[X]) →+* K :=
    IsFractionRing.lift (rfPolyEval_injective F t S htc) with hψ
  have hψalg : ∀ a : (↥(RFa F t S))[X], ψ (algebraMap _ _ a) = rfPolyEval F t S c a :=
    fun a => IsFractionRing.lift_algebraMap _ _
  have hψinj : Function.Injective ψ := ψ.injective
  haveI hDD : IsDedekindDomain ↥(RFa F t S) := isDedekindDomain_RFa F t S ht hSfin hSint
  haveI hFR : IsFractionRing ↥(RFa F t S) ↥(KFldT F t S) :=
    isFractionRing_RFa F t S ht hSfin hSint

  have hrange : ∀ z ∈ IntermediateField.adjoin ↥(KFldT F t S) {c'}, z ∈ ψ.fieldRange := by
    intro z hz
    rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield] at hz
    refine Subfield.closure_le (t := ψ.fieldRange) |>.mpr ?_ hz
    rintro w (⟨w', rfl⟩ | rfl)
    · obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := ↥(RFa F t S)) w'
      rw [← hrs]
      have h1 : algebraMap ↥(KFldT F t S) K (algebraMap ↥(RFa F t S) ↥(KFldT F t S) r) =
          ψ (algebraMap _ _ (Polynomial.C r)) := by rw [hψalg]; simp [rfPolyEval]
      have h2 : algebraMap ↥(KFldT F t S) K (algebraMap ↥(RFa F t S) ↥(KFldT F t S) s) =
          ψ (algebraMap _ _ (Polynomial.C s)) := by rw [hψalg]; simp [rfPolyEval]
      rw [map_div₀, h1, h2]
      exact div_mem (RingHom.mem_fieldRange_self ψ _) (RingHom.mem_fieldRange_self ψ _)
    · exact ⟨algebraMap _ _ Polynomial.X, by rw [hψalg, hc']; simp [rfPolyEval]⟩

  have hxψ : x ∈ ψ.fieldRange := by
    refine hrange x ?_
    have h1 := closure_adjoin_le F S hxK
    have heq : (IntermediateField.adjoin ↥(KFld F S) {c'}).toSubfield =
        (IntermediateField.adjoin ↥(KFldT F t S) {c'}).toSubfield := by
      rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield]
      have hrng : Set.range ⇑(algebraMap ↥(KFld F S) K) =
          Set.range ⇑(algebraMap ↥(KFldT F t S) K) := by
        ext z
        exact ⟨fun ⟨w, hw⟩ => ⟨⟨w, (mem_KFldT_iff F t S htS w).mpr w.2⟩, hw⟩,
          fun ⟨w, hw⟩ => ⟨⟨w, (mem_KFldT_iff F t S htS w).mp w.2⟩, hw⟩⟩
      rw [hrng]
    rw [← IntermediateField.mem_toSubfield, ← heq]; exact h1

  obtain ⟨P, hPmonic, hPc, hPx⟩ := (isIntegral_subalgebra_iff _ x).mp hxint
  set n := P.natDegree with hn
  have hrel : x ^ n + ∑ k ∈ Finset.range n, (P.coeff k) * x ^ k = 0 := by
    have h1 := hPx
    rw [hPmonic.as_sum, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finsetSum] at h1
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      at h1
    linear_combination h1
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at hrel; simp at hrel
    · exact h0

  choose qd hqd0 hqdW using fun (k : ℕ) (hk : k ∈ Finset.range n) =>
    exists_clear_denominator F t S htS (c := c) (hPc k)
  set Q : ℕ → (↥F)[X] := fun k => if h : k ∈ Finset.range n then qd k h else 1 with hQ
  have hQ0 : ∀ k, Q k ≠ 0 := by
    intro k; by_cases h : k ∈ Finset.range n
    · simp only [hQ, dif_pos h]; exact hqd0 k h
    · simp only [hQ, dif_neg h]; exact one_ne_zero
  set D : (↥F)[X] := ∏ k ∈ Finset.range n, Q k with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hQ0 k
  set Dv : K := Polynomial.aeval c' D with hDv
  have hDv0 : Dv ≠ 0 := evalF_ne_zero F hc hD0
  have hDvrange : Dv ∈ Set.range ⇑(rfPolyEval F t S c) := evalF_mem_range_rfPolyEval F t S htS D

  have hbW : ∀ k ∈ Finset.range n, Dv ^ (n - k) * (P.coeff k) ∈
      Set.range ⇑(rfPolyEval F t S c) := by
    intro k hk
    have hQk : Q k = qd k hk := by simp only [hQ, dif_pos hk]
    obtain ⟨A₁, hA₁⟩ := hqdW k hk
    obtain ⟨B₁, hB₁⟩ := evalF_mem_range_rfPolyEval F t S htS (c := c)
      ((∏ j ∈ (Finset.range n).erase k, Q j) * D ^ (n - k - 1))
    refine ⟨B₁ * A₁, ?_⟩
    rw [map_mul, hB₁, hA₁, map_mul, map_pow, ← hDv]
    have hDvsplit : Dv ^ (n - k) = Polynomial.aeval c' (qd k hk) *
        Polynomial.aeval c' (∏ j ∈ (Finset.range n).erase k, Q j) * Dv ^ (n - k - 1) := by
      have h1 : Polynomial.aeval c' (qd k hk) *
          Polynomial.aeval c' (∏ j ∈ (Finset.range n).erase k, Q j) = Dv := by
        rw [← hQk, ← map_mul, Finset.mul_prod_erase _ _ hk, hDv, hD]
      rw [h1, ← pow_succ']
      congr 1
      have hkn := Finset.mem_range.mp hk; omega
    rw [hDvsplit]; ring

  set y : K := Dv * x with hy
  have hDψ : Dv ∈ ψ.fieldRange := by
    obtain ⟨a, ha⟩ := hDvrange
    exact ⟨algebraMap _ _ a, by rw [hψalg]; exact ha⟩
  have hyψ : y ∈ ψ.fieldRange := mul_mem hDψ hxψ
  have hyrel : y ^ n + ∑ k ∈ Finset.range n, (Dv ^ (n - k) * (P.coeff k)) * y ^ k = 0 := by
    have h1 : ∀ k ∈ Finset.range n, (Dv ^ (n - k) * (P.coeff k)) * y ^ k =
        Dv ^ n * ((P.coeff k) * x ^ k) := by
      intro k hk
      have hkn : k ≤ n := (Finset.mem_range.mp hk).le
      rw [hy, mul_pow, show Dv ^ n = Dv ^ (n - k) * Dv ^ k from by
        rw [← pow_add, Nat.sub_add_cancel hkn]]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, hy, mul_pow, ← mul_add, hrel, mul_zero]

  choose B hB using fun k (hk : k ∈ Finset.range n) => hbW k hk
  set BB : ℕ → (↥(RFa F t S))[X] := fun k => if h : k ∈ Finset.range n then B k h else 0 with hBB
  obtain ⟨m, hm⟩ := RingHom.mem_fieldRange.mp hyψ
  have hmrel : m ^ n + ∑ k ∈ Finset.range n, algebraMap _ _ (BB k) * m ^ k = 0 := by
    apply hψinj
    rw [map_add, map_pow, map_sum, map_zero, hm]
    rw [show (∑ k ∈ Finset.range n, ψ (algebraMap _ _ (BB k) * m ^ k)) =
        ∑ k ∈ Finset.range n, (Dv ^ (n - k) * (P.coeff k)) * y ^ k from
      Finset.sum_congr rfl fun k hk => by
        rw [map_mul, map_pow, hm, hψalg]; simp only [hBB, dif_pos hk]; rw [hB k hk]]
    exact hyrel

  have hmint : IsIntegral ((↥(RFa F t S))[X]) m := by
    refine ⟨Polynomial.X ^ n + ∑ k ∈ Finset.range n, Polynomial.C (BB k) * Polynomial.X ^ k,
      ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add ((Polynomial.degree_sum_le _ _).trans_lt
        ((Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun k hk =>
          (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt
            (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hk))))
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_finsetSum]
      rw [show (∑ k ∈ Finset.range n, Polynomial.eval₂ (algebraMap _ _) m
          (Polynomial.C (BB k) * Polynomial.X ^ k)) =
          ∑ k ∈ Finset.range n, algebraMap _ _ (BB k) * m ^ k from
        Finset.sum_congr rfl fun k _ => by
          rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
            Polynomial.eval₂_X]]
      exact hmrel
  haveI hDomRFa : IsDomain ↥(RFa F t S) := Subalgebra.isDomain _
  haveI hICR : IsIntegrallyClosed ↥(RFa F t S) := inferInstance
  haveI hICX : IsIntegrallyClosed ((↥(RFa F t S))[X]) :=
    isIntegrallyClosed_RFa_polynomial F t S ht hSfin hSint
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hmint
  have hyrange : y ∈ Set.range ⇑(rfPolyEval F t S c) :=
    ⟨a, by rw [← hψalg, ha, hm]⟩
  have hyspan := range_rfPolyEval_subset_span F t S htS hyrange

  have hsmul : (Polynomial.aeval c D : ℂ) • x = y := by
    rw [Algebra.smul_def, hy, hDv, Polynomial.aeval_algebraMap_apply]
  have hs0 : (Polynomial.aeval c D : ℂ) ≠ 0 := by
    intro h0; exact hD0 ((transcendental_iff.mp hc) D h0)
  have hsx : (Polynomial.aeval c D : ℂ) • x ∈ Submodule.span ℂ (RSet F t S) := by
    rw [hsmul]; exact hyspan
  have h2 := Submodule.smul_mem (Submodule.span ℂ (RSet F t S))
    ((Polynomial.aeval c D : ℂ))⁻¹ hsx
  rwa [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hs0, one_smul] at h2

variable (F) in
private theorem mem_KFld_iff_closure (z : K) :
    z ∈ KFld F S ↔ z ∈ Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) := by
  rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield,
    range_algebraMap_subfield]

variable (F t) in
private theorem isIntegral_TRng_iff_closure (z : K) :
    IsIntegral ↥(TRng F t) z ↔
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ {t})) z := by
  rw [isIntegral_adjoin_iff_closure, range_algebraMap_subfield]

variable (F) in
private theorem isIntegral_adjoin_iff_closure' (E₀ : IntermediateField ↥F ℂ) (z : K) :
    IsIntegral ↥(Algebra.adjoin ↥E₀ ({t} : Set K)) z ↔
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (E₀ : Set ℂ) ∪ {t})) z := by
  rw [isIntegral_adjoin_iff_closure, range_algebraMap_subfield']

variable (F t) in
private theorem KFldT_toSubfield_eq (htS : t ∈ S) :
    (KFldT F t S).toSubfield = Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) := by
  have h1 : (KFldT F t S).toSubfield = ((KFldT F t S).restrictScalars ↥F).toSubfield := rfl
  rw [h1, KFldT_restrictScalars F t S htS, IntermediateField.adjoin_toSubfield,
    range_algebraMap_subfield]

variable (F t) in
private theorem transcendental_KFldT_of_closure (htS : t ∈ S)
    (htc : Transcendental ↥(Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S))
      (algebraMap ℂ K c)) :
    Transcendental ↥(KFldT F t S) (algebraMap ℂ K c) := by
  rw [Transcendental] at htc ⊢
  intro ⟨P, hP0, hPe⟩
  set e := (RingEquiv.subfieldCongr (KFldT_toSubfield_eq F t S htS)).toRingHom
  refine htc ⟨P.map e, fun h => hP0 (Polynomial.map_eq_zero_iff (RingEquiv.injective _) |>.mp h),
    ?_⟩
  have hcomp : (algebraMap ↥(Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S)) K).comp e =
      algebraMap ↥(KFldT F t S) K := by
    ext z; rfl
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
  exact hPe

end WLightR8a

/-- Span descent after adjoining an independent transcendental constant.

Let `t` be transcendental over `ℂ`, let `S` be a finite set containing `t`
whose elements are integral over the ring generated by the constants `F`
and `t`, and let `c` be transcendental over `F` whose image remains
transcendental over the field generated by `F` and `S`. Then every element
of the field obtained by adjoining `c` to the constants and `S` which is
integral over the corresponding ring with `t` adjoined lies in the
`ℂ`-span of the elements of the original field integral over that ring. -/
public theorem IsIntegral.mem_span_of_adjoin_simple_constants_transcendental
    {K : Type*} [Field K] [Algebra ℂ K]
    (F : IntermediateField ℚ ℂ) (t : K) (ht : Transcendental ℂ t)
    (S : Set K) (htS : t ∈ S) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral
      ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ {t})) s)
    (c : ℂ) (hc : Transcendental ↥F c)
    (htc : Transcendental ↥(Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S))
      (algebraMap ℂ K c))
    (y : K)
    (hyS : y ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    (hyB : IsIntegral ↥(Subring.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ {t})) y) :
    y ∈ Submodule.span ℂ {z : K | z ∈ Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) ∧
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ {t})) z} := by
  have hSint' : ∀ s ∈ S, IsIntegral ↥(WLightR8a.TRng F t) s := fun s hs =>
    (WLightR8a.isIntegral_TRng_iff_closure F t s).mpr (hSint s hs)
  have hyB' : IsIntegral
      ↥(Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) ({t} : Set K)) y :=
    (WLightR8a.isIntegral_adjoin_iff_closure' F _ y).mpr hyB
  have htc' := WLightR8a.transcendental_KFldT_of_closure F t S htS htc
  have h := WLightR8a.mem_span_RSet_of_adjoin_simple_transcendental
    S ht htS hSfin hSint' hc htc' hyS hyB'
  refine Submodule.span_mono (fun z hz => ?_) h
  exact ⟨(WLightR8a.mem_KFld_iff_closure F S z).mp hz.1,
    (WLightR8a.isIntegral_TRng_iff_closure F t z).mp hz.2⟩

