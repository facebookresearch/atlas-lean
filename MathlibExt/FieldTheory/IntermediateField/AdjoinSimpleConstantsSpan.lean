/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsIntegral_mem_span_of_adjoin_simple_constants.lean`
and
`P2M/Sol/S_IsIntegral_mem_span_of_adjoin_simple_constants.lean`
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

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

open Polynomial
open scoped IntermediateField

namespace AdjoinSimpleConstantsAux

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
private theorem isIntegral_of_isIntegral_adjoin_singleton {A : Type*} [CommRing A]
    [Algebra A K] {r z : K}
    (hr : IsIntegral A r) (hz : IsIntegral ↥(Algebra.adjoin A {r}) z) : IsIntegral A z := by
  haveI : Algebra.IsIntegral A ↥(Algebra.adjoin A {r}) :=
    Algebra.IsIntegral.adjoin fun _ h ↦ by rw [Set.mem_singleton_iff] at h; rw [h]; exact hr
  exact isIntegral_trans z hz

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

private theorem charZero_KFld (F : IntermediateField ℚ ℂ) (L₀ : IntermediateField ↥F K) :
    CharZero ↥L₀ :=
  haveI : CharZero ↥F := charZero_of_injective_algebraMap (algebraMap ℚ ↥F).injective
  charZero_of_injective_algebraMap (algebraMap ↥F ↥L₀).injective

variable (F : IntermediateField ℚ ℂ) (B S : Set K)

private noncomputable abbrev KFld : IntermediateField ↥F K := IntermediateField.adjoin ↥F S

private noncomputable abbrev TRng : Subalgebra ↥F K := Algebra.adjoin ↥F B

private def RSet : Set K := {y | y ∈ KFld F S ∧ IsIntegral ↥(TRng F B) y}

variable {B S}

private theorem isIntegral_TRng_algebraMap {a : ℂ} (ha : IsIntegral ↥F a) :
    IsIntegral ↥(TRng F B) (algebraMap ℂ K a) :=
  (ha.algebraMap (B := K)).tower_top

private theorem isIntegral_KFld_algebraMap {a : ℂ} (ha : IsIntegral ↥F a) :
    IsIntegral ↥(KFld F S) (algebraMap ℂ K a) :=
  (ha.algebraMap (B := K)).tower_top

private theorem minpoly_KFld_dvd (c : ℂ) :
    minpoly ↥(KFld F S) (algebraMap ℂ K c) ∣ (minpoly ↥F c).map (algebraMap ↥F ↥(KFld F S)) := by
  apply minpoly.dvd
  rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algebraMap_apply, minpoly.aeval, map_zero]

private theorem root_minpoly_KFld_eq_algebraMap {c : ℂ} (hc : IsIntegral ↥F c) {r : K}
    (hr : r ∈ (minpoly ↥(KFld F S) (algebraMap ℂ K c)).aroots K) :
    ∃ a : ℂ, IsIntegral ↥F a ∧ algebraMap ℂ K a = r := by
  set ι := algebraMap ℂ K
  set q : ℂ[X] := (minpoly ↥F c).map (algebraMap ↥F ℂ) with hq
  have hqm : q.Monic := (minpoly.monic hc).map _
  have hq0 : q.map ι ≠ 0 := (hqm.map ι).ne_zero
  have hdvd : (minpoly ↥(KFld F S) (ι c)).map (algebraMap ↥(KFld F S) K) ∣ q.map ι := by
    have := Polynomial.map_dvd (algebraMap ↥(KFld F S) K) (minpoly_KFld_dvd F (S := S) c)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
    rwa [hq, Polynomial.map_map, ← IsScalarTower.algebraMap_eq ↥F ℂ K]
  have hroots : (q.map ι).roots = q.roots.map ι :=
    (IsAlgClosed.splits q).roots_map_of_injective (algebraMap ℂ K).injective
  have hr' : r ∈ (q.map ι).roots := Multiset.mem_of_le (Polynomial.roots.le_of_dvd hq0 hdvd) hr
  rw [hroots, Multiset.mem_map] at hr'
  obtain ⟨a, ha, rfl⟩ := hr'
  refine ⟨a, ?_, rfl⟩
  rw [Polynomial.mem_roots hqm.ne_zero, Polynomial.IsRoot.def, hq, Polynomial.eval_map,
    ← Polynomial.aeval_def] at ha
  exact ⟨minpoly ↥F c, minpoly.monic hc, by rwa [← Polynomial.aeval_def]⟩

attribute [local instance] Classical.propDecidable in
private theorem card_rootFinset_minpoly_KFld {c : ℂ} (hc : IsIntegral ↥F c) :
    ((minpoly ↥(KFld F S) (algebraMap ℂ K c)).aroots K).toFinset.card =
      (minpoly ↥(KFld F S) (algebraMap ℂ K c)).natDegree := by
  set ι := algebraMap ℂ K
  set L₀ := KFld F S
  haveI : CharZero ↥L₀ := charZero_KFld F L₀
  have hint : IsIntegral ↥L₀ (ι c) := isIntegral_KFld_algebraMap F hc
  set m₁ := minpoly ↥L₀ (ι c)
  have hsep : (m₁.map (algebraMap ↥L₀ K)).Separable :=
    (PerfectField.separable_of_irreducible (minpoly.irreducible hint)).map
  rw [Polynomial.aroots_def, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)]
  set q : ℂ[X] := (minpoly ↥F c).map (algebraMap ↥F ℂ) with hq
  have hqm : q.Monic := (minpoly.monic hc).map _
  have hdvd : m₁.map (algebraMap ↥L₀ K) ∣ q.map ι := by
    have := Polynomial.map_dvd (algebraMap ↥L₀ K) (minpoly_KFld_dvd F (S := S) c)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
    rwa [hq, Polynomial.map_map, ← IsScalarTower.algebraMap_eq ↥F ℂ K]
  have hspl : (m₁.map (algebraMap ↥L₀ K)).Splits :=
    ((IsAlgClosed.splits q).map ι).of_dvd (hqm.map ι).ne_zero hdvd
  rw [← hspl.natDegree_eq_card_roots, Polynomial.natDegree_map]

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
  · exact algebraMap_adjoinF_mem F hz
  · exact (IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}).algebraMap_mem
      ⟨y, IntermediateField.subset_adjoin ↥F S hy⟩

variable (B) in
private theorem exists_lift_of_mem_adjoin (hBS : B ⊆ S) {c : ℂ} (hc : IsIntegral ↥F c) {y : K}
    (hy : y ∈ Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) B) :
    ∃ y' : ↥(IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}),
      (y' : K) = y ∧
      ∀ φ : ↥(IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}) →ₐ[↥(KFld F S)] K,
        φ y' ∈ Algebra.adjoin ↥(TRng F B) {φ (IntermediateField.AdjoinSimple.gen ↥(KFld F S)
          (algebraMap ℂ K c))} := by
  set ι := algebraMap ℂ K
  set L₀ := KFld F S
  set E := IntermediateField.adjoin ↥L₀ {ι c}
  set g := IntermediateField.AdjoinSimple.gen ↥L₀ (ι c)
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    refine ⟨algebraMap ↥L₀ ↥E ⟨x, IntermediateField.subset_adjoin ↥F S (hBS hx)⟩, rfl, fun φ ↦ ?_⟩
    rw [AlgHom.commutes]
    exact Subalgebra.algebraMap_mem (Algebra.adjoin ↥(TRng F B) {φ g})
      (⟨x, Algebra.subset_adjoin hx⟩ : ↥(TRng F B))
  | algebraMap z =>
    have hz : (z : ℂ) ∈ IntermediateField.adjoin ↥F {c} := z.2
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hc.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨u, hu⟩ := hz
    refine ⟨Polynomial.aeval g (u.map (algebraMap ↥F ↥L₀)), ?_, fun φ ↦ ?_⟩
    · rw [algebraMap_subfield_apply', ← IntermediateField.aeval_coe,
        Polynomial.aeval_map_algebraMap, IntermediateField.AdjoinSimple.coe_gen,
        Polynomial.aeval_algebraMap_apply]
      exact congrArg ι hu
    · rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap,
        ← Polynomial.aeval_map_algebraMap ↥(TRng F B)]
      exact Polynomial.aeval_mem_adjoin_singleton _ _
  | add x y _ _ ihx ihy =>
    obtain ⟨x', hx', hx⟩ := ihx
    obtain ⟨y', hy', hy⟩ := ihy
    exact ⟨x' + y', by rw [IntermediateField.coe_add, hx', hy'], fun φ ↦ by
      rw [map_add]; exact Subalgebra.add_mem _ (hx φ) (hy φ)⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨x', hx', hx⟩ := ihx
    obtain ⟨y', hy', hy⟩ := ihy
    exact ⟨x' * y', by rw [IntermediateField.coe_mul, hx', hy'], fun φ ↦ by
      rw [map_mul]; exact Subalgebra.mul_mem _ (hx φ) (hy φ)⟩

attribute [local instance] Classical.propDecidable in
private theorem isIntegral_coeff_lagrangeBasis {s : Finset K}
    (hs : ∀ r ∈ s, ∃ a : ℂ, IsIntegral ↥F a ∧ algebraMap ℂ K a = r)
    {r : K} (hr : r ∈ s) (k : ℕ) :
    IsIntegral ↥(TRng F B) ((Lagrange.basis s id r).coeff k) := by
  set ι := algebraMap ℂ K
  set Sf : Subfield K := (algebraicClosure ↥F ℂ).toSubfield.map ι
  have hmemS : ∀ r ∈ s, r ∈ Sf := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := hs r hr
    exact ⟨a, mem_algebraicClosure_iff.mpr ha.isAlgebraic, rfl⟩
  have hlift : Lagrange.basis s id r ∈ Polynomial.liftsRing Sf.subtype := by
    unfold Lagrange.basis
    refine Subring.prod_mem _ fun j hj ↦ ?_
    unfold Lagrange.basisDivisor
    have hrS : (id r : K) ∈ Set.range Sf.subtype := ⟨⟨r, hmemS r hr⟩, rfl⟩
    have hjS : (id j : K) ∈ Set.range Sf.subtype :=
      ⟨⟨j, hmemS j (Finset.mem_of_mem_erase hj)⟩, rfl⟩
    refine Subring.mul_mem _ ?_ (Subring.sub_mem _ ?_ ?_)
    · rw [← Polynomial.lifts_iff_liftsRing]
      apply Polynomial.C'_mem_lifts
      obtain ⟨a, ha⟩ := hrS; obtain ⟨b, hb⟩ := hjS
      exact ⟨(a - b)⁻¹, by rw [map_inv₀, map_sub, ha, hb]⟩
    · rw [← Polynomial.lifts_iff_liftsRing]; exact Polynomial.X_mem_lifts _
    · rw [← Polynomial.lifts_iff_liftsRing]; exact Polynomial.C'_mem_lifts hjS
  rw [← Polynomial.lifts_iff_liftsRing, Polynomial.lifts_iff_coeff_lifts] at hlift
  obtain ⟨⟨w, hw⟩, hw'⟩ := hlift k
  obtain ⟨a, ha, rfl⟩ := hw
  change ι a = _ at hw'
  rw [← hw']
  exact isIntegral_TRng_algebraMap F
    (isAlgebraic_iff_isIntegral.mp (mem_algebraicClosure_iff.mp ha))

variable (B S) in
set_option maxHeartbeats 6400000 in
private theorem mem_span_RSet_of_adjoin_simple (hBS : B ⊆ S) {c : ℂ} (hc : IsIntegral ↥F c) {x : K}
    (hxK : x ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    (hxint : IsIntegral ↥(Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) B) x) :
    x ∈ Submodule.span ℂ (RSet F B S) := by
  classical
  set ι := algebraMap ℂ K
  set L₀ := KFld F S
  haveI : CharZero ↥L₀ := charZero_KFld F L₀
  have hint : IsIntegral ↥L₀ (ι c) := isIntegral_KFld_algebraMap F hc
  set E := IntermediateField.adjoin ↥L₀ {ι c}
  set g := IntermediateField.AdjoinSimple.gen ↥L₀ (ι c)
  set pb := IntermediateField.adjoin.powerBasis hint
  have hpbg : pb.gen = g := IntermediateField.adjoin.powerBasis_gen hint
  have hpbd : pb.dim = (minpoly ↥L₀ (ι c)).natDegree :=
    IntermediateField.adjoin.powerBasis_dim hint
  set x' : ↥E := ⟨x, closure_adjoin_le F hxK⟩
  set y : Fin pb.dim → ↥L₀ := fun i ↦ pb.basis.repr x' i
  have hx' : x' = ∑ i, y i • g ^ (i : ℕ) := by
    conv_lhs => rw [← pb.basis.sum_repr x']
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [pb.coe_basis, hpbg]

  obtain ⟨P, hPm, hPc, hPx⟩ := (isIntegral_subalgebra_iff _ x).mp hxint
  set d := P.natDegree
  choose pc hpc hpcφ using fun n ↦ exists_lift_of_mem_adjoin F B hBS hc (hPc n)
  have hw : x' ^ d + ∑ n ∈ Finset.range d, pc n * x' ^ n = 0 := by
    apply Subtype.ext
    rw [IntermediateField.coe_add, IntermediateField.coe_pow, AddSubmonoidClass.coe_finsetSum,
      ZeroMemClass.coe_zero]
    have := hPx
    rw [hPm.as_sum, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finsetSum] at this
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      at this
    rw [← this]
    congr 1
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [IntermediateField.coe_mul, IntermediateField.coe_pow, hpc]

  set roots := (minpoly ↥L₀ (ι c)).aroots K
  set s := roots.toFinset
  have hsconst : ∀ r ∈ s, ∃ a : ℂ, IsIntegral ↥F a ∧ ι a = r := fun r hr ↦
    root_minpoly_KFld_eq_algebraMap F hc (Multiset.mem_toFinset.mp hr)
  let φ : ∀ r, r ∈ roots → (↥E →ₐ[↥L₀] K) := fun r hr ↦
    (IntermediateField.algHomAdjoinIntegralEquiv ↥L₀ hint).symm ⟨r, hr⟩
  have hφg : ∀ r hr, φ r hr g = r := fun r hr ↦
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ↥L₀ hint ⟨r, hr⟩
  let zf : K → K := fun r ↦ if hr : r ∈ roots then φ r hr x' else 0

  have hZ1 : ∀ r hr, IsIntegral ↥(TRng F B) (φ r hr x') := by
    intro r hr
    set T := Algebra.adjoin ↥(TRng F B) {r}
    have hrint : IsIntegral ↥(TRng F B) r := by
      obtain ⟨a, ha, rfl⟩ := root_minpoly_KFld_eq_algebraMap F hc hr
      exact isIntegral_TRng_algebraMap F ha
    have hpcT : ∀ n, φ r hr (pc n) ∈ T := by
      intro n
      have := hpcφ n (φ r hr)
      rwa [hφg] at this
    have hT : IsIntegral ↥T (φ r hr x') := by
      rw [isIntegral_subalgebra_iff]
      refine ⟨X ^ d + ∑ n ∈ Finset.range d, C (φ r hr (pc n)) * X ^ n, ?_, ?_, ?_⟩
      · apply Polynomial.monic_X_pow_add
        refine (Polynomial.degree_sum_le _ _).trans_lt ?_
        refine (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr fun k hk ↦ ?_
        exact (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt
          (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hk))
      · intro k
        rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
        refine Subalgebra.add_mem _ ?_ (Subalgebra.sum_mem _ fun n _ ↦ ?_)
        · split_ifs
          · exact Subalgebra.one_mem _
          · exact Subalgebra.zero_mem _
        · rw [Polynomial.coeff_C_mul_X_pow]
          split_ifs
          · exact hpcT n
          · exact Subalgebra.zero_mem _
      · rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum]
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        rw [← map_pow]
        simp_rw [← map_pow, ← map_mul]
        rw [← map_sum, ← map_add, hw, map_zero]
    exact isIntegral_of_isIntegral_adjoin_singleton hrint hT

  have hZ2 : ∀ r hr, φ r hr x' = ∑ i, (y i : K) * r ^ (i : ℕ) := by
    intro r hr
    rw [hx', map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, map_mul, map_pow, hφg, AlgHom.commutes]
    rfl

  set Y : K[X] := ∑ i : Fin pb.dim, C (y i : K) * X ^ (i : ℕ)
  have hcard : s.card = pb.dim := by
    rw [hpbd]; exact card_rootFinset_minpoly_KFld F hc
  have hYdeg : Y.degree < s.card := by
    rw [hcard]; exact Polynomial.degree_sum_fin_lt _
  have hYeval : ∀ r ∈ s, Y.eval (id r) = zf r := by
    intro r hr
    have hr' : r ∈ roots := Multiset.mem_toFinset.mp hr
    simp only [zf, dite_eq_left hr', id, hZ2 r hr', Y, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hY : Y = Lagrange.interpolate s id zf :=
    Lagrange.eq_interpolate_of_eval_eq zf (Set.injOn_id _) hYdeg hYeval
  have hYcoeff : ∀ i : Fin pb.dim, Y.coeff i = (y i : K) := by
    intro i
    simp only [Y, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [ite_eq_right (fun h ↦ hji (Fin.ext h.symm))]
    · intro h; exact absurd (Finset.mem_univ i) h

  have hZ4 : ∀ i : Fin pb.dim, IsIntegral ↥(TRng F B) (y i : K) := by
    intro i
    rw [← hYcoeff, hY, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
    refine IsIntegral.sum _ fun r hr ↦ ?_
    rw [Polynomial.coeff_C_mul]
    refine IsIntegral.mul ?_ (isIntegral_coeff_lagrangeBasis F hsconst hr _)
    have hr' : r ∈ roots := Multiset.mem_toFinset.mp hr
    simp only [zf, dite_eq_left hr']
    exact hZ1 r hr'

  have hZ5 : ∀ i : Fin pb.dim, (y i : K) ∈ RSet F B S := fun i ↦ ⟨(y i).2, hZ4 i⟩

  have hxsum : x = ∑ i : Fin pb.dim, (y i : K) * ι c ^ (i : ℕ) := by
    have := congrArg (fun e : ↥E ↦ (e : K)) hx'
    rw [IntermediateField.coe_sum] at this
    rw [show x = (x' : K) from rfl, this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [IntermediateField.coe_smul, IntermediateField.coe_pow,
      IntermediateField.AdjoinSimple.coe_gen, IntermediateField.smul_def, smul_eq_mul]
  rw [hxsum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have : (y i : K) * ι c ^ (i : ℕ) = (c ^ (i : ℕ)) • (y i : K) := by
    rw [Algebra.smul_def, map_pow, mul_comm]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hZ5 i))

private theorem mem_KFld_iff_closure (z : K) :
    z ∈ KFld F S ↔ z ∈ Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) := by
  rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield,
    range_algebraMap_subfield]

private theorem isIntegral_TRng_iff_closure (z : K) :
    IsIntegral ↥(TRng F B) z ↔
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ B)) z := by
  rw [isIntegral_adjoin_iff_closure, range_algebraMap_subfield]

private theorem isIntegral_adjoin_iff_closure' (E₀ : IntermediateField ↥F ℂ) (z : K) :
    IsIntegral ↥(Algebra.adjoin ↥E₀ B) z ↔
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (E₀ : Set ℂ) ∪ B)) z := by
  rw [isIntegral_adjoin_iff_closure, range_algebraMap_subfield']

end AdjoinSimpleConstantsAux

/-- Algebraic extension of the constant field preserves the complex span of
integral elements in a generated subfield.

Let `K` be a field with a `ℂ`-algebra structure, `F` an intermediate field
of `ℚ` in `ℂ`, `B ⊆ S` subsets of `K`, and `c : ℂ` algebraic over `F`.
If `y : K` lies in the subfield generated by the image of `F(c)` together
with `S`, and `y` is integral over the subring generated by that image
together with `B`, then `y` lies in the `ℂ`-linear span of the elements
that already lie in the subfield generated by the image of `F` together
with `S` and are integral over the subring generated by that image
together with `B`. -/
public theorem IsIntegral.mem_span_of_adjoin_simple_constants {K : Type*} [Field K] [Algebra ℂ K]
    (F : IntermediateField ℚ ℂ) (B S : Set K) (hBS : B ⊆ S) (c : ℂ) (hc : IsAlgebraic ↥F c)
    (y : K)
    (hyS : y ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    (hyB : IsIntegral ↥(Subring.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ B)) y) :
    y ∈ Submodule.span ℂ {z : K | z ∈ Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) ∧
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ B)) z} := by
  have hyB' : IsIntegral ↥(Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) B) y := by
    rw [AdjoinSimpleConstantsAux.isIntegral_adjoin_iff_closure' F]
    exact hyB
  have h := AdjoinSimpleConstantsAux.mem_span_RSet_of_adjoin_simple F B S hBS hc.isIntegral hyS hyB'
  refine Submodule.span_mono (fun z hz => ?_) h
  exact ⟨(AdjoinSimpleConstantsAux.mem_KFld_iff_closure F z).mp hz.1,
    (AdjoinSimpleConstantsAux.isIntegral_TRng_iff_closure F z).mp hz.2⟩
