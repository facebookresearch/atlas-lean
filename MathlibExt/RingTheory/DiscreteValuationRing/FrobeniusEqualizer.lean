/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CerednikDrinfeld_FormalOmega_frobTwo_frobTwo_and_exists_generator.lean`,
`P2M/Sol/S_CerednikDrinfeld_FormalOmega_frobTwo_frobTwo_and_exists_generator.lean`,
`Theorems/Thm_CerednikDrinfeld_FormalOmega_algHom_eq_or_eq_comp_frobTwo_of_isLocalRing.lean` and
`P2M/Sol/S_CerednikDrinfeld_FormalOmega_algHom_eq_or_eq_comp_frobTwo_of_isLocalRing.lean`
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

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.LinearCombination

@[expose] public section

universe u

namespace IsDiscreteValuationRing

set_option autoImplicit false

open scoped TensorProduct
open Polynomial

namespace UQA

private theorem approx {𝒪 : Type u} [CommRing 𝒪] {S : Type*} [CommRing S] [Algebra 𝒪 S] (π : 𝒪)
    [IsPrecomplete (Ideal.span {π}) 𝒪] [IsHausdorff (Ideal.span {algebraMap 𝒪 S π}) S]
    (V : Set S) {n : ℕ} (e : Fin n → S)
    (hstep : ∀ v ∈ V, ∃ (c : Fin n → 𝒪) (v' : S), v' ∈ V ∧ v = (∑ i, algebraMap 𝒪 S (c i) * e i) +
      algebraMap 𝒪 S π * v')
    (v : S) (hv : v ∈ V) : ∃ a : Fin n → 𝒪, v = ∑ i, algebraMap 𝒪 S (a i) * e i := by
  classical
  choose cf nx hnx hdec using hstep

  let step : (Fin n → 𝒪) × {w : S // w ∈ V} → ℕ → (Fin n → 𝒪) × {w : S // w ∈ V} :=
    fun sw k => (sw.1 + fun i => π ^ k * cf sw.2.1 sw.2.2 i, ⟨nx sw.2.1 sw.2.2, hnx sw.2.1 sw.2.2⟩)
  let seq : ℕ → (Fin n → 𝒪) × {w : S // w ∈ V} := fun k => Nat.rec ((0 : Fin n → 𝒪), ⟨v, hv⟩) (fun
    k sw => step sw k) k
  have seq_zero : seq 0 = (0, ⟨v, hv⟩) := rfl
  have seq_succ : ∀ k, seq (k + 1) = step (seq k) k := fun k => rfl
  set π' := algebraMap 𝒪 S π with hπ'

  have hinv : ∀ k, v = (∑ i, algebraMap 𝒪 S ((seq k).1 i) * e i) + π' ^ k * (seq k).2.1 := by
    intro k
    induction k with
    | zero => simp [seq_zero]
    | succ k ih =>
      rw [seq_succ]
      show v = (∑ i, algebraMap 𝒪 S (((seq k).1 + fun i => π ^ k * cf (seq k).2.1 (seq k).2.2 i) i)
        * e i) +
        π' ^ (k + 1) * nx (seq k).2.1 (seq k).2.2
      have hd := hdec (seq k).2.1 (seq k).2.2
      rw [ih]
      conv_lhs => rw [hd]
      simp only [Pi.add_apply, map_add, map_mul, map_pow, add_mul, Finset.sum_add_distrib, ← hπ']
      rw [pow_succ, mul_add, Finset.mul_sum]
      ring_nf

  have hdiff : ∀ k i, (seq (k + 1)).1 i - (seq k).1 i ∈ Ideal.span {π} ^ k := by
    intro k i
    rw [seq_succ]
    show ((seq k).1 + fun i => π ^ k * cf (seq k).2.1 (seq k).2.2 i) i - (seq k).1 i ∈ Ideal.span
      {π} ^ k
    simp only [Pi.add_apply, add_sub_cancel_left]
    rw [Ideal.span_singleton_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hcauchy : ∀ i {m k : ℕ}, m ≤ k → (seq m).1 i ≡ (seq k).1 i [SMOD (Ideal.span {π} ^ m • ⊤ :
    Submodule 𝒪 𝒪)] := by
    intro i m k hmk
    induction k, hmk using Nat.le_induction with
    | base => rfl
    | succ k hmk ih =>
      refine ih.trans ?_
      rw [SModEq.sub_mem]
      have : (seq k).1 i - (seq (k + 1)).1 i ∈ Ideal.span {π} ^ m := by
        rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 (Ideal.pow_le_pow_right hmk (hdiff k i))
      simpa using this
  choose a ha using fun i => IsPrecomplete.prec' (I := Ideal.span {π}) (fun k => (seq k).1 i)
    (hcauchy i)
  refine ⟨a, ?_⟩
  apply eq_of_sub_eq_zero
  apply IsHausdorff.haus' (I := Ideal.span {π'})
  intro k
  rw [SModEq.sub_mem, sub_zero]
  have h1 : v - ∑ i, algebraMap 𝒪 S (a i) * e i = (∑ i, algebraMap 𝒪 S ((seq k).1 i - a i) * e i) +
    π' ^ k * (seq k).2.1 := by
    conv_lhs => rw [hinv k]
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [h1]
  have h2 : ∀ i, algebraMap 𝒪 S ((seq k).1 i - a i) ∈ Ideal.span {π'} ^ k := by
    intro i
    have := (ha i k)
    rw [SModEq.sub_mem] at this
    have h3 : (seq k).1 i - a i ∈ Ideal.span {π} ^ k := by simpa using this
    rw [Ideal.span_singleton_pow] at h3 ⊢
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h3
    rw [← hc, map_mul, map_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have h4 : (∑ i, algebraMap 𝒪 S ((seq k).1 i - a i) * e i) + π' ^ k * (seq k).2.1 ∈ Ideal.span
    {π'} ^ k := by
    refine Ideal.add_mem _ (sum_mem fun i _ => Ideal.mul_mem_right _ _ (h2 i)) ?_
    rw [Ideal.span_singleton_pow]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  simpa using h4

end UQA

private theorem F3a_core

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})

    (Onr : Type u) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span
      {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p
      ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    :
    ∃ ζ : Onr, ζ ∈ AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪
      Onr) ∧
      (∀ v : Onr, v ∈ AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪
        Onr) → ∃ a b : 𝒪, v = algebraMap 𝒪 Onr a + algebraMap 𝒪 Onr b * ζ) ∧
      IsUnit (Fr ζ - ζ) ∧
      (∀ x : Onr, Fr x = x ↔ ∃ a : 𝒪, x = algebraMap 𝒪 Onr a) := by
  classical
  haveI := hdvr
  set π' : Onr := algebraMap 𝒪 Onr π with hπ'
  let I : Ideal Onr := Ideal.span {π'}
  haveI hImax : I.IsMaximal := hOnr_max
  letI : Field (Onr ⧸ I) := Ideal.Quotient.field I
  have hrP : r.Prime := Fact.out

  have hπ'0 : π' ≠ 0 := by
    intro h0
    have hr : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.subset_span rfl
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hr
    have : ((r : ℕ) : Onr) = 0 := by
      rw [← map_natCast (algebraMap 𝒪 Onr), ← hc, map_mul, ← hπ', h0, mul_zero]
    exact Nat.cast_ne_zero.2 hrP.ne_zero this
  have hFrπ : ∀ e : Onr ≃ₐ[𝒪] Onr, e π' = π' := fun e => e.commutes π

  have hmax𝒪 : IsLocalRing.maximalIdeal 𝒪 = Ideal.span {π} := Irreducible.maximalIdeal_eq hπ
  haveI hπmax : (Ideal.span {π}).IsMaximal := hmax𝒪 ▸ IsLocalRing.maximalIdeal.isMaximal 𝒪
  letI : Field (𝒪 ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by rw [hres]; exact
    hrP.ne_zero)
  letI : Fintype (𝒪 ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hcard𝒪 : Fintype.card (𝒪 ⧸ Ideal.span {π}) = r := by rw [Fintype.card_eq_nat_card, hres]

  have hIπ : ∀ a ∈ Ideal.span {π}, (Ideal.Quotient.mk I).comp (algebraMap 𝒪 Onr) a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [RingHom.comp_apply, map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
  let φ : 𝒪 ⧸ Ideal.span {π} →+* Onr ⧸ I := Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp
    (algebraMap 𝒪 Onr)) hIπ
  have hφ : ∀ a : 𝒪, φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk I (algebraMap 𝒪 Onr a) := fun a
    => rfl
  have hφinj : Function.Injective φ := φ.injective

  have hFrb : ∀ y : Onr, Ideal.Quotient.mk I (Fr y) = (Ideal.Quotient.mk I y) ^ r := by
    intro y; rw [← map_pow, Ideal.Quotient.eq]; exact hFr y

  have hres_fixed : ∀ y : Onr, Ideal.Quotient.mk I (Fr y) = Ideal.Quotient.mk I y →
      ∃ a : 𝒪, y - algebraMap 𝒪 Onr a ∈ I := by
    intro y hy
    let f : (Onr ⧸ I)[X] := X ^ r - X
    have hf0 : f ≠ 0 := by
      intro h
      have := congrArg Polynomial.natDegree h
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt
          (by rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; exact hrP.one_lt),
        Polynomial.natDegree_X_pow, Polynomial.natDegree_zero] at this
      exact hrP.ne_zero this
    have hroot : ∀ z : Onr ⧸ I, z ^ r = z → z ∈ f.roots.toFinset := by
      intro z hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hf0, Polynomial.IsRoot, Polynomial.eval_sub,
        Polynomial.eval_pow,
        Polynomial.eval_X, hz, sub_self]
    let T : Finset (Onr ⧸ I) := Finset.univ.image φ
    have hTcard : T.card = r := by rw [Finset.card_image_of_injective _ hφinj, Finset.card_univ,
      hcard𝒪]
    have hTsub : T ⊆ f.roots.toFinset := by
      intro z hz
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hz
      apply hroot
      rw [← map_pow, ← hcard𝒪, FiniteField.pow_card]
    have hrcard : f.roots.toFinset.card ≤ r := by
      refine le_trans (Multiset.toFinset_card_le _) (le_trans (Polynomial.card_roots' f) ?_)
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt
          (by rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; exact hrP.one_lt),
        Polynomial.natDegree_X_pow]
    have hTeq : T = f.roots.toFinset := Finset.eq_of_subset_of_card_le hTsub (by rw [hTcard]; exact
      hrcard)
    have hzT : Ideal.Quotient.mk I y ∈ T := by
      rw [hTeq]; apply hroot; rw [← hFrb, hy]
    obtain ⟨u, -, hu⟩ := Finset.mem_image.1 hzT
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    refine ⟨a, ?_⟩
    rw [← Ideal.Quotient.eq, ← hφ, hu]

  have hdivFr : ∀ (e : Onr ≃ₐ[𝒪] Onr) (y : Onr), e (π' * y) = π' * y → e y = y := by
    intro e y h
    rw [map_mul, hFrπ e] at h
    exact mul_left_cancel₀ hπ'0 h

  haveI : IsPrecomplete (Ideal.span {π}) 𝒪 := hcomplete.toIsPrecomplete
  haveI : IsHausdorff (Ideal.span {algebraMap 𝒪 Onr π}) Onr := hOnr_complete.toIsHausdorff

  have hfix : ∀ x : Onr, Fr x = x ↔ ∃ a : 𝒪, x = algebraMap 𝒪 Onr a := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := UQA.approx π {y : Onr | Fr y = y} (![1] : Fin 1 → Onr) (by
        intro v hv
        obtain ⟨a, ha⟩ := hres_fixed v (by rw [show Fr v = v from hv])
        obtain ⟨v', hv'⟩ := Ideal.mem_span_singleton'.1 ha
        refine ⟨![a], v', ?_, ?_⟩
        · show Fr v' = v'
          apply hdivFr Fr
          rw [mul_comm, hv', map_sub, show Fr v = v from hv, Fr.commutes]
        · simp [Fin.sum_univ_one, ← hπ']; rw [mul_comm, hv']; ring) x hx
      exact ⟨a 0, by simpa [Fin.sum_univ_one] using ha⟩
    · rintro ⟨a, rfl⟩; exact Fr.commutes a

  set O2 := (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))
    with hO2
  have memO2 : ∀ y : Onr, y ∈ O2 ↔ Fr (Fr y) = y := by
    intro y; rw [hO2, AlgHom.mem_equalizer]; rfl
  have hstabO2 : ∀ x : Onr, x ∈ O2 → Fr x ∈ O2 := by
    intro x hx; rw [memO2] at hx ⊢; rw [hx]

  have hIle : I ≤ Ideal.comap Fr.toRingEquiv.toRingHom I := by
    rw [Ideal.span_le]; intro y hy
    rw [Set.mem_singleton_iff.1 hy, SetLike.mem_coe, Ideal.mem_comap]
    show Fr π' ∈ I
    rw [hFrπ Fr]; exact Ideal.subset_span rfl
  let Frb : Onr ⧸ I →+* Onr ⧸ I := Ideal.quotientMap I Fr.toRingEquiv.toRingHom hIle
  have hFrb' : ∀ y : Onr, Frb (Ideal.Quotient.mk I y) = Ideal.Quotient.mk I (Fr y) := fun y =>
    Ideal.quotientMap_mk
  have hFrb_pow : ∀ z : Onr ⧸ I, Frb z = z ^ r := by
    intro z; obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z; rw [hFrb', hFrb]
  have hr0 : ((r : ℕ) : Onr ⧸ I) = 0 := by
    have hr : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.subset_span rfl
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hr
    rw [← map_natCast ((Ideal.Quotient.mk I).comp (algebraMap 𝒪 Onr)), ← hc]
    simp only [RingHom.comp_apply, map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))

  haveI hAC : IsAlgClosed (Onr ⧸ I) := by
    apply IsAlgClosed.of_exists_root
    intro p hp hirr
    have hlift : p ∈ Polynomial.lifts (Ideal.Quotient.mk I) :=
      (Polynomial.lifts_iff_coeff_lifts p).2 fun j => Ideal.Quotient.mk_surjective _
    obtain ⟨q, hq, hdeg, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hp
    have hpos : 0 < q.natDegree := by rw [hdeg]; exact hirr.natDegree_pos
    obtain ⟨x, hx⟩ := hOnr_closed q hqm hpos
    refine ⟨Ideal.Quotient.mk I x, ?_⟩
    rw [← hq, Polynomial.eval_map, Polynomial.eval₂_hom]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hx

  let f₂ : (Onr ⧸ I)[X] := X ^ (r ^ 2) - X
  have hr2 : 1 < r ^ 2 := lt_of_lt_of_le hrP.one_lt (Nat.le_self_pow two_ne_zero r)
  have hf₂deg : f₂.natDegree = r ^ 2 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt
        (by rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; exact hr2),
      Polynomial.natDegree_X_pow]
  have hf₂0 : f₂ ≠ 0 := by intro h; rw [h, Polynomial.natDegree_zero] at hf₂deg; omega
  have hf₂sep : f₂.Separable := by
    rw [Polynomial.separable_def]
    have : derivative f₂ = -1 := by
      show derivative (X ^ (r ^ 2) - X : (Onr ⧸ I)[X]) = -1
      rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
      rw [show (Polynomial.C ((r ^ 2 : ℕ) : Onr ⧸ I)) = 0 from by rw [Nat.cast_pow, hr0, zero_pow
        two_ne_zero, map_zero], zero_mul, zero_sub]
    rw [this]; exact (isCoprime_one_right (x := f₂)).neg_right
  let T₂ : Finset (Onr ⧸ I) := f₂.roots.toFinset
  have memT₂ : ∀ z, z ∈ T₂ ↔ z ^ (r ^ 2) = z := by
    intro z
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf₂0, Polynomial.IsRoot, Polynomial.eval_sub,
      Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero]
  have hT₂card : T₂.card = r ^ 2 := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hf₂sep), ← (IsAlgClosed.splits
      f₂).natDegree_eq_card_roots, hf₂deg]

  let T : Finset (Onr ⧸ I) := Finset.univ.image φ
  have hTcard : T.card = r := by rw [Finset.card_image_of_injective _ hφinj, Finset.card_univ,
    hcard𝒪]
  have hφpow : ∀ u, (φ u) ^ r = φ u := fun u => by rw [← map_pow, ← hcard𝒪, FiniteField.pow_card]
  have hTsub₂ : T ⊆ T₂ := by
    intro z hz
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hz
    rw [memT₂, pow_two, pow_mul, hφpow, hφpow]

  obtain ⟨ζb, hζbT₂, hζbT⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := T) (t := T₂) (by
    rw [hTcard, hT₂card]; exact lt_self_pow₀ hrP.one_lt one_lt_two)
  have hζb0 : ζb ≠ 0 := by
    intro h; apply hζbT; rw [h]; exact Finset.mem_image.2 ⟨0, Finset.mem_univ _, map_zero φ⟩
  have hζbN : ζb ^ (r ^ 2 - 1) = 1 := by
    have := (memT₂ ζb).1 hζbT₂
    rw [← Nat.sub_add_cancel hr2.le, pow_succ] at this
    exact mul_left_eq_self₀.1 this |>.resolve_right hζb0
  haveI : HenselianRing Onr I := inferInstance
  obtain ⟨y₀, hy₀⟩ := Ideal.Quotient.mk_surjective ζb
  let f₃ : Onr[X] := X ^ (r ^ 2 - 1) - 1
  have hf₃m : f₃.Monic := Polynomial.monic_X_pow_sub_C _ (by omega)
  obtain ⟨ζ, hζroot, hζy₀⟩ := HenselianRing.is_henselian (I := I) f₃ hf₃m y₀ (by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      show Ideal.Quotient.mk I (Polynomial.eval y₀ (X ^ (r ^ 2 - 1) - 1)) = 0
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        map_sub, map_pow, map_one, hy₀, hζbN, sub_self])
    (by
      show IsUnit (Ideal.Quotient.mk I (Polynomial.eval y₀ (derivative (X ^ (r ^ 2 - 1) - 1 :
        Onr[X]))))
      rw [Polynomial.derivative_sub, Polynomial.derivative_one, Polynomial.derivative_X_pow,
        sub_zero, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, map_mul, map_pow, hy₀,
          map_natCast]
      refine isUnit_iff_ne_zero.2 (mul_ne_zero ?_ (pow_ne_zero _ hζb0))
      rw [Nat.cast_sub hr2.le, Nat.cast_pow, hr0, zero_pow two_ne_zero, Nat.cast_one, zero_sub]
      exact neg_ne_zero.2 one_ne_zero)
  have hζres : Ideal.Quotient.mk I ζ = ζb := by
    rw [← hy₀, Ideal.Quotient.eq]; exact hζy₀
  have hζN : ζ ^ (r ^ 2 - 1) = 1 := by
    have := hζroot; rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, sub_eq_zero] at this
    exact this

  have hζO2 : ζ ∈ O2 := by
    rw [memO2]
    set ζ' := Fr (Fr ζ) with hζ'
    have hζ'N : ζ' ^ (r ^ 2 - 1) = 1 := by rw [hζ', ← map_pow, ← map_pow, hζN, map_one, map_one]
    have hζ'res : Ideal.Quotient.mk I ζ' = Ideal.Quotient.mk I ζ := by
      rw [hζ', hFrb, hFrb, ← pow_mul, ← pow_two, hζres]; exact (memT₂ ζb).1 hζbT₂
    set N := r ^ 2 - 1 with hN
    have hN1 : 1 ≤ N := by omega
    let η : Onr := ζ' * ζ ^ (N - 1)
    have hζinv : ζ ^ (N - 1) * ζ = 1 := by rw [← pow_succ, Nat.sub_add_cancel hN1, hζN]
    have hηN : η ^ N = 1 := by
      show (ζ' * ζ ^ (N - 1)) ^ N = 1
      rw [mul_pow, hζ'N, one_mul, ← pow_mul, mul_comm, pow_mul, hζN, one_pow]
    have hηres : Ideal.Quotient.mk I η = 1 := by
      show Ideal.Quotient.mk I (ζ' * ζ ^ (N - 1)) = 1
      rw [map_mul, hζ'res, ← map_mul, mul_comm, hζinv, map_one]

    have hG : Ideal.Quotient.mk I (∑ i ∈ Finset.range N, η ^ i) = (N : Onr ⧸ I) := by
      rw [map_sum]; simp only [map_pow, hηres, one_pow, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
    have hN0 : ((N : ℕ) : Onr ⧸ I) ≠ 0 := by
      rw [hN, Nat.cast_sub hr2.le, Nat.cast_pow, hr0, zero_pow two_ne_zero, Nat.cast_one, zero_sub]
      exact neg_ne_zero.2 one_ne_zero
    have hG0 : (∑ i ∈ Finset.range N, η ^ i) ≠ 0 := by
      intro h; apply hN0; rw [← hG, h, map_zero]
    have hη1 : η = 1 := by
      have := mul_geom_sum η N
      rw [hηN, sub_self] at this
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hG0)
    calc ζ' = ζ' * (ζ ^ (N - 1) * ζ) := by rw [hζinv, mul_one]
      _ = η * ζ := by rw [mul_assoc]
      _ = ζ := by rw [hη1, one_mul]

  let S₂ : Finset (Onr ⧸ I) :=
    (Finset.univ ×ˢ Finset.univ).image fun p : (𝒪 ⧸ Ideal.span {π}) × (𝒪 ⧸ Ideal.span {π}) => φ p.1
      + φ p.2 * ζb
  have hS₂inj : ∀ u w u' w' : 𝒪 ⧸ Ideal.span {π}, φ u + φ w * ζb = φ u' + φ w' * ζb → u = u' ∧ w =
    w' := by
    intro u w u' w' h
    by_cases hw : w = w'
    · subst hw; exact ⟨hφinj (add_right_cancel h), rfl⟩
    · exfalso
      apply hζbT
      have hne : φ w - φ w' ≠ 0 := fun h0 => hw (hφinj (sub_eq_zero.1 h0))
      have h1 : ζb = (φ u' - φ u) * (φ w - φ w')⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq₀ hne]; linear_combination h
      rw [h1, ← map_sub, ← map_sub, ← map_inv₀, ← map_mul]
      exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩
  have hS₂card : S₂.card = r ^ 2 := by
    rw [Finset.card_image_of_injective, Finset.card_product, Finset.card_univ, hcard𝒪, pow_two]
    rintro ⟨u, w⟩ ⟨u', w'⟩ h
    obtain ⟨h1, h2⟩ := hS₂inj u w u' w' h
    rw [h1, h2]
  have hFrbφ : ∀ u, Frb (φ u) = φ u := fun u => by rw [hFrb_pow, hφpow]
  have hFrb2 : ∀ z : Onr ⧸ I, Frb (Frb z) = z ^ (r ^ 2) := fun z => by rw [hFrb_pow, hFrb_pow, ←
    pow_mul, ← pow_two]
  have hζbfix : Frb (Frb ζb) = ζb := by rw [hFrb2]; exact (memT₂ ζb).1 hζbT₂
  have hS₂sub : S₂ ⊆ T₂ := by
    intro z hz
    obtain ⟨⟨u, w⟩, -, rfl⟩ := Finset.mem_image.1 hz
    rw [memT₂, ← hFrb2]
    simp only [map_add, map_mul, hFrbφ, hζbfix]
  have hS₂eq : S₂ = T₂ := Finset.eq_of_subset_of_card_le hS₂sub (by rw [hS₂card, hT₂card])

  have hO2res : ∀ v : Onr, v ∈ O2 → Ideal.Quotient.mk I v ∈ T₂ := by
    intro v hv
    rw [memT₂, ← hFrb2, hFrb', hFrb', (memO2 v).1 hv]
  have hstepO2 : ∀ v ∈ (O2 : Set Onr), ∃ (c : Fin 2 → 𝒪) (v' : Onr), v' ∈ (O2 : Set Onr) ∧
      v = (∑ i, algebraMap 𝒪 Onr (c i) * (![1, ζ] : Fin 2 → Onr) i) + algebraMap 𝒪 Onr π * v' := by
    intro v hv
    have hv' : v ∈ O2 := hv
    have hvT := hO2res v hv'
    rw [← hS₂eq] at hvT
    obtain ⟨⟨u, w⟩, -, huw⟩ := Finset.mem_image.1 hvT
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    have hd : v - (algebraMap 𝒪 Onr a + algebraMap 𝒪 Onr b * ζ) ∈ I := by
      rw [← Ideal.Quotient.eq, map_add, map_mul, hζres, ← hφ, ← hφ]; exact huw.symm
    obtain ⟨v', hv''⟩ := Ideal.mem_span_singleton'.1 hd
    have hmem : π' * v' ∈ O2 := by
      rw [mul_comm, hv'']
      exact O2.sub_mem hv' (O2.add_mem (O2.algebraMap_mem a) (O2.mul_mem (O2.algebraMap_mem b)
        hζO2))
    refine ⟨![a, b], v', ?_, ?_⟩
    · show v' ∈ O2
      rw [memO2] at hmem ⊢
      have := hdivFr (Fr.trans Fr) v' (by simpa [AlgEquiv.trans_apply] using hmem)
      simpa [AlgEquiv.trans_apply] using this
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ←
      hπ', mul_one]
      linear_combination (-1 : Onr) * hv''
  have hspan : ∀ v : Onr, v ∈ O2 → ∃ a b : 𝒪, v = algebraMap 𝒪 Onr a + algebraMap 𝒪 Onr b * ζ := by
    intro v hv
    obtain ⟨c, hc⟩ := UQA.approx π (O2 : Set Onr) (![1, ζ] : Fin 2 → Onr) hstepO2 v hv
    refine ⟨c 0, c 1, ?_⟩
    simpa [Fin.sum_univ_two] using hc

  have hinjO : ∀ a : 𝒪, algebraMap 𝒪 Onr a = 0 → a = 0 := by
    intro a ha
    by_contra hne
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hπ
    have : π' ^ n = 0 := by rw [hπ', ← map_pow, ← hu, map_mul, ha, zero_mul]
    exact pow_ne_zero n hπ'0 this

  have hindep : ∀ a b : 𝒪, algebraMap 𝒪 Onr a + algebraMap 𝒪 Onr b * ζ = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    by_contra hne

    haveI : IsPrincipalIdealRing 𝒪 := inferInstance
    let d : 𝒪 := Submodule.IsPrincipal.generator (Ideal.span {a, b})
    have hdspan : Ideal.span {d} = Ideal.span {a, b} :=
      Submodule.IsPrincipal.span_singleton_generator _
    have ha : a ∈ Ideal.span {d} := hdspan ▸ Ideal.subset_span (by simp)
    have hb : b ∈ Ideal.span {d} := hdspan ▸ Ideal.subset_span (by simp)
    have hdm : d ∈ Ideal.span {a, b} := hdspan.symm ▸ Ideal.subset_span rfl
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 ha
    obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton'.1 hb
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 hdm
    have hd0 : d ≠ 0 := by
      intro hd0
      apply hne
      rw [← ha', ← hb', hd0, mul_zero, mul_zero]; exact ⟨rfl, rfl⟩

    have h' : algebraMap 𝒪 Onr a' + algebraMap 𝒪 Onr b' * ζ = 0 := by
      have : algebraMap 𝒪 Onr d * (algebraMap 𝒪 Onr a' + algebraMap 𝒪 Onr b' * ζ) = 0 := by
        rw [mul_add, ← mul_assoc, ← map_mul, ← map_mul, mul_comm d a', mul_comm d b', ha', hb'];
          exact h
      exact (mul_eq_zero.1 this).resolve_left (fun h0 => hd0 (hinjO d h0))

    have hres' := hS₂inj (Ideal.Quotient.mk _ a') (Ideal.Quotient.mk _ b') 0 0 (by
      rw [map_zero, zero_add, zero_mul, hφ, hφ, ← hζres, ← map_mul, ← map_add, h', map_zero])
    have ha'π : a' ∈ Ideal.span {π} := Ideal.Quotient.eq_zero_iff_mem.1 hres'.1
    have hb'π : b' ∈ Ideal.span {π} := Ideal.Quotient.eq_zero_iff_mem.1 hres'.2

    have h1 : d * (x * a' + y * b') = d * 1 := by
      rw [mul_one, mul_add, ← mul_assoc, ← mul_assoc, mul_comm d x, mul_comm d y, mul_assoc,
        mul_assoc, mul_comm d a', mul_comm d b',
        ha', hb']; exact hxy
    have h2 : x * a' + y * b' = 1 := mul_left_cancel₀ hd0 h1
    have : (1 : 𝒪) ∈ Ideal.span {π} := h2 ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha'π)
      (Ideal.mul_mem_left _ _ hb'π)
    exact hπmax.ne_top ((Ideal.eq_top_iff_one _).2 this)

  have hunit : IsUnit (Fr ζ - ζ) := by
    have hnot : Fr ζ - ζ ∉ I := by
      intro hmem
      have h1 : Ideal.Quotient.mk I (Fr ζ) = Ideal.Quotient.mk I ζ := (Ideal.Quotient.eq).2 hmem
      obtain ⟨a, ha⟩ := hres_fixed ζ h1
      apply hζbT
      rw [← hζres]
      have : Ideal.Quotient.mk I ζ = φ (Ideal.Quotient.mk _ a) := by
        rw [hφ]; exact Ideal.Quotient.eq.2 ha
      rw [this]; exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩
    have hfield : IsUnit (Ideal.Quotient.mk I (Fr ζ - ζ)) :=
      isUnit_iff_ne_zero.2 (fun h0 => hnot ((Ideal.Quotient.eq_zero_iff_mem).1 h0))
    obtain ⟨v, hv⟩ := hfield.exists_right_inv
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hmem : (Fr ζ - ζ) * w - 1 ∈ I := by
      rw [← Ideal.Quotient.eq, map_mul, map_one]; exact hv
    haveI : IsAdicComplete I Onr := hOnr_complete
    have hj := IsAdicComplete.le_jacobson_bot I hmem
    rw [Ideal.mem_jacobson_bot] at hj
    have h2 := hj 1
    rw [mul_one, sub_add_cancel] at h2
    exact isUnit_of_mul_isUnit_left h2
  exact ⟨ζ, hζO2, hspan, hunit, hfix⟩

/-- The Frobenius-square equalizer modulo `π ^ (n + 1)` is generated by
one element `α` with `Fr₂ α - α` a unit and a quadratic relation over
`𝒪`, and `Fr₂` is an involution on that quotient. -/
public theorem frobTwo_frobTwo_and_exists_generator

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})

    (Onr : Type u) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span
      {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p
      ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})

    (n : ℕ)
    (Fr₂ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸
      Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)
        (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) ≃ₐ[𝒪] (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr)
          : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer
            ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))
    (hFr₂ : ∀ (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id
      𝒪 Onr))), (y' : Onr) = Fr (y : Onr) → Fr₂ (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y') :
    (∀ z : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸
      Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)
        (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}), Fr₂ (Fr₂ z) = z) ∧
    ∃ α : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸
      Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)
        (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}), IsUnit (Fr₂ α - α) ∧
      Algebra.adjoin 𝒪 {α} = ⊤ ∧
      ∃ s t : 𝒪, α ^ 2 = algebraMap 𝒪 _ s * α + algebraMap 𝒪 _ t := by
  classical

  have memE : ∀ y : Onr, y ∈ AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)
    (AlgHom.id 𝒪 Onr) ↔ Fr (Fr y) = y := by
    intro y; rw [AlgHom.mem_equalizer]; rfl
  have hstab : ∀ y : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id
    𝒪 Onr)), Fr (y : Onr) ∈ AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)
      (AlgHom.id 𝒪 Onr) := by
    intro y; have h := (memE y).1 y.2; rw [memE, h]
  refine ⟨?_, ?_⟩
  ·
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    let y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))
      := ⟨Fr (y : Onr), hstab y⟩
    have hy : (y : Onr) = Fr (y' : Onr) := ((memE y).1 y.2).symm
    rw [hFr₂ y y' rfl, hFr₂ y' y hy]
  · obtain ⟨ζ, hζE, hspan, hunit, hfix⟩ :=
      F3a_core 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr
        hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr
    let ζE : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))
      := ⟨ζ, hζE⟩
    let ζE' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))
      := ⟨Fr ζ, hstab ζE⟩
    refine ⟨Ideal.Quotient.mk _ ζE, ?_, ?_, ?_⟩
    ·
      rw [hFr₂ ζE ζE' rfl, ← map_sub]
      apply IsUnit.map

      obtain ⟨u, hu⟩ := hunit
      have hwE : ((u⁻¹ : Onrˣ) : Onr) ∈ AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪]
        Onr) (AlgHom.id 𝒪 Onr) := by
        rw [memE]
        have h1 : Fr (Fr (u : Onr)) = (u : Onr) := by rw [hu]; exact (memE _).1 (ζE' - ζE).2
        have h2 : Fr (Fr ((u : Onr) * ((u⁻¹ : Onrˣ) : Onr))) = 1 := by rw [Units.mul_inv, map_one,
          map_one]
        rw [map_mul, map_mul, h1] at h2
        calc Fr (Fr ((u⁻¹ : Onrˣ) : Onr)) = ((u⁻¹ : Onrˣ) : Onr) * ((u : Onr) * Fr (Fr ((u⁻¹ :
          Onrˣ) : Onr))) := by
              rw [← mul_assoc, Units.inv_mul, one_mul]
          _ = ((u⁻¹ : Onrˣ) : Onr) := by rw [h2, mul_one]
      refine ⟨⟨ζE' - ζE, ⟨((u⁻¹ : Onrˣ) : Onr), hwE⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
      · change (Fr ζ - ζ) * ((u⁻¹ : Onrˣ) : Onr) = 1; rw [← hu, Units.mul_inv]
      · change ((u⁻¹ : Onrˣ) : Onr) * (Fr ζ - ζ) = 1; rw [← hu, Units.inv_mul]
    ·
      refine eq_top_iff.2 fun z _ => ?_
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨a, b, hv⟩ := hspan v.1 v.2
      have hv' : v = algebraMap 𝒪 _ a + algebraMap 𝒪 _ b * ζE := Subtype.ext (by simpa using hv)
      rw [hv', map_add, map_mul]
      refine Subalgebra.add_mem _ ?_ (Subalgebra.mul_mem _ ?_ (Algebra.self_mem_adjoin_singleton 𝒪
        _))
      · exact Subalgebra.algebraMap_mem _ a
      · exact Subalgebra.algebraMap_mem _ b
    ·
      have hζ2 : Fr (Fr ζ) = ζ := (memE ζ).1 hζE
      obtain ⟨s, hs⟩ := (hfix (ζ + Fr ζ)).1 (by rw [map_add, hζ2, add_comm])
      obtain ⟨p, hp⟩ := (hfix (ζ * Fr ζ)).1 (by rw [map_mul, hζ2, mul_comm])
      refine ⟨s, -p, ?_⟩
      have key : ζ ^ 2 = algebraMap 𝒪 Onr s * ζ + algebraMap 𝒪 Onr (-p) := by
        rw [map_neg, ← hs, ← hp]; ring
      have keyE : ζE ^ 2 = algebraMap 𝒪 _ s * ζE + algebraMap 𝒪 _ (-p) := Subtype.ext (by simpa
        using key)
      have := congrArg (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans
        Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) keyE
      rw [map_pow, map_add, map_mul] at this
      exact this

set_option autoImplicit false

namespace O2Rigid

private theorem eq_or_eq_of_mul_eq_zero {B : Type*} [CommRing B] [IsLocalRing B] {a a' b : B}
    (h : (b - a) * (b - a') = 0) (hu : IsUnit (a - a')) : b = a ∨ b = a' := by
  by_cases h1 : IsUnit (b - a)
  · right
    have : b - a' = 0 := by
      obtain ⟨u, hu'⟩ := h1
      have := congrArg (fun x => (↑u⁻¹ : B) * x) h
      simp only [mul_zero] at this
      rwa [← mul_assoc, ← hu', Units.inv_mul, one_mul] at this
    exact sub_eq_zero.mp this
  · left
    by_cases h2 : IsUnit (b - a')
    · have : b - a = 0 := by
        obtain ⟨u, hu'⟩ := h2
        have := congrArg (fun x => x * (↑u⁻¹ : B)) h
        simp only [zero_mul] at this
        rwa [mul_assoc, ← hu', Units.mul_inv, mul_one] at this
      exact sub_eq_zero.mp this
    · exfalso
      have hm1 : b - a ∈ IsLocalRing.maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr h1
      have hm2 : b - a' ∈ IsLocalRing.maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr h2
      have : a - a' ∈ IsLocalRing.maximalIdeal B := by
        have := Ideal.sub_mem _ hm2 hm1
        rwa [sub_sub_sub_cancel_left] at this
      exact (IsLocalRing.mem_maximalIdeal _).mp this hu

end O2Rigid

/-- Two `𝒪`-algebra maps from the Frobenius-square equalizer quotient
to a local ring are equal or differ by precomposition with `Fr₂`. -/
public theorem algHom_eq_or_eq_comp_frobTwo_of_isLocalRing

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type u) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})

    (Onr : Type u) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span
      {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p
      ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})

    (n : ℕ)
    (Fr₂ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸
      Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)
        (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) ≃ₐ[𝒪] (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr)
          : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer
            ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))
    (hFr₂ : ∀ (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id
      𝒪 Onr))), (y' : Onr) = Fr (y : Onr) → Fr₂ (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y')
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B]
    (ε ε' : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))
      ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪]
        Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) :
    ε' = ε ∨ ε' = ε.comp Fr₂.toAlgHom := by
  obtain ⟨hsq, α, hunit, hadj, s, t, hα⟩ :=
    IsDiscreteValuationRing.frobTwo_frobTwo_and_exists_generator 𝒪 hdvr π hπ hcomplete hres
      hunr Onr Fr hOnr_complete hOnr_max
      hOnr_alg hOnr_closed hFr n Fr₂ hFr₂

  have hα' : (Fr₂ α) ^ 2 = algebraMap 𝒪 _ s * Fr₂ α + algebraMap 𝒪 _ t := by
    have := congrArg Fr₂ hα
    rwa [map_pow, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes] at this
  have htr : α + Fr₂ α = algebraMap 𝒪 _ s := by
    have h1 : (Fr₂ α - α) * (α + Fr₂ α - algebraMap 𝒪 _ s) = 0 := by
      have := sub_eq_zero.mpr hα'
      linear_combination hα' - hα
    obtain ⟨u, hu⟩ := hunit
    have := congrArg (fun x => ((↑u⁻¹ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr
      →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr :
        Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))) * x) h1
    simp only [mul_zero] at this
    rw [← mul_assoc, ← hu, Units.inv_mul, one_mul] at this
    exact sub_eq_zero.mp this
  have hnorm : α * Fr₂ α = - algebraMap 𝒪 _ t := by
    have : Fr₂ α = algebraMap 𝒪 _ s - α := by rw [← htr]; ring
    rw [this]; linear_combination (-1 : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr
      →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr :
        Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) * hα

  set a := ε α with ha
  set a' := ε (Fr₂ α) with ha'
  set b := ε' α with hb
  have hprod : (b - a) * (b - a') = 0 := by
    have h1 : b ^ 2 = algebraMap 𝒪 B s * b + algebraMap 𝒪 B t := by
      have := congrArg ε' hα
      rwa [map_pow, map_add, map_mul, AlgHom.commutes, AlgHom.commutes] at this
    have h2 : a + a' = algebraMap 𝒪 B s := by rw [ha, ha', ← map_add, htr, AlgHom.commutes]
    have h3 : a * a' = - algebraMap 𝒪 B t := by rw [ha, ha', ← map_mul, hnorm, map_neg,
      AlgHom.commutes]
    linear_combination h1 - b * h2 + h3
  have hu : IsUnit (a - a') := by
    rw [ha, ha', ← map_sub]
    have : IsUnit (α - Fr₂ α) := by rw [← neg_sub]; exact hunit.neg
    exact this.map ε

  have hext : ∀ (φ ψ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)
    (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪]
      Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B), φ α = ψ α → φ = ψ := by
    intro φ ψ hφψ
    have hle : Algebra.adjoin 𝒪 {α} ≤ AlgHom.equalizer φ ψ := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact hφψ
    rw [hadj, top_le_iff] at hle
    ext z
    have hz : z ∈ AlgHom.equalizer φ ψ := hle ▸ Algebra.mem_top
    exact hz
  rcases O2Rigid.eq_or_eq_of_mul_eq_zero hprod hu with h | h
  · left; exact hext ε' ε (by rw [← hb, ← ha, h])
  · right; exact hext ε' (ε.comp Fr₂.toAlgHom) (by rw [← hb, h, ha', AlgHom.comp_apply]; rfl)

end IsDiscreteValuationRing
