/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_PhiGen_phiProd_conj_coeff_zero_lead.lean`,
`Theorems/Thm_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le.lean`,
`P2M/Sol/S_ModularCurve_PhiGen_phiProd_conj_coeff_zero_lead.lean`,
`Theorems/Thm_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.lean`,
and
`P2M/Sol/S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.PhiGen
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

open Polynomial

namespace ModularCurve
namespace PhiGen

section CoeffEmbJq

variable (K : Type*) [Field K] [Algebra ℚ K]

theorem coeff_coeffEmb_jq_neg_one : (coeffEmb K jq).coeff (-1 : ℤ) = 1 := by
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]

private theorem coeff_coeffEmb_jq_of_lt {k : ℤ} (hk : k < -1) : (coeffEmb K jq).coeff k = 0 := by
  rw [coeffEmb_coeff, coeff_jq_of_lt hk, map_zero]

end CoeffEmbJq

private theorem _root_.ModularCurve.PoleOrderLE.mono
    {K : Type*} [Field K] {f : LaurentSeries K} {m n : ℕ}
    (hf : PoleOrderLE f m) (hmn : m ≤ n) : PoleOrderLE f n :=
  fun k hk => hf k (by omega)

private theorem poleOrderLE_zero {K : Type*} [Field K] (n : ℕ) :
    PoleOrderLE (0 : LaurentSeries K) n :=
  fun _ _ => rfl

private theorem poleOrderLE_one {K : Type*} [Field K] :
    PoleOrderLE (1 : LaurentSeries K) 0 := by
  intro m hm
  rw [HahnSeries.coeff_one, ite_eq_right (by omega)]

private theorem _root_.ModularCurve.PoleOrderLE.neg
    {K : Type*} [Field K] {f : LaurentSeries K} {n : ℕ}
    (hf : PoleOrderLE f n) : PoleOrderLE (-f) n := by
  intro m hm
  rw [HahnSeries.coeff_neg, hf m hm, neg_zero]

private theorem _root_.ModularCurve.PoleOrderLE.add
    {K : Type*} [Field K] {f g : LaurentSeries K} {n : ℕ}
    (hf : PoleOrderLE f n) (hg : PoleOrderLE g n) : PoleOrderLE (f + g) n := by
  intro m hm
  rw [HahnSeries.coeff_add, hf m hm, hg m hm, add_zero]

private theorem _root_.ModularCurve.PoleOrderLE.mul
    {K : Type*} [Field K] {f g : LaurentSeries K} {m n : ℕ}
    (hf : PoleOrderLE f m) (hg : PoleOrderLE g n) : PoleOrderLE (f * g) (m + n) := by
  intro k hk
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  obtain ⟨-, -, hsum⟩ := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1 < -(m : ℤ)
  · rw [hf ij.1 hi, zero_mul]
  · refine mul_eq_zero_of_right _ (hg ij.2 ?_)
    push_cast at hk
    omega

private theorem _root_.ModularCurve.PoleOrderLE.qTwist
    {K : Type*} [Field K] {f : LaurentSeries K} {n : ℕ}
    (hf : PoleOrderLE f n) (u : Kˣ) : PoleOrderLE (ModularCurve.qTwist u f) n := by
  intro m hm
  rw [qTwist_coeff, hf m hm, mul_zero]

private theorem _root_.ModularCurve.PoleOrderLE.qExpand
    {K : Type*} [Field K] {f : LaurentSeries K} {n : ℕ}
    (hf : PoleOrderLE f n) (N : ℕ) [NeZero N] :
    PoleOrderLE (ModularCurve.qExpand K N f) (N * n) := by
  intro m hm
  by_cases hdvd : (N : ℤ) ∣ m
  · obtain ⟨c, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    refine hf c ?_
    have hN : 0 < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    push_cast at hm
    nlinarith
  · exact qExpand_coeff_of_not_dvd N f hdvd

private def conjPoleBound (ℓ : ℕ) : Fin (ℓ + 1) → ℕ :=
  fun i => if i = 0 then ℓ * ℓ else 1

private theorem conjPoleBound_zero (ℓ : ℕ) : conjPoleBound ℓ 0 = ℓ * ℓ := ite_eq_left rfl

private theorem conjPoleBound_succ (ℓ : ℕ) (b : Fin ℓ) : conjPoleBound ℓ b.succ = 1 :=
  ite_eq_right (Fin.succ_ne_zero b)

private theorem sum_conjPoleBound (ℓ : ℕ) :
    ∑ i : Fin (ℓ + 1), conjPoleBound ℓ i = ℓ * ℓ + ℓ := by
  rw [Fin.sum_univ_succ, conjPoleBound_zero]
  congr 1
  simp only [conjPoleBound_succ]
  simp

private theorem poleOrderLE_conj_zero {K : Type*} [Field K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {J : LaurentSeries K}
    {conj : Fin (ℓ + 1) → LaurentSeries K} (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J)
    (hJ : PoleOrderLE J 1) : PoleOrderLE (conj 0) (ℓ * ℓ) := by
  rw [hconj0]
  have h := hJ.qExpand (ℓ * ℓ)
  simpa using h

private theorem poleOrderLE_conj_succ {K : Type*} [Field K] {ℓ : ℕ} {ζ : Kˣ}
    {J : LaurentSeries K} {conj : Fin (ℓ + 1) → LaurentSeries K}
    (hconjS : ∀ b : Fin ℓ, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ)) J)
    (hJ : PoleOrderLE J 1) (b : Fin ℓ) : PoleOrderLE (conj b.succ) 1 := by
  rw [hconjS b]
  exact hJ.qTwist _

private theorem poleOrderLE_conj {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {ζ : Kˣ} {J : LaurentSeries K} {conj : Fin (ℓ + 1) → LaurentSeries K}
    (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J)
    (hconjS : ∀ b : Fin ℓ, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ)) J)
    (hJ : PoleOrderLE J 1) (i : Fin (ℓ + 1)) :
    PoleOrderLE (conj i) (conjPoleBound ℓ i) := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨b, rfl⟩
  · rw [conjPoleBound_zero]
    exact poleOrderLE_conj_zero hconj0 hJ
  · rw [conjPoleBound_succ]
    exact poleOrderLE_conj_succ hconjS hJ b

private theorem poleOrderLE_coeff_X_sub_C {K : Type*} [Field K] {a : LaurentSeries K}
    {n : ℕ} (ha : PoleOrderLE a n) (k : ℕ) :
    PoleOrderLE ((Polynomial.X - Polynomial.C a).coeff k) n := by
  match k with
  | 0 =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub]
    exact ha.neg
  | 1 =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C,
      ite_eq_right (one_ne_zero), sub_zero]
    exact poleOrderLE_one.mono (Nat.zero_le _)
  | (k + 2) =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_zero]
    exact poleOrderLE_zero _

private theorem phiProd_def {K : Type*} [Field K] (ℓ : ℕ)
    (conj : Fin (ℓ + 1) → LaurentSeries K) :
    phiProd ℓ conj = ∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (conj i)) := rfl

private theorem poleOrderLE_prod {K : Type*} [Field K] {ι : Type*} (s : Finset ι)
    (f : ι → LaurentSeries K) (n : ι → ℕ) (hf : ∀ i ∈ s, PoleOrderLE (f i) (n i)) :
    PoleOrderLE (∏ i ∈ s, f i) (∑ i ∈ s, n i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using poleOrderLE_one
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact (hf a (Finset.mem_cons_self a s)).mul
      (ih fun i hi => hf i (Finset.mem_cons_of_mem hi))

private theorem coeff_mul_lead {K : Type*} [Field K] {f g : LaurentSeries K} {m n : ℕ}
    (hf : PoleOrderLE f m) (hg : PoleOrderLE g n) :
    (f * g).coeff (-((m + n : ℕ) : ℤ)) = f.coeff (-(m : ℤ)) * g.coeff (-(n : ℤ)) := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_single ((-(m : ℤ), -(n : ℤ))) ?_ ?_
  · rintro ⟨i, j⟩ hij hne
    obtain ⟨hi, hj, hsum⟩ := Finset.mem_antidiagonal.mp hij
    rw [HahnSeries.mem_support] at hi hj
    have him : ¬ i < -(m : ℤ) := fun h => hi (hf i h)
    have hjn : ¬ j < -(n : ℤ) := fun h => hj (hg j h)
    push_cast at hsum
    have hi' : i = -(m : ℤ) := by omega
    have hj' : j = -(n : ℤ) := by omega
    exact absurd (by rw [hi', hj']) hne
  · intro hni
    by_contra hne
    refine hni (Finset.mem_antidiagonal.mpr ⟨?_, ?_, by push_cast; ring⟩) <;>
      rw [HahnSeries.mem_support]
    · exact fun h0 => hne (by rw [h0, zero_mul])
    · exact fun h0 => hne (by rw [h0, mul_zero])

private theorem coeff_prod_lead {K : Type*} [Field K] {ι : Type*} (s : Finset ι)
    (f : ι → LaurentSeries K) (n : ι → ℕ) (hf : ∀ i ∈ s, PoleOrderLE (f i) (n i)) :
    (∏ i ∈ s, f i).coeff (-((∑ i ∈ s, n i : ℕ) : ℤ)) =
      ∏ i ∈ s, (f i).coeff (-(n i : ℤ)) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons, Finset.prod_cons,
      coeff_mul_lead (hf a (Finset.mem_cons_self a s))
        (poleOrderLE_prod s f n fun i hi => hf i (Finset.mem_cons_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_cons_of_mem hi)]

private theorem pow_sum_range_isPrimitiveRoot {K : Type*} [Field K] {ℓ : ℕ} (hℓ : Nat.Prime ℓ)
    {z : K} (hz : IsPrimitiveRoot z ℓ) :
    z ^ (∑ i ∈ Finset.range ℓ, i) = (-1) ^ (ℓ + 1) := by
  rcases hℓ.eq_two_or_odd' with rfl | hodd
  · rw [hz.eq_neg_one_of_two_right]
    norm_num [Finset.sum_range_succ]
  · obtain ⟨m, hm⟩ := hodd
    have hsum : ∑ i ∈ Finset.range ℓ, i = ℓ * m := by
      have h2 := Finset.sum_range_id_mul_two ℓ
      have hℓ1 : ℓ - 1 = 2 * m := by omega
      rw [hℓ1, show ℓ * (2 * m) = ℓ * m * 2 by ring] at h2
      omega
    rw [hsum, pow_mul, hz.pow_eq_one, one_pow]
    exact (Even.neg_one_pow ⟨m + 1, by omega⟩).symm

private theorem prod_inv_pow_isPrimitiveRoot {K : Type*} [Field K] {ℓ : ℕ} (hℓ : Nat.Prime ℓ)
    {z : K} (hz : IsPrimitiveRoot z ℓ) :
    ∏ b : Fin ℓ, ((z ^ (b : ℕ))⁻¹ : K) = (-1) ^ (ℓ + 1) := by
  have hsum : (∑ b : Fin ℓ, (b : ℕ)) = ∑ i ∈ Finset.range ℓ, i :=
    Fin.sum_univ_eq_sum_range (fun i => i) ℓ
  rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, hsum,
    pow_sum_range_isPrimitiveRoot hℓ hz, ← inv_pow, inv_neg, inv_one]

private theorem phiProd_coeff_zero_eq_prod_neg {K : Type*} [Field K] {ℓ : ℕ}
    {conj : Fin (ℓ + 1) → LaurentSeries K} :
    (phiProd ℓ conj).coeff 0 = ∏ i : Fin (ℓ + 1), (-(conj i)) := by
  rw [phiProd_def, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun i _ => by
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]

private theorem conj_zero_coeff_lead {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {J : LaurentSeries K} {conj : Fin (ℓ + 1) → LaurentSeries K}
    (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J) (hJlead : J.coeff (-1 : ℤ) = 1) :
    (conj 0).coeff (-((ℓ * ℓ : ℕ) : ℤ)) = 1 := by
  rw [hconj0, show (-((ℓ * ℓ : ℕ) : ℤ)) = ((ℓ * ℓ : ℕ) : ℤ) * (-1 : ℤ) by ring,
    qExpand_coeff_mul, hJlead]

private theorem conj_succ_coeff_lead {K : Type*} [Field K] {ℓ : ℕ} {ζ : Kˣ}
    {J : LaurentSeries K} {conj : Fin (ℓ + 1) → LaurentSeries K}
    (hconjS : ∀ b : Fin ℓ, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ)) J)
    (hJlead : J.coeff (-1 : ℤ) = 1) (b : Fin ℓ) :
    (conj b.succ).coeff (-(1 : ℤ)) = (((ζ : K) ^ (b : ℕ))⁻¹ : K) := by
  rw [hconjS b, qTwist_coeff, hJlead, mul_one, zpow_neg_one, ← Units.val_pow_eq_pow_val,
    ← Units.val_inv_eq_inv_val]

private theorem phiProd_coeff_zero_lead {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {ζ : Kˣ} {J : LaurentSeries K} {conj : Fin (ℓ + 1) → LaurentSeries K}
    (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J)
    (hconjS : ∀ b : Fin ℓ, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ)) J)
    (hJ : PoleOrderLE J 1) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (hJlead : J.coeff (-1 : ℤ) = 1) :
    ((phiProd ℓ conj).coeff 0).coeff (-((ℓ * ℓ + ℓ : ℕ) : ℤ)) = 1 := by
  rw [phiProd_coeff_zero_eq_prod_neg, ← sum_conjPoleBound ℓ,
    coeff_prod_lead Finset.univ _ (conjPoleBound ℓ)
      (fun i _ => (poleOrderLE_conj hconj0 hconjS hJ i).neg),
    Fin.prod_univ_succ]
  have h0 : (-(conj 0)).coeff (-((conjPoleBound ℓ 0 : ℕ) : ℤ)) = -1 := by
    rw [HahnSeries.coeff_neg, conjPoleBound_zero, conj_zero_coeff_lead hconj0 hJlead]
  have hS : ∀ b : Fin ℓ, (-(conj b.succ)).coeff (-((conjPoleBound ℓ b.succ : ℕ) : ℤ)) =
      -((((ζ : K) ^ (b : ℕ))⁻¹ : K)) := by
    intro b
    rw [HahnSeries.coeff_neg, conjPoleBound_succ, Nat.cast_one,
      conj_succ_coeff_lead hconjS hJlead b]
  rw [h0]
  simp only [hS]
  rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin,
    prod_inv_pow_isPrimitiveRoot hℓ.out hζ, ← pow_add, ← pow_succ']
  exact Even.neg_one_pow ⟨ℓ + 1, by ring⟩

private theorem poleOrderLE_coeff_prod_X_sub_C_card {K : Type*} [Field K] {ι : Type*}
    (s : Finset ι) (a : ι → LaurentSeries K) (ha : ∀ i ∈ s, PoleOrderLE (a i) 1) :
    ∀ k : ℕ, PoleOrderLE ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff k)
      (s.card - k) := by
  induction s using Finset.cons_induction with
  | empty =>
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using poleOrderLE_one
    · rw [Finset.prod_empty, Polynomial.coeff_one, ite_eq_right (by omega)]
      exact poleOrderLE_zero _
  | cons a₀ s ha₀ ih =>
    intro k
    have hmem : ∀ i ∈ s, PoleOrderLE (a i) 1 :=
      fun i hi => ha i (Finset.mem_cons_of_mem hi)
    rw [Finset.prod_cons, Finset.card_cons]
    match k with
    | 0 =>
      rw [Polynomial.mul_coeff_zero]
      exact ((poleOrderLE_coeff_X_sub_C (ha a₀ (Finset.mem_cons_self a₀ s)) 0).mul
        (ih hmem 0)).mono (by omega)
    | (k + 1) =>
      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
        sub_eq_add_neg]
      refine PoleOrderLE.add ?_ (PoleOrderLE.neg ?_)
      · exact (ih hmem k).mono (by omega)
      · by_cases hks : k + 1 ≤ s.card
        · exact ((ha a₀ (Finset.mem_cons_self a₀ s)).mul (ih hmem (k + 1))).mono
            (by omega)
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
          · exact poleOrderLE_zero _
          · rw [Polynomial.natDegree_prod_of_monic _ _
              (fun i _ => Polynomial.monic_X_sub_C (a i))]
            simp only [Polynomial.natDegree_X_sub_C, ← Finset.card_eq_sum_ones]
            omega

private theorem poleOrderLE_phiProd_coeff_of_ne_zero {K : Type*} [Field K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {J : LaurentSeries K}
    {conj : Fin (ℓ + 1) → LaurentSeries K} (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J)
    (hconjS : ∀ b : Fin ℓ, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ)) J)
    (hJ : PoleOrderLE J 1) (k : ℕ) (hk : k ≠ 0) :
    PoleOrderLE ((phiProd ℓ conj).coeff k) (ℓ * ℓ + ℓ - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hℓ2 : 2 ≤ ℓ := hℓ.out.two_le
  have hsq : 4 ≤ ℓ * ℓ := Nat.mul_le_mul hℓ2 hℓ2
  rw [phiProd_def, Fin.prod_univ_succ, sub_mul, Polynomial.coeff_sub,
    Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, sub_eq_add_neg]
  have hR : ∀ j : ℕ, PoleOrderLE
      ((∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (conj b.succ))).coeff j)
      (Finset.univ.card - j) :=
    poleOrderLE_coeff_prod_X_sub_C_card Finset.univ _
      (fun b _ => poleOrderLE_conj_succ hconjS hJ b)
  rw [Finset.card_univ, Fintype.card_fin] at hR
  refine PoleOrderLE.add ?_ (PoleOrderLE.neg ?_)
  · exact (hR k).mono (by omega)
  · exact ((poleOrderLE_conj_zero hconj0 hJ).mul (hR (k + 1))).mono (by omega)

private theorem poleOrderLE_coeffEmb_jq {K : Type*} [Field K] [Algebra ℚ K] :
    PoleOrderLE (coeffEmb K jq) 1 :=
  fun _ hm => coeff_coeffEmb_jq_of_lt K (by exact_mod_cast hm)

theorem phiProd_conj_coeff_zero_lead {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    ((phiProd ℓ (conj ℓ ζ)).coeff 0).coeff (-((ℓ * ℓ + ℓ : ℕ) : ℤ)) = 1 :=
  phiProd_coeff_zero_lead (conj_zero ℓ ζ) (conj_succ ℓ ζ)
    (poleOrderLE_coeffEmb_jq (K := K)) hζ (coeff_coeffEmb_jq_neg_one K)

private theorem poleOrderLE_phiProd_conj_of_ne_zero {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (k : ℕ) (hk : k ≠ 0) :
    PoleOrderLE ((phiProd ℓ (conj ℓ ζ)).coeff k) (ℓ * ℓ + ℓ - 1) :=
  poleOrderLE_phiProd_coeff_of_ne_zero (conj_zero ℓ ζ) (conj_succ ℓ ζ)
    (poleOrderLE_coeffEmb_jq (K := K)) k hk

theorem phiProd_conj_coeff_eq_zero_of_le {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (k : ℕ) (hk : k ≠ 0) (m : ℕ)
    (hm : ℓ * ℓ + ℓ ≤ m) : ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff (-(m : ℤ)) = 0 := by
  have hℓ2 : 2 ≤ ℓ := hℓ.out.two_le
  exact poleOrderLE_phiProd_conj_of_ne_zero ℓ ζ k hk (-(m : ℤ)) (by omega)

theorem poleOrderLE_phiProd_conj_coeff {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (k : ℕ) :
    PoleOrderLE ((phiProd ℓ (conj ℓ ζ)).coeff k) (ℓ * ℓ + ℓ) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [phiProd_coeff_zero_eq_prod_neg, ← sum_conjPoleBound ℓ]
    exact poleOrderLE_prod Finset.univ _ (conjPoleBound ℓ) fun i _ =>
      (poleOrderLE_conj (conj_zero ℓ ζ) (conj_succ ℓ ζ) poleOrderLE_coeffEmb_jq i).neg
  · exact (poleOrderLE_phiProd_conj_of_ne_zero ℓ ζ k hk).mono (Nat.sub_le _ _)

end PhiGen
end ModularCurve

end

noncomputable section

open Polynomial

namespace ModularCurve
namespace PhiGen

section Splitting

variable {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
variable (ζ : Kˣ) {c : ℕ → LaurentSeries ℚ}

theorem splits_of_coeff_evalAtJ_eq (hc : PhiGenDescends ℓ ζ c)
    (data : ModularPolynomialData ℓ)
    (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) :
    data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ) := by
  ext k
  rw [Polynomial.coeff_map, RingHom.comp_apply, RingHom.comp_apply, hcoeff k, hc k]

end Splitting

end PhiGen
end ModularCurve

end
