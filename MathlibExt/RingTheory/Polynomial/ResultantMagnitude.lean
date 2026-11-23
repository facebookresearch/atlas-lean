/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Polynomial_eq_of_forall_abs_resultant_X_pow_add_C_le.lean`,
`Theorems/Thm_Polynomial_eq_of_forall_natAbs_resultant_X_pow_add_C_le.lean`,
`P2M/Sol/S_Polynomial_eq_of_forall_abs_resultant_X_pow_add_C_le.lean`
and
`P2M/Sol/S_Polynomial_eq_of_forall_natAbs_resultant_X_pow_add_C_le.lean`
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

public import MathlibExt.Algebra.Polynomial.RootPowerSums
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Topology.Algebra.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Int.Lemmas


set_option autoImplicit false

namespace P2mResCmpQ

open Polynomial Filter


noncomputable def A (P : ℚ[X]) (n : ℕ) : ℚ[X] :=
  resultant ((X : ℚ[X][X]) ^ n + C (X : ℚ[X])) (P.map C) n P.natDegree

theorem eval_A (P : ℚ[X]) (n : ℕ) (c : ℚ) : (A P n).eval c = (X ^ n + C c : ℚ[X]).resultant
  P := by
  have hdeg : (X ^ n + C c : ℚ[X]).natDegree = n := natDegree_X_pow_add_C
  have key := resultant_map_map ((X : ℚ[X][X]) ^ n + C (X : ℚ[X])) (P.map C) n P.natDegree
    (evalRingHom c)
  rw [coe_evalRingHom] at key
  rw [A, ← key]
  have hf : ((X : ℚ[X][X]) ^ n + C (X : ℚ[X])).map (evalRingHom c) = X ^ n + C c := by
    rw [Polynomial.map_add, Polynomial.map_pow, map_X, map_C, coe_evalRingHom, eval_X]
  have hg : (P.map C).map (evalRingHom c) = P := by
    rw [Polynomial.map_map]
    conv_rhs => rw [← Polynomial.map_id (p := P)]
    congr 1
    ext a
    simp
  rw [hf, hg]
  show _ = resultant (X ^ n + C c) P (X ^ n + C c : ℚ[X]).natDegree P.natDegree
  rw [hdeg]

theorem resultant_map_eq_prod (G P : ℚ[X]) (hP : P.Monic) :
    (algebraMap ℚ ℂ) (G.resultant P) =
      (-1) ^ (G.natDegree * P.natDegree) * ((P.map (algebraMap ℚ ℂ)).roots.map (fun z => (G.map
        (algebraMap ℚ ℂ)).eval z)).prod
        := by
  set Gc := G.map (algebraMap ℚ ℂ) with hGc
  set Pc := P.map (algebraMap ℚ ℂ) with hPc
  have hPcm : Pc.Monic := hP.map _
  have hPcdeg : Pc.natDegree = P.natDegree := hP.natDegree_map _
  have hGcdeg : Gc.natDegree = G.natDegree := natDegree_map_eq_of_injective (algebraMap ℚ
    ℂ).injective _
  have h1 : (algebraMap ℚ ℂ) (G.resultant P) = Gc.resultant Pc G.natDegree P.natDegree := by
    show (algebraMap ℚ ℂ) (G.resultant P G.natDegree P.natDegree) = _
    rw [← resultant_map_map]
  have h2 : Gc.resultant Pc G.natDegree P.natDegree =
      (-1) ^ (G.natDegree * P.natDegree) * Pc.resultant Gc Pc.natDegree G.natDegree := by
    rw [resultant_comm, hPcdeg]
  have h3 : Pc.resultant Gc Pc.natDegree G.natDegree = (Pc.roots.map (fun z => Gc.eval z)).prod :=
    by
    rw [resultant_eq_prod_eval Pc Gc G.natDegree hGcdeg.le (IsAlgClosed.splits Pc),
      hPcm.leadingCoeff, one_pow, one_mul]
  rw [h1, h2, h3]

theorem cast_resultant_X_pow_add_C (P : ℚ[X]) (hP : P.Monic) (n : ℕ) (c : ℚ) :
    (algebraMap ℚ ℂ) ((X ^ n + C c : ℚ[X]).resultant P) =
      (-1) ^ (n * P.natDegree) * ((P.map (algebraMap ℚ ℂ)).roots.map (fun z : ℂ => z ^ n +
        (algebraMap ℚ ℂ) c)).prod := by
  rw [resultant_map_eq_prod _ _ hP, natDegree_X_pow_add_C]
  congr 2
  apply Multiset.map_congr rfl
  intro z _
  rw [Polynomial.map_add, Polynomial.map_pow, map_X, map_C, eval_add, eval_pow, eval_X, eval_C]

noncomputable def B (P : ℚ[X]) (n : ℕ) : ℂ[X] :=
  C ((-1 : ℂ) ^ (n * P.natDegree)) * (((P.map (algebraMap ℚ ℂ)).roots.map (fun z => z ^ n)).map
    (fun r => X + C
    r)).prod

theorem eval_B (P : ℚ[X]) (n : ℕ) (c : ℂ) :
    (B P n).eval c = (-1) ^ (n * P.natDegree) * ((P.map (algebraMap ℚ ℂ)).roots.map (fun z => z ^ n
      + c)).prod :=
      by
  rw [B, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  apply congr_arg
  apply Multiset.map_congr rfl
  intro z _
  simp only [Function.comp_apply, eval_add, eval_X, eval_C]
  ring

theorem map_A_eq_B (P : ℚ[X]) (hP : P.Monic) (n : ℕ) : (A P n).map (algebraMap ℚ ℂ) = B P n := by
  apply eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.range (algebraMap ℚ ℂ))
  · rintro _ ⟨c, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [eval_map, eval₂_at_apply, eval_A, cast_resultant_X_pow_add_C P hP, eval_B]
  · exact Set.infinite_range_of_injective (algebraMap ℚ ℂ).injective

theorem esymm_one {R : Type*} [CommSemiring R] (s : Multiset R) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]

noncomputable def psum (P : ℚ[X]) (n : ℕ) : ℂ := ((P.map (algebraMap ℚ ℂ)).roots.map (fun z => z ^
  n)).sum

theorem coeff_B (P : ℚ[X]) (hP : P.Monic) (n : ℕ) :
    (∀ k, P.natDegree < k → (B P n).coeff k = 0) ∧
    (B P n).coeff P.natDegree = (-1) ^ (n * P.natDegree) ∧
    (0 < P.natDegree → (B P n).coeff (P.natDegree - 1) = (-1) ^ (n * P.natDegree) * psum P n) := by
  set s : Multiset ℂ := (P.map (algebraMap ℚ ℂ)).roots.map (fun z => z ^ n) with hs
  have hcard : Multiset.card s = P.natDegree := by
    rw [hs, Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, hP.natDegree_map]
  set Pr : ℂ[X] := (s.map (fun r => X + C r)).prod with hPr
  have hB : B P n = C ((-1 : ℂ) ^ (n * P.natDegree)) * Pr := rfl
  have hPrmonic : Pr.Monic := monic_multiset_prod_of_monic _ _ (fun r _ => monic_X_add_C r)
  have hPrdeg : Pr.natDegree = P.natDegree := by
    rw [hPr, natDegree_multiset_prod_of_monic _ (by
      intro f hf
      obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hf
      exact monic_X_add_C r), Multiset.map_map]
    have : (s.map (natDegree ∘ fun r => X + C r)) = s.map (fun _ => 1) := by
      apply Multiset.map_congr rfl
      intro r _
      simp
    rw [this, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one, hcard]
  refine ⟨fun k hk => ?_, ?_, fun hd => ?_⟩
  · rw [hB, coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by rw [hPrdeg]; exact hk), mul_zero]
  · rw [hB, coeff_C_mul]
    have : Pr.coeff P.natDegree = 1 := by
      rw [← hPrdeg]; exact hPrmonic.coeff_natDegree
    rw [this, mul_one]
  · rw [hB, coeff_C_mul, hPr, Multiset.prod_X_add_C_coeff s (by rw [hcard]; omega), hcard,
      show P.natDegree - (P.natDegree - 1) = 1 by omega, esymm_one]
    rfl

theorem coeff_A (P : ℚ[X]) (hP : P.Monic) (n : ℕ) :
    (∀ k, P.natDegree < k → (A P n).coeff k = 0) ∧
    (A P n).coeff P.natDegree = (-1) ^ (n * P.natDegree) ∧
    (0 < P.natDegree → (algebraMap ℚ ℂ) ((A P n).coeff (P.natDegree - 1)) = (-1) ^ (n *
      P.natDegree) * psum P n)
      := by
  obtain ⟨h1, h2, h3⟩ := coeff_B P hP n
  have hmap := map_A_eq_B P hP n
  have hcoeff : ∀ k, (algebraMap ℚ ℂ) ((A P n).coeff k) = (B P n).coeff k := by
    intro k
    rw [← hmap, coeff_map]
  refine ⟨fun k hk => ?_, ?_, fun hd => ?_⟩
  · have := hcoeff k
    rw [h1 k hk] at this
    exact (algebraMap ℚ ℂ).injective (by rw [this, map_zero])
  · exact (algebraMap ℚ ℂ).injective (by rw [hcoeff, h2, map_pow, map_neg, map_one])
  · rw [hcoeff, h3 hd]

theorem leadingCoeff_nonneg_of_eventually_nonneg (F A : ℚ[X]) (hF : 0 < F.degree) (hA : A ≠
  0)
    (S : Set ℤ) (hS : ∀ b : ℤ, ∃ c ∈ S, b ≤ c)
    (h : ∀ c ∈ S, A.eval (c : ℚ) ≠ 0 → 0 ≤ F.eval (c : ℚ)) : 0 ≤ F.leadingCoeff := by
  by_contra hlc
  push Not at hlc
  set Fr := F.map (algebraMap ℚ ℝ) with hFr
  set Ar := A.map (algebraMap ℚ ℝ) with hAr
  have hinj : Function.Injective (algebraMap ℚ ℝ) := (algebraMap ℚ ℝ).injective
  have hFr_deg : 0 < Fr.degree := by
    rwa [hFr, degree_map_eq_of_injective hinj]
  have hFr_lc : Fr.leadingCoeff ≤ 0 := by
    rw [hFr, leadingCoeff_map_of_injective hinj, eq_ratCast]
    exact_mod_cast hlc.le
  have h1 : Tendsto (fun x => Fr.eval x) atTop atBot :=
    Polynomial.tendsto_atBot_of_leadingCoeff_nonpos hFr_deg hFr_lc
  have h2 : ∀ᶠ x in atTop, Fr.eval x < 0 := h1.eventually_lt_atBot 0
  have hAr0 : Ar ≠ 0 := by
    rw [hAr, Ne, Polynomial.map_eq_zero_iff hinj]
    exact hA
  have h3 : ∀ᶠ x in atTop, ¬ Ar.IsRoot x := Polynomial.eventually_atTop_not_isRoot hAr0
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp (h2.and h3)
  obtain ⟨c, hcS, hcb⟩ := hS ⌈b⌉
  have hcast : (algebraMap ℚ ℝ) (c : ℚ) = (c : ℝ) := by simp
  have hcb' : b ≤ (algebraMap ℚ ℝ) (c : ℚ) := by
    rw [hcast]
    exact (Int.le_ceil b).trans (by exact_mod_cast hcb)
  obtain ⟨hFc, hAc⟩ := hb _ hcb'
  have hAc' : A.eval (c : ℚ) ≠ 0 := by
    intro h0
    apply hAc
    rw [IsRoot, hAr, eval_map, eval₂_at_apply, h0, map_zero]
  have hpos := h c hcS hAc'
  have : (0 : ℝ) ≤ Fr.eval ((algebraMap ℚ ℝ) (c : ℚ)) := by
    rw [hFr, eval_map, eval₂_at_apply, eq_ratCast]
    exact_mod_cast hpos
  linarith

theorem leadingCoeff_comp_neg_X_nonneg (F A : ℚ[X]) (hF : 0 < F.degree) (hA : A ≠ 0)
    (S : Set ℤ) (hS : ∀ b : ℤ, ∃ c ∈ S, c ≤ b)
    (h : ∀ c ∈ S, A.eval (c : ℚ) ≠ 0 → 0 ≤ F.eval (c : ℚ)) : 0 ≤ (F.comp (-X)).leadingCoeff := by
  refine leadingCoeff_nonneg_of_eventually_nonneg (F.comp (-X)) (A.comp (-X)) ?_ ?_
    {c : ℤ | -c ∈ S} ?_ ?_
  · rwa [degree_comp_neg_X]
  · rwa [Ne, comp_neg_X_eq_zero_iff]
  · intro b
    obtain ⟨c, hcS, hcb⟩ := hS (-b)
    exact ⟨-c, by simpa using hcS, by omega⟩
  · intro c hc hAc
    simp only [Set.mem_setOf_eq] at hc
    rw [eval_comp, eval_neg, eval_X] at hAc ⊢
    rw [← Int.cast_neg] at hAc ⊢
    exact h (-c) hc hAc

theorem psum_eq (P Q : ℚ[X]) (hP : P.Monic) (hQ : Q.Monic) (hdeg : P.natDegree =
  Q.natDegree)
    (hd : 0 < P.natDegree)
    (S : Set ℤ) (hS₁ : ∀ b : ℤ, ∃ c ∈ S, b ≤ c) (hS₂ : ∀ b : ℤ, ∃ c ∈ S, c ≤ b)
    (n : ℕ)
    (h : ∀ c ∈ S, (X ^ n + C (c : ℚ) : ℚ[X]).resultant P ≠ 0 →
      |(X ^ n + C (c : ℚ) : ℚ[X]).resultant Q| ≤ |(X ^ n + C (c : ℚ) : ℚ[X]).resultant P|) :
    psum P n = psum Q n := by
  set ε : ℚ := (-1) ^ (n * P.natDegree) with hε
  obtain ⟨hA1, hA2, hA3⟩ := coeff_A P hP n
  obtain ⟨hB1, hB2, hB3⟩ := coeff_A Q hQ n
  rw [← hdeg] at hB1 hB2 hB3
  set d := P.natDegree with hd'
  set α := (A P n).coeff (d - 1) with hα
  set β := (A Q n).coeff (d - 1) with hβ

  suffices hαβ : α = β by
    have h1 := hA3 hd
    have h2 := hB3 hd
    rw [hαβ] at h1
    rw [h1] at h2
    have hε0 : ((-1 : ℂ)) ^ (n * d) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    exact mul_left_cancel₀ hε0 h2
  by_contra hαβ

  set D := A P n - A Q n with hD
  set E := A P n + A Q n with hE
  have hDdeg : D.natDegree = d - 1 ∧ D.leadingCoeff = α - β := by
    have hle : D.natDegree ≤ d - 1 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [hD, coeff_sub]
      rcases Nat.lt_or_ge d k with hdk | hdk
      · rw [hA1 k hdk, hB1 k hdk, sub_zero]
      · have : k = d := by omega
        rw [this, hA2, hB2, sub_self]
    have hcoeff : D.coeff (d - 1) = α - β := by rw [hD, coeff_sub]
    have hne : D.coeff (d - 1) ≠ 0 := by rw [hcoeff]; exact sub_ne_zero.mpr hαβ
    have hdeg' : D.natDegree = d - 1 := natDegree_eq_of_le_of_coeff_ne_zero hle hne
    exact ⟨hdeg', by rw [leadingCoeff, hdeg', hcoeff]⟩
  have hEdeg : E.natDegree = d ∧ E.leadingCoeff = 2 * ε := by
    have hle : E.natDegree ≤ d := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [hE, coeff_add, hA1 k hk, hB1 k hk, add_zero]
    have hcoeff : E.coeff d = 2 * ε := by rw [hE, coeff_add, hA2, hB2, hε]; ring
    have hne : E.coeff d ≠ 0 := by
      rw [hcoeff, hε]
      exact mul_ne_zero two_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    have hdeg' : E.natDegree = d := natDegree_eq_of_le_of_coeff_ne_zero hle hne
    exact ⟨hdeg', by rw [leadingCoeff, hdeg', hcoeff]⟩
  have hD0 : D ≠ 0 := fun h0 => by
    have := hDdeg.2; rw [h0, leadingCoeff_zero] at this; exact hαβ (sub_eq_zero.mp this.symm)
  have hE0 : E ≠ 0 := fun h0 => by
    have := hEdeg.2; rw [h0, leadingCoeff_zero, hε] at this
    exact absurd this.symm (mul_ne_zero two_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))
  set F := D * E with hF
  have hFdeg : F.natDegree = (d - 1) + d := by rw [hF, natDegree_mul hD0 hE0, hDdeg.1, hEdeg.1]
  have hFlc : F.leadingCoeff = (α - β) * (2 * ε) := by rw [hF, leadingCoeff_mul, hDdeg.2, hEdeg.2]
  have hFpos : 0 < F.degree := by
    rw [degree_eq_natDegree (mul_ne_zero hD0 hE0), hFdeg]
    exact_mod_cast (show 0 < d - 1 + d by omega)
  have hFeval : ∀ c : ℚ, F.eval c =
      ((X ^ n + C c : ℚ[X]).resultant P) ^ 2 - ((X ^ n + C c : ℚ[X]).resultant Q) ^ 2 := by
    intro c
    rw [hF, hD, hE, eval_mul, eval_sub, eval_add, eval_A, eval_A]
    ring
  have hAP0 : A P n ≠ 0 := by
    intro h0
    have := hA2
    rw [h0, coeff_zero] at this
    exact absurd this.symm (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  have hnonneg : ∀ c ∈ S, (A P n).eval (c : ℚ) ≠ 0 → 0 ≤ F.eval (c : ℚ) := by
    intro c hc hAc
    rw [eval_A] at hAc
    have hle := h c hc hAc
    have hsq := sq_le_sq.mpr hle
    rw [hFeval]
    linarith
  have h1 := leadingCoeff_nonneg_of_eventually_nonneg F (A P n) hFpos hAP0 S hS₁ hnonneg
  have h2 := leadingCoeff_comp_neg_X_nonneg F (A P n) hFpos hAP0 S hS₂ hnonneg
  rw [comp_neg_X_leadingCoeff_eq, hFdeg] at h2
  have hodd : Odd (d - 1 + d) := ⟨d - 1, by omega⟩
  rw [hodd.neg_one_pow, neg_one_mul] at h2
  have hlc0 : F.leadingCoeff = 0 := le_antisymm (by linarith) h1
  exact (mul_ne_zero hD0 hE0) (leadingCoeff_eq_zero.mp hlc0)

theorem main (P Q : ℚ[X]) (hP : P.Monic) (hQ : Q.Monic) (hdeg : P.natDegree = Q.natDegree)
    (S : Set ℤ) (hS₁ : ∀ b : ℤ, ∃ c ∈ S, b ≤ c) (hS₂ : ∀ b : ℤ, ∃ c ∈ S, c ≤ b)
    (h : ∀ n : ℕ, 0 < n → ∀ c ∈ S, (X ^ n + C (c : ℚ) : ℚ[X]).resultant P ≠ 0 →
      |(X ^ n + C (c : ℚ) : ℚ[X]).resultant Q| ≤ |(X ^ n + C (c : ℚ) : ℚ[X]).resultant P|) :
    P = Q := by
  rcases Nat.eq_zero_or_pos P.natDegree with hd | hd
  · rw [(Polynomial.Monic.natDegree_eq_zero hP).mp hd,
      (Polynomial.Monic.natDegree_eq_zero hQ).mp (hdeg ▸ hd)]
  have hps : ∀ n : ℕ, 0 < n → psum P n = psum Q n := fun n hn =>
    psum_eq P Q hP hQ hdeg hd S hS₁ hS₂ n (h n hn)
  have key : P.map (algebraMap ℚ ℂ) = Q.map (algebraMap ℚ ℂ) :=
    Polynomial.eq_of_forall_sum_roots_pow_eq _ _ (hP.map _) (hQ.map _) (IsAlgClosed.splits _)
      (IsAlgClosed.splits _) (by rw [hP.natDegree_map, hQ.natDegree_map, hdeg]) hps
  exact Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective key

end P2mResCmpQ

@[expose] public section

namespace Polynomial

/-- Monic rational polynomials of equal degree are determined by two-sided
unbounded resultant magnitude comparisons against `X ^ n + C c`. -/
public theorem eq_of_forall_abs_resultant_X_pow_add_C_le (P Q : Polynomial ℚ)
    (hP : P.Monic) (hQ : Q.Monic) (hdeg : P.natDegree = Q.natDegree)
    (S : Set ℤ) (hS₁ : ∀ b : ℤ, ∃ c ∈ S, b ≤ c) (hS₂ : ∀ b : ℤ, ∃ c ∈ S, c ≤ b)
    (h : ∀ n : ℕ, 0 < n → ∀ c ∈ S,
      (Polynomial.X ^ n + Polynomial.C (c : ℚ) : Polynomial ℚ).resultant P ≠ 0 →
        |(Polynomial.X ^ n + Polynomial.C (c : ℚ) : Polynomial ℚ).resultant Q| ≤
          |(Polynomial.X ^ n + Polynomial.C (c : ℚ) : Polynomial ℚ).resultant P|) :
    P = Q :=
  P2mResCmpQ.main P Q hP hQ hdeg S hS₁ hS₂ h

/-- Monic integer polynomials of equal degree are determined by two-sided
unbounded resultant magnitude comparisons against `X ^ n + C c`. -/
public theorem eq_of_forall_natAbs_resultant_X_pow_add_C_le (P Q : Polynomial ℤ)
    (hP : P.Monic) (hQ : Q.Monic) (hdeg : P.natDegree = Q.natDegree)
    (S : Set ℤ) (hS₁ : ∀ b : ℤ, ∃ c ∈ S, b ≤ c) (hS₂ : ∀ b : ℤ, ∃ c ∈ S, c ≤ b)
    (h : ∀ n : ℕ, 0 < n → ∀ c ∈ S,
      (Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).resultant P ≠ 0 →
        ((Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).resultant Q).natAbs ≤
          ((Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).resultant P).natAbs) :
    P = Q := by
  classical
  set f : ℤ →+* ℚ := Int.castRingHom ℚ with hf
  have hmap : ∀ (A : Polynomial ℤ) (n : ℕ) (c : ℤ),
      ((Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).resultant A : ℚ) =
        (Polynomial.X ^ n + Polynomial.C (c : ℚ) : Polynomial ℚ).resultant
          (A.map f) := by
    intro A n c
    have h1 : (Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).map f =
        Polynomial.X ^ n + Polynomial.C (c : ℚ) := by
      simp [hf, Polynomial.map_add, Polynomial.map_pow]
    have hdegA : (A.map f).natDegree = A.natDegree :=
      natDegree_map_eq_of_injective Int.cast_injective A
    have hdegX : ((Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).map
        f).natDegree =
        (Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).natDegree :=
      natDegree_map_eq_of_injective Int.cast_injective _
    rw [← h1, hdegX, hdegA]
    exact (Polynomial.resultant_map_map _ A _ _ f).symm
  have hdeg' : (P.map f).natDegree = (Q.map f).natDegree := by
    rw [hP.natDegree_map, hQ.natDegree_map, hdeg]
  have key := Polynomial.eq_of_forall_abs_resultant_X_pow_add_C_le (P.map f)
    (Q.map f) (hP.map f) (hQ.map f) hdeg' S hS₁ hS₂ (fun n hn c hc hne => by
      have hneZ : (Polynomial.X ^ n + Polynomial.C c : Polynomial ℤ).resultant
          P ≠ 0 := by
        intro hz
        apply hne
        rw [← hmap P n c, hz]
        simp
      have hle := h n hn c hc hneZ
      have hq := hmap Q n c
      have hp := hmap P n c
      rw [← hq, ← hp]
      have habs : ∀ a : ℤ, |(a : ℚ)| = (a.natAbs : ℚ) := fun a => by
        rw [← Int.cast_abs]
        exact (Nat.cast_natAbs (α := ℚ) a).symm
      rw [habs, habs]
      exact_mod_cast hle)
  exact Polynomial.map_injective f Int.cast_injective key

end Polynomial
