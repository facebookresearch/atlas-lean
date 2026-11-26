/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.GDifferenceBases
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Additive.FiniteFieldDifferenceBases
import MathlibExt.Combinatorics.Additive.ZModDifferenceBasis

/-!
# Square-root bound for difference bases of finite fields

Every element of a finite field is a difference of two elements of a subset of size at most
a hundred times the square root of the field size.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem one_le_subRepCount_univ (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (x : G) : 1 ≤ subRepCount Finset.univ x := by
  apply Finset.card_pos.mpr
  refine ⟨(x, 0), Finset.mem_filter.mpr ⟨?_, sub_zero x⟩⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_univ x, Finset.mem_univ 0⟩

private theorem exists_min_groupDiffBasis_one (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] :
    ∃ B : Finset G, B.card = groupDiffBasisNumber 1 G ∧ ∀ x, 1 ≤ subRepCount B x := by
  apply Nat.sInf_mem (s := {k | ∃ B : Finset G, B.card = k ∧ ∀ x, 1 ≤ subRepCount B x})
  exact ⟨Finset.univ.card, Finset.univ, rfl, fun x => one_le_subRepCount_univ G x⟩

private theorem groupDiffBasisNumber_one_le_card (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] : groupDiffBasisNumber 1 G ≤ Nat.card G := by
  apply Nat.sInf_le
  refine ⟨Finset.univ, ?_, fun x => one_le_subRepCount_univ G x⟩
  rw [Finset.card_univ, Nat.card_eq_fintype_card]

private theorem groupDiffBasisNumber_one_prod_le (G H : Type*) [AddCommGroup G]
    [AddCommGroup H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H] :
    groupDiffBasisNumber 1 (G × H) ≤
      groupDiffBasisNumber 1 G * groupDiffBasisNumber 1 H := by
  obtain ⟨B₁, hB₁card, hB₁⟩ := exists_min_groupDiffBasis_one G
  obtain ⟨B₂, hB₂card, hB₂⟩ := exists_min_groupDiffBasis_one H
  apply Nat.sInf_le
  refine ⟨B₁ ×ˢ B₂, ?_, fun x => ?_⟩
  · rw [Finset.card_product, hB₁card, hB₂card]
  · have h := subRepCount_prod_ge 1 1 B₁ B₂ hB₁ hB₂ x
    simpa using h

private theorem groupDiffBasisNumber_one_prod_le_add (G H : Type*) [AddCommGroup G]
    [AddCommGroup H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H] :
    groupDiffBasisNumber 1 (G × H) ≤ Nat.card G + Nat.card H := by
  let A : Finset (G × H) := (Finset.univ ×ˢ ({0} : Finset H)) ∪ (({0} : Finset G) ×ˢ Finset.univ)
  have hAcard : A.card ≤ Nat.card G + Nat.card H := by
    calc A.card
        ≤ (Finset.univ ×ˢ ({0} : Finset H)).card + ((({0} : Finset G) ×ˢ Finset.univ)).card :=
          Finset.card_union_le _ _
      _ = Nat.card G + Nat.card H := by
          rw [Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
            Finset.card_singleton, Finset.card_singleton, Nat.card_eq_fintype_card,
            Nat.card_eq_fintype_card, mul_one, one_mul]
  have hAbasis : ∀ x : G × H, 1 ≤ subRepCount A x := by
    rintro ⟨x, y⟩
    apply Finset.card_pos.mpr
    refine ⟨((x, 0), (0, -y)), Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_product.mpr
          ⟨Finset.mem_univ x, Finset.mem_singleton_self (0 : H)⟩),
         Finset.mem_union_right _ (Finset.mem_product.mpr
          ⟨Finset.mem_singleton_self (0 : G), Finset.mem_univ (-y)⟩)⟩
    · exact Prod.ext (sub_zero x) (by simp)
  calc groupDiffBasisNumber 1 (G × H) ≤ A.card := Nat.sInf_le ⟨A, rfl, hAbasis⟩
    _ ≤ Nat.card G + Nat.card H := hAcard

private theorem subRepCount_map_addEquiv (G H : Type*) [AddCommGroup G] [AddCommGroup H]
    [DecidableEq G] [DecidableEq H] (e : G ≃+ H) (A : Finset G) (x : G) :
    subRepCount (A.map e.toEmbedding) (e x) = subRepCount A x := by
  unfold subRepCount
  rw [← Finset.prodMap_map_product, Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro q _
  simp only [Function.comp_apply, Function.Embedding.coe_prodMap, Prod.map_fst,
    Prod.map_snd]
  show e q.1 - e q.2 = e x ↔ q.1 - q.2 = x
  rw [← map_sub]
  exact ⟨fun h => e.toEquiv.injective h, fun h => by rw [h]⟩

private theorem groupDiffBasisNumber_one_congr (G H : Type*) [AddCommGroup G]
    [AddCommGroup H] [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H] (e : G ≃+ H) :
    groupDiffBasisNumber 1 G = groupDiffBasisNumber 1 H := by
  apply le_antisymm
  · obtain ⟨B, hBcard, hB⟩ := exists_min_groupDiffBasis_one H
    rw [← hBcard]
    apply Nat.sInf_le
    refine ⟨B.map e.symm.toEmbedding, Finset.card_map _, fun x => ?_⟩
    have hx : x = e.symm (e x) := (e.symm_apply_apply x).symm
    rw [hx, subRepCount_map_addEquiv _ _ e.symm B (e x)]
    exact hB (e x)
  · obtain ⟨B, hBcard, hB⟩ := exists_min_groupDiffBasis_one G
    rw [← hBcard]
    apply Nat.sInf_le
    refine ⟨B.map e.toEmbedding, Finset.card_map _, fun y => ?_⟩
    have hy : y = e (e.symm y) := (e.apply_symm_apply y).symm
    rw [hy, subRepCount_map_addEquiv _ _ e B (e.symm y)]
    exact hB (e.symm y)

private theorem natCard_zmod (p : ℕ) [Fact p.Prime] : Nat.card (ZMod p) = p := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_eq_fintype_card, ZMod.card]

private theorem natCard_pi_fin_zmod (p m : ℕ) [Fact p.Prime] :
    Nat.card (Fin m → ZMod p) = p ^ m := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  simp [ZMod.card, Finset.prod_const, Fintype.card_fin]

private theorem finrank_eq_of_card (F : Type*) [Field F] [Fintype F] (p n : ℕ) [Fact p.Prime]
    [Module (ZMod p) F] (hcard : Nat.card F = p ^ n) : Module.finrank (ZMod p) F = n := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have h := Module.card_eq_pow_finrank (K := ZMod p) (V := F)
  rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard] at h
  exact (Nat.pow_right_injective hp.two_le h).symm

private noncomputable def addEquiv_zmod_of_card_one (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (p : ℕ) [Fact p.Prime] [CharP F p] [Module (ZMod p) F]
    (hcard : Nat.card F = p ^ 1) : F ≃+ ZMod p :=
  (LinearEquiv.ofFinrankEq F (ZMod p) (by
    rw [finrank_eq_of_card F p 1 hcard, Module.finrank_self])).toAddEquiv

private noncomputable def addEquiv_prod_galois_of_card (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (p k : ℕ) [Fact p.Prime] [CharP F p] [Module (ZMod p) F]
    [DecidableEq (GaloisField p k)] [Fintype (GaloisField p k)]
    [Module (ZMod p) (GaloisField p k)]
    (hcard : Nat.card F = p ^ (k + k)) (hk : k ≠ 0) :
    F ≃+ (GaloisField p k × GaloisField p k) :=
  (LinearEquiv.ofFinrankEq F _ (by
    have hG : Module.finrank (ZMod p) (GaloisField p k) = k :=
      finrank_eq_of_card _ p k (GaloisField.card p k hk)
    rw [finrank_eq_of_card F p (k + k) hcard, Module.finrank_prod, hG])).toAddEquiv

private noncomputable def addEquiv_zmod_prod_galois_of_card (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (p k : ℕ) [Fact p.Prime] [CharP F p] [Module (ZMod p) F]
    [DecidableEq (GaloisField p (2 * k))] [Fintype (GaloisField p (2 * k))]
    [Module (ZMod p) (GaloisField p (2 * k))]
    (hcard : Nat.card F = p ^ (2 * k + 1)) (hk : k ≠ 0) :
    F ≃+ (ZMod p × GaloisField p (2 * k)) :=
  (LinearEquiv.ofFinrankEq F _ (by
    have hG : Module.finrank (ZMod p) (GaloisField p (2 * k)) = 2 * k :=
      finrank_eq_of_card _ p (2 * k) (GaloisField.card p (2 * k) (by omega))
    rw [finrank_eq_of_card F p (2 * k + 1) hcard, Module.finrank_prod, Module.finrank_self, hG]
    omega)).toAddEquiv

private noncomputable def addEquiv_prod_pi_of_card (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (p k : ℕ) [Fact p.Prime] [CharP F p] [Module (ZMod p) F]
    (hcard : Nat.card F = p ^ (k + k)) :
    F ≃+ ((Fin k → ZMod p) × (Fin k → ZMod p)) :=
  (LinearEquiv.ofFinrankEq F _ (by
    have hV : Module.finrank (ZMod p) (Fin k → ZMod p) = k := by
      rw [Module.finrank_pi, Fintype.card_fin]
    rw [finrank_eq_of_card F p (k + k) hcard, Module.finrank_prod, hV])).toAddEquiv

private noncomputable def addEquiv_pi_prod_zmod_of_card (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (p k : ℕ) [Fact p.Prime] [CharP F p] [Module (ZMod p) F]
    (hcard : Nat.card F = p ^ (2 * k + 1)) :
    F ≃+ ((Fin (2 * k) → ZMod p) × ZMod p) :=
  (LinearEquiv.ofFinrankEq F _ (by
    have hV : Module.finrank (ZMod p) (Fin (2 * k) → ZMod p) = 2 * k := by
      rw [Module.finrank_pi, Fintype.card_fin]
    rw [finrank_eq_of_card F p (2 * k + 1) hcard, Module.finrank_prod, hV,
      Module.finrank_self])).toAddEquiv

private noncomputable def addEquiv_pi_prod_pi (p k : ℕ) [Fact p.Prime] :
    (Fin (2 * k) → ZMod p) ≃+ ((Fin k → ZMod p) × (Fin k → ZMod p)) :=
  (LinearEquiv.ofFinrankEq _ _ (by
    have h2 : Module.finrank (ZMod p) (Fin (2 * k) → ZMod p) = 2 * k := by
      rw [Module.finrank_pi, Fintype.card_fin]
    have h1 : Module.finrank (ZMod p) (Fin k → ZMod p) = k := by
      rw [Module.finrank_pi, Fintype.card_fin]
    rw [h2, Module.finrank_prod, h1]
    omega)).toAddEquiv

private theorem hundred_sqrt_of_small_card (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (h : Nat.card G ≤ 10000) :
    (groupDiffBasisNumber 1 G : ℝ) ≤ 100 * Real.sqrt (Nat.card G) := by
  have hcard : (groupDiffBasisNumber 1 G : ℝ) ≤ Nat.card G :=
    by exact_mod_cast groupDiffBasisNumber_one_le_card G
  have hsqrt : Real.sqrt (Nat.card G) ≤ 100 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · calc (Nat.card G : ℝ) ≤ 10000 := by exact_mod_cast h
        _ = 100 ^ 2 := by norm_num
  calc (groupDiffBasisNumber 1 G : ℝ) ≤ Nat.card G := hcard
    _ = Real.sqrt (Nat.card G) * Real.sqrt (Nat.card G) :=
        (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
    _ ≤ 100 * Real.sqrt (Nat.card G) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)

private theorem two_ceil_sqrt_le (p : ℕ) (hp : 1 ≤ p) :
    2 * (⌈Real.sqrt p⌉₊ : ℝ) ≤ 4 * Real.sqrt p := by
  have hceil : (⌈Real.sqrt p⌉₊ : ℝ) ≤ Real.sqrt p + 1 :=
    (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
  have h1 : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.le_sqrt zero_le_one (Nat.cast_nonneg _)]
    have hsq1 : (1 : ℝ) ^ 2 = 1 := one_pow 2
    rw [hsq1]
    exact_mod_cast hp
  linarith

private theorem sqrt_natcast_pow_add (p k : ℕ) :
    Real.sqrt ((p ^ (k + k) : ℕ) : ℝ) = ((p ^ k : ℕ) : ℝ) := by
  have hexp : ((p ^ (k + k) : ℕ) : ℝ) = ((p ^ k : ℕ) : ℝ) ^ 2 := by
    rw [pow_add, Nat.cast_mul, pow_two]
  rw [hexp, Real.sqrt_sq (Nat.cast_nonneg _)]

private theorem sqrt_natcast_pow_succ (p k : ℕ) :
    Real.sqrt ((p ^ (2 * k + 1) : ℕ) : ℝ) = ((p ^ k : ℕ) : ℝ) * Real.sqrt p := by
  have hexp : ((p ^ (2 * k + 1) : ℕ) : ℝ) = ((p ^ k : ℕ) : ℝ) ^ 2 * (p : ℝ) := by
    rw [pow_add, pow_one, show (2 * k : ℕ) = k + k from by omega, pow_add]
    push_cast
    ring
  rw [hexp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

private theorem sqrt_le_half_of_four_le (p k : ℕ) (h : (4 : ℝ) ≤ ((p ^ k : ℕ) : ℝ)) :
    Real.sqrt ((p ^ k : ℕ) : ℝ) ≤ ((p ^ k : ℕ) : ℝ) / 2 := by
  have ht0 : 0 ≤ Real.sqrt ((p ^ k : ℕ) : ℝ) := Real.sqrt_nonneg _
  have htsq : Real.sqrt ((p ^ k : ℕ) : ℝ) ^ 2 = ((p ^ k : ℕ) : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  nlinarith [sq_nonneg (Real.sqrt ((p ^ k : ℕ) : ℝ) - 2), h, htsq, ht0]

private theorem four_hundred_sqrt_le (p k : ℕ) (h : (625 / 36 : ℝ) ≤ ((p ^ k : ℕ) : ℝ)) :
    400 * Real.sqrt ((p ^ k : ℕ) : ℝ) ≤ 96 * ((p ^ k : ℕ) : ℝ) := by
  have ht0 : 0 ≤ Real.sqrt ((p ^ k : ℕ) : ℝ) := Real.sqrt_nonneg _
  have htsq : Real.sqrt ((p ^ k : ℕ) : ℝ) ^ 2 = ((p ^ k : ℕ) : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have h25 : (25 / 6 : ℝ) ≤ Real.sqrt ((p ^ k : ℕ) : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]
    have h625 : (25 / 6 : ℝ) ^ 2 = 625 / 36 := by norm_num
    rw [h625]
    exact h
  nlinarith [mul_nonneg ht0 (show (0 : ℝ) ≤ Real.sqrt ((p ^ k : ℕ) : ℝ) - 25 / 6 by linarith),
    htsq, ht0]

private theorem hundred_sqrt_le_of_three_le (p : ℕ) (hp : 3 ≤ p) :
    (100 : ℝ) * Real.sqrt p ≤ 99 * p := by
  have hs0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hge : (100 / 99 : ℝ) ≤ Real.sqrt p := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]
    have h100 : (100 / 99 : ℝ) ^ 2 = 10000 / 9801 := by norm_num
    rw [h100]
    calc (10000 / 9801 : ℝ) ≤ 3 := by norm_num
      _ ≤ (p : ℝ) := by exact_mod_cast hp
  nlinarith [mul_nonneg hs0 (show (0 : ℝ) ≤ Real.sqrt (p : ℝ) - 100 / 99 by linarith), hsq,
    hs0]

private theorem eighteen_le_pow_of_large (p k : ℕ) (hp : 3 ≤ p) (hk : 1 ≤ k)
    (hlarge : 10001 ≤ p ^ (2 * k + 1)) : 18 ≤ p ^ k := by
  by_contra hcon
  have hpk : p ^ k ≤ 17 := by omega
  have hple : p ≤ 17 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
      _ ≤ 17 := hpk
  have hsq : (p ^ k) ^ 2 ≤ 17 ^ 2 := Nat.pow_le_pow_left hpk 2
  have hexp : p ^ (2 * k + 1) = p * (p ^ k) ^ 2 := by
    rw [pow_add, show (2 : ℕ) * k = k * 2 from mul_comm _ _, pow_mul]
    ring
  have hmul : p * (p ^ k) ^ 2 ≤ 17 * 17 ^ 2 := Nat.mul_le_mul hple hsq
  rw [hexp] at hlarge
  norm_num at hmul
  omega

private theorem one_div_25_le_sqrt_two : (1 / 25 : ℝ) ≤ Real.sqrt 2 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

private noncomputable instance decEqGaloisField (p : ℕ) [Fact p.Prime] (n : ℕ) :
    DecidableEq (GaloisField p n) :=
  Classical.decEq _

private theorem auxGF (p : ℕ) [Fact p.Prime] (n : ℕ) :
    n ≠ 0 →
      (groupDiffBasisNumber 1 (GaloisField p n) : ℝ) ≤
        100 * Real.sqrt (Nat.card (GaloisField p n)) := by
  refine Nat.strong_induction_on n ?_
  intro n IH hn
  have hp : p.Prime := Fact.out
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn
  let := Fintype.ofFinite (GaloisField p n)
  by_cases hsmall : Nat.card (GaloisField p n) ≤ 10000
  · exact hundred_sqrt_of_small_card _ hsmall
  · by_cases hp2 : p = 2
    · subst hp2
      have : NeZero (2 : ℕ) := ⟨two_ne_zero⟩
      rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have hVcard : Nat.card (Fin k → ZMod 2) = 2 ^ k := natCard_pi_fin_zmod 2 k
        have e := addEquiv_prod_pi_of_card (GaloisField 2 (k + k)) 2 k hcard
        rw [groupDiffBasisNumber_one_congr _ _ e]
        have hle :
            groupDiffBasisNumber 1 ((Fin k → ZMod 2) × (Fin k → ZMod 2)) ≤ 2 * 2 ^ k :=
          calc _ ≤ Nat.card (Fin k → ZMod 2) + Nat.card (Fin k → ZMod 2) :=
                groupDiffBasisNumber_one_prod_le_add _ _
            _ = 2 * 2 ^ k := by rw [hVcard]; ring
        have hsqrt : Real.sqrt (Nat.card (GaloisField 2 (k + k))) = ((2 ^ k : ℕ) : ℝ) := by
          rw [hcard]
          exact sqrt_natcast_pow_add 2 k
        have hnn : (0 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
        calc ((groupDiffBasisNumber 1 ((Fin k → ZMod 2) × (Fin k → ZMod 2)) : ℕ) : ℝ)
            ≤ ((2 * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hle
          _ = 2 * ((2 ^ k : ℕ) : ℝ) := by norm_cast
          _ ≤ 100 * ((2 ^ k : ℕ) : ℝ) := by
              have h2 : (2 : ℝ) ≤ 100 := by norm_num
              exact mul_le_mul_of_nonneg_right h2 hnn
          _ = 100 * Real.sqrt (Nat.card (GaloisField 2 (k + k))) := by rw [hsqrt]
      · have e := addEquiv_pi_prod_zmod_of_card (GaloisField 2 (2 * k + 1)) 2 k hcard
        rw [groupDiffBasisNumber_one_congr _ _ e]
        have hWcard : Nat.card (Fin k → ZMod 2) = 2 ^ k := natCard_pi_fin_zmod 2 k
        have hV : groupDiffBasisNumber 1 (Fin (2 * k) → ZMod 2) ≤ 2 * 2 ^ k := by
          have eV := addEquiv_pi_prod_pi 2 k
          rw [groupDiffBasisNumber_one_congr _ _ eV]
          calc groupDiffBasisNumber 1 ((Fin k → ZMod 2) × (Fin k → ZMod 2))
              ≤ Nat.card (Fin k → ZMod 2) + Nat.card (Fin k → ZMod 2) :=
                groupDiffBasisNumber_one_prod_le_add _ _
            _ = 2 * 2 ^ k := by rw [hWcard]; ring
        have hZ : groupDiffBasisNumber 1 (ZMod 2) ≤ 2 :=
          calc _ ≤ Nat.card (ZMod 2) := groupDiffBasisNumber_one_le_card _
            _ = 2 := natCard_zmod 2
        have hprod := groupDiffBasisNumber_one_prod_le (Fin (2 * k) → ZMod 2) (ZMod 2)
        have hle : groupDiffBasisNumber 1 ((Fin (2 * k) → ZMod 2) × ZMod 2) ≤ 4 * 2 ^ k :=
          calc _ ≤ _ * _ := hprod
            _ ≤ (2 * 2 ^ k) * 2 := Nat.mul_le_mul hV hZ
            _ = 4 * 2 ^ k := by ring
        have hsqrt : Real.sqrt (Nat.card (GaloisField 2 (2 * k + 1))) =
            ((2 ^ k : ℕ) : ℝ) * Real.sqrt 2 := by
          rw [hcard]
          exact sqrt_natcast_pow_succ 2 k
        have hnn : (0 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
        have h4 : (4 : ℝ) ≤ 100 * Real.sqrt 2 := by linarith [one_div_25_le_sqrt_two]
        calc ((groupDiffBasisNumber 1 ((Fin (2 * k) → ZMod 2) × ZMod 2) : ℕ) : ℝ)
            ≤ ((4 * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hle
          _ = 4 * ((2 ^ k : ℕ) : ℝ) := by norm_cast
          _ ≤ (100 * Real.sqrt 2) * ((2 ^ k : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_right h4 hnn
          _ = 100 * (((2 ^ k : ℕ) : ℝ) * Real.sqrt 2) := by ring
          _ = 100 * Real.sqrt (Nat.card (GaloisField 2 (2 * k + 1))) := by rw [hsqrt]
    · have hp3 : 3 ≤ p := by
        have h2 := hp.two_le
        omega
      have : NeZero p := ⟨hp.ne_zero⟩
      rcases Nat.even_or_odd n with hev | hod
      · obtain ⟨k, rfl⟩ := hev
        by_cases hk0 : k = 0
        · subst hk0
          omega
        by_cases hk1 : k = 1
        · subst hk1
          let := Fintype.ofFinite (GaloisField p 1)
          have hGcard : Nat.card (GaloisField p 1) = p ^ 1 :=
            GaloisField.card p 1 one_ne_zero
          have e := addEquiv_prod_galois_of_card (GaloisField p (1 + 1)) p 1 hcard one_ne_zero
          rw [groupDiffBasisNumber_one_congr _ _ e]
          have hchar : ringChar (GaloisField p 1) ≠ 2 := by
            rw [ringChar.eq (GaloisField p 1) p]
            exact hp2
          have hL6 := groupDiffBasisNumber_prod_self_le (K := GaloisField p 1) hchar
          have ihG := IH 1 (by omega : 1 < 1 + 1) one_ne_zero
          have hsqrtG : Real.sqrt (Nat.card (GaloisField p 1)) = Real.sqrt p := by
            rw [hGcard, pow_one]
          rw [hsqrtG] at ihG
          have hcardG1 : ((Nat.card (GaloisField p 1) : ℕ) : ℝ) = (p : ℝ) := by
            rw [hGcard, pow_one]
          have hsqrt100 : (100 : ℝ) * Real.sqrt p ≤ 99 * p :=
            hundred_sqrt_le_of_three_le p hp3
          have hsqrtF : Real.sqrt (Nat.card (GaloisField p (1 + 1))) = (p : ℝ) := by
            rw [hcard, sqrt_natcast_pow_add p 1, pow_one]
          calc ((groupDiffBasisNumber 1 (GaloisField p 1 × GaloisField p 1) : ℕ) : ℝ)
              ≤ ((Nat.card (GaloisField p 1) +
                  groupDiffBasisNumber 1 (GaloisField p 1) : ℕ) : ℝ) := by
                exact_mod_cast hL6
            _ = (p : ℝ) + (groupDiffBasisNumber 1 (GaloisField p 1) : ℝ) := by
                rw [Nat.cast_add, hcardG1]
            _ ≤ (p : ℝ) + 100 * Real.sqrt p := by linarith [ihG]
            _ ≤ 100 * (p : ℝ) := by linarith [hsqrt100]
            _ = 100 * Real.sqrt (Nat.card (GaloisField p (1 + 1))) := by rw [hsqrtF]
        · have hk2 : 2 ≤ k := by omega
          let := Fintype.ofFinite (GaloisField p k)
          have hGcard : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
          have e := addEquiv_prod_galois_of_card (GaloisField p (k + k)) p k hcard hk0
          rw [groupDiffBasisNumber_one_congr _ _ e]
          have hchar : ringChar (GaloisField p k) ≠ 2 := by
            rw [ringChar.eq (GaloisField p k) p]
            exact hp2
          have hL6 := groupDiffBasisNumber_prod_self_le (K := GaloisField p k) hchar
          have ihG := IH k (by omega : k < k + k) hk0
          rw [hGcard] at ihG
          have hpk9 : (9 : ℕ) ≤ p ^ k :=
            calc (9 : ℕ) = 3 ^ 2 := by norm_num
              _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
              _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk2
          have h4 : (4 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by
            have h49 : (4 : ℕ) ≤ p ^ k := by omega
            exact_mod_cast h49
          have hsqrt_half := sqrt_le_half_of_four_le p k h4
          have hsqrtF : Real.sqrt (Nat.card (GaloisField p (k + k))) = ((p ^ k : ℕ) : ℝ) := by
            rw [hcard]
            exact sqrt_natcast_pow_add p k
          have hcardG : ((Nat.card (GaloisField p k) : ℕ) : ℝ) = ((p ^ k : ℕ) : ℝ) := by
            rw [hGcard]
          have hnn : (0 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
          calc ((groupDiffBasisNumber 1 (GaloisField p k × GaloisField p k) : ℕ) : ℝ)
              ≤ ((Nat.card (GaloisField p k) +
                  groupDiffBasisNumber 1 (GaloisField p k) : ℕ) : ℝ) := by
                exact_mod_cast hL6
            _ = ((p ^ k : ℕ) : ℝ) + (groupDiffBasisNumber 1 (GaloisField p k) : ℝ) := by
                rw [Nat.cast_add, hcardG]
            _ ≤ ((p ^ k : ℕ) : ℝ) + 100 * Real.sqrt ((p ^ k : ℕ) : ℝ) := by linarith [ihG]
            _ ≤ 100 * ((p ^ k : ℕ) : ℝ) := by linarith [hsqrt_half, hnn]
            _ = 100 * Real.sqrt (Nat.card (GaloisField p (k + k))) := by rw [hsqrtF]
      · obtain ⟨k, rfl⟩ := hod
        by_cases hk0 : k = 0
        · subst hk0
          have h21 : (2 : ℕ) * 0 + 1 = 1 := by omega
          rw [h21] at hcard
          rw [h21]
          have e := addEquiv_zmod_of_card_one (GaloisField p 1) p hcard
          rw [groupDiffBasisNumber_one_congr _ _ e]
          have hz := groupDiffBasisNumber_zmod_le p
          have hsqrtF : Real.sqrt (Nat.card (GaloisField p 1)) = Real.sqrt p := by
            rw [hcard, pow_one]
          have hceil := two_ceil_sqrt_le p (by omega : 1 ≤ p)
          have hnn : (0 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
          calc ((groupDiffBasisNumber 1 (ZMod p) : ℕ) : ℝ)
              ≤ ((2 * ⌈Real.sqrt p⌉₊ : ℕ) : ℝ) := by exact_mod_cast hz
            _ = 2 * (⌈Real.sqrt p⌉₊ : ℝ) := by norm_cast
            _ ≤ 4 * Real.sqrt p := hceil
            _ ≤ 100 * Real.sqrt p := by linarith [hnn]
            _ = 100 * Real.sqrt (Nat.card (GaloisField p 1)) := by rw [hsqrtF]
        · have hk1 : 1 ≤ k := by omega
          have h2k0 : 2 * k ≠ 0 := by omega
          let := Fintype.ofFinite (GaloisField p (2 * k))
          let := Fintype.ofFinite (GaloisField p k)
          have hG2card : Nat.card (GaloisField p (2 * k)) = p ^ (2 * k) :=
            GaloisField.card p (2 * k) h2k0
          have hG1card : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
          have e :=
            addEquiv_zmod_prod_galois_of_card (GaloisField p (2 * k + 1)) p k hcard hk0
          rw [groupDiffBasisNumber_one_congr _ _ e]
          have hprod := groupDiffBasisNumber_one_prod_le (ZMod p) (GaloisField p (2 * k))
          have hz := groupDiffBasisNumber_zmod_le p
          have h2k : (2 : ℕ) * k = k + k := by omega
          have hcard2 : Nat.card (GaloisField p (2 * k)) = p ^ (k + k) := by
            rw [← h2k]
            exact hG2card
          have e2 := addEquiv_prod_galois_of_card (GaloisField p (2 * k)) p k hcard2 hk0
          have hcongr2 := groupDiffBasisNumber_one_congr _ _ e2
          have hchar : ringChar (GaloisField p k) ≠ 2 := by
            rw [ringChar.eq (GaloisField p k) p]
            exact hp2
          have hL6 := groupDiffBasisNumber_prod_self_le (K := GaloisField p k) hchar
          have ihG1 := IH k (by omega : k < 2 * k + 1) hk0
          rw [hG1card] at ihG1
          have hG2le : groupDiffBasisNumber 1 (GaloisField p (2 * k)) ≤
              p ^ k + groupDiffBasisNumber 1 (GaloisField p k) := by
            rw [hcongr2]
            calc groupDiffBasisNumber 1 (GaloisField p k × GaloisField p k)
                ≤ Nat.card (GaloisField p k) + groupDiffBasisNumber 1 (GaloisField p k) := hL6
              _ = p ^ k + groupDiffBasisNumber 1 (GaloisField p k) := by rw [hG1card]
          have hle : groupDiffBasisNumber 1 (ZMod p × GaloisField p (2 * k)) ≤
              (2 * ⌈Real.sqrt p⌉₊) * (p ^ k + groupDiffBasisNumber 1 (GaloisField p k)) :=
            calc _ ≤ _ * _ := hprod
              _ ≤ _ := Nat.mul_le_mul hz hG2le
          have hlarge : 10001 ≤ p ^ (2 * k + 1) := by omega
          have h18 := eighteen_le_pow_of_large p k hp3 hk1 hlarge
          have h625 : (625 / 36 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) :=
            calc (625 / 36 : ℝ) ≤ 18 := by norm_num
              _ ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast h18
          have hkey := four_hundred_sqrt_le p k h625
          have hsqrtF : Real.sqrt (Nat.card (GaloisField p (2 * k + 1))) =
              ((p ^ k : ℕ) : ℝ) * Real.sqrt p := by
            rw [hcard]
            exact sqrt_natcast_pow_succ p k
          have hceil := two_ceil_sqrt_le p (by omega : 1 ≤ p)
          have hr0 : (0 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
          have ht0 : (0 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
          have h4t : 4 * (((p ^ k : ℕ) : ℝ) + 100 * Real.sqrt ((p ^ k : ℕ) : ℝ)) ≤
              100 * ((p ^ k : ℕ) : ℝ) := by linarith [hkey, ht0]
          calc ((groupDiffBasisNumber 1 (ZMod p × GaloisField p (2 * k)) : ℕ) : ℝ)
              ≤ ((((2 * ⌈Real.sqrt p⌉₊) *
                  (p ^ k + groupDiffBasisNumber 1 (GaloisField p k)) : ℕ)) : ℝ) := by
                exact_mod_cast hle
            _ = (2 * (⌈Real.sqrt p⌉₊ : ℝ)) *
                (((p ^ k : ℕ) : ℝ) + (groupDiffBasisNumber 1 (GaloisField p k) : ℝ)) := by
                norm_cast
            _ ≤ (4 * Real.sqrt p) * (((p ^ k : ℕ) : ℝ) + 100 * Real.sqrt ((p ^ k : ℕ) : ℝ)) := by
                apply mul_le_mul hceil (by linarith [ihG1]) (by positivity) (by positivity)
            _ = Real.sqrt p * (4 * (((p ^ k : ℕ) : ℝ) + 100 * Real.sqrt ((p ^ k : ℕ) : ℝ))) := by
                ring
            _ ≤ Real.sqrt p * (100 * ((p ^ k : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_left h4t hr0
            _ = 100 * (((p ^ k : ℕ) : ℝ) * Real.sqrt p) := by ring
            _ = 100 * Real.sqrt (Nat.card (GaloisField p (2 * k + 1))) := by rw [hsqrtF]

/-- **Square-root bound for difference bases of finite fields.** For every finite field $K$ with
$q$ elements, the least size $\eta_1(K)$ of a set $A \subseteq K$ such that every element of $K$
is a difference $a - a'$ of two elements of $A$ satisfies $\eta_1(K) \le 100 \sqrt{q}$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 7 (`integers-2025-A77-lem-7`). -/
public theorem groupDiffBasisNumber_le_hundred_sqrt {K : Type*} [Field K] [Finite K]
    [DecidableEq K] :
    (groupDiffBasisNumber 1 K : ℝ) ≤ 100 * Real.sqrt (Nat.card K)
    := by
  let := Fintype.ofFinite K
  have : CharP K (ringChar K) := ⟨ringChar.spec K⟩
  obtain ⟨N, hprime, hcard⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hprime⟩
  have hN0 : (N : ℕ) ≠ 0 := N.ne_zero
  rw [← Nat.card_eq_fintype_card] at hcard
  let : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
  let := Fintype.ofFinite (GaloisField (ringChar K) ↑N)
  have e := GaloisField.algEquivGaloisField _ _ hcard
  have eAdd : K ≃+ GaloisField (ringChar K) ↑N := e.toRingEquiv.toAddEquiv
  have hcongr := groupDiffBasisNumber_one_congr K _ eAdd
  have hcardEq : Nat.card K = Nat.card (GaloisField (ringChar K) ↑N) :=
    Nat.card_congr e.toRingEquiv.toEquiv
  have hmain := auxGF (ringChar K) ↑N hN0
  rw [hcongr, hcardEq]
  exact hmain

end

end MetaMathlibExt
