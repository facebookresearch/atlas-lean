/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Enumerative.FubiniNumber

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.StirlingMatrices

/-! # r-horse numbers via Stirling-weighted Fubini values

This file proves the formula for `r`-horse numbers as a signed first-kind Stirling transform of
Fubini numbers.
-/

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

private def rHorse_finSplit {n r : ℕ} (hrn : r ≤ n) :
    Fin r ⊕ Fin (n - r) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hrn))

private theorem rHorse_finSplit_inl {n r : ℕ} (hrn : r ≤ n) (i : Fin r) :
    rHorse_finSplit hrn (Sum.inl i) = Fin.castLE hrn i := by
  apply Fin.ext
  rfl

private def rHorse_functionSplit {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
    (Fin n → Fin k) ≃ (Fin r → Fin k) × (Fin (n - r) → Fin k) :=
  (Equiv.arrowCongr (rHorse_finSplit hrn) (Equiv.refl (Fin k))).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin r) (Fin (n - r)) (Fin k))

private theorem rHorse_functionSplit_fst {n r : ℕ} (hrn : r ≤ n) (k : ℕ)
    (f : Fin n → Fin k) (i : Fin r) :
    (rHorse_functionSplit hrn k f).1 i = f (Fin.castLE hrn i) := by
  simp [rHorse_functionSplit, rHorse_finSplit_inl]

private def rHorse_strictMonoEquivFinset (r k : ℕ) :
    { f : Fin r → Fin k // StrictMono f } ≃
      { s : Finset (Fin k) // s.card = r } where
  toFun f := ⟨Finset.image f.1 Finset.univ, by
    rw [Finset.card_image_of_injective _ f.property.injective, Finset.card_univ,
      Fintype.card_fin]⟩
  invFun s := ⟨s.1.orderEmbOfFin s.2, (s.1.orderEmbOfFin s.2).strictMono⟩
  left_inv f := by
    apply Subtype.ext
    symm
    apply Finset.orderEmbOfFin_unique
    · intro i
      simp
    · exact f.property
  right_inv s := by
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ s.1 s.2

private theorem rHorse_card_strictMono (r k : ℕ) :
    Nat.card { f : Fin r → Fin k // StrictMono f } = k.choose r := by
  rw [Nat.card_eq_fintype_card,
    Fintype.card_congr (rHorse_strictMonoEquivFinset r k),
    Fintype.card_finset_len, Fintype.card_fin]

private abbrev rHorseIncreasing {n r k : ℕ} (hrn : r ≤ n) (f : Fin n → Fin k) : Prop :=
  ∀ i j : Fin r, i < j → f (Fin.castLE hrn i) < f (Fin.castLE hrn j)

private abbrev rHorseSurjectiveIncreasing {n r k : ℕ} (hrn : r ≤ n)
    (f : Fin n → Fin k) : Prop :=
  Function.Surjective f ∧ rHorseIncreasing hrn f

private def rHorse_conditionEquiv {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
    { f : Fin n → Fin k // rHorseIncreasing hrn f } ≃
      { p : (Fin r → Fin k) × (Fin (n - r) → Fin k) // StrictMono p.1 } :=
  Equiv.subtypeEquiv (rHorse_functionSplit hrn k) fun f => by
    constructor
    · intro h i j hij
      simpa only [rHorse_functionSplit_fst] using h i j hij
    · intro h i j hij
      simpa only [rHorse_functionSplit_fst] using h hij

private def rHorse_conditionProdEquiv (n r k : ℕ) :
    { p : (Fin r → Fin k) × (Fin (n - r) → Fin k) // StrictMono p.1 } ≃
      { f : Fin r → Fin k // StrictMono f } × (Fin (n - r) → Fin k) where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv _p := rfl
  right_inv _p := rfl

private theorem rHorse_card_functions {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
    Nat.card { f : Fin n → Fin k // rHorseIncreasing hrn f } =
      k.choose r * k ^ (n - r) := by
  rw [Nat.card_congr ((rHorse_conditionEquiv hrn k).trans
    (rHorse_conditionProdEquiv n r k)), Nat.card_prod, rHorse_card_strictMono,
    Nat.card_fun, Nat.card_fin, Nat.card_fin]

private def rHorse_imageFiberEquiv {n r k : ℕ} (hrn : r ≤ n) (s : Finset (Fin k)) :
    { g : { g : Fin n → Fin k // rHorseIncreasing hrn g } //
        Finset.image g.1 Finset.univ = s } ≃
      { f : Fin n → Fin s.card // rHorseSurjectiveIncreasing hrn f } where
  toFun g := ⟨fun x => (s.orderIsoOfFin rfl).symm ⟨g.1.1 x, by
      have hx : g.1.1 x ∈ Finset.image g.1.1 Finset.univ :=
        Finset.mem_image_of_mem g.1.1 (Finset.mem_univ x)
      simpa only [← g.2] using hx⟩, by
    constructor
    · intro y
      have hy : ((s.orderIsoOfFin rfl y : s) : Fin k) ∈
          Finset.image g.1.1 Finset.univ := by
        rw [g.2]
        exact (s.orderIsoOfFin rfl y).property
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hy
      refine ⟨x, ?_⟩
      apply (s.orderIsoOfFin rfl).injective
      rw [OrderIso.apply_symm_apply]
      exact Subtype.ext hx
    · intro i j hij
      apply (s.orderIsoOfFin rfl).symm.lt_iff_lt.mpr
      exact g.1.2 i j hij⟩
  invFun f := ⟨⟨fun x => s.orderEmbOfFin rfl (f.1 x), by
      intro i j hij
      exact (s.orderEmbOfFin rfl).strictMono (f.2.2 i j hij)⟩, by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      exact Finset.orderEmbOfFin_mem s rfl (f.1 x)
    · intro hz
      obtain ⟨x, hx⟩ := f.2.1 ((s.orderIsoOfFin rfl).symm ⟨z, hz⟩)
      refine ⟨x, ?_⟩
      rw [hx, ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    simp only
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  right_inv f := by
    apply Subtype.ext
    funext x
    apply (s.orderIsoOfFin rfl).injective
    rw [OrderIso.apply_symm_apply]
    exact Subtype.ext (Finset.coe_orderIsoOfFin_apply s rfl (f.1 x)).symm

private theorem rHorse_card_functions_eq_sum {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
    Nat.card { g : Fin n → Fin k // rHorseIncreasing hrn g } =
      ∑ i ∈ Finset.range (k + 1), k.choose i *
        Nat.card { f : Fin n → Fin i // rHorseSurjectiveIncreasing hrn f } := by
  let q := fun g : { g : Fin n → Fin k // rHorseIncreasing hrn g } =>
    Finset.image g.1 Finset.univ
  calc
    Nat.card { g : Fin n → Fin k // rHorseIncreasing hrn g } =
        Nat.card ((s : Finset (Fin k)) ×
          { g : { g : Fin n → Fin k // rHorseIncreasing hrn g } // q g = s }) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv q).symm
    _ = ∑ s : Finset (Fin k),
          Nat.card { g : { g : Fin n → Fin k // rHorseIncreasing hrn g } // q g = s } :=
      Nat.card_sigma
    _ = ∑ s : Finset (Fin k),
          Nat.card { f : Fin n → Fin s.card // rHorseSurjectiveIncreasing hrn f } := by
      apply Finset.sum_congr rfl
      intro s _
      exact Nat.card_congr (rHorse_imageFiberEquiv hrn s)
    _ = ∑ i ∈ Finset.range (k + 1),
          ∑ s ∈ (Finset.univ : Finset (Fin k)).powersetCard i,
            Nat.card { f : Fin n → Fin s.card // rHorseSurjectiveIncreasing hrn f } := by
      simpa only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] using
        Finset.sum_powerset (Finset.univ : Finset (Fin k))
          (fun s => Nat.card
            { f : Fin n → Fin s.card // rHorseSurjectiveIncreasing hrn f })
    _ = ∑ i ∈ Finset.range (k + 1), k.choose i *
          Nat.card { f : Fin n → Fin i // rHorseSurjectiveIncreasing hrn f } := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] using
        Finset.sum_powersetCard i (Finset.univ : Finset (Fin k))
          (fun j => Nat.card
            { f : Fin n → Fin j // rHorseSurjectiveIncreasing hrn f })

private theorem rHorse_pow_eq_sum_choose (k m : ℕ) :
    k ^ m = ∑ i ∈ Finset.range (m + 1),
      k.choose i * (Nat.factorial i * Nat.stirlingSecond m i) := by
  rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  ring

private theorem rHorse_sum_choose_stirlingSecond (k m : ℕ) :
    (∑ i ∈ Finset.range (k + 1),
      k.choose i * (Nat.factorial i * Nat.stirlingSecond m i)) = k ^ m := by
  rw [rHorse_pow_eq_sum_choose]
  rcases le_total m k with hmk | hkm
  · symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmk))
    intro i hik him
    rw [Finset.mem_range] at hik
    simp only [Finset.mem_range, not_lt] at him
    have hmi : m < i := by omega
    rw [Nat.stirlingSecond_eq_zero_of_lt hmi, mul_zero, mul_zero]
  · apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hkm))
    intro i him hik
    rw [Finset.mem_range] at him
    simp only [Finset.mem_range, not_lt] at hik
    have hki : k < i := by omega
    rw [Nat.choose_eq_zero_of_lt hki, zero_mul]

private theorem rHorse_sum_choose_stirlingSecond_rat (k m : ℕ) :
    (∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℚ) *
        ((Nat.factorial i : ℚ) * (Nat.stirlingSecond m i : ℚ))) =
      (k : ℚ) ^ m := by
  exact_mod_cast rHorse_sum_choose_stirlingSecond k m

private theorem rHorse_pow_eq_sum_stirlingSecond_descFactorial
    (k m N : ℕ) (hmN : m ≤ N) :
    k ^ m = ∑ i ∈ Finset.range (N + 1),
      Nat.stirlingSecond m i * k.descFactorial i := by
  rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmN))
  intro i hiN him
  simp only [Finset.mem_range, not_lt] at him
  have hmi : m < i := by omega
  rw [Nat.stirlingSecond_eq_zero_of_lt hmi, zero_mul]

private theorem rHorse_pow_eq_sum_stirlingSecond_descFactorial_rat
    (k m N : ℕ) (hmN : m ≤ N) :
    (k : ℚ) ^ m = ∑ i ∈ Finset.range (N + 1),
      (Nat.stirlingSecond m i : ℚ) * (k.descFactorial i : ℚ) := by
  exact_mod_cast rHorse_pow_eq_sum_stirlingSecond_descFactorial k m N hmN

private theorem rHorse_signedStirling_orthogonal_rat (r i : ℕ) :
    (∑ m ∈ Finset.range (r + 1),
      (signedStirlingFirst r m : ℚ) * (Nat.stirlingSecond m i : ℚ)) =
      if r = i then 1 else 0 := by
  exact_mod_cast sum_signedStirlingFirst_mul_stirlingSecond r i

private theorem rHorse_signedStirling_power (r k : ℕ) :
    (∑ m ∈ Finset.range (r + 1),
      (signedStirlingFirst r m : ℚ) * (k : ℚ) ^ m) =
      (k.descFactorial r : ℚ) := by
  calc
    (∑ m ∈ Finset.range (r + 1),
        (signedStirlingFirst r m : ℚ) * (k : ℚ) ^ m) =
        ∑ m ∈ Finset.range (r + 1), (signedStirlingFirst r m : ℚ) *
          ∑ i ∈ Finset.range (r + 1),
            (Nat.stirlingSecond m i : ℚ) * (k.descFactorial i : ℚ) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_range] at hm
      rw [rHorse_pow_eq_sum_stirlingSecond_descFactorial_rat k m r (by omega)]
    _ = ∑ i ∈ Finset.range (r + 1),
          (∑ m ∈ Finset.range (r + 1),
            (signedStirlingFirst r m : ℚ) * (Nat.stirlingSecond m i : ℚ)) *
              (k.descFactorial i : ℚ) := by
      simp_rw [Finset.mul_sum]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = ∑ i ∈ Finset.range (r + 1),
          (if r = i then 1 else 0) * (k.descFactorial i : ℚ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rHorse_signedStirling_orthogonal_rat]
    _ = (k.descFactorial r : ℚ) := by simp

private theorem rHorse_sum_range_reflect (r : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ Finset.range (r + 1), f (r - j)) =
      ∑ m ∈ Finset.range (r + 1), f m := by
  refine Finset.sum_bij (fun j _ => r - j) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  · intro j₁ hj₁ j₂ hj₂ h
    rw [Finset.mem_range] at hj₁ hj₂
    omega
  · intro m hm
    rw [Finset.mem_range] at hm
    refine ⟨r - m, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  · intro j _
    rfl

private theorem rHorse_signedStirlingFirst_cast (r m : ℕ) :
    (signedStirlingFirst r m : ℚ) =
      (-1 : ℚ) ^ (r - m) * (Nat.stirlingFirst r m : ℚ) := by
  rw [signedStirlingFirst_apply]
  push_cast
  rfl

private theorem rHorse_falling_stirling (r k : ℕ) :
    (∑ j ∈ Finset.range (r + 1),
      (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
        (k : ℚ) ^ (r - j)) = (k.descFactorial r : ℚ) := by
  calc
    (∑ j ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
          (k : ℚ) ^ (r - j)) =
        ∑ j ∈ Finset.range (r + 1),
          (-1 : ℚ) ^ (r - (r - j)) * (Nat.stirlingFirst r (r - j) : ℚ) *
            (k : ℚ) ^ (r - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have hsub : r - (r - j) = j := by omega
      rw [hsub]
    _ = ∑ m ∈ Finset.range (r + 1),
          (-1 : ℚ) ^ (r - m) * (Nat.stirlingFirst r m : ℚ) * (k : ℚ) ^ m :=
      rHorse_sum_range_reflect r
        (fun m => (-1 : ℚ) ^ (r - m) * (Nat.stirlingFirst r m : ℚ) * (k : ℚ) ^ m)
    _ = ∑ m ∈ Finset.range (r + 1),
          (signedStirlingFirst r m : ℚ) * (k : ℚ) ^ m := by
      apply Finset.sum_congr rfl
      intro m _
      rw [rHorse_signedStirlingFirst_cast]
    _ = (k.descFactorial r : ℚ) := rHorse_signedStirling_power r k

private theorem rHorse_shifted_falling_stirling {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
    (∑ j ∈ Finset.range (r + 1),
      (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
        (k : ℚ) ^ (n - j)) =
      (k : ℚ) ^ (n - r) * (k.descFactorial r : ℚ) := by
  calc
    (∑ j ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
          (k : ℚ) ^ (n - j)) =
        ∑ j ∈ Finset.range (r + 1),
          (k : ℚ) ^ (n - r) *
            ((-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
              (k : ℚ) ^ (r - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have hsub : n - j = (n - r) + (r - j) := by omega
      rw [hsub, pow_add]
      ring
    _ = (k : ℚ) ^ (n - r) *
          ∑ j ∈ Finset.range (r + 1),
            (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
              (k : ℚ) ^ (r - j) := by
      rw [Finset.mul_sum]
    _ = (k : ℚ) ^ (n - r) * (k.descFactorial r : ℚ) := by
      rw [rHorse_falling_stirling]

private def rHorseCandidate (n r i : ℕ) : ℚ :=
  (1 / (Nat.factorial r : ℚ)) *
    ∑ j ∈ Finset.range (r + 1),
      (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
        ((Nat.factorial i : ℚ) * (Nat.stirlingSecond (n - j) i : ℚ))

private theorem rHorse_candidate_transform {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (k.choose i : ℚ) * rHorseCandidate n r i) =
      (k.choose r : ℚ) * (k : ℚ) ^ (n - r) := by
  calc
    (∑ i ∈ Finset.range (k + 1), (k.choose i : ℚ) * rHorseCandidate n r i) =
        (1 / (Nat.factorial r : ℚ)) *
          ∑ i ∈ Finset.range (k + 1), (k.choose i : ℚ) *
            ∑ j ∈ Finset.range (r + 1),
              (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
                ((Nat.factorial i : ℚ) * (Nat.stirlingSecond (n - j) i : ℚ)) := by
      unfold rHorseCandidate
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (1 / (Nat.factorial r : ℚ)) *
          ∑ j ∈ Finset.range (r + 1),
            (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
              ∑ i ∈ Finset.range (k + 1),
                (k.choose i : ℚ) *
                  ((Nat.factorial i : ℚ) * (Nat.stirlingSecond (n - j) i : ℚ)) := by
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (1 / (Nat.factorial r : ℚ)) *
          ∑ j ∈ Finset.range (r + 1),
            (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
              (k : ℚ) ^ (n - j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [rHorse_sum_choose_stirlingSecond_rat]
    _ = (1 / (Nat.factorial r : ℚ)) *
          ((k : ℚ) ^ (n - r) * (k.descFactorial r : ℚ)) := by
      rw [rHorse_shifted_falling_stirling hrn k]
    _ = (k.choose r : ℚ) * (k : ℚ) ^ (n - r) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      have hfac : (Nat.factorial r : ℚ) ≠ 0 := by positivity
      rw [one_div_mul_eq_div]
      apply (div_eq_iff hfac).2
      ring

private theorem rHorse_actual_transform {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℚ) *
        (Nat.card
          { f : Fin n → Fin i // rHorseSurjectiveIncreasing hrn f } : ℚ)) =
      (k.choose r : ℚ) * (k : ℚ) ^ (n - r) := by
  have hnat :
      (∑ i ∈ Finset.range (k + 1), k.choose i *
        Nat.card { f : Fin n → Fin i // rHorseSurjectiveIncreasing hrn f }) =
        k.choose r * k ^ (n - r) :=
    (rHorse_card_functions_eq_sum hrn k).symm.trans (rHorse_card_functions hrn k)
  exact_mod_cast hnat

private theorem rHorse_binomial_injective (a b : ℕ → ℚ)
    (h : ∀ k, (∑ i ∈ Finset.range (k + 1), (k.choose i : ℚ) * a i) =
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℚ) * b i) :
    ∀ k, a k = b k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      have hk := h k
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at hk
      have hlow : (∑ i ∈ Finset.range k, (k.choose i : ℚ) * a i) =
          ∑ i ∈ Finset.range k, (k.choose i : ℚ) * b i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih i (Finset.mem_range.mp hi)]
      rw [hlow] at hk
      simpa using hk

private theorem rHorse_card_surjective_eq_candidate {n r : ℕ} (hrn : r ≤ n) (i : ℕ) :
    (Nat.card
      { f : Fin n → Fin i // rHorseSurjectiveIncreasing hrn f } : ℚ) =
      rHorseCandidate n r i := by
  apply rHorse_binomial_injective
    (fun k => (Nat.card
      { f : Fin n → Fin k // rHorseSurjectiveIncreasing hrn f } : ℚ))
    (rHorseCandidate n r)
  · intro k
    rw [rHorse_actual_transform hrn k, rHorse_candidate_transform hrn k]

private theorem rHorse_fubini_sum_extend {n j : ℕ} (hj : j ≤ n) :
    (∑ i ∈ Finset.range (n + 1),
      (Nat.factorial i : ℚ) * (Nat.stirlingSecond (n - j) i : ℚ)) =
      (fubiniNumber (n - j) : ℚ) := by
  have hnat :
      (∑ i ∈ Finset.range (n + 1),
        Nat.factorial i * Nat.stirlingSecond (n - j) i) =
        fubiniNumber (n - j) := by
    rw [fubiniNumber_eq_sum]
    calc
      (∑ i ∈ Finset.range (n + 1),
          Nat.factorial i * Nat.stirlingSecond (n - j) i) =
          ∑ i ∈ Finset.range (n + 1),
            Nat.stirlingSecond (n - j) i * Nat.factorial i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i ∈ Finset.range (n - j + 1),
            Nat.stirlingSecond (n - j) i * Nat.factorial i := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro i hin hij
        simp only [Finset.mem_range, not_lt] at hij
        have hlt : n - j < i := by omega
        rw [Nat.stirlingSecond_eq_zero_of_lt hlt, zero_mul]
  exact_mod_cast hnat

/-- **Schreyer's Fubini formula for r-horse numbers.** Let $r \le n$ be natural numbers. For each
$k$, count the surjections $f : \{0, \dots, n - 1\} \to \{0, \dots, k - 1\}$ whose values on the
first $r$ points are strictly increasing, $f(0) < f(1) < \dots < f(r - 1)$, and let $H$ (the
$r$-horse number) be the sum of these counts over $0 \le k \le n$. Then, as rational numbers,
$$
H = \frac{1}{r!} \sum_{j=0}^{r} (-1)^j \, c(r, r - j) \, F_{n-j},
$$
where $c(r, i)$ is the unsigned Stirling number of the first kind (the number of permutations of
$r$ elements with exactly $i$ cycles) and $F_m$ is the $m$-th Fubini number.

The proof follows Schreyer's: the signed falling-factorial expansion is evaluated at integers and
transported to surjection counts by image decomposition and binomial inversion, rather than by
shift operators.

Proves `Wanted` entry `rHorseNumber_eq_stirlingFirst_sum_fubini`.

Source: Benjamin Schreyer, "Rigged Horse Numbers and their Modular
Periodicity," Journal of Integer Sequences 28 (2025), Article 25.4.1,
Theorem (label thm:fubinir), lines 211–215,
https://cs.uwaterloo.ca/journals/JIS/VOL28/Schreyer/schreyer7.tex
-/
public theorem rHorseNumber_eq_stirlingFirst_sum_fubini
    (n r : ℕ) (hrn : r ≤ n) :
    ((∑ k ∈ Finset.range (n + 1),
        Nat.card
          { f : Fin n → Fin k //
            Function.Surjective f ∧
              ∀ i j : Fin r, i < j →
                f (Fin.castLE hrn i) < f (Fin.castLE hrn j) }) : ℚ) =
      (1 / (Nat.factorial r : ℚ)) *
        ∑ j ∈ Finset.range (r + 1),
          (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
            (fubiniNumber (n - j) : ℚ) := by
  calc
    ((∑ k ∈ Finset.range (n + 1),
        Nat.card
          { f : Fin n → Fin k //
            Function.Surjective f ∧
              ∀ i j : Fin r, i < j →
                f (Fin.castLE hrn i) < f (Fin.castLE hrn j) }) : ℚ) =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.card
            { f : Fin n → Fin k // rHorseSurjectiveIncreasing hrn f } : ℚ) := by
      rfl
    _ = ∑ k ∈ Finset.range (n + 1), rHorseCandidate n r k := by
      apply Finset.sum_congr rfl
      intro k _
      exact rHorse_card_surjective_eq_candidate hrn k
    _ = (1 / (Nat.factorial r : ℚ)) *
          ∑ k ∈ Finset.range (n + 1),
            ∑ j ∈ Finset.range (r + 1),
              (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
                ((Nat.factorial k : ℚ) * (Nat.stirlingSecond (n - j) k : ℚ)) := by
      unfold rHorseCandidate
      rw [Finset.mul_sum]
    _ = (1 / (Nat.factorial r : ℚ)) *
          ∑ j ∈ Finset.range (r + 1),
            (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
              ∑ k ∈ Finset.range (n + 1),
                (Nat.factorial k : ℚ) * (Nat.stirlingSecond (n - j) k : ℚ) := by
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = (1 / (Nat.factorial r : ℚ)) *
          ∑ j ∈ Finset.range (r + 1),
            (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
              (fubiniNumber (n - j) : ℚ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [rHorse_fubini_sum_extend (by omega)]

end MetaMathlibExt
