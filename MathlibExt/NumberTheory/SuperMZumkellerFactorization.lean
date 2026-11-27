/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import MathlibExt.NumberTheory.SuperMZumkeller
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Ring

/-!
# The factorization criterion for super-m-Zumkeller numbers

Put `M = divisorProd n`. Complementary divisors of `M` have product `M`. If `M` is
not a square, the criterion allows a quarter of the divisor count in whole pairs.
If `M` is a square, its exponents are multiples of four; use whole pairs and the
fourth root, avoiding the pair that contains it.

## References

* Harish Patodia, *Super-m-Zumkeller Numbers*, INTEGERS 26 (2026), Article A79,
  Lemma 1 and Theorem 2.
* David M. Burton, *Elementary Number Theory*, 7th ed., McGraw-Hill, 2011, §6.1,
  pp. 106–107 (the complementary-divisor argument for the formula in Patodia's
  Lemma 1, which cites the 2012 McGraw Hill Education India edition).
-/

namespace MathlibExt.NumberTheory.SuperMZumkellerWanted

private theorem twice_factorization_divisorProd {n : ℕ} (hn : 0 < n) (p : ℕ) :
    2 * (divisorProd n).factorization p = n.factorization p * n.divisors.card := by
  have h := congrArg (fun x : ℕ => x.factorization p) (divisorProd_sq n hn)
  simpa only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    mul_comm n.divisors.card] using h

private theorem divisorProd_pos (n : ℕ) : 0 < divisorProd n := by
  apply Nat.pos_of_ne_zero
  exact Finset.prod_ne_zero_iff.mpr fun d hd => (Nat.pos_of_mem_divisors hd).ne'

private theorem mul_complement {m d : ℕ} (hd : d ∈ m.divisors) : d * (m / d) = m :=
  Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)

private theorem complement_mem {m d : ℕ} (hd : d ∈ m.divisors) : m / d ∈ m.divisors := by
  obtain ⟨hdvd, hm⟩ := Nat.mem_divisors.mp hd
  exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hm⟩

private theorem complement_complement {m d : ℕ} (hd : d ∈ m.divisors) : m / (m / d) = d := by
  obtain ⟨hdvd, hm⟩ := Nat.mem_divisors.mp hd
  exact Nat.div_div_self hdvd hm

private def lowerDivisors (m : ℕ) : Finset ℕ := m.divisors.filter fun d => d < m / d

private def middleDivisors (m : ℕ) : Finset ℕ := m.divisors.filter fun d => d = m / d

private def pairedDivisors (m : ℕ) (s : Finset ℕ) : Finset ℕ := s ∪ s.image (m / ·)

private theorem paired_subset {m : ℕ} {s : Finset ℕ} (hs : s ⊆ lowerDivisors m) :
    pairedDivisors m s ⊆ m.divisors := by
  apply Finset.union_subset
  · exact hs.trans (Finset.filter_subset _ _)
  · intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    exact complement_mem (Finset.mem_filter.mp (hs ha)).1

private theorem lower_disjoint_image {m : ℕ} {s : Finset ℕ} (hs : s ⊆ lowerDivisors m) :
    Disjoint s (s.image (m / ·)) := by
  rw [Finset.disjoint_left]
  intro d hd hd'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd'
  obtain ⟨had, haq⟩ := Finset.mem_filter.mp (hs ha)
  have h := (Finset.mem_filter.mp (hs hd)).2
  rw [complement_complement had] at h
  exact (lt_asymm haq) h

private theorem complement_injOn {m : ℕ} {s : Finset ℕ} (hs : s ⊆ m.divisors) :
    Set.InjOn (m / ·) (↑s : Set ℕ) := by
  intro a ha b hb h
  have ha' := complement_complement (hs (Finset.mem_coe.mp ha))
  have hb' := complement_complement (hs (Finset.mem_coe.mp hb))
  change m / a = m / b at h
  rw [h] at ha'
  exact ha'.symm.trans hb'

private theorem paired_prod {m : ℕ} {s : Finset ℕ} (hs : s ⊆ lowerDivisors m) :
    (∏ d ∈ pairedDivisors m s, d) = m ^ s.card := by
  rw [pairedDivisors, Finset.prod_union (lower_disjoint_image hs),
    Finset.prod_image (complement_injOn (hs.trans (Finset.filter_subset _ _))),
    ← Finset.prod_mul_distrib, ← Finset.prod_const]
  exact Finset.prod_congr rfl fun d hd => mul_complement (Finset.mem_filter.mp (hs hd)).1

private theorem paired_card {m : ℕ} {s : Finset ℕ} (hs : s ⊆ lowerDivisors m) :
    (pairedDivisors m s).card = 2 * s.card := by
  rw [pairedDivisors, Finset.card_union_of_disjoint (lower_disjoint_image hs),
    Finset.card_image_of_injOn (complement_injOn (hs.trans (Finset.filter_subset _ _))), two_mul]

private theorem card_divisors_paired (m : ℕ) :
    m.divisors.card = 2 * (lowerDivisors m).card + (middleDivisors m).card := by
  have hd : Disjoint (pairedDivisors m (lowerDivisors m)) (middleDivisors m) := by
    rw [Finset.disjoint_left]
    intro d hd hm
    have hfix := (Finset.mem_filter.mp hm).2
    rcases Finset.mem_union.mp hd with hlow | hhigh
    · exact (lt_irrefl d) ((Finset.mem_filter.mp hlow).2.trans_eq hfix.symm)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hhigh
      obtain ⟨had, haq⟩ := Finset.mem_filter.mp ha
      rw [complement_complement had] at hfix
      exact haq.ne hfix.symm
  have hcover : pairedDivisors m (lowerDivisors m) ∪ middleDivisors m = m.divisors := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset (paired_subset (Finset.Subset.refl _)) (Finset.filter_subset _ _)
    · intro d hd'
      rcases lt_trichotomy d (m / d) with h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd', h⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd', h⟩)
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨m / d, Finset.mem_filter.mpr ⟨complement_mem hd',
          by rwa [complement_complement hd']⟩, complement_complement hd'⟩
  rw [← hcover, Finset.card_union_of_disjoint hd, paired_card (Finset.Subset.refl _)]

private theorem middle_empty_of_not_square {m : ℕ} (hm : ¬ IsSquare m) :
    middleDivisors m = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  obtain ⟨hdiv, heq⟩ := Finset.mem_filter.mp hd
  exact hm ⟨d, by simpa only [← heq] using (mul_complement hdiv).symm⟩

private theorem middle_square {m a : ℕ} (hm : m ≠ 0) (ha : m = a * a) :
    middleDivisors m = {a} := by
  ext d
  rw [Finset.mem_singleton]
  constructor
  · intro hd
    obtain ⟨hdiv, heq⟩ := Finset.mem_filter.mp hd
    apply Nat.mul_self_inj.mp
    rw [← ha]
    simpa only [← heq] using mul_complement hdiv
  · intro hd
    subst d
    have hane : a ≠ 0 := left_ne_zero_of_mul (ha ▸ hm)
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨a, ha⟩, hm⟩,
      by rw [ha, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hane)]⟩

private theorem four_dvd_right_of_odd {a b : ℕ} (ha : Odd a) (h : 4 ∣ a * b) : 4 ∣ b := by
  have hc : Nat.Coprime 4 a := ha.coprime_two_left.pow_left 2
  exact hc.dvd_of_dvd_mul_left h

private theorem card_divisors_mod_four {m : ℕ} (hm : m ≠ 0)
    (he : ∀ p, 4 ∣ m.factorization p) : m.divisors.card % 4 = 1 := by
  rw [Nat.card_divisors hm]
  have hprod (s : Finset ℕ) : (∏ p ∈ s, (m.factorization p + 1)) % 4 = 1 := by
    induction s using Finset.induction with
    | empty => rfl
    | @insert p s hp ih =>
      have hp' : (m.factorization p + 1) % 4 = 1 := by have := he p; omega
      rw [Finset.prod_insert hp, Nat.mul_mod, hp', ih]
  exact hprod _

private theorem exists_fourth_root {m : ℕ} (hm : m ≠ 0) (he : ∀ p, 4 ∣ m.factorization p) :
    ∃ q : ℕ, q ^ 4 = m := by
  refine ⟨∏ p ∈ m.primeFactors, p ^ (m.factorization p / 4), ?_⟩
  refine (Finset.prod_pow _ _ _).symm.trans ?_
  refine (Finset.prod_congr rfl fun p _ => ?_).trans
    (Nat.prod_primeFactors_pow_factorization hm).symm
  rw [← pow_mul, Nat.div_mul_cancel (he p)]

private theorem equal_products_of_fourth_pow {m : ℕ} (hm : 0 < m) {A : Finset ℕ}
    (hA : A ⊆ m.divisors) (hpow : (∏ d ∈ A, d) ^ 4 = m ^ m.divisors.card) :
    (∏ d ∈ A, d) = ∏ d ∈ m.divisors \ A, d := by
  have hsq : (∏ d ∈ A, d) ^ 2 = divisorProd m := by
    apply pow_left_injective (n := 2) (by decide)
    change ((∏ d ∈ A, d) ^ 2) ^ 2 = (divisorProd m) ^ 2
    rwa [← pow_mul, divisorProd_sq m hm]
  have hprod := Finset.prod_sdiff (f := fun d : ℕ => d) hA
  change _ = divisorProd m at hprod
  rw [← hsq, sq] at hprod
  have hne : (∏ d ∈ A, d) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun d hd =>
    (Nat.pos_of_mem_divisors (hA hd)).ne'
  exact (mul_right_cancel₀ hne hprod).symm

private theorem exists_equal_products_of_factorization {m : ℕ} (hm : 0 < m)
    (h : ∀ p, 4 ∣ m.factorization p * m.divisors.card) :
    ∃ A : Finset ℕ, A ⊆ m.divisors ∧ (∏ d ∈ A, d) = ∏ d ∈ m.divisors \ A, d := by
  by_cases hsq : IsSquare m
  · obtain ⟨a, ha⟩ := hsq
    have hcard := card_divisors_paired m
    rw [middle_square hm.ne' ha, Finset.card_singleton] at hcard
    have hodd : Odd m.divisors.card := ⟨(lowerDivisors m).card, by omega⟩
    have he (p : ℕ) : 4 ∣ m.factorization p :=
      four_dvd_right_of_odd hodd (by simpa only [mul_comm m.divisors.card] using h p)
    have hmod := card_divisors_mod_four hm.ne' he
    obtain ⟨q, hq⟩ := exists_fourth_root hm.ne' he
    have hqpos : 0 < q := Nat.pos_of_ne_zero fun hq0 => hm.ne' (by simpa [hq0] using hq.symm)
    -- The fourth root is no larger than its complement, so erasing it from
    -- the lower divisors also keeps it out of the image of any selected pair.
    have hqle : q ≤ m / q := by
      rw [← hq, show q ^ 4 = q * q ^ 3 by ring, Nat.mul_div_cancel_left _ hqpos]
      exact le_trans (by simp : q ≤ q ^ 1) (Nat.pow_le_pow_right hqpos (by decide))
    let k := m.divisors.card / 4
    have hk : m.divisors.card = 4 * k + 1 := by dsimp [k]; omega
    have hkle : k ≤ ((lowerDivisors m).erase q).card := by
      have hh : (lowerDivisors m).card - 1 ≤ ((lowerDivisors m).erase q).card :=
        Finset.pred_card_le_card_erase
      omega
    obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq hkle
    have hs' := hs.trans (Finset.erase_subset _ _)
    have hqnot : q ∉ pairedDivisors m s := by
      intro hmem
      rcases Finset.mem_union.mp hmem with hd | hd
      · exact (Finset.notMem_erase q _) (hs hd)
      · obtain ⟨d, hd, hdc⟩ := Finset.mem_image.mp hd
        obtain ⟨hdiv, hlt⟩ := Finset.mem_filter.mp (hs' hd)
        rw [← hdc, complement_complement hdiv] at hqle
        exact (not_lt_of_ge hqle) hlt
    have hqm : q ∈ m.divisors := Nat.mem_divisors.mpr ⟨⟨q ^ 3, by rw [← hq]; ring⟩, hm.ne'⟩
    have hA : insert q (pairedDivisors m s) ⊆ m.divisors :=
      Finset.insert_subset_iff.mpr ⟨hqm, paired_subset hs'⟩
    refine ⟨_, hA, equal_products_of_fourth_pow hm hA ?_⟩
    rw [Finset.prod_insert hqnot, paired_prod hs', hsc, mul_pow, hq, ← pow_mul, hk, pow_succ]
    rw [mul_comm k 4, mul_comm m]
  · have hnot : ¬ ∀ p : ℕ, p.Prime → Even (m.factorization p) :=
      fun hEven => hsq (Nat.isSquare_iff_even_factorization.mpr hEven)
    push Not at hnot
    obtain ⟨p, _, hp⟩ := hnot
    have hD := four_dvd_right_of_odd hp (h p)
    obtain ⟨k, hk⟩ := hD
    have hcard := card_divisors_paired m
    rw [middle_empty_of_not_square hsq, Finset.card_empty, add_zero] at hcard
    obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq
      (show k ≤ (lowerDivisors m).card by omega)
    have hA := paired_subset hs
    refine ⟨pairedDivisors m s, hA, equal_products_of_fourth_pow hm hA ?_⟩
    rw [paired_prod hs, hsc, ← pow_mul, hk, mul_comm k 4]

/-- **Criterion for super-m-Zumkeller numbers.** Let $n \ge 2$ be an integer, let $\tau(n)$ be the
number of positive divisors of $n$ and $T(n)$ their product. Then $n$ is super-m-Zumkeller if and
only if $8$ divides $\alpha \cdot \tau(n) \cdot \tau(T(n))$ for every prime $p$ dividing $n$,
where $\alpha$ is the exponent of $p$ in $n$.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 2. -/
public theorem isSuperMZumkeller_iff (n : ℕ) (hn : 2 ≤ n) :
    IsSuperMZumkeller n ↔
      ∀ p ∈ n.primeFactors,
        8 ∣ (n.factorization p) * n.divisors.card *
          (divisorProd n).divisors.card := by
  have hn' : 0 < n := by omega
  let M := divisorProd n
  have hM : 0 < M := divisorProd_pos n
  have he (p : ℕ) : 2 * (M.factorization p * M.divisors.card) =
      n.factorization p * n.divisors.card * M.divisors.card := by
    rw [← mul_assoc, twice_factorization_divisorProd hn']
  constructor
  · rintro ⟨A, hA, hprod⟩ p _
    have hsq : (∏ d ∈ A, d) ^ 2 = divisorProd M := by
      rw [sq]
      nth_rw 1 [hprod]
      exact Finset.prod_sdiff hA
    have hF := congrArg (fun x : ℕ => x.factorization p) hsq
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hF
    rw [← he, ← twice_factorization_divisorProd hM, ← hF]
    refine ⟨(∏ d ∈ A, d).factorization p, ?_⟩
    ring
  · intro h
    apply exists_equal_products_of_factorization hM
    intro p
    by_cases hp : p ∈ n.primeFactors
    · have h' := h p hp
      rw [← he] at h'
      omega
    · have hzero : n.factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        simpa only [Nat.support_factorization] using hp
      have h' := he p
      rw [hzero, zero_mul, zero_mul] at h'
      omega

end MathlibExt.NumberTheory.SuperMZumkellerWanted
