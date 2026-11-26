/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SuperMZumkeller
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Ring

/-!
# Super-m-Zumkeller numbers with two odd prime factors

For odd `k` and distinct odd primes `p` and `q`, the divisor product of `2 ^ k * (p * q)` is a
fourth power. Partitioning the divisors of that fourth power gives the super-m-Zumkeller property.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.SuperMZumkellerWanted

open Finset

-- A partition with a prescribed ratio between its two products.
private def HasPartition (s : Finset ℕ) (r : ℕ) : Prop :=
  ∃ A B : Finset ℕ, Disjoint A B ∧ A ∪ B = s ∧ (∏ d ∈ A, d) = r * ∏ d ∈ B, d

-- Adjoining a complementary pair to the smaller side exchanges the ratios 1 and m.
private lemma HasPartition.insert_pair {s : Finset ℕ} {d e u v : ℕ}
    (h : HasPartition s v) (hd : d ∉ s) (he : e ∉ s) (hne : d ≠ e)
    (hde : d * e = u * v) : HasPartition (insert d (insert e s)) u := by
  obtain ⟨A, B, hAB, rfl, hprod⟩ := h
  simp only [mem_union, not_or] at hd he
  refine ⟨insert d (insert e B), A, ?_, ?_, ?_⟩
  · simp [hd.1, he.1, hAB.symm]
  · simp [insert_union, union_comm B A]
  · rw [prod_insert (by simp [hne, hd.2]), prod_insert he.2, ← mul_assoc, hde,
      mul_assoc, ← hprod]

-- The three central powers admit both ratios. Every other divisor comes with a distinct
-- partner, so removing a pair preserves the induction hypotheses.
private lemma partitions_of_divisor_pairs (a : ℕ) (ha : 1 < a) (s : Finset ℕ)
    (hcore : {a, a ^ 2, a ^ 3} ⊆ s)
    (hclosed : ∀ d ∈ s, ∃ e ∈ s, d * e = a ^ 4) :
    HasPartition s 1 ∧ HasPartition s (a ^ 4) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have ha0 : 0 < a := by omega
    by_cases hsub : s ⊆ {a, a ^ 2, a ^ 3}
    · obtain rfl := Subset.antisymm hsub hcore
      have h12 : a < a ^ 2 := by simpa using Nat.pow_lt_pow_right ha (show 1 < 2 by decide)
      have h23 : a ^ 2 < a ^ 3 := Nat.pow_lt_pow_right ha (by decide)
      constructor
      · refine ⟨{a ^ 3}, {a, a ^ 2}, ?_, ?_, ?_⟩
        · simp [h23.ne', (h12.trans h23).ne']
        · ext d
          simp [or_comm]
        · simp [h12.ne]
          ring
      · refine ⟨{a ^ 2, a ^ 3}, {a}, ?_, ?_, ?_⟩
        · simp [h12.ne, (h12.trans h23).ne]
        · ext d
          simp [or_comm, or_left_comm]
        · simp [h23.ne]
          ring
    · obtain ⟨d, hd, hout⟩ := Finset.not_subset.mp hsub
      obtain ⟨e, he, hde⟩ := hclosed d hd
      have unique {x y z : ℕ} (hxy : x * y = a ^ 4) (hzy : z * y = a ^ 4) : x = z := by
        apply mul_right_cancel₀ _ (hxy.trans hzy.symm)
        rintro rfl
        exact (pow_ne_zero 4 ha0.ne') (by simpa using hxy.symm)
      have hne : d ≠ e := by
        rintro rfl
        have h : d ^ 2 = (a ^ 2) ^ 2 := by rw [sq d, hde, ← pow_mul]
        have := Nat.pow_left_injective (by decide : 2 ≠ 0) h
        simp [this] at hout
      have heout : e ∉ ({a, a ^ 2, a ^ 3} : Finset ℕ) := by
        simp only [mem_insert, mem_singleton] at hout ⊢
        rintro (h | h | h) <;> subst e
        · exact hout (.inr (.inr (unique hde (by ring))))
        · exact hout (.inr (.inl (unique hde (by ring))))
        · exact hout (.inl (unique hde (by ring)))
      let t := (s.erase d).erase e
      have hdt : d ∉ t := by simp [t]
      have het : e ∉ t := by simp [t]
      have hcore' : {a, a ^ 2, a ^ 3} ⊆ t := by
        intro x hx
        exact mem_erase.mpr ⟨ne_of_mem_of_not_mem hx heout,
          mem_erase.mpr ⟨ne_of_mem_of_not_mem hx hout, hcore hx⟩⟩
      have hclosed' : ∀ x ∈ t, ∃ y ∈ t, x * y = a ^ 4 := by
        intro x hx
        simp only [t, mem_erase] at hx
        obtain ⟨y, hy, hxy⟩ := hclosed x hx.2.2
        refine ⟨y, mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, hy⟩⟩, hxy⟩
        · rintro rfl
          exact hx.2.1 (unique hxy hde)
        · rintro rfl
          exact hx.1 (unique hxy (by rwa [mul_comm]))
      have hrec := ih t ((erase_subset e _).trans_ssubset (erase_ssubset hd)) hcore' hclosed'
      rw [show s = insert d (insert e t) by simp [t, he, hd, hne.symm]]
      exact ⟨hrec.2.insert_pair hdt het hne (by simpa using hde),
        hrec.1.insert_pair hdt het hne (by simpa using hde)⟩

private lemma partition_fourth_pow (a : ℕ) (ha : 1 < a) :
    ∃ A ⊆ (a ^ 4).divisors, (∏ d ∈ A, d) = ∏ d ∈ (a ^ 4).divisors \ A, d := by
  have hpos : a ^ 4 ≠ 0 := pow_ne_zero 4 (by omega)
  have hcore : {a, a ^ 2, a ^ 3} ⊆ (a ^ 4).divisors := by
    simp only [insert_subset_iff, singleton_subset_iff, Nat.mem_divisors]
    exact ⟨⟨dvd_pow_self _ (by decide), hpos⟩, ⟨pow_dvd_pow a (by decide), hpos⟩,
      pow_dvd_pow a (by decide), hpos⟩
  have hclosed : ∀ d ∈ (a ^ 4).divisors, ∃ e ∈ (a ^ 4).divisors, d * e = a ^ 4 := by
    intro d hd
    obtain ⟨e, he⟩ := Nat.dvd_of_mem_divisors hd
    exact ⟨e, Nat.mem_divisors.mpr ⟨he ▸ dvd_mul_left e d, hpos⟩, he.symm⟩
  obtain ⟨A, B, hAB, hab, hprod⟩ := (partitions_of_divisor_pairs a ha _ hcore hclosed).1
  refine ⟨A, hab ▸ subset_union_left, ?_⟩
  simpa [← hab, hAB.symm.sdiff_eq_left] using hprod

/-- **Odd powers of $2$ times two distinct odd primes are super-m-Zumkeller.** Let $k$ be an odd
natural number and let $p$ and $q$ be distinct odd primes. Then $2^k p q$ is super-m-Zumkeller.

The primes are required to be odd because the paper's proof uses that this number has
$(k+1) \cdot 2^2$ divisors.

Source: Harish Patodia, "Super m-Zumkeller Numbers",
Corollary 2. -/
public theorem isSuperMZumkeller_two_pow_mul_two_primes (k : ℕ)
    (hk : Odd k) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    IsSuperMZumkeller ((2 : ℕ) ^ k * (p * q)) := by
  obtain ⟨j, rfl⟩ := hk
  let n := 2 ^ (2 * j + 1) * (p * q)
  have h2 : Nat.Coprime 2 (p * q) := Nat.coprime_mul_iff_right.mpr
    ⟨(Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm,
      (Nat.coprime_primes Nat.prime_two hq).mpr hq2.symm⟩
  have hcard : n.divisors.card = (j + 1) * 4 * 2 := by
    dsimp only [n]
    rw [(h2.pow_left _).card_divisors_mul,
      ((Nat.coprime_primes hp hq).mpr hpq).card_divisors_mul,
      Nat.divisors_prime_pow Nat.prime_two, hp.divisors, hq.divisors]
    simp [hp.ne_one.symm, hq.ne_one.symm]
    omega
  have hn : 1 < n := by
    exact one_lt_mul_of_le_of_lt (Nat.one_le_pow _ _ (by decide))
      (one_lt_mul_of_le_of_lt hp.pos hq.one_lt)
  have hT : divisorProd n = (n ^ (j + 1)) ^ 4 := by
    apply Nat.pow_left_injective (by decide : 2 ≠ 0)
    change divisorProd n ^ 2 = _
    rw [divisorProd_sq n (by omega), hcard, pow_mul, pow_mul]
  change IsSuperMZumkeller n
  rw [IsSuperMZumkeller, hT]
  exact partition_fourth_pow _ (one_lt_pow₀ hn (by omega))

end MathlibExt.NumberTheory.SuperMZumkellerWanted
