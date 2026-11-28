/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.CompletelyAdditiveHeight

/-! # Tests for completely additive heights and the ordinary partition profile -/

open MetaMathlibExt

-- The product range is empty at level one.
example {H : ℕ → ℕ} (hH : IsHeightFunction H) :
    {m : ℕ | 0 < m ∧ H m = 1} = {p : ℕ | p.Prime ∧ H p = 1} := by
  rw [heightLevel_eq_products_union_primes hH (by decide : 1 ≤ 1)]
  ext m
  constructor
  · rintro (⟨ℓ, hpos, hbound, _⟩ | hp)
    · omega
    · exact hp
  · exact Or.inr

-- A prime square attains the upper bound on the height of the extracted factor.
example {H : ℕ → ℕ} (hH : IsHeightFunction H) {p : ℕ} (hp : p.Prime) :
    p ^ 2 ∈ {m : ℕ | 0 < m ∧ H m = 2 * H p} := by
  have hpH := hH.prime_pos p hp
  rw [heightLevel_eq_products_union_primes hH (by omega : 1 ≤ 2 * H p)]
  exact Or.inl ⟨H p, hpH, by omega, p, p, hp, rfl, hp.pos, by omega, pow_two p⟩

-- The profile starts at level one, even when its unused zeroth entry is nonzero.
example (a : ℕ) : profilePartialSum (fun k => if k = 0 then a else 1) 0 = 0 := by
  simp [profilePartialSum]

-- An unattained positive index uses the empty-set value.
example : seqHeightIndex (fun _ => 0) 1 = 0 := by
  simp [seqHeightIndex, profilePartialSum]

-- At the first allowed index, the strict lower bound is tight by one.
example : nthPrimeOne 6 - 2 * 6 = 1 := by
  have hl := two_mul_lt_nthPrimeOne (k := 6) (by decide)
  have hu : nthPrimeOne 6 < 14 :=
    Nat.nth_lt_of_lt_count (by decide : 5 < Nat.count Nat.Prime 14)
  omega

-- At the prime-square endpoint, 2 divides two terms and 4 contributes once more.
example {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H) :
    ∑ m ∈ Finset.Icc 1 4, H m = 3 * H 2 + H 3 := by
  rw [sum_height_eq_sum_prime_powers hH (by decide),
    show (Finset.Iic 4).filter Nat.Prime = {2, 3} by decide,
    Finset.sum_pair (by decide)]
  rw [show (Finset.Icc 1 4).filter (fun a => 2 ^ a ≤ 4) = {1, 2} by decide,
    show (Finset.Icc 1 4).filter (fun a => 3 ^ a ≤ 4) = {1} by decide,
    Finset.sum_pair (by decide), Finset.sum_singleton]
  simp
  omega

-- The one-based prime labels used as weights apply to every prime in the sequence.
example (i : ℕ) : canonicalSeqHeight (fun _ => 1) (nthPrimeOne (i + 1)) = i + 1 := by
  simp only [canonicalSeqHeight, nthPrimeOne, Nat.add_sub_cancel,
    additiveOfPrimeValues_prime _ (Nat.prime_nth_prime i), seqHeightIndex_const_one]
  exact congrArg (· + 1) (Nat.primeCounting'_nth_eq i)

-- Multiplicity matters: 12 has two factors of height one and one factor of height two.
example : canonicalSeqHeight (fun _ => 1) 12 = 4 := by
  unfold canonicalSeqHeight
  rw [show 12 = 2 * (2 * 3) by decide]
  rw [isCompletelyAdditiveNat_additiveOfPrimeValues _ 2 6 (by decide) (by decide),
    isCompletelyAdditiveNat_additiveOfPrimeValues _ 2 3 (by decide) (by decide),
    additiveOfPrimeValues_prime _ Nat.prime_two, additiveOfPrimeValues_prime _ Nat.prime_three]
  simp only [seqHeightIndex_const_one]
  decide

-- Matula iteration starts at eight when the iteration count truncates to zero.
example : matulaMax 2 = 8 := rfl

-- The ordinary partition coefficient at two counts 2 and 1+1.
example : weightedPartitionCoeff (fun _ => 1) 2 = 2 := by
  rw [weightedPartitionCoeff.eq_2, Fin.sum_univ_two]
  norm_num [Nat.prime_two.divisors, weightedPartitionCoeff_zero,
    weightedPartitionCoeff_one]

section Multipartitions

-- At level zero, any prime divisor would contribute positive height.
example {H : ℕ → ℕ} (hH : IsHeightFunction H) :
    Nat.card {m : ℕ // 0 < m ∧ H m = 0} = 1 := by
  refine Nat.card_eq_one_iff_exists.mpr ⟨⟨1, one_pos, hH.additive.map_one⟩, fun m => ?_⟩
  apply Subtype.ext
  change m.1 = 1
  by_contra hm
  obtain ⟨p, hp, k, hk⟩ := Nat.exists_prime_and_dvd hm
  have hkpos : 0 < k := Nat.pos_of_mul_pos_left (hk ▸ m.2.1)
  have hz := m.2.2
  rw [hk, hH.additive p k hp.pos hkpos] at hz
  have := hH.prime_pos p hp
  omega

-- No part sizes are available: the only assignment is the empty function.
example (H : ℕ → ℕ) :
    Nat.card {a : (Σ ℓ : Fin 0, Fin {p : ℕ | p.Prime ∧ H p = ℓ.1 + 1}.ncard) → ℕ //
      ∑ x, (x.1.1 + 1) * a x = 0} = 1 := by
  refine Nat.card_eq_one_iff_exists.mpr ⟨⟨fun _ => 0, by simp⟩, fun a => ?_⟩
  exact Subtype.ext (funext fun x => x.1.elim0)

private noncomputable def testHeight : ℕ → ℕ :=
  additiveOfPrimeValues fun p => if p ≤ 3 then 1 else if p = 5 then 2 else p

private lemma testHeight_prime {p : ℕ} (hp : p.Prime) :
    testHeight p = (if p ≤ 3 then 1 else if p = 5 then 2 else p) :=
  additiveOfPrimeValues_prime _ hp

private lemma testHeight_isHeight : IsHeightFunction testHeight where
  additive := isCompletelyAdditiveNat_additiveOfPrimeValues _
  prime_pos p hp := by
    rw [testHeight_prime hp]
    have := hp.two_le
    split_ifs <;> omega
  finite_primes n _ := (Set.finite_Iic (max 5 n)).subset fun p hp => by
    change p ≤ max 5 n
    obtain ⟨hp, hn⟩ := hp
    rw [testHeight_prime hp] at hn
    split_ifs at hn <;> omega

private lemma testPrimesOne : {p : ℕ | p.Prime ∧ testHeight p = 1} = {2, 3} := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, h⟩
    rw [testHeight_prime hp] at h
    have := hp.two_le
    split_ifs at h <;> omega
  · rintro (rfl | rfl)
    · exact ⟨Nat.prime_two, testHeight_prime Nat.prime_two⟩
    · exact ⟨Nat.prime_three, testHeight_prime Nat.prime_three⟩

private lemma testPrimesTwo : {p : ℕ | p.Prime ∧ testHeight p = 2} = {5} := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, h⟩
    rw [testHeight_prime hp] at h
    split_ifs at h <;> omega
  · rintro rfl
    exact ⟨Nat.prime_five, testHeight_prime Nat.prime_five⟩

-- The integer level consists of the three products of 2 and 3, and the prime 5.
private lemma testLevelTwo : {m : ℕ | 0 < m ∧ testHeight m = 2} = {4, 6, 9, 5} := by
  have hone : {m : ℕ | 0 < m ∧ testHeight m = 1} = {2, 3} := by
    rw [heightLevel_eq_products_union_primes testHeight_isHeight (n := 1) (by decide),
      testPrimesOne]
    ext m
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    exact or_iff_right (by rintro ⟨ℓ, hlo, hhi, _⟩; omega)
  rw [heightLevel_eq_products_union_primes testHeight_isHeight (n := 2) (by decide), testPrimesTwo]
  ext m
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨ℓ, hlo, hhi, p, k, hp, hpH, hk, hkH, rfl⟩ | rfl)
    · have hℓ : ℓ = 1 := by omega
      rw [hℓ] at hpH hkH
      have hp' : p = 2 ∨ p = 3 := by
        have h : p ∈ {q : ℕ | q.Prime ∧ testHeight q = 1} := ⟨hp, hpH⟩
        simpa only [testPrimesOne, Set.mem_insert_iff, Set.mem_singleton_iff] using h
      have hk' : k = 2 ∨ k = 3 := by
        have h : k ∈ {m : ℕ | 0 < m ∧ testHeight m = 1} := ⟨hk, hkH⟩
        simpa only [hone, Set.mem_insert_iff, Set.mem_singleton_iff] using h
      rcases hp' with rfl | rfl <;> rcases hk' with rfl | rfl <;> decide
    · decide
  · have h2 := testHeight_prime Nat.prime_two
    have h3 := testHeight_prime Nat.prime_three
    rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl ⟨1, by decide, by decide, 2, 2, Nat.prime_two, h2, by decide, h2, rfl⟩
    · exact Or.inl ⟨1, by decide, by decide, 2, 3, Nat.prime_two, h2, by decide, h3, rfl⟩
    · exact Or.inl ⟨1, by decide, by decide, 3, 3, Nat.prime_three, h3, by decide, h3, rfl⟩
    · exact Or.inr rfl

example : Nat.card {m : ℕ // 0 < m ∧ testHeight m = 2} = 4 := by
  change {m : ℕ | 0 < m ∧ testHeight m = 2}.ncard = 4
  rw [testLevelTwo, Set.ncard_eq_four]
  exact ⟨4, 6, 9, 5, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩

-- Independently count three assignments using the two size-one colours, and one using size two.
private lemma testMultipartitionsTwo :
    Nat.card {a : (Σ ℓ : Fin 2, Fin {p : ℕ | p.Prime ∧ testHeight p = ℓ.1 + 1}.ncard) → ℕ //
      ∑ x, (x.1.1 + 1) * a x = 2} = 4 := by
  have hprofile : (fun ℓ : Fin 2 => {p : ℕ | p.Prime ∧ testHeight p = ℓ.1 + 1}.ncard) =
      (fun ℓ => if ℓ = 0 then 2 else 1) := by
    funext ℓ
    fin_cases ℓ
    · change {p : ℕ | p.Prime ∧ testHeight p = 1}.ncard = 2
      rw [testPrimesOne, Set.ncard_pair (by decide : (2 : ℕ) ≠ 3)]
    · change {p : ℕ | p.Prime ∧ testHeight p = 2}.ncard = 1
      rw [testPrimesTwo, Set.ncard_singleton]
  let count (π : Fin 2 → ℕ) := Nat.card {a : (Σ ℓ : Fin 2, Fin (π ℓ)) → ℕ //
    ∑ x, (x.1.1 + 1) * a x = 2}
  change count (fun ℓ => {p : ℕ | p.Prime ∧ testHeight p = ℓ.1 + 1}.ncard) = 4
  rw [hprofile]
  let Labels := Σ ℓ : Fin 2, Fin (if ℓ = 0 then 2 else 1)
  change Nat.card {a : Labels → ℕ // ∑ x, (x.1.1 + 1) * a x = 2} = 4
  let e : {a : Labels → ℕ // ∑ x, (x.1.1 + 1) * a x = 2} ≃
      {a : Labels → Fin 3 // ∑ x, (x.1.1 + 1) * (a x).1 = 2} :=
    { toFun := fun a => ⟨fun x => ⟨a.1 x, by
        have h : (x.1.1 + 1) * a.1 x ≤ 2 := calc
          _ ≤ ∑ y : Labels, (y.1.1 + 1) * a.1 y :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
          _ = 2 := a.2
        exact Nat.lt_succ_of_le ((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans h)⟩, a.2⟩
      invFun := fun a => ⟨fun x => (a.1 x).1, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

-- A client can get the integer level count from the independently computed partition count.
example : Nat.card {m : ℕ // 0 < m ∧ testHeight m = 2} = 4 := by
  rw [heightLevel_card_eq_multipartitions testHeight_isHeight, testMultipartitionsTwo]

end Multipartitions
