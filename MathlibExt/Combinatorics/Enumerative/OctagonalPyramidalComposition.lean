/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.OctagonalPyramidalNumber
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- Membership in `octagonalPyramidalCompositions` unfolds to a bound on each
part together with the sum constraint. -/
private lemma mem_comp_iff (k : ℕ) (c : Fin k → ℕ) :
    c ∈ octagonalPyramidalCompositions k ↔
      (∀ i, 1 ≤ c i ∧ c i ≤ k + 14 ∧ c i ≠ 2 ∧ c i ≠ 3 ∧ c i ≠ 4) ∧ ∑ i, c i = k + 14 := by
  simp only [octagonalPyramidalCompositions, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => ⟨(h1 i).1.1, (h1 i).1.2, (h1 i).2.1, (h1 i).2.2.1, (h1 i).2.2.2⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => ⟨⟨(h1 i).1, (h1 i).2.1⟩, (h1 i).2.2.1, (h1 i).2.2.2.1, (h1 i).2.2.2.2⟩, h2⟩

/-- Split the total sum into the sum over `S` and the constant `1` off `S`. -/
private lemma sum_split (k : ℕ) (S : Finset (Fin k)) (c : Fin k → ℕ)
    (hcompl : ∀ i, i ∉ S → c i = 1) :
    ∑ i, c i = (∑ i ∈ S, c i) + (k - S.card) := by
  rw [← Finset.sum_add_sum_compl S c]
  congr 1
  rw [Finset.sum_congr rfl (fun i hi => hcompl i (Finset.mem_compl.mp hi))]
  rw [Finset.sum_const, Finset.card_compl, Fintype.card_fin, smul_eq_mul, mul_one]

/-- Characterisation of the fibre of the "support" map: a composition has
support exactly `S` iff each part on `S` is at least `5`, every part off `S`
equals `1`, and the parts on `S` sum to `14 + |S|`. -/
private lemma mem_fiber_iff (k : ℕ) (S : Finset (Fin k)) (c : Fin k → ℕ) :
    (c ∈ octagonalPyramidalCompositions k ∧ (Finset.univ.filter fun i => c i ≠ 1) = S) ↔
      ((∀ i ∈ S, 5 ≤ c i) ∧ (∀ i, i ∉ S → c i = 1) ∧ (∀ i ∈ S, c i ≤ k + 14)
        ∧ ∑ i ∈ S, c i = 14 + S.card) := by
  have hScard : S.card ≤ k := by
    calc S.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = k := by simp
  constructor
  · rintro ⟨hc, hS⟩
    rw [mem_comp_iff] at hc
    obtain ⟨hcod, hsum⟩ := hc
    have hmemS : ∀ i, i ∈ S ↔ c i ≠ 1 := by intro i; rw [← hS, Finset.mem_filter]; simp
    have hcompl : ∀ i, i ∉ S → c i = 1 := by intro i hi; by_contra h; exact hi ((hmemS i).2 h)
    refine ⟨fun i hi => ?_, hcompl, fun i _ => (hcod i).2.1, ?_⟩
    · have hne1 : c i ≠ 1 := (hmemS i).1 hi
      have := hcod i; omega
    · have := sum_split k S c hcompl; omega
  · rintro ⟨hbig, hcompl, hub, hsumS⟩
    have hmemS : ∀ i, i ∈ S ↔ c i ≠ 1 := by
      intro i; constructor
      · intro hi; have := hbig i hi; omega
      · intro hne; by_contra hi; exact hne (hcompl i hi)
    refine ⟨?_, ?_⟩
    · rw [mem_comp_iff]
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i ∈ S
        · have := hbig i hi; have := hub i hi; omega
        · have := hcompl i hi; omega
      · have := sum_split k S c hcompl; omega
    · ext i; rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
      exact (hmemS i).symm

/-- The support of a composition has size `1`, `2`, or `3`. -/
private lemma supp_card_bounds (k : ℕ) (c : Fin k → ℕ) (hc : c ∈ octagonalPyramidalCompositions k) :
    1 ≤ (Finset.univ.filter fun i => c i ≠ 1).card
      ∧ (Finset.univ.filter fun i => c i ≠ 1).card ≤ 3 := by
  set S := Finset.univ.filter fun i => c i ≠ 1 with hSdef
  have hmem : c ∈ octagonalPyramidalCompositions k
      ∧ (Finset.univ.filter fun i => c i ≠ 1) = S := ⟨hc, rfl⟩
  rw [mem_fiber_iff] at hmem
  obtain ⟨hbig, hcompl, hub, hsum⟩ := hmem
  have hlow : 5 * S.card ≤ ∑ i ∈ S, c i := by
    calc 5 * S.card = ∑ _i ∈ S, 5 := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ i ∈ S, c i := Finset.sum_le_sum (fun i hi => hbig i hi)
  refine ⟨?_, by omega⟩
  by_contra h
  have hc0 : S.card = 0 := by omega
  rw [Finset.card_eq_zero] at hc0
  rw [hc0] at hsum
  simp at hsum

/-- Singleton supports contribute exactly one composition each. -/
private lemma fiber_card_one (k : ℕ) (hk : 0 < k) (S : Finset (Fin k)) (hcard : S.card = 1) :
    ((octagonalPyramidalCompositions k).filter
      (fun c => (Finset.univ.filter fun i => c i ≠ 1) = S)).card = 1 := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  rw [Finset.card_eq_one]
  refine ⟨fun i => if i = a then 15 else 1, ?_⟩
  ext c
  rw [Finset.mem_filter, mem_fiber_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hbig, hcompl, hub, hsum⟩
    rw [Finset.sum_singleton, Finset.card_singleton] at hsum
    funext i
    by_cases hi : i = a
    · subst hi; rw [hsum]; simp
    · rw [hcompl i (by simp [hi])]; simp [hi]
  · rintro rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi; rw [Finset.mem_singleton] at hi; subst hi; simp
    · intro i hi; rw [Finset.mem_singleton] at hi; simp [hi]
    · intro i hi; rw [Finset.mem_singleton] at hi; subst hi; simp; omega
    · rw [Finset.sum_singleton, Finset.card_singleton]; simp

/-- Two-element supports contribute exactly seven compositions each. -/
private lemma fiber_card_two (k : ℕ) (S : Finset (Fin k)) (hcard : S.card = 2) :
    ((octagonalPyramidalCompositions k).filter
      (fun c => (Finset.univ.filter fun i => c i ≠ 1) = S)).card = 7 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have hcard2 : ({a, b} : Finset (Fin k)).card = 2 := by rw [Finset.card_pair hab]
  have hba : b ≠ a := Ne.symm hab
  have key : ((octagonalPyramidalCompositions k).filter
      (fun c => (Finset.univ.filter fun i => c i ≠ 1) = {a, b})).card = (Finset.Icc 5 11).card := by
    refine Finset.card_bij' (fun c _ => c a)
      (fun x _ => fun i => if i = a then x else if i = b then 16 - x else 1) ?hi ?hj ?linv ?rinv
    case hi =>
      intro c hc
      rw [Finset.mem_filter, mem_fiber_iff] at hc
      obtain ⟨hbig, hcompl, hub, hsum⟩ := hc
      rw [Finset.sum_pair hab, hcard2] at hsum
      have h5a : 5 ≤ c a := hbig a (by simp)
      have h5b : 5 ≤ c b := hbig b (by simp)
      rw [Finset.mem_Icc]; omega
    case hj =>
      intro x hx
      rw [Finset.mem_Icc] at hx
      rw [Finset.mem_filter, mem_fiber_iff, Finset.sum_pair hab, hcard2]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl <;> simp [hba] <;> omega
      · intro i hi
        rw [Finset.mem_insert, Finset.mem_singleton] at hi
        simp only [not_or] at hi
        simp [hi.1, hi.2]
      · intro i hi
        rw [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl <;> simp [hba] <;> omega
      · simp [hba]; omega
    case linv =>
      intro c hc
      rw [Finset.mem_filter, mem_fiber_iff] at hc
      obtain ⟨hbig, hcompl, hub, hsum⟩ := hc
      rw [Finset.sum_pair hab, hcard2] at hsum
      funext i
      by_cases hia : i = a
      · subst hia; simp
      · by_cases hib : i = b
        · subst hib; simp [hba]; omega
        · rw [hcompl i (by simp [hia, hib])]; simp [hia, hib]
    case rinv =>
      intro x hx
      simp
  rw [key]; decide

/-- Three-element supports contribute exactly six compositions each. -/
private lemma fiber_card_three (k : ℕ) (S : Finset (Fin k)) (hcard : S.card = 3) :
    ((octagonalPyramidalCompositions k).filter
      (fun c => (Finset.univ.filter fun i => c i ≠ 1) = S)).card = 6 := by
  obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := Finset.card_eq_three.mp hcard
  have hba : b ≠ a := Ne.symm hab
  have hda : d ≠ a := Ne.symm had
  have hdb : d ≠ b := Ne.symm hbd
  have hcard3 : ({a, b, d} : Finset (Fin k)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, had]), Finset.card_pair hbd]
  have hsumpair : ∀ f : Fin k → ℕ, ∑ i ∈ ({a, b, d} : Finset (Fin k)), f i = f a + f b + f d := by
    intro f
    rw [Finset.sum_insert (by simp [hab, had]), Finset.sum_pair hbd]; ring
  set T3 := (Finset.Icc 5 12 ×ˢ Finset.Icc 5 12).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ 12) with hT3
  have key : ((octagonalPyramidalCompositions k).filter
      (fun c => (Finset.univ.filter fun i => c i ≠ 1) = {a, b, d})).card = T3.card := by
    refine Finset.card_bij' (fun c _ => (c a, c b))
      (fun p _ => fun i => if i = a then p.1 else if i = b then p.2
        else if i = d then 17 - p.1 - p.2 else 1) ?hi ?hj ?linv ?rinv
    case hi =>
      intro c hc
      rw [Finset.mem_filter, mem_fiber_iff] at hc
      obtain ⟨hbig, hcompl, hub, hsum⟩ := hc
      rw [hsumpair, hcard3] at hsum
      have h5a : 5 ≤ c a := hbig a (by simp)
      have h5b : 5 ≤ c b := hbig b (by simp)
      have h5d : 5 ≤ c d := hbig d (by simp)
      rw [hT3, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      refine ⟨⟨⟨h5a, ?_⟩, ⟨h5b, ?_⟩⟩, ?_⟩ <;> omega
    case hj =>
      intro p hp
      rw [hT3, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
      rw [Finset.mem_filter, mem_fiber_iff, hsumpair, hcard3]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl <;> simp [hba, hda, hdb] <;> omega
      · intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        simp only [not_or] at hi
        simp [hi.1, hi.2.1, hi.2.2]
      · intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl <;> simp [hba, hda, hdb] <;> omega
      · simp [hba, hda, hdb]; omega
    case linv =>
      intro c hc
      rw [Finset.mem_filter, mem_fiber_iff] at hc
      obtain ⟨hbig, hcompl, hub, hsum⟩ := hc
      rw [hsumpair, hcard3] at hsum
      funext i
      by_cases hia : i = a
      · subst hia; simp
      · by_cases hib : i = b
        · subst hib; simp [hba]
        · by_cases hid : i = d
          · subst hid; simp [hda, hdb]; omega
          · rw [hcompl i (by simp [hia, hib, hid])]; simp [hia, hib, hid]
    case rinv =>
      intro p hp
      simp [hba]
  rw [key, hT3]; decide

/-- The counting identity `k + 7·C(k,2) + 6·C(k,3) = k(k+1)(2k-1)/2`. -/
private lemma octag_arith (k : ℕ) :
    k + 7 * k.choose 2 + 6 * k.choose 3 = k * (k + 1) * (2 * k - 1) / 2 := by
  have h2 : 2 * k.choose 2 = (k - 1) * k := by
    have h := Nat.descFactorial_eq_factorial_mul_choose k 2
    norm_num [Nat.descFactorial, Nat.factorial] at h; exact h.symm
  have h3 : 6 * k.choose 3 = (k - 2) * ((k - 1) * k) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose k 3
    norm_num [Nat.descFactorial, Nat.factorial] at h; exact h.symm
  have key : 2 * (k + 7 * k.choose 2 + 6 * k.choose 3) = k * (k + 1) * (2 * k - 1) := by
    have expand : 2 * (k + 7 * k.choose 2 + 6 * k.choose 3)
        = 2 * k + 7 * (2 * k.choose 2) + 2 * (6 * k.choose 3) := by ring
    rw [expand, h2, h3]
    rcases k with _ | _ | n
    · rfl
    · rfl
    · have s1 : n + 1 + 1 - 1 = n + 1 := by omega
      have s2 : n + 1 + 1 - 2 = n := by omega
      have s3 : 2 * (n + 1 + 1) - 1 = 2 * n + 3 := by omega
      rw [s1, s2, s3]; ring
  omega

section
/-- **Octagonal pyramidal numbers count restricted compositions.** For every positive integer $k$,
the number of ordered compositions of $k + 14$ into $k$ positive parts with no part equal to $2$,
$3$ or $4$ is the $k$-th octagonal pyramidal number $k(k+1)(2k-1)/2$.

Proves `Wanted` entry `octagonalPyramidalNumber_eq_composition_card`.

Source: Milan Janjić, *Binomial Coefficients and Enumeration of Restricted Words*, Journal of
Integer Sequences 19 (2016), Article 16.7.3, the corollary attached to statement
`jis_4f77f6102ca88eba755447c5`.
-/
theorem octagonalPyramidalNumber_eq_composition_card (k : ℕ) (hk : 0 < k) :
    (octagonalPyramidalCompositions k).card = octagonalPyramidalNumber k := by
  have hmaps : Set.MapsTo (fun c : Fin k → ℕ => Finset.univ.filter fun i => c i ≠ 1)
      ↑(octagonalPyramidalCompositions k)
      ↑((Finset.univ.powersetCard 1 ∪ Finset.univ.powersetCard 2
          ∪ Finset.univ.powersetCard 3 : Finset (Finset (Fin k)))) := by
    intro c hc
    rw [Finset.mem_coe] at hc
    rw [Finset.mem_coe, Finset.mem_union, Finset.mem_union, Finset.mem_powersetCard,
      Finset.mem_powersetCard, Finset.mem_powersetCard]
    obtain ⟨h1, h3⟩ := supp_card_bounds k c hc
    have hsub : (Finset.univ.filter fun i => c i ≠ 1) ⊆ Finset.univ := Finset.subset_univ _
    rcases (by omega : (Finset.univ.filter fun i => c i ≠ 1).card = 1
        ∨ (Finset.univ.filter fun i => c i ≠ 1).card = 2
        ∨ (Finset.univ.filter fun i => c i ≠ 1).card = 3) with h | h | h
    · exact Or.inl (Or.inl ⟨hsub, h⟩)
    · exact Or.inl (Or.inr ⟨hsub, h⟩)
    · exact Or.inr ⟨hsub, h⟩
  have hd12 : Disjoint (Finset.univ.powersetCard 1 : Finset (Finset (Fin k)))
      (Finset.univ.powersetCard 2) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_powersetCard] at hx1 hx2; omega
  have hd123 : Disjoint (Finset.univ.powersetCard 1 ∪ Finset.univ.powersetCard 2
      : Finset (Finset (Fin k))) (Finset.univ.powersetCard 3) := by
    rw [Finset.disjoint_left]
    intro x hx12 hx3
    rw [Finset.mem_union] at hx12
    rw [Finset.mem_powersetCard] at hx3
    rcases hx12 with h | h <;> · rw [Finset.mem_powersetCard] at h; omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_union hd123, Finset.sum_union hd12]
  have e1 : ∑ b ∈ Finset.univ.powersetCard 1,
      ({a ∈ octagonalPyramidalCompositions k
        | (Finset.univ.filter fun i => a i ≠ 1) = b}).card = k := by
    rw [Finset.sum_congr rfl fun b hb =>
      fiber_card_one k hk b (Finset.mem_powersetCard.mp hb).2]
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, Nat.choose_one_right]
  have e2 : ∑ b ∈ Finset.univ.powersetCard 2,
      ({a ∈ octagonalPyramidalCompositions k
        | (Finset.univ.filter fun i => a i ≠ 1) = b}).card = 7 * k.choose 2 := by
    rw [Finset.sum_congr rfl fun b hb =>
      fiber_card_two k b (Finset.mem_powersetCard.mp hb).2]
    rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, Nat.mul_comm]
  have e3 : ∑ b ∈ Finset.univ.powersetCard 3,
      ({a ∈ octagonalPyramidalCompositions k
        | (Finset.univ.filter fun i => a i ≠ 1) = b}).card = 6 * k.choose 3 := by
    rw [Finset.sum_congr rfl fun b hb =>
      fiber_card_three k b (Finset.mem_powersetCard.mp hb).2]
    rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, Nat.mul_comm]
  rw [e1, e2, e3, octagonalPyramidalNumber]
  have := octag_arith k
  omega

end

end MetaMathlibExt
