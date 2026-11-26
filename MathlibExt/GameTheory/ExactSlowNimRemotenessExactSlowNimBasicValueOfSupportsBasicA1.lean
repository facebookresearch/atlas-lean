/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ExactSlowNimRemoteness
import Mathlib.Data.Finset.Max

/-!
# Moves at positions supported by type (A1) basic vectors

Every option lowers the basic-vector value by at most two, and the M-move lowers it by one,
for positions supported by a type (A1) basic vector.

Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi,
*On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1
(arXiv:2304.06498), Lemma 3.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem le_value {k b : ℕ} (hk : 0 < k) {x y : Fin (k + 1) → ℕ}
    (hyx : y ≤ x) (hy : IsExactSlowNimBasicA0 k b y ∨
      IsExactSlowNimBasicA1 k b y ∨ IsExactSlowNimBasicB k b y) :
    b ≤ exactSlowNimBasicValue k x := by
  classical
  have hmass : k * b ≤ ∑ i, y i := by
    rcases hy with h | h | h
    · exact h.1.ge
    · exact h.1.ge
    · have := h.1
      omega
  unfold exactSlowNimBasicValue
  exact Nat.le_findGreatest ((Nat.le_mul_of_pos_left _ hk).trans
    (hmass.trans (Finset.sum_le_sum fun i _ => hyx i))) ⟨y, hyx, hy⟩

private theorem value_mono {k : ℕ} (hk : 0 < k) {x y : Fin (k + 1) → ℕ}
    (hyx : y ≤ x) : exactSlowNimBasicValue k y ≤ exactSlowNimBasicValue k x := by
  obtain ⟨z, hzy, hz⟩ := exists_supports_exactSlowNimBasicValue k y
  exact le_value hk (hzy.trans hyx) hz

private theorem odd_pile {k b : ℕ} {z : Fin (k + 1) → ℕ}
    (hz : IsExactSlowNimBasicA1 k b z) {p : Fin (k + 1)}
    (hp : Even (z p)) {i : Fin (k + 1)} (hi : i ≠ p) : Odd (z i) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  obtain ⟨j, hj, hu⟩ := hz.2.2.2
  exact hi ((hu i he).trans (hu p hp).symm)

private theorem pair_bound {k b : ℕ} (hk : 0 < k) {z : Fin (k + 1) → ℕ}
    (hz : IsExactSlowNimBasicA1 k b z) (p q : Fin (k + 1)) (hpq : p ≠ q) :
    b ≤ z p + z q := by
  have hqp : q ≠ p := Ne.symm hpq
  have hq : q ∈ Finset.univ.erase p := by simp [hqp]
  let s := (Finset.univ.erase p).erase q
  have hc : s.card = k - 1 := by
    simp only [s, Finset.card_erase_of_mem hq]
    simp
  have hs : (∑ i ∈ s, z i) ≤ (k - 1) * b := by
    simpa [hc] using Finset.sum_le_sum (s := s) (fun i _ => hz.2.1 i)
  have hsum := Finset.sum_erase_add (Finset.univ.erase p) z
    hq
  have hsum' := Finset.sum_erase_add Finset.univ z (Finset.mem_univ p)
  have hm : (k - 1) * b + b = k * b := by
    rw [← Nat.add_one_mul, Nat.sub_add_cancel hk]
  change (∑ i ∈ s, z i) + z q = _ at hsum
  rw [hz.1] at hsum'
  omega

private theorem sum_sub {k : ℕ} (z d : Fin (k + 1) → ℕ) (hd : d ≤ z) :
    (∑ i, (z i - d i)) + (∑ i, d i) = ∑ i, z i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hd i)

private theorem after_le {k : ℕ} (x : Fin (k + 1) → ℕ)
    (s : Finset (Fin (k + 1))) : slowANimAfter x s ≤ x := by
  intro i
  simp only [slowANimAfter]
  split <;> omega

private theorem lower_options {k b : ℕ} (hk : 0 < k) {x z : Fin (k + 1) → ℕ}
    (hzx : z ≤ x) (hz : IsExactSlowNimBasicA1 k b z)
    (s : Finset (Fin (k + 1))) : b - 2 ≤ exactSlowNimBasicValue k (slowANimAfter x s) := by
  classical
  by_cases hb : b ≤ 2
  · exact (by omega : b - 2 = 0) ▸ Nat.zero_le _
  have hb3 : 3 ≤ b := by omega
  have hbo := Nat.odd_iff.mp hz.2.2.1
  obtain ⟨p, hp, _⟩ := hz.2.2.2
  have hpe := Nat.even_iff.mp hp
  have hpbound := hz.2.1 p
  by_cases hp0 : z p = 0
  · have hall (i : Fin (k + 1)) (hi : i ≠ p) : z i = b := by
      have := pair_bound hk hz p i (Ne.symm hi)
      have := hz.2.1 i
      omega
    let d i := if i = p then 0 else 2
    let y i := z i - d i
    have hd : d ≤ z := by
      intro i
      by_cases hi : i = p
      · simp [d, hi]
      · simp [d, hi, hall i hi]
        omega
    have hyx : y ≤ slowANimAfter x s := by
      intro i
      have hxi : z i ≤ x i := hzx i
      by_cases hi : i = p
      · simp [y, d, hi, hp0]
      · simp only [y, d, hi, ite_false, slowANimAfter]
        split <;> omega
    apply le_value hk hyx (Or.inr (Or.inl ?_))
    refine ⟨?_, ?_, ?_, p, ?_, ?_⟩
    · have hsum := sum_sub z d hd
      have hds : ∑ i, d i = k * 2 := by simp [d, Finset.sum_ite, Finset.filter_ne']
      change (∑ i, y i) + (∑ i, d i) = _ at hsum
      rw [hds, hz.1] at hsum
      have hm : k * (b - 2) + k * 2 = k * b := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by omega : 2 ≤ b)]
      omega
    · intro i
      by_cases hi : i = p
      · simp [y, d, hi, hp0]
      · simp [y, d, hi, hall i hi]
    · rw [Nat.odd_iff]
      omega
    · simp [y, d, hp0]
    · intro i hi
      by_contra hip
      simp only [y, d, hip, ite_false, hall i hip, Nat.even_iff] at hi
      omega
  · let s' := Finset.univ.erase p
    have hs' : s'.Nonempty := by
      apply Finset.card_pos.mp
      simpa [s'] using hk
    obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image s' z hs'
    have hrp : r ≠ p := (Finset.mem_erase.mp hr).1
    have hro := Nat.odd_iff.mp (odd_pile hz hp hrp)
    have hrlt : z r < b := by
      by_contra h
      have hrb : z r = b := by have := hz.2.1 r; omega
      have hrest : ∑ i ∈ s', z i = k * b := by
        have heq : ∀ i ∈ s', z i = b := by
          intro i hi
          have := hmin i hi
          have := hz.2.1 i
          omega
        simp [Finset.sum_congr rfl heq, s']
      have hsum := Finset.sum_erase_add Finset.univ z (Finset.mem_univ p)
      change (∑ i ∈ s', z i) + z p = _ at hsum
      rw [hrest, hz.1] at hsum
      omega
    have htwo (i : Fin (k + 1)) (hip : i ≠ p) (hir : i ≠ r) : 2 ≤ z i := by
      have hpair := pair_bound hk hz r i (Ne.symm hir)
      have hmini := hmin i (by simp [s', hip])
      omega
    let d i := if i = p ∨ i = r then 1 else 2
    let y i := z i - d i
    have hd : d ≤ z := by
      intro i
      by_cases hip : i = p
      · simp [d, hip]
        omega
      · by_cases hir : i = r
        · simp [d, hir]
          omega
        · simpa [d, hip, hir] using htwo i hip hir
    have hyx : y ≤ slowANimAfter x s := by
      intro i
      have hxi : z i ≤ x i := hzx i
      simp only [y, d, slowANimAfter]
      split <;> split <;> omega
    apply le_value hk hyx (Or.inr (Or.inl ?_))
    refine ⟨?_, ?_, ?_, r, ?_, ?_⟩
    · have hsum := sum_sub z d hd
      have hds : ∑ i, d i = k * 2 := by
        have heq (i : Fin (k + 1)) : d i + (if i = p then 1 else 0) +
            (if i = r then 1 else 0) = 2 := by
          simp only [d]
          by_cases hip : i = p <;> by_cases hir : i = r <;> simp [hip, hir] <;>
            simp_all
        have := Finset.sum_congr (s₁ := Finset.univ) rfl fun i _ => heq i
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
        omega
      change (∑ i, y i) + (∑ i, d i) = _ at hsum
      rw [hds, hz.1] at hsum
      have hm : k * (b - 2) + k * 2 = k * b := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by omega : 2 ≤ b)]
      omega
    · intro i
      have hi := hz.2.1 i
      by_cases hip : i = p
      · simp only [y, d, hip, true_or, ite_true]
        omega
      · by_cases hir : i = r
        · simp only [y, d, hir, or_true, ite_true]
          omega
        · simp only [y, d, hip, hir, or_self, ite_false]
          omega
    · rw [Nat.odd_iff]
      omega
    · simp only [y, d, or_true, ite_true, Nat.even_iff]
      omega
    · intro i hi
      by_contra hir
      by_cases hip : i = p
      · simp only [y, d, hip, true_or, ite_true, Nat.even_iff] at hi
        omega
      · have ho := Nat.odd_iff.mp (odd_pile hz hp hip)
        have ht := htwo i hip hir
        simp only [y, d, hip, hir, or_self, ite_false, Nat.even_iff] at hi
        omega

private theorem after_erase {k : ℕ} (x : Fin (k + 1) → ℕ) (p i : Fin (k + 1)) :
    slowANimAfter x (Finset.univ.erase p) i = if i = p then x i else x i - 1 := by
  simp [slowANimAfter, ite_not]

private theorem mmove_apply {k : ℕ} (x : Fin (k + 1) → ℕ) (i : Fin (k + 1)) :
    exactSlowNimMRuleMove x i =
      if i = exactSlowNimMRuleKept x then x i else x i - 1 := by
  exact after_erase x _ i

private theorem found_property {k : ℕ} (f : Fin (k + 1) → Bool)
    (h : ∃ i, f i = true) :
    f (((List.finRange (k + 1)).find? f).getD 0) = true := by
  have hs : ((List.finRange (k + 1)).find? f).isSome = true := by
    apply List.find?_isSome.mpr
    obtain ⟨i, hi⟩ := h
    exact ⟨i, List.mem_finRange i, hi⟩
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hs
  simpa [hi] using List.find?_some hi

private theorem kept_even {k : ℕ} (x : Fin (k + 1) → ℕ) (h : ∃ i, Even (x i)) :
    Even (x (exactSlowNimMRuleKept x)) ∧
      ∀ j, Even (x j) → x (exactSlowNimMRuleKept x) ≤ x j := by
  classical
  have ha : (List.finRange (k + 1)).any (fun i => decide (Even (x i))) = true := by
    apply List.any_eq_true.mpr
    obtain ⟨i, hi⟩ := h
    exact ⟨i, List.mem_finRange i, by simp [hi]⟩
  have hn : (Finset.univ.filter fun i => Even (x i)).Nonempty := by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, by simp [hi]⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _ x hn
  have hf : ∃ i, decide (Even (x i) ∧ ∀ j, Even (x j) → x i ≤ x j) = true := by
    refine ⟨i, ?_⟩
    simp only [decide_eq_true_eq]
    exact ⟨(Finset.mem_filter.mp hi).2, fun j hj => hmin j (by simp [hj])⟩
  simpa only [exactSlowNimMRuleKept, ha, Bool.true_eq, ↓reduceIte,
    decide_eq_true_eq] using found_property _ hf

private theorem kept_max {k : ℕ} (x : Fin (k + 1) → ℕ) (h : ¬ ∃ i, Even (x i)) :
    ∀ j, x j ≤ x (exactSlowNimMRuleKept x) := by
  classical
  have ha : (List.finRange (k + 1)).any (fun i => decide (Even (x i))) = false := by
    apply Bool.eq_false_iff.mpr
    intro ha
    obtain ⟨i, _, hi⟩ := List.any_eq_true.mp ha
    exact h ⟨i, of_decide_eq_true hi⟩
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  have hf : ∃ i, decide (∀ j, x j ≤ x i) = true := by
    exact ⟨i, by simp only [decide_eq_true_eq]; exact fun j => hmax j (Finset.mem_univ j)⟩
  simpa only [exactSlowNimMRuleKept, ha, Bool.false_eq_true, ↓reduceIte,
    decide_eq_true_eq] using found_property _ hf

private theorem a0_after {k b : ℕ} {z : Fin (k + 1) → ℕ}
    (hz : IsExactSlowNimBasicA1 k b z) (p : Fin (k + 1)) (hp : Even (z p)) :
    IsExactSlowNimBasicA0 k (b - 1) (slowANimAfter z (Finset.univ.erase p)) := by
  have hb := Nat.odd_iff.mp hz.2.2.1
  have hep := Nat.even_iff.mp hp
  have hpb := hz.2.1 p
  let d i := if i = p then 0 else 1
  have hd : d ≤ z := by
    intro i
    by_cases hi : i = p
    · simp [d, hi]
    · have ho := Nat.odd_iff.mp (odd_pile hz hp hi)
      simp only [d, hi, ite_false]
      omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs := sum_sub z d hd
    have hds : ∑ i, d i = k := by simp [d, Finset.sum_ite, Finset.filter_ne']
    have heq : (fun i => z i - d i) = slowANimAfter z (Finset.univ.erase p) := by
      funext i
      by_cases hi : i = p <;> simp [d, slowANimAfter, hi]
    change (∑ i, (fun i => z i - d i) i) + (∑ i, d i) = ∑ i, z i at hs
    rw [heq, hds, hz.1] at hs
    have hm : k * (b - 1) + k = k * b := by
      rw [← Nat.mul_add_one]
      congr 1
      omega
    exact Nat.add_right_cancel (hs.trans hm.symm)
  · intro i
    have hi := hz.2.1 i
    by_cases hip : i = p
    · simp only [slowANimAfter, hip, Finset.notMem_erase, ite_false]
      omega
    · simp only [slowANimAfter, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, hip,
        not_false_eq_true, ite_true]
      omega
  · rw [Nat.even_iff]
    omega
  · intro i
    by_cases hip : i = p
    · simpa [slowANimAfter, hip] using hp
    · have ho := Nat.odd_iff.mp (odd_pile hz hp hip)
      simp only [slowANimAfter, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, hip,
        not_false_eq_true, ite_true, Nat.even_iff]
      omega

private theorem lower_mmove {k b : ℕ} (hk : 0 < k) {x z : Fin (k + 1) → ℕ}
    (hzx : z ≤ x) (hz : IsExactSlowNimBasicA1 k b z) :
    b - 1 ≤ exactSlowNimBasicValue k (exactSlowNimMRuleMove x) := by
  classical
  obtain ⟨p, hp, _⟩ := hz.2.2.2
  let e := exactSlowNimMRuleKept x
  let v := slowANimAfter z (Finset.univ.erase p)
  have hv := a0_after hz p hp
  by_cases h : p = e ∨ z p < x p
  · have hvx : v ≤ exactSlowNimMRuleMove x := by
      intro i
      have hxi : z i ≤ x i := hzx i
      by_cases hip : i = p
      · subst i
        rcases h with h | h <;> simp only [v, exactSlowNimMRuleMove, slowANimAfter,
          Finset.mem_erase, Finset.mem_univ, and_true, ne_eq] <;> split_ifs <;> simp_all; omega
      · simp only [v, exactSlowNimMRuleMove, slowANimAfter, Finset.mem_erase,
          Finset.mem_univ, and_true, ne_eq, hip,
        not_false_eq_true, ite_true]
        split <;> omega
    exact le_value hk hvx (Or.inl hv)
  · have hpe : p ≠ e := by tauto
    have hpx : x p = z p := by have hxi : z p ≤ x p := hzx p; omega
    have hxp : Even (x p) := hpx ▸ hp
    have heven := kept_even x ⟨p, hxp⟩
    have hemin : x e ≤ x p := heven.2 p hxp
    have hep : e ≠ p := Ne.symm hpe
    have heo := Nat.odd_iff.mp (odd_pile hz hp hep)
    have hexi : z e ≤ x e := hzx e
    have hpb := hz.2.1 p
    have hpmod := Nat.even_iff.mp hp
    have hbmod := Nat.odd_iff.mp hz.2.2.1
    have hp2 : 2 ≤ z p := by omega
    have heb : z e + 1 ≤ b - 1 := by omega
    let w i := if i = p then z p - 2 else if i = e then z e + 1 else v i
    have hwx : w ≤ exactSlowNimMRuleMove x := by
      intro i
      rw [mmove_apply]
      change w i ≤ if i = e then x i else x i - 1
      have hxi : z i ≤ x i := hzx i
      by_cases hip : i = p
      · subst i
        simp only [w, ite_true, hpe, ite_false]
        omega
      · by_cases hie : i = e
        · subst i
          have hem : x e % 2 = 0 := Nat.even_iff.mp heven.1
          simp only [w, hep, ite_false, ite_true]
          omega
        · simp only [w, hip, hie, ite_false, v, after_erase]
          omega
    apply le_value hk hwx (Or.inl ?_)
    refine ⟨?_, ?_, hv.2.2.1, ?_⟩
    · have heq (i : Fin (k + 1)) : w i + (if i = p then 2 else 0) =
          v i + (if i = e then 2 else 0) := by
        by_cases hip : i = p
        · simp [w, hip, v, slowANimAfter, hpe]
          omega
        · by_cases hie : i = e
          · simp [w, hie, hep, v, slowANimAfter]
            omega
          · simp [w, hip, hie]
      have hs := Finset.sum_congr (s₁ := Finset.univ) rfl fun i _ => heq i
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hs
      have hvs : ∑ i, v i = k * (b - 1) := hv.1
      omega
    · intro i
      by_cases hip : i = p
      · simp only [w, hip, ite_true]
        omega
      · by_cases hie : i = e
        · simpa [w, hie, hep] using heb
        · simpa [w, hip, hie] using hv.2.1 i
    · intro i
      by_cases hip : i = p
      · simp only [w, hip, ite_true, Nat.even_iff]
        omega
      · by_cases hie : i = e
        · simp only [w, hie, hep, ite_false, ite_true, Nat.even_iff]
          omega
        · simpa [w, hip, hie] using hv.2.2.2 i

private theorem sum_add_except {k : ℕ} (y : Fin (k + 1) → ℕ) (p : Fin (k + 1)) :
    (∑ i, (y i + if i = p then 0 else 1)) = (∑ i, y i) + k := by
  simp [Finset.sum_add_distrib, Finset.sum_ite, Finset.filter_ne']

private theorem lift_a1 {k b : ℕ} {x y : Fin (k + 1) → ℕ}
    (hyx : y ≤ exactSlowNimMRuleMove x) (hy : IsExactSlowNimBasicA1 k b y)
    (p : Fin (k + 1)) (hp : Even (y p))
    (h : p = exactSlowNimMRuleKept x ∨ y (exactSlowNimMRuleKept x) <
      x (exactSlowNimMRuleKept x)) :
    ∃ w ≤ x, IsExactSlowNimBasicA0 k (b + 1) w := by
  classical
  let w i := y i + if i = p then 0 else 1
  refine ⟨w, ?_, ?_, ?_, hy.2.2.1.add_odd (by decide : Odd 1), ?_⟩
  · intro i
    have hxi : y i ≤ exactSlowNimMRuleMove x i := hyx i
    rw [mmove_apply] at hxi
    by_cases hip : i = p
    · subst i
      simp only [w, ite_true, Nat.add_zero]
      split at hxi <;> omega
    · simp only [w, hip, ite_false]
      by_cases hie : i = exactSlowNimMRuleKept x
      · subst i
        rcases h with h | h
        · exact (hip h.symm).elim
        · omega
      · simp only [hie, ite_false] at hxi
        have ho := Nat.odd_iff.mp (odd_pile hy hp hip)
        omega
  · have hs := sum_add_except y p
    change (∑ i, w i) = (∑ i, y i) + k at hs
    rw [hs, hy.1, Nat.mul_add_one]
  · intro i
    have hiy : y i ≤ b := hy.2.1 i
    simp only [w]
    split <;> omega
  · intro i
    by_cases hip : i = p
    · simpa [w, hip] using hp
    · simpa [w, hip] using (odd_pile hy hp hip).add_odd (by decide : Odd 1)

private theorem lift_all_odd {k b : ℕ} (hk : 0 < k) {x y : Fin (k + 1) → ℕ}
    (hyx : y ≤ exactSlowNimMRuleMove x) (hy : IsExactSlowNimBasicA1 k b y)
    (p : Fin (k + 1)) (hp : Even (y p))
    (hpe : p ≠ exactSlowNimMRuleKept x)
    (hey : y (exactSlowNimMRuleKept x) = x (exactSlowNimMRuleKept x))
    (hodd : ∀ i, Odd (x i))
    (hmax : ∀ i, x i ≤ x (exactSlowNimMRuleKept x)) :
    b + 1 ≤ exactSlowNimBasicValue k x := by
  classical
  let e := exactSlowNimMRuleKept x
  have hep : e ≠ p := Ne.symm hpe
  have heo := Nat.odd_iff.mp (odd_pile hy hp hep)
  have hpmod := Nat.even_iff.mp hp
  have hpb : y p ≤ b := hy.2.1 p
  have hb := Nat.odd_iff.mp hy.2.2.1
  have heb : y e ≤ b := hy.2.1 e
  have hye : y e = x e := hey
  let v i := y i + if i = p then 0 else 1
  have hvs : (∑ i, v i) = k * (b + 1) := by
    change (∑ i, (y i + if i = p then 0 else 1)) = _
    rw [sum_add_except, hy.1, Nat.mul_add_one]
  have hve : v e = y e + 1 := by simp [v, hep]
  have hva (i : Fin (k + 1)) : Even (v i) := by
    by_cases hip : i = p
    · simpa [v, hip] using hp
    · simpa [v, hip] using (odd_pile hy hp hip).add_odd (by decide : Odd 1)
  have hvb (i : Fin (k + 1)) : v i ≤ b + 1 := by
    have hiy : y i ≤ b := hy.2.1 i
    simp only [v]
    split <;> omega
  have hvx (i : Fin (k + 1)) (hi : i ≠ e) : v i ≤ x i := by
    have hxi : y i ≤ exactSlowNimMRuleMove x i := hyx i
    rw [mmove_apply] at hxi
    change y i ≤ if i = e then x i else x i - 1 at hxi
    simp only [hi, ite_false] at hxi
    simp only [v]
    have ho := Nat.odd_iff.mp (hodd i)
    split <;> omega
  by_cases hr : ∃ r, r ≠ e ∧ v r + 2 ≤ x r
  · obtain ⟨r, hre, hr⟩ := hr
    let w i := if i = e then v e - 2 else if i = r then v r + 2 else v i
    have hwx : w ≤ x := by
      intro i
      by_cases hie : i = e
      · simp only [w, hie, ite_true, hve]
        omega
      · by_cases hir : i = r
        · simpa [w, hir, hre] using hr
        · simpa [w, hie, hir] using hvx i hie
    apply le_value hk hwx (Or.inl ?_)
    refine ⟨?_, ?_, hy.2.2.1.add_odd (by decide : Odd 1), ?_⟩
    · have heq (i : Fin (k + 1)) : w i + (if i = e then 2 else 0) =
          v i + (if i = r then 2 else 0) := by
        by_cases hie : i = e
        · simp only [w, hie, ite_true, Ne.symm hre, ite_false, Nat.add_zero, hve]
          omega
        · by_cases hir : i = r
          · simp [w, hir, hre]
          · simp [w, hie, hir]
      have hs := Finset.sum_congr (s₁ := Finset.univ) rfl fun i _ => heq i
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hs
      exact (Nat.add_right_cancel hs).trans hvs
    · intro i
      by_cases hie : i = e
      · simp only [w, hie, ite_true]
        have := hvb e
        omega
      · by_cases hir : i = r
        · have hrb := (hwx r).trans ((hmax r).trans_eq hye.symm)
          simpa [w, hir, hre] using hrb.trans (Nat.le_succ_of_le heb)
        · simpa [w, hie, hir] using hvb i
    · intro i
      by_cases hie : i = e
      · have hemod := Nat.even_iff.mp (hva e)
        simp only [w, hie, ite_true, Nat.even_iff]
        rw [hve] at hemod ⊢
        omega
      · by_cases hir : i = r
        · simpa [w, hir, hre] using (hva r).add (by decide : Even 2)
        · simpa [w, hie, hir] using hva i
  · have hxeq (i : Fin (k + 1)) (hi : i ≠ e) : x i = v i + 1 := by
      have hvi := hvx i hi
      have hn : ¬ v i + 2 ≤ x i := fun h => hr ⟨i, hi, h⟩
      have ho := Nat.odd_iff.mp (hodd i)
      have he := Nat.even_iff.mp (hva i)
      omega
    apply le_value hk le_rfl (Or.inr (Or.inr ?_))
    refine ⟨?_, ?_, hy.2.2.1.add_odd (by decide : Odd 1), hodd⟩
    · have heq (i : Fin (k + 1)) : x i + (if i = e then 2 else 0) +
          (if i = p then 1 else 0) = y i + 2 := by
        by_cases hie : i = e
        · simp [hie, hye, hep]
        · rw [hxeq i hie]
          by_cases hip : i = p
          · subst i
            simp [v, Ne.symm hep]
          · simp [v, hip, hie]
      have hs := Finset.sum_congr (s₁ := Finset.univ) rfl fun i _ => heq i
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
      rw [hy.1] at hs
      rw [Nat.mul_add_one]
      omega
    · intro i
      exact Nat.lt_succ_of_le ((hmax i).trans (hye.symm.le.trans heb))

private theorem upper_mmove {k : ℕ} (hk : 0 < k) (x : Fin (k + 1) → ℕ)
    (hb : Odd (exactSlowNimBasicValue k x)) :
    exactSlowNimBasicValue k (exactSlowNimMRuleMove x) ≤ exactSlowNimBasicValue k x - 1 := by
  classical
  have hqx : exactSlowNimMRuleMove x ≤ x := after_le x _
  have hmono := value_mono hk hqx
  by_contra hn
  have heq : exactSlowNimBasicValue k (exactSlowNimMRuleMove x) =
      exactSlowNimBasicValue k x := by omega
  obtain ⟨y, hyx, hy⟩ := exists_supports_exactSlowNimBasicValue k (exactSlowNimMRuleMove x)
  rw [heq] at hy
  have hy1 : IsExactSlowNimBasicA1 k (exactSlowNimBasicValue k x) y := by
    rcases hy with hy | hy | hy
    · exact ((Nat.not_even_iff_odd.mpr hb) hy.2.2.1).elim
    · exact hy
    · exact ((Nat.not_even_iff_odd.mpr hb) hy.2.2.1).elim
  obtain ⟨p, hp, _⟩ := hy1.2.2.2
  by_cases h : p = exactSlowNimMRuleKept x ∨ y (exactSlowNimMRuleKept x) <
      x (exactSlowNimMRuleKept x)
  · obtain ⟨w, hwx, hw⟩ := lift_a1 hyx hy1 p hp h
    exact (Nat.not_succ_le_self _) (le_value hk hwx (Or.inl hw))
  · have hpe : p ≠ exactSlowNimMRuleKept x := by tauto
    have hey : y (exactSlowNimMRuleKept x) = x (exactSlowNimMRuleKept x) := by
      have hle : y (exactSlowNimMRuleKept x) ≤ x (exactSlowNimMRuleKept x) :=
        (hyx.trans hqx) (exactSlowNimMRuleKept x)
      omega
    have heo : Odd (x (exactSlowNimMRuleKept x)) :=
      hey ▸ odd_pile hy1 hp (Ne.symm hpe)
    have hne : ¬ ∃ i, Even (x i) := by
      intro hex
      exact (Nat.not_even_iff_odd.mpr heo) (kept_even x hex).1
    have hodd (i : Fin (k + 1)) : Odd (x i) :=
      Nat.not_even_iff_odd.mp fun hi => hne ⟨i, hi⟩
    exact (Nat.not_succ_le_self _)
      (lift_all_odd hk hyx hy1 p hp hpe hey hodd (kept_max x hne))

/-- **Moves at a position supported by an (A1) basic vector (Lemma 3).** Let $k \ge 1$, let
$B$ be the basic-vector value on $\mathbb{N}^{k+1}$, and let $x, z \in \mathbb{N}^{k+1}$ with
$z \le x$ componentwise, where $z$ is a basic vector of type (A1) with parameter $B(x)$. Then
every option $x'$ of $x$ in Slow$\{k\}$-Nim on $k + 1$ stacks (a move removes one token from
each of exactly $k$ nonempty stacks) satisfies $B(x') \ge B(x) - 2$, and the position $x''$
obtained from $x$ by the M-move satisfies $B(x'') = B(x) - 1$, where subtraction is truncated
at $0$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Lemma 3. -/
public theorem exactSlowNimBasicValue_of_supports_basicA1 {k : ℕ} (hk : 0 < k)
    (x z : Fin (k + 1) → ℕ) (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicA1 k (exactSlowNimBasicValue k x) z) :
    (∀ x' ∈ slowANimMoves {k} x, exactSlowNimBasicValue k x - 2 ≤ exactSlowNimBasicValue k x') ∧
      exactSlowNimBasicValue k (exactSlowNimMRuleMove x) = exactSlowNimBasicValue k x - 1
    := by
  constructor
  · intro x' hx'
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hx'
    exact lower_options hk hzx hz s
  · exact le_antisymm (upper_mmove hk x hz.2.2.1) (lower_mmove hk hzx hz)

end

end MetaMathlibExt
