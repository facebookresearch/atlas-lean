/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Function
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Nat.SuccPred

@[expose] public section

namespace MetaMathlibExt

/-! # Minimal descent permutations
-/

private def descents (f : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  Finset.filter (fun i => f (i + 1) < f i) (Finset.Icc 1 (n - 1))

private lemma exists_descent_between (f : ℕ → ℕ) (a b : ℕ) (hab : a < b)
    (hba : f b < f a) :
    ∃ j, a ≤ j ∧ j < b ∧ f (j + 1) < f j := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hlast : f (b + 1) < f b
    · exact ⟨b, by omega, by omega, hlast⟩
    · have hle : f b ≤ f (b + 1) := by omega
      by_cases hab' : a = b
      · subst a
        omega
      · have hab' : a < b := by omega
        obtain ⟨j, haj, hjb, hd⟩ := ih hab' (lt_of_le_of_lt hle hba)
        exact ⟨j, haj, by omega, hd⟩

private lemma descent_card_le_of_pattern (n k : ℕ) (f g φ : ℕ → ℕ)
    (hmap : Set.MapsTo φ (Set.Icc 1 k) (Set.Icc 1 n))
    (hinc : ∀ a ∈ Set.Icc 1 k, ∀ b ∈ Set.Icc 1 k, a < b → φ a < φ b)
    (hpat : ∀ a ∈ Set.Icc 1 k, ∀ b ∈ Set.Icc 1 k,
      (g a < g b ↔ f (φ a) < f (φ b))) :
    (descents g k).card ≤ (descents f n).card := by
  classical
  have hasDesc : ∀ i ∈ descents g k,
      ∃ j, φ i ≤ j ∧ j < φ (i + 1) ∧ f (j + 1) < f j := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hiI : i ∈ Finset.Icc 1 (k - 1) := hi'.1
    have hiD : g (i + 1) < g i := hi'.2
    have hib : 1 ≤ i ∧ i ≤ k - 1 := Finset.mem_Icc.mp hiI
    have hii : i ∈ Set.Icc 1 k := ⟨hib.1, by omega⟩
    have his : i + 1 ∈ Set.Icc 1 k := ⟨by omega, by omega⟩
    exact exists_descent_between f (φ i) (φ (i + 1))
      (hinc i hii (i + 1) his (by omega)) ((hpat (i + 1) his i hii).mp hiD)
  let pick : ℕ → ℕ := fun i =>
    if hi : i ∈ descents g k then
      Nat.find (hasDesc i hi)
    else 0
  apply Finset.card_le_card_of_injOn pick
  · intro i hi
    have hiF : i ∈ descents g k := hi
    have hi' := Finset.mem_filter.mp hiF
    have hib := Finset.mem_Icc.mp hi'.1
    have hp := Nat.find_spec (hasDesc i hiF)
    have hleft := hmap ⟨hib.1, by omega⟩
    have hright := hmap (show i + 1 ∈ Set.Icc 1 k from ⟨by omega, by omega⟩)
    simp only [Set.mem_Icc] at hleft hright
    rw [show pick i = Nat.find (hasDesc i hiF) by simp [pick, hiF]]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hp.2.2⟩
  · intro i hi j hj heq
    have hiF : i ∈ descents g k := hi
    have hjF : j ∈ descents g k := hj
    have hi' := Finset.mem_filter.mp hiF
    have hj' := Finset.mem_filter.mp hjF
    have hib := Finset.mem_Icc.mp hi'.1
    have hjb := Finset.mem_Icc.mp hj'.1
    have hpi := Nat.find_spec (hasDesc i hiF)
    have hpj := Nat.find_spec (hasDesc j hjF)
    rw [show pick i = Nat.find (hasDesc i hiF) by simp [pick, hiF]] at heq
    rw [show pick j = Nat.find (hasDesc j hjF) by simp [pick, hjF]] at heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hbetween : φ (i + 1) ≤ φ j := by
        rcases lt_or_eq_of_le (show i + 1 ≤ j by omega) with hlt | he
        · exact (hinc (i + 1) ⟨by omega, by omega⟩ j ⟨hjb.1, by omega⟩ hlt).le
        · exact (congrArg φ he).le
      omega
    · have hbetween : φ (j + 1) ≤ φ i := by
        rcases lt_or_eq_of_le (show j + 1 ≤ i by omega) with hlt | he
        · exact (hinc (j + 1) ⟨by omega, by omega⟩ i ⟨hib.1, by omega⟩ hlt).le
        · exact (congrArg φ he).le
      omega

private def skipIndex (j a : ℕ) : ℕ :=
  if a < j then a else a + 1

private def eraseValue (r x : ℕ) : ℕ :=
  if x < r then x else x - 1

private def deletePerm (f : ℕ → ℕ) (j a : ℕ) : ℕ :=
  eraseValue (f j) (f (skipIndex j a))

private def unskipIndex (j x : ℕ) : ℕ :=
  if x < j then x else x - 1

private lemma skip_unskip (j x : ℕ) (hx : x ≠ j) (hxp : 0 < x) :
    skipIndex j (unskipIndex j x) = x := by
  by_cases h : x < j
  · simp [unskipIndex, skipIndex, h]
  · have hjx : j < x := by omega
    have hnlt : ¬ x - 1 < j := by omega
    simp [unskipIndex, skipIndex, h, hnlt]
    omega

private lemma unskip_mem (n j x : ℕ) (hj : j ∈ Set.Icc 1 n)
    (hx : x ∈ Set.Icc 1 n) (hne : x ≠ j) :
    unskipIndex j x ∈ Set.Icc 1 (n - 1) := by
  simp only [Set.mem_Icc] at hj hx ⊢
  simp only [unskipIndex]
  split <;> omega

private lemma unskip_lt_iff (j x y : ℕ) (_hx : x ≠ j) (hy : y ≠ j)
    (hxp : 0 < x) (hyp : 0 < y) :
    unskipIndex j x < unskipIndex j y ↔ x < y := by
  simp only [unskipIndex]
  split <;> split <;> omega

private lemma skipIndex_mem (n j a : ℕ) (hj : j ∈ Set.Icc 1 n)
    (ha : a ∈ Set.Icc 1 (n - 1)) :
    skipIndex j a ∈ Set.Icc 1 n := by
  simp only [Set.mem_Icc] at hj ha ⊢
  simp only [skipIndex]
  split <;> omega

private lemma skipIndex_ne (j a : ℕ) : skipIndex j a ≠ j := by
  simp only [skipIndex]
  split <;> omega

private lemma skipIndex_strictMonoOn (n j : ℕ) :
    ∀ a ∈ Set.Icc 1 (n - 1), ∀ b ∈ Set.Icc 1 (n - 1), a < b →
      skipIndex j a < skipIndex j b := by
  intro a ha b hb hab
  simp only [skipIndex]
  split <;> split <;> omega

private lemma eraseValue_lt_iff (r x y : ℕ) (hr : 0 < r) (_hx : x ≠ r) (hy : y ≠ r) :
    eraseValue r x < eraseValue r y ↔ x < y := by
  simp only [eraseValue]
  split <;> split <;> omega

private lemma deletePerm_bijOn (n j : ℕ) (σ : ℕ → ℕ)
    (hσ : Set.BijOn σ (Set.Icc 1 n) (Set.Icc 1 n)) (hj : j ∈ Set.Icc 1 n) :
    Set.BijOn (deletePerm σ j) (Set.Icc 1 (n - 1)) (Set.Icc 1 (n - 1)) := by
  have hrangej := hσ.mapsTo hj
  simp only [Set.mem_Icc] at hrangej
  apply Set.BijOn.mk
  · intro a ha
    have hskip := skipIndex_mem n j a hj ha
    have hx := hσ.mapsTo hskip
    have hnepos : skipIndex j a ≠ j := skipIndex_ne j a
    have hneval : σ (skipIndex j a) ≠ σ j := fun h =>
      hnepos (hσ.injOn hskip hj h)
    simp only [Set.mem_Icc] at ha hx ⊢
    simp only [deletePerm, eraseValue]
    split <;> omega
  · intro a ha b hb heq
    have hsa := skipIndex_mem n j a hj ha
    have hsb := skipIndex_mem n j b hj hb
    have hnea : σ (skipIndex j a) ≠ σ j := fun h =>
      skipIndex_ne j a (hσ.injOn hsa hj h)
    have hneb : σ (skipIndex j b) ≠ σ j := fun h =>
      skipIndex_ne j b (hσ.injOn hsb hj h)
    have heqv : σ (skipIndex j a) = σ (skipIndex j b) := by
      simp only [deletePerm, eraseValue] at heq
      split at heq <;> split at heq <;> omega
    have heqs := hσ.injOn hsa hsb heqv
    simp only [skipIndex] at heqs
    split at heqs <;> split at heqs <;> omega
  · intro y hy
    have hjv := hσ.mapsTo hj
    simp only [Set.mem_Icc] at hj hy hjv
    let x := if y < σ j then y else y + 1
    have hx : x ∈ Set.Icc 1 n := by
      simp only [Set.mem_Icc, x]
      split <;> omega
    obtain ⟨p, hp, hsp⟩ := hσ.surjOn hx
    simp only [Set.mem_Icc] at hp
    have hpj : p ≠ j := by
      intro h
      subst p
      simp only [x] at hsp
      split at hsp <;> omega
    let a := if p < j then p else p - 1
    have ha : a ∈ Set.Icc 1 (n - 1) := by
      simp only [Set.mem_Icc, a]
      split <;> omega
    refine ⟨a, ha, ?_⟩
    have hskip : skipIndex j a = p := by
      by_cases hp_lt : p < j
      · simp [a, skipIndex, hp_lt]
      · have hjp : j < p := by omega
        have hnlt : ¬ p - 1 < j := by omega
        simp [a, skipIndex, hp_lt, hnlt]
        omega
    simp only [deletePerm, hskip, hsp, x, eraseValue]
    by_cases hylt : y < σ j
    · simp [hylt]
    · have hnlt : ¬ y + 1 < σ j := by omega
      simp [hylt, hnlt]

private lemma deletePerm_pattern (n j : ℕ) (σ : ℕ → ℕ)
    (hσ : Set.BijOn σ (Set.Icc 1 n) (Set.Icc 1 n)) (hj : j ∈ Set.Icc 1 n) :
    Set.MapsTo (skipIndex j) (Set.Icc 1 (n - 1)) (Set.Icc 1 n) ∧
      (∀ a ∈ Set.Icc 1 (n - 1), ∀ b ∈ Set.Icc 1 (n - 1), a < b →
        skipIndex j a < skipIndex j b) ∧
      ∀ a ∈ Set.Icc 1 (n - 1), ∀ b ∈ Set.Icc 1 (n - 1),
        (deletePerm σ j a < deletePerm σ j b ↔
          σ (skipIndex j a) < σ (skipIndex j b)) := by
  refine ⟨?_, skipIndex_strictMonoOn n j, ?_⟩
  · exact fun _ ha => skipIndex_mem n j _ hj ha
  · intro a ha b hb
    have hsa := skipIndex_mem n j a hj ha
    have hsb := skipIndex_mem n j b hj hb
    have hr := hσ.mapsTo hj
    have hnea : σ (skipIndex j a) ≠ σ j := fun h =>
      skipIndex_ne j a (hσ.injOn hsa hj h)
    have hneb : σ (skipIndex j b) ≠ σ j := fun h =>
      skipIndex_ne j b (hσ.injOn hsb hj h)
    exact eraseValue_lt_iff (σ j) (σ (skipIndex j a)) (σ (skipIndex j b)) hr.1 hnea hneb

private lemma delete_descent_iff_skip (n j a : ℕ) (σ : ℕ → ℕ)
    (hσ : Set.BijOn σ (Set.Icc 1 n) (Set.Icc 1 n)) (hj : j ∈ Set.Icc 1 n)
    (ha : a ∈ Finset.Icc 1 ((n - 1) - 1))
    (hbridge : 1 < j → j < n →
      (σ (j + 1) < σ (j - 1) ↔ σ j < σ (j - 1))) :
    (deletePerm σ j (a + 1) < deletePerm σ j a ↔
      σ (skipIndex j a + 1) < σ (skipIndex j a)) := by
  have hab := Finset.mem_Icc.mp ha
  have haS : a ∈ Set.Icc 1 (n - 1) := ⟨hab.1, by omega⟩
  have hasS : a + 1 ∈ Set.Icc 1 (n - 1) := ⟨by omega, by omega⟩
  rw [(deletePerm_pattern n j σ hσ hj).2.2 (a + 1) hasS a haS]
  by_cases hlt : a + 1 < j
  · have halt : a < j := by omega
    simp [skipIndex, hlt, halt]
  · by_cases heq : a + 1 = j
    · have hjlt : j < n := by
        simp only [Set.mem_Icc] at hj
        omega
      have hjone : 1 < j := by omega
      have hb := hbridge hjone hjlt
      subst j
      simpa [skipIndex] using hb
    · have hjle : j ≤ a := by omega
      have hnaj : ¬ a < j := by omega
      have hnasj : ¬ a + 1 < j := by omega
      simp [skipIndex, hnaj, hnasj]

private lemma delete_card_eq_of_left_bridge (n j : ℕ) (σ : ℕ → ℕ)
    (hσ : Set.BijOn σ (Set.Icc 1 n) (Set.Icc 1 n)) (hj : j ∈ Set.Icc 1 n)
    (hjlt : j < n)
    (hskip : j ∉ descents σ n)
    (hbridge : 1 < j → j < n →
      (σ (j + 1) < σ (j - 1) ↔ σ j < σ (j - 1))) :
    (descents (deletePerm σ j) (n - 1)).card = (descents σ n).card := by
  classical
  apply Finset.card_bij (fun a _ => skipIndex j a)
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hab := Finset.mem_Icc.mp ha'.1
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      simp only [Set.mem_Icc] at hj
      simp only [skipIndex]
      split <;> omega
    · exact (delete_descent_iff_skip n j a σ hσ hj ha'.1 hbridge).mp ha'.2
  · intro a ha b hb heq
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have hab := Finset.mem_Icc.mp ha'.1
    have hbb := Finset.mem_Icc.mp hb'.1
    simp only [skipIndex] at heq
    split at heq <;> split at heq <;> omega
  · intro b hb
    have hb' := Finset.mem_filter.mp hb
    have hbb := Finset.mem_Icc.mp hb'.1
    have hbj : b ≠ j := by
      intro h
      subst b
      exact hskip hb
    let a := if b < j then b else b - 1
    have ha_bounds : a ∈ Finset.Icc 1 ((n - 1) - 1) := by
      apply Finset.mem_Icc.mpr
      simp only [Set.mem_Icc] at hj
      simp only [a]
      split <;> omega
    have hsa : skipIndex j a = b := by
      by_cases hbjlt : b < j
      · simp [a, skipIndex, hbjlt]
      · have hjb : j < b := by omega
        have hnlt : ¬ b - 1 < j := by omega
        simp [a, skipIndex, hbjlt, hnlt]
        omega
    have hdel : deletePerm σ j (a + 1) < deletePerm σ j a :=
      (delete_descent_iff_skip n j a σ hσ hj ha_bounds hbridge).mpr (by
        rw [hsa]
        exact hb'.2)
    exact ⟨a, Finset.mem_filter.mpr ⟨ha_bounds, hdel⟩, hsa⟩

private lemma delete_descent_iff_skipPrev (n j a : ℕ) (σ : ℕ → ℕ)
    (hσ : Set.BijOn σ (Set.Icc 1 n) (Set.Icc 1 n)) (hj : j ∈ Set.Icc 1 n)
    (hjone : 1 < j) (ha : a ∈ Finset.Icc 1 ((n - 1) - 1))
    (hbridge : j < n →
      (σ (j + 1) < σ (j - 1) ↔ σ (j + 1) < σ j)) :
    (deletePerm σ j (a + 1) < deletePerm σ j a ↔
      σ (skipIndex (j - 1) a + 1) < σ (skipIndex (j - 1) a)) := by
  have hab := Finset.mem_Icc.mp ha
  have haS : a ∈ Set.Icc 1 (n - 1) := ⟨hab.1, by omega⟩
  have hasS : a + 1 ∈ Set.Icc 1 (n - 1) := ⟨by omega, by omega⟩
  rw [(deletePerm_pattern n j σ hσ hj).2.2 (a + 1) hasS a haS]
  by_cases hlt : a < j - 1
  · have halt : a < j := by omega
    have haslt : a + 1 < j := by omega
    simp [skipIndex, hlt, halt, haslt]
  · by_cases heq : a = j - 1
    · have hjlt : j < n := by
        simp only [Set.mem_Icc] at hj
        omega
      have hb := hbridge hjlt
      have haj : a < j := by omega
      have hnasj : ¬ a + 1 < j := by omega
      have hnaq : ¬ a < j - 1 := hlt
      subst a
      have hjsub : j - 1 + 1 = j := by omega
      have hnltj : ¬ j - 1 + 1 < j := by omega
      have hjpos : 0 < j := by omega
      simpa [skipIndex, hjone, hjpos, hjsub, hnltj] using hb
    · have hja : j ≤ a := by omega
      have hna : ¬ a < j := by omega
      have hnas : ¬ a + 1 < j := by omega
      have hnaq : ¬ a < j - 1 := by omega
      simp [skipIndex, hna, hnas, hnaq]

private lemma delete_card_eq_of_right_bridge (n j : ℕ) (σ : ℕ → ℕ)
    (hσ : Set.BijOn σ (Set.Icc 1 n) (Set.Icc 1 n)) (hj : j ∈ Set.Icc 1 n)
    (hjone : 1 < j) (hskip : j - 1 ∉ descents σ n)
    (hbridge : j < n →
      (σ (j + 1) < σ (j - 1) ↔ σ (j + 1) < σ j)) :
    (descents (deletePerm σ j) (n - 1)).card = (descents σ n).card := by
  classical
  let q := j - 1
  have hqpos : 0 < q := by simp only [q]; omega
  have hqlt : q < n := by
    simp only [Set.mem_Icc] at hj
    simp only [q]
    omega
  apply Finset.card_bij (fun a _ => skipIndex q a)
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hab := Finset.mem_Icc.mp ha'.1
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      simp only [skipIndex]
      split <;> omega
    · simpa only [q] using
        (delete_descent_iff_skipPrev n j a σ hσ hj hjone ha'.1 hbridge).mp ha'.2
  · intro a ha b hb heq
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have hab := Finset.mem_Icc.mp ha'.1
    have hbb := Finset.mem_Icc.mp hb'.1
    simp only [skipIndex] at heq
    split at heq <;> split at heq <;> omega
  · intro b hb
    have hb' := Finset.mem_filter.mp hb
    have hbb := Finset.mem_Icc.mp hb'.1
    have hbq : b ≠ q := by
      intro h
      subst b
      exact hskip hb
    let a := if b < q then b else b - 1
    have ha_bounds : a ∈ Finset.Icc 1 ((n - 1) - 1) := by
      apply Finset.mem_Icc.mpr
      simp only [a]
      split <;> omega
    have hsa : skipIndex q a = b := by
      by_cases hbq_lt : b < q
      · simp [a, skipIndex, hbq_lt]
      · have hqb : q < b := by omega
        have hnlt : ¬ b - 1 < q := by omega
        simp [a, skipIndex, hbq_lt, hnlt]
        omega
    have hdel : deletePerm σ j (a + 1) < deletePerm σ j a :=
      (delete_descent_iff_skipPrev n j a σ hσ hj hjone ha_bounds hbridge).mpr (by
        simpa only [q] using (show σ (skipIndex q a + 1) < σ (skipIndex q a) by
          rw [hsa]
          exact hb'.2))
    exact ⟨a, Finset.mem_filter.mpr ⟨ha_bounds, hdel⟩, hsa⟩

private lemma delete_card_lt_of_diamonds (n j : ℕ) (σ : ℕ → ℕ)
    (hσ : Set.BijOn σ (Set.Icc 1 n) (Set.Icc 1 n)) (hj : j ∈ Set.Icc 1 n)
    (hn : 1 < n)
    (hdiamond : ∀ i ∈ Finset.Icc 1 (n - 1), σ i < σ (i + 1) →
      2 ≤ i ∧ i ≤ n - 2 ∧
        (σ i < σ (i - 1) ∧ σ (i - 1) < σ (i + 2) ∧ σ (i + 2) < σ (i + 1) ∨
          σ i < σ (i + 2) ∧ σ (i + 2) < σ (i - 1) ∧ σ (i - 1) < σ (i + 1))) :
    (descents (deletePerm σ j) (n - 1)).card < (descents σ n).card := by
  classical
  let S := descents (deletePerm σ j) (n - 1)
  let T := descents σ n
  have hmap : ∀ a ∈ S, skipIndex j a ∈ T := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hab := Finset.mem_Icc.mp ha'.1
    have haS : a ∈ Set.Icc 1 (n - 1) := ⟨hab.1, by omega⟩
    have hasS : a + 1 ∈ Set.Icc 1 (n - 1) := ⟨by omega, by omega⟩
    have hcmp := ((deletePerm_pattern n j σ hσ hj).2.2
      (a + 1) hasS a haS).mp ha'.2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      simp only [Set.mem_Icc] at hj
      simp only [skipIndex]
      split <;> omega
    · by_cases hlt : a + 1 < j
      · have halt : a < j := by omega
        simpa [skipIndex, hlt, halt] using hcmp
      · by_cases heq : a + 1 = j
        · by_contra hnot
          have hjone : 1 < j := by omega
          have hjlt : j < n := by omega
          have hamem : a ∈ Finset.Icc 1 (n - 1) := by
            apply Finset.mem_Icc.mpr
            omega
          have hneq : σ a ≠ σ (a + 1) := by
            intro h
            have haN : a ∈ Set.Icc 1 n := ⟨by omega, by omega⟩
            have hasN : a + 1 ∈ Set.Icc 1 n := ⟨by omega, by omega⟩
            have := hσ.injOn haN hasN h
            omega
          have haj : a = j - 1 := by omega
          have hjsub : j - 1 + 1 = j := by omega
          have hneq' : σ (j - 1) ≠ σ j := by simpa [haj, hjsub] using hneq
          have hnot' : ¬ σ j < σ (j - 1) := by
            simpa [skipIndex, haj, hjone, show 0 < j by omega, hjsub] using hnot
          have hold : σ (j - 1) < σ j := by
            omega
          have hd := hdiamond (j - 1) (by
            apply Finset.mem_Icc.mpr
            omega) (by simpa [show j - 1 + 1 = j by omega] using hold)
          have hcross : σ (j - 1) < σ (j + 1) := by
            rcases hd.2.2 with h | h
            · exact lt_trans h.1 (by
                simpa [show j - 1 + 2 = j + 1 by omega] using h.2.1)
            · simpa [show j - 1 + 2 = j + 1 by omega] using h.1
          have hcmp' : σ (j + 1) < σ (j - 1) := by
            simpa [skipIndex, haj, hjone, show 0 < j by omega, hjsub] using hcmp
          exact (not_lt_of_ge hcross.le) hcmp'
        · have hja : j ≤ a := by omega
          have hna : ¬ a < j := by omega
          have hnas : ¬ a + 1 < j := by omega
          simpa [skipIndex, hna, hnas] using hcmp
  have hinj : Set.InjOn (skipIndex j) (↑S : Set ℕ) := by
    intro a ha b hb heq
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have hab := Finset.mem_Icc.mp ha'.1
    have hbb := Finset.mem_Icc.mp hb'.1
    simp only [skipIndex] at heq
    split at heq <;> split at heq <;> omega
  have hsubset : S.image (skipIndex j) ⊆ T := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact hmap a ha
  have hwitness : ∃ b, b ∈ T ∧ b ∉ S.image (skipIndex j) := by
    simp only [Set.mem_Icc] at hj
    by_cases hjlt : j < n
    · have hjN : j ∈ Set.Icc 1 n := ⟨hj.1, hj.2⟩
      have hjsN : j + 1 ∈ Set.Icc 1 n := ⟨by omega, by omega⟩
      have hneq : σ j ≠ σ (j + 1) := fun h => by
        have := hσ.injOn hjN hjsN h
        omega
      by_cases hdes : σ (j + 1) < σ j
      · refine ⟨j, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj.1, by omega⟩, hdes⟩
        · intro him
          obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp him
          have ha' := Finset.mem_filter.mp ha
          have hab := Finset.mem_Icc.mp ha'.1
          simp only [skipIndex] at heq
          split at heq <;> omega
      · have hasc : σ j < σ (j + 1) := by omega
        have hd := hdiamond j (Finset.mem_Icc.mpr ⟨hj.1, by omega⟩) hasc
        have hjone : 1 < j := by omega
        have hleftdesc : σ j < σ (j - 1) := by rcases hd.2.2 with h | h <;> omega
        refine ⟨j - 1, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
          simpa [show j - 1 + 1 = j by omega] using hleftdesc
        · intro him
          obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp him
          have ha' := Finset.mem_filter.mp ha
          have hab := Finset.mem_Icc.mp ha'.1
          have hae : a = j - 1 := by
            simp only [skipIndex] at heq
            split at heq <;> omega
          subst a
          have hdel := ha'.2
          have haS : j - 1 ∈ Set.Icc 1 (n - 1) := ⟨by omega, by omega⟩
          have hasS : j - 1 + 1 ∈ Set.Icc 1 (n - 1) := ⟨by omega, by omega⟩
          have hcmp := ((deletePerm_pattern n j σ hσ ⟨hj.1, hj.2⟩).2.2
            (j - 1 + 1) hasS (j - 1) haS).mp hdel
          have hcross : σ (j - 1) < σ (j + 1) := by
            rcases hd.2.2 with h | h
            · exact lt_trans h.2.1 h.2.2
            · exact h.2.2
          have hcmp' : σ (j + 1) < σ (j - 1) := by
            simpa [skipIndex, hjone, show 0 < j by omega,
              show j - 1 + 1 = j by omega] using hcmp
          exact (not_lt_of_ge hcross.le) hcmp'
    · have hjeq : j = n := by omega
      have hn1mem : n - 1 ∈ Finset.Icc 1 (n - 1) := by
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hn1S : n - 1 ∈ Set.Icc 1 n := ⟨by omega, by omega⟩
      have hnS : n ∈ Set.Icc 1 n := ⟨by omega, by omega⟩
      have hneq : σ (n - 1) ≠ σ n := fun h => by
        have := hσ.injOn hn1S hnS h
        omega
      have hlast : σ n < σ (n - 1) := by
        by_contra hnot
        have hasc : σ (n - 1) < σ n := by omega
        have hd := hdiamond (n - 1) hn1mem (by
          simpa [show n - 1 + 1 = n by omega] using hasc)
        omega
      refine ⟨n - 1, Finset.mem_filter.mpr ⟨hn1mem, by
        simpa [show n - 1 + 1 = n by omega] using hlast⟩, ?_⟩
      intro him
      obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp him
      have ha' := Finset.mem_filter.mp ha
      have hab := Finset.mem_Icc.mp ha'.1
      subst j
      simp only [skipIndex] at heq
      split at heq <;> omega
  have hproper : S.image (skipIndex j) ⊂ T := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsubset, ?_⟩
    obtain ⟨b, hbT, hbI⟩ := hwitness
    intro heq
    exact hbI (heq.symm ▸ hbT)
  calc
    S.card = (S.image (skipIndex j)).card := (Finset.card_image_iff.mpr hinj).symm
    _ < T.card := Finset.card_lt_card hproper

/--
**Characterization of minimal permutations with a given number of descents.** Let $\sigma$ be a
permutation of $\{1, \dots, n\}$ and let $d$ be a natural number. A descent of a permutation
$\tau$ of $\{1, \dots, k\}$ is an index $1 \le i \le k - 1$ with $\tau(i+1) < \tau(i)$, and $\tau$
occurs in $\sigma$ if there are positions $\varphi(1) < \dots < \varphi(k)$ in $\{1, \dots, n\}$
with $\tau(a) < \tau(b)$ exactly when $\sigma(\varphi(a)) < \sigma(\varphi(b))$. Then $\sigma$ has
exactly $d$ descents and no permutation $\tau$ of $\{1, \dots, k\}$ with $0 < k < n$ occurring in
$\sigma$ has exactly $d$ descents if and only if $\sigma$ has exactly $d$ descents and every
ascent $i$ of $\sigma$ (an index $1 \le i \le n - 1$ with $\sigma(i) < \sigma(i+1)$) satisfies
$2 \le i \le n - 2$ and either $\sigma(i) < \sigma(i-1) < \sigma(i+2) < \sigma(i+1)$ or
$\sigma(i) < \sigma(i+2) < \sigma(i-1) < \sigma(i+1)$; that is, the entries at positions
$i-1, i, i+1, i+2$ form the pattern $2143$ or $3142$.

Source: Stefano Bilotta, Elisabetta Grazzini, and Elisa Pergola, "Enumeration of Two Particular Sets
of Minimal Permutations", Journal of Integer Sequences 18 (2015), Article 15.10.2, Theorem
`thm:characterization`, lines 230-237,
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Grazzini/graz3.tex>.

Proves `Wanted` entry `descent_minimal_iff`.
-/
theorem descent_minimal_iff (n d : ℕ) (σ : ℕ → ℕ)
    (hσ : Set.BijOn σ (Set.Icc 1 n) (Set.Icc 1 n)) :
    ((Finset.filter (fun i => σ (i + 1) < σ i) (Finset.Icc 1 (n - 1))).card = d ∧
      ∀ (k : ℕ) (τ : ℕ → ℕ), 0 < k → k < n → Set.BijOn τ (Set.Icc 1 k) (Set.Icc 1 k) →
        (∃ φ : ℕ → ℕ, Set.MapsTo φ (Set.Icc 1 k) (Set.Icc 1 n) ∧
          (∀ a ∈ Set.Icc 1 k, ∀ b ∈ Set.Icc 1 k, a < b → φ a < φ b) ∧
          ∀ a ∈ Set.Icc 1 k, ∀ b ∈ Set.Icc 1 k, (τ a < τ b ↔ σ (φ a) < σ (φ b))) →
        (Finset.filter (fun i => τ (i + 1) < τ i) (Finset.Icc 1 (k - 1))).card ≠ d) ↔
    ((Finset.filter (fun i => σ (i + 1) < σ i) (Finset.Icc 1 (n - 1))).card = d ∧
      ∀ i ∈ Finset.Icc 1 (n - 1), σ i < σ (i + 1) →
        2 ≤ i ∧ i ≤ n - 2 ∧
          (σ i < σ (i - 1) ∧ σ (i - 1) < σ (i + 2) ∧ σ (i + 2) < σ (i + 1) ∨
            σ i < σ (i + 2) ∧ σ (i + 2) < σ (i - 1) ∧ σ (i - 1) < σ (i + 1))) := by
  constructor
  · rintro ⟨hcard, hmin⟩
    refine ⟨hcard, ?_⟩
    intro i hi hasi
    have hib := Finset.mem_Icc.mp hi
    have hin : i < n := by omega
    have hn : 1 < n := by omega
    have hiS : i ∈ Set.Icc 1 n := ⟨hib.1, by omega⟩
    have hisS : i + 1 ∈ Set.Icc 1 n := ⟨by omega, by omega⟩
    have hneq_i : σ i ≠ σ (i + 1) := fun h => by
      have := hσ.injOn hiS hisS h
      omega
    have deletion_ne : ∀ j, j ∈ Set.Icc 1 n →
        (descents (deletePerm σ j) (n - 1)).card ≠ d := by
      intro j hj
      apply hmin (n - 1) (deletePerm σ j) (by omega) (by omega)
        (deletePerm_bijOn n j σ hσ hj)
      exact ⟨skipIndex j, (deletePerm_pattern n j σ hσ hj).1,
        (deletePerm_pattern n j σ hσ hj).2⟩
    have hi_not_desc : i ∉ descents σ n := by
      intro h
      exact (not_lt_of_ge hasi.le) (Finset.mem_filter.mp h).2
    have hi_two : 2 ≤ i := by
      by_contra hnot
      have hieq : i = 1 := by omega
      have hdelcard := delete_card_eq_of_left_bridge n i σ hσ hiS hin hi_not_desc
        (by intro hjone; omega)
      exact deletion_ne i hiS (hdelcard.trans hcard)
    have himS : i - 1 ∈ Set.Icc 1 n := ⟨by omega, by omega⟩
    have hneq_im_i : σ (i - 1) ≠ σ i := fun h => by
      have := hσ.injOn himS hiS h
      omega
    have hleft1 : σ i < σ (i - 1) := by
      by_contra hnot
      have hrev : σ (i - 1) < σ i := by omega
      have hbridgeFalse : ¬ σ (i + 1) < σ (i - 1) := by omega
      have holdFalse : ¬ σ i < σ (i - 1) := hnot
      have hdelcard := delete_card_eq_of_left_bridge n i σ hσ hiS hin hi_not_desc
        (by
          intro _ _
          exact iff_of_false hbridgeFalse holdFalse)
      exact deletion_ne i hiS (hdelcard.trans hcard)
    have hleft2 : σ (i - 1) < σ (i + 1) := by
      by_contra hnot
      have hneq : σ (i - 1) ≠ σ (i + 1) := fun h => by
        have := hσ.injOn himS hisS h
        omega
      have hbridgeTrue : σ (i + 1) < σ (i - 1) := by omega
      have hdelcard := delete_card_eq_of_left_bridge n i σ hσ hiS hin hi_not_desc
        (by
          intro _ _
          exact iff_of_true hbridgeTrue hleft1)
      exact deletion_ne i hiS (hdelcard.trans hcard)
    have hi_upper : i ≤ n - 2 := by
      by_contra hnot
      have hieq : i + 1 = n := by omega
      have hjS : i + 1 ∈ Set.Icc 1 n := hisS
      have hi_not_desc' : (i + 1) - 1 ∉ descents σ n := by
        simpa [show (i + 1) - 1 = i by omega] using hi_not_desc
      have hdelcard := delete_card_eq_of_right_bridge n (i + 1) σ hσ hjS
        (by omega) hi_not_desc' (by intro hjlt; omega)
      exact deletion_ne (i + 1) hjS (hdelcard.trans hcard)
    have hi2S : i + 2 ∈ Set.Icc 1 n := ⟨by omega, by omega⟩
    have hjS : i + 1 ∈ Set.Icc 1 n := hisS
    have hi_not_desc' : (i + 1) - 1 ∉ descents σ n := by
      simpa [show (i + 1) - 1 = i by omega] using hi_not_desc
    have hneq_ip1_ip2 : σ (i + 1) ≠ σ (i + 2) := fun h => by
      have := hσ.injOn hisS hi2S h
      omega
    have hright2 : σ (i + 2) < σ (i + 1) := by
      by_contra hnot
      have hforward : σ (i + 1) < σ (i + 2) := by omega
      have hbridgeFalse : ¬ σ (i + 2) < σ i := by omega
      have holdFalse : ¬ σ (i + 2) < σ (i + 1) := hnot
      have hdelcard := delete_card_eq_of_right_bridge n (i + 1) σ hσ hjS
        (by omega) hi_not_desc' (by
          intro _
          simpa [show i + 1 - 1 = i by omega] using iff_of_false hbridgeFalse holdFalse)
      exact deletion_ne (i + 1) hjS (hdelcard.trans hcard)
    have hright1 : σ i < σ (i + 2) := by
      by_contra hnot
      have hneq : σ i ≠ σ (i + 2) := fun h => by
        have := hσ.injOn hiS hi2S h
        omega
      have hbridgeTrue : σ (i + 2) < σ i := by omega
      have hdelcard := delete_card_eq_of_right_bridge n (i + 1) σ hσ hjS
        (by omega) hi_not_desc' (by
          intro _
          simpa [show i + 1 - 1 = i by omega] using iff_of_true hbridgeTrue hright2)
      exact deletion_ne (i + 1) hjS (hdelcard.trans hcard)
    refine ⟨hi_two, hi_upper, ?_⟩
    rcases lt_or_gt_of_ne (show σ (i - 1) ≠ σ (i + 2) by
      intro h
      have := hσ.injOn himS hi2S h
      omega) with hmid | hmid
    · exact Or.inl ⟨hleft1, hmid, hright2⟩
    · exact Or.inr ⟨hright1, hmid, hleft2⟩
  · rintro ⟨hcard, hdiamond⟩
    refine ⟨hcard, ?_⟩
    intro k τ hk hkn hτ hex
    obtain ⟨φ, hmap, hinc, hpat⟩ := hex
    classical
    have hn : 1 < n := by omega
    let A := Finset.Icc 1 k
    let B := Finset.Icc 1 n
    have hφinj : Set.InjOn φ (↑A : Set ℕ) := by
      intro a ha b hb heq
      have haS : a ∈ Set.Icc 1 k := by simpa [A] using ha
      have hbS : b ∈ Set.Icc 1 k := by simpa [A] using hb
      by_contra hne
      rcases lt_or_gt_of_ne hne with hab | hba
      · exact (ne_of_lt (hinc a haS b hbS hab)) heq
      · exact (ne_of_lt (hinc b hbS a haS hba)) heq.symm
    have himage_sub : A.image φ ⊆ B := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      have haS : a ∈ Set.Icc 1 k := by simpa [A] using ha
      have hm := hmap haS
      simpa [B] using hm
    have hcards : (A.image φ).card = k ∧ B.card = n := by
      constructor
      · rw [Finset.card_image_iff.mpr hφinj, Nat.card_Icc]
        omega
      · rw [Nat.card_Icc]
        omega
    have homit : ∃ j, j ∈ B ∧ j ∉ A.image φ := by
      by_contra hno
      push Not at hno
      have hrev : B ⊆ A.image φ := fun x hx => hno x hx
      have hc := Finset.card_le_card hrev
      rcases hcards with ⟨hcA, hcB⟩
      omega
    obtain ⟨j, hjB, hjomit⟩ := homit
    have hj : j ∈ Set.Icc 1 n := by simpa [B] using hjB
    have hφne : ∀ a ∈ Set.Icc 1 k, φ a ≠ j := by
      intro a ha hEq
      apply hjomit
      apply Finset.mem_image.mpr
      exact ⟨a, by simpa [A] using ha, hEq⟩
    let ψ : ℕ → ℕ := fun a => unskipIndex j (φ a)
    have hψmap : Set.MapsTo ψ (Set.Icc 1 k) (Set.Icc 1 (n - 1)) := by
      intro a ha
      exact unskip_mem n j (φ a) hj (hmap ha) (hφne a ha)
    have hψinc : ∀ a ∈ Set.Icc 1 k, ∀ b ∈ Set.Icc 1 k, a < b → ψ a < ψ b := by
      intro a ha b hb hab
      exact (unskip_lt_iff j (φ a) (φ b) (hφne a ha) (hφne b hb)
        (hmap ha).1 (hmap hb).1).mpr (hinc a ha b hb hab)
    have hψpat : ∀ a ∈ Set.Icc 1 k, ∀ b ∈ Set.Icc 1 k,
        (τ a < τ b ↔ deletePerm σ j (ψ a) < deletePerm σ j (ψ b)) := by
      intro a ha b hb
      have hpa := hmap ha
      have hpb := hmap hb
      have hsa : skipIndex j (ψ a) = φ a :=
        skip_unskip j (φ a) (hφne a ha) hpa.1
      have hsb : skipIndex j (ψ b) = φ b :=
        skip_unskip j (φ b) (hφne b hb) hpb.1
      rw [(deletePerm_pattern n j σ hσ hj).2.2 (ψ a) (hψmap ha) (ψ b) (hψmap hb)]
      rw [hsa, hsb]
      exact hpat a ha b hb
    have hle : (descents τ k).card ≤
        (descents (deletePerm σ j) (n - 1)).card :=
      descent_card_le_of_pattern (n - 1) k (deletePerm σ j) τ ψ
        hψmap hψinc hψpat
    have hlt := delete_card_lt_of_diamonds n j σ hσ hj hn hdiamond
    change (descents τ k).card ≠ d
    change (descents σ n).card = d at hcard
    omega
end MetaMathlibExt
