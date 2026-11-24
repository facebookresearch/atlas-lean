/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.GameTheory.SlowANim
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The general reduction lemma for Slow A-Nim

The general reduction lemma bounds the token surplus of a reduced position when a move
produces a nonreduced option.
-/

namespace MetaMathlibExt

namespace slowANim_generalReduction

private theorem sum_after_add_card {n : ℕ} (p : Fin n → ℕ) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, 1 ≤ p i) : (∑ i, slowANimAfter p S i) + S.card = ∑ i, p i := by
  calc
    _ = ∑ i, (slowANimAfter p S i + if i ∈ S then 1 else 0) := by
      simp [Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S
      · simp [slowANimAfter, hi, Nat.sub_add_cancel (hS i hi)]
      · simp [slowANimAfter, hi]

private theorem tokens_needed_to_empty {n : ℕ} {A : Finset ℕ} (hA : A.Nonempty)
    (i : Fin n) {p t : Fin n → ℕ}
    (hpt : Relation.ReflTransGen (fun x y => y ∈ slowANimMoves A x) p t) (ht : t i = 0) :
    A.min' hA * p i ≤ ∑ j, p j := by
  induction hpt using Relation.ReflTransGen.head_induction_on with
  | refl => simp [ht]
  | @head p q hpq _ ih =>
    simp only [slowANimMoves, Finset.mem_image, Finset.mem_filter] at hpq
    obtain ⟨S, ⟨-, -, hcard, hS⟩, rfl⟩ := hpq
    have hsum := sum_after_add_card p S hS
    have hsize := Finset.min'_le A S.card hcard
    have hheight : p i ≤ slowANimAfter p S i + 1 := by
      unfold slowANimAfter
      split_ifs <;> omega
    have hmul := Nat.mul_le_mul_left (A.min' hA) hheight
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

-- Empty a chosen stack by playing on it in every move. Only the tokens up to its
-- current height can contribute to the remaining moves.
private theorem reaches_empty_of_capped_total {n : ℕ} {A : Finset ℕ} {a : ℕ}
    (ha : a ∈ A) (ha_pos : 0 < a) (i : Fin n) (p : Fin n → ℕ)
    (h : a * p i ≤ ∑ j, min (p j) (p i)) :
    ∃ t, Relation.ReflTransGen (fun x y => y ∈ slowANimMoves A x) p t ∧ t i = 0 := by
  induction he : p i generalizing p with
  | zero => exact ⟨p, .refl, he⟩
  | succ k ih =>
    let tall := Finset.univ.filter fun j => k + 1 ≤ p j
    let positive := Finset.univ.filter fun j => 0 < p j
    have hi : i ∈ tall := Finset.mem_filter.mpr ⟨Finset.mem_univ i, he.ge⟩
    have htall : tall ⊆ positive := by
      intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, by omega⟩
    have hpositive : a ≤ positive.card := by
      rw [he] at h
      have hsum : (∑ j, min (p j) (k + 1)) = ∑ j ∈ positive, min (p j) (k + 1) := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hj
        have hz : p j = 0 := by simpa [positive] using hj
        simp [hz]
      have hbound : (∑ j ∈ positive, min (p j) (k + 1)) ≤ positive.card * (k + 1) :=
        (Finset.sum_le_sum fun j (_ : j ∈ positive) => min_le_right (p j) (k + 1)).trans_eq
          (Finset.sum_const_nat fun _ _ => rfl)
      exact Nat.le_of_mul_le_mul_right (h.trans (hsum ▸ hbound)) (Nat.succ_pos k)
    obtain ⟨S, hiS, hSpos, hcard, hcover⟩ :
        ∃ S : Finset (Fin n), i ∈ S ∧ S ⊆ positive ∧ S.card = a ∧
          (a ≤ tall.card ∨ tall ⊆ S) := by
      by_cases hlarge : a ≤ tall.card
      · obtain ⟨S, hsub, hStall, hcard⟩ :=
          Finset.exists_subsuperset_card_eq (Finset.singleton_subset_iff.mpr hi)
            (show ({i} : Finset (Fin n)).card ≤ a by simpa using Nat.succ_le_of_lt ha_pos) hlarge
        exact ⟨S, hsub (Finset.mem_singleton_self i), hStall.trans htall, hcard, Or.inl hlarge⟩
      · obtain ⟨S, hsub, hSpos, hcard⟩ :=
          Finset.exists_subsuperset_card_eq htall (Nat.le_of_not_ge hlarge) hpositive
        exact ⟨S, hsub hi, hSpos, hcard, Or.inr hsub⟩
    let q := slowANimAfter p S
    have hqi : q i = k := by simp [q, slowANimAfter, hiS, he]
    have hmove : q ∈ slowANimMoves A p := by
      simp only [slowANimMoves, Finset.mem_image, Finset.mem_filter]
      exact ⟨S, ⟨Finset.mem_univ _, ⟨i, hiS⟩, hcard ▸ ha,
        fun j hj => (Finset.mem_filter.mp (hSpos hj)).2⟩, rfl⟩
    have hq : a * k ≤ ∑ j, min (q j) k := by
      rcases hcover with hlarge | hcover
      · have hsum : (∑ j ∈ tall, min (q j) k) = tall.card * k := by
          apply Finset.sum_const_nat
          intro j hj
          have hj' := (Finset.mem_filter.mp hj).2
          apply min_eq_right
          unfold q slowANimAfter
          split_ifs <;> omega
        calc
          a * k ≤ tall.card * k := Nat.mul_le_mul_right k hlarge
          _ = ∑ j ∈ tall, min (q j) k := hsum.symm
          _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ tall)
      · have hsum : (∑ j, min (p j) (k + 1)) ≤ (∑ j, min (q j) k) + a := by
          calc
            _ ≤ ∑ j, (min (q j) k + if j ∈ S then 1 else 0) := by
              apply Finset.sum_le_sum
              intro j _
              by_cases hj : j ∈ S
              · simp only [q, slowANimAfter, hj, ite_true]
                omega
              · have hshort : ¬ k + 1 ≤ p j :=
                  fun h => hj (hcover (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩))
                simp only [q, slowANimAfter, hj, ite_false]
                omega
            _ = _ := by simp [Finset.sum_add_distrib, hcard]
        rw [he, Nat.mul_succ] at h
        omega
    obtain ⟨t, hqt, hti⟩ := ih q (by simpa only [hqi] using hq) hqi
    exact ⟨t, hqt.head hmove, hti⟩

private theorem reaches_terminal {n : ℕ} (A : Finset ℕ) (i : Fin n) (p : Fin n → ℕ)
    (hi : p i = 0) :
    ∃ t, Relation.ReflTransGen (fun x y => y ∈ slowANimMoves A x) p t ∧
      slowANimMoves A t = ∅ ∧ t i = 0 := by
  induction htotal : (∑ j, p j) using Nat.strong_induction_on generalizing p with
  | ind total ih =>
    rcases (slowANimMoves A p).eq_empty_or_nonempty with hemp | ⟨q, hq⟩
    · exact ⟨p, .refl, hemp, hi⟩
    · have hlt := sum_lt_of_mem_slowANimMoves A p q hq
      have hqi : q i = 0 := by
        simp only [slowANimMoves, Finset.mem_image, Finset.mem_filter] at hq
        obtain ⟨S, -, rfl⟩ := hq
        simp [slowANimAfter, hi]
      obtain ⟨t, hqt, ht, hti⟩ := ih _ (htotal ▸ hlt) q hqi rfl
      exact ⟨t, hqt.head hq, ht, hti⟩

private theorem reduced_of_total {n : ℕ} {A : Finset ℕ} {a : ℕ} (ha : a ∈ A)
    (ha_pos : 0 < a) {p : Fin n → ℕ} (h : a * Finset.univ.sup p ≤ ∑ j, p j) :
    SlowANimReduced A p := by
  intro i
  let M := Finset.univ.sup p
  have hle (j : Fin n) : p j ≤ M := Finset.le_sup (Finset.mem_univ j)
  have hcap : a * p i ≤ ∑ j, min (p j) (p i) := by
    by_cases hM : M = 0
    · have hi : p i = 0 := Nat.eq_zero_of_le_zero (hM ▸ hle i)
      simp [hi]
    · apply Nat.le_of_mul_le_mul_left _ (Nat.pos_of_ne_zero hM)
      calc
        M * (a * p i) = p i * (a * M) := by ac_rfl
        _ ≤ p i * ∑ j, p j := Nat.mul_le_mul_left _ h
        _ ≤ M * ∑ j, min (p j) (p i) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro j _
          rcases le_total (p j) (p i) with hj | hj
          · rw [min_eq_left hj]
            exact Nat.mul_le_mul_right _ (hle i)
          · rw [min_eq_right hj, Nat.mul_comm (p i)]
            exact Nat.mul_le_mul_right _ (hle j)
  obtain ⟨q, hpq, hqi⟩ := reaches_empty_of_capped_total ha ha_pos i p hcap
  obtain ⟨t, hqt, ht, hti⟩ := reaches_terminal A i q hqi
  exact ⟨t, hpq.trans hqt, ht, hti⟩

end slowANim_generalReduction

/-- **General reduction lemma.** Let $A \subseteq \{1, \dots, n\}$ be nonempty with least element
$a$, and let $p$ be a reduced position of Slow$A$-Nim $\mathrm{SN}(n, A)$ with largest stack
height $M$ and total $\Sigma(p) = \sum_i p_i$. Let $S$ be a set of $\ell \in A$ stacks, each
holding at least one token, and suppose that the position obtained from $p$ by removing one token
from each stack of $S$ is not reduced. Then $a M \le \Sigma(p)$ and, writing
$r = \Sigma(p) - a M$, either (R1) $\ell > a$, every stack of height $M$ lies in $S$, and
$r < \ell - a$; or (R2) some stack of height $M$ is not in $S$, and $r < \ell$.

The hypothesis that $p$ is reduced is implicit in the source, whose proof uses $r \ge 0$.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 4. -/
public theorem slowANim_generalReduction (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 n) (hAne : A.Nonempty) (p : Fin n → ℕ) (hp : SlowANimReduced A p)
    (S : Finset (Fin n)) (hS : S.card ∈ A) (hSp : ∀ i ∈ S, 1 ≤ p i)
    (hnot : ¬ SlowANimReduced A (slowANimAfter p S)) :
    (A.min' hAne < S.card ∧ (∀ i, p i = Finset.univ.sup p → i ∈ S) ∧
        A.min' hAne * Finset.univ.sup p ≤ ∑ i, p i ∧
        ∑ i, p i < A.min' hAne * Finset.univ.sup p + (S.card - A.min' hAne)) ∨
      ((∃ i, p i = Finset.univ.sup p ∧ i ∉ S) ∧
        A.min' hAne * Finset.univ.sup p ≤ ∑ i, p i ∧
        ∑ i, p i < A.min' hAne * Finset.univ.sup p + S.card) := by
  classical
  let a := A.min' hAne
  let M := Finset.univ.sup p
  let q := slowANimAfter p S
  have ha : a ∈ A := Finset.min'_mem _ _
  have ha_pos : 0 < a := (Finset.mem_Icc.mp (hA ha)).1
  have haS : a ≤ S.card := Finset.min'_le _ _ hS
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hM : 1 ≤ M := (hSp i hi).trans (Finset.le_sup (Finset.mem_univ i))
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨i, Finset.mem_univ i⟩ p
  obtain ⟨t, hpt, -, ht⟩ := hp j
  have hbefore : a * M ≤ ∑ i, p i := by
    change a * Finset.univ.sup p ≤ _
    rw [hj]
    exact slowANim_generalReduction.tokens_needed_to_empty hAne j hpt ht
  have hafter : (∑ i, q i) < a * Finset.univ.sup q :=
    lt_of_not_ge fun h => hnot (slowANim_generalReduction.reduced_of_total ha ha_pos h)
  have hsum : (∑ i, q i) + S.card = ∑ i, p i :=
    slowANim_generalReduction.sum_after_add_card p S hSp
  have hstack (i : Fin n) : q i ≤ p i := by
    unfold q slowANimAfter
    split_ifs <;> omega
  by_cases hmiss : ∃ i, p i = M ∧ i ∉ S
  · have hmax : Finset.univ.sup q ≤ M :=
      Finset.sup_le fun i hi => (hstack i).trans (Finset.le_sup hi)
    have hmul := Nat.mul_le_mul_left a hmax
    have hbound : (∑ i, p i) < a * M + S.card := by omega
    exact Or.inr ⟨hmiss, hbefore, hbound⟩
  · have hall (i) (hi : p i = M) : i ∈ S := by
      by_contra h
      exact hmiss ⟨i, hi, h⟩
    have hmax : Finset.univ.sup q ≤ M - 1 := by
      apply Finset.sup_le
      intro i hi
      by_cases htop : p i = M
      · simp [q, slowANimAfter, hall i htop, htop]
      · have hle : p i ≤ M := Finset.le_sup hi
        have := hstack i
        omega
    have hmul := Nat.mul_le_mul_left a hmax
    have hsplit : a * (M - 1) + a = a * M := by
      simpa only [Nat.mul_add, Nat.mul_one] using
        congrArg (a * ·) (Nat.sub_add_cancel hM)
    have hsize : a < S.card := by omega
    have hbound : (∑ i, p i) < a * M + (S.card - a) := by omega
    exact Or.inl ⟨hsize, hall, hbefore, hbound⟩

end MetaMathlibExt
