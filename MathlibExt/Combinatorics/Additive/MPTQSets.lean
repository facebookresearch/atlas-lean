/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Ring.Pointwise.Finset
import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Sets with more products than quotients

This module defines MPTQ sets and describes which pairings of four distinct positive
real numbers can have equal products.
-/

@[expose] public section

namespace MetaMathlibExt

open Pointwise

/-- **MPTQ set.** A finite set $A$ of real numbers is an MPTQ (more products than quotients) set
when $0 \notin A$ and $|A/A| < |A \cdot A|$, where $A \cdot A = \{ab : a, b \in A\}$ is the
product set, $A/A = \{a/b : a, b \in A\}$ is the quotient set, and $|X|$ is the number of
elements of $X$.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Definition 1. -/
def IsMPTQSet (A : Finset ℝ) : Prop :=
  (0 : ℝ) ∉ A ∧ (A / A).card < (A * A).card

/-- **A singleton is not an MPTQ set.** For every real number $a$, the one-element set $\{a\}$
is not an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Definition 1. -/
theorem not_isMPTQSet_singleton (a : ℝ) : ¬ IsMPTQSet {a} := by
  simp [IsMPTQSet]

/-- **Sets containing zero are not MPTQ sets.** If $A$ is a finite set of real numbers with
$0 \in A$, then $A$ is not an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Definition 1. -/
theorem not_isMPTQSet_of_zero_mem {A : Finset ℝ} (h : (0 : ℝ) ∈ A) : ¬ IsMPTQSet A :=
  fun hA => hA.1 h

/-- **Adjoining an element that adds no more products than quotients.** Let $A$ be a finite set
of real numbers that is not an MPTQ set, let $x$ be a real number, let $n \le m$ be natural
numbers, and write $A' = A \cup \{x\}$. If $|A' \cdot A'| \le |A \cdot A| + n$ and
$|A/A| + m \le |A'/A'|$, where $X \cdot X$ and $X/X$ denote the product set and quotient set of
$X$, then $A'$ is not an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 1 (`integers-2024-A96-lem-1`). -/
public theorem not_isMPTQSet_insert_of_le {A : Finset ℝ} {x : ℝ} {n m : ℕ}
    (hA : ¬ IsMPTQSet A) (hn : (insert x A * insert x A).card ≤ (A * A).card + n)
    (hm : (A / A).card + m ≤ (insert x A / insert x A).card) (hnm : n ≤ m) :
    ¬ IsMPTQSet (insert x A) := by
  intro h
  have hz : (0 : ℝ) ∉ A := fun hzero => h.1 (Finset.mem_insert_of_mem hzero)
  have hle : (A * A).card ≤ (A / A).card :=
    le_of_not_gt (fun hlt => hA ⟨hz, hlt⟩)
  refine (not_lt_of_ge ?_) h.2
  calc
    (insert x A * insert x A).card ≤ (A * A).card + n := hn
    _ ≤ (A / A).card + m := Nat.add_le_add hle hnm
    _ ≤ (insert x A / insert x A).card := hm

set_option linter.unusedVariables false in
/-- **One equal pairing of products excludes the other two.** Let $a$, $b$, $c$, $d$ be pairwise
distinct positive real numbers with $ab = cd$. Then $ad \neq bc$ and $ac \neq bd$.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 2 (`integers-2024-A96-lem-2`). -/
theorem mul_ne_of_mul_eq_of_distinct {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (h : a * b = c * d) : a * d ≠ b * c ∧ a * c ≠ b * d := by
  constructor
  · intro hadbc
    apply hac
    apply mul_right_cancel₀ (add_pos hb hd).ne'
    rw [mul_add, mul_add, h, hadbc]
    ac_rfl
  · intro hacbd
    apply had
    apply mul_right_cancel₀ (add_pos hb hc).ne'
    rw [mul_add, mul_add, h, hacbd]
    ac_rfl

private theorem card_union_neg_of_pos {s : Finset ℝ} (hs : ∀ x ∈ s, 0 < x) :
    (s ∪ -s).card = 2 * s.card := by
  have hd : Disjoint s (-s) := by
    refine Finset.disjoint_left.2 ?_
    intro x hx hx'
    exact (not_lt_of_ge (hs x hx).le) (neg_pos.mp (hs (-x) (Finset.mem_neg'.mp hx')))
  rw [Finset.card_union_of_disjoint hd, Finset.card_neg, two_mul]

private theorem union_neg_mul_union_neg (A B : Finset ℝ) :
    (A ∪ -A) * (B ∪ -B) = (A * B) ∪ -(A * B) := by
  rw [Finset.union_mul, Finset.mul_union, Finset.mul_union, mul_neg, neg_mul, mul_neg,
    neg_mul, neg_neg]
  ext x
  simp only [Finset.mem_union, or_comm, or_self]

/-- **Adjoining negatives preserves the MPTQ property.** Let $A$ be a finite set of positive real
numbers and $-A = \{-a : a \in A\}$. Then $A \cup (-A)$ is an MPTQ set if and only if $A$ is an
MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Proposition 1 (`integers-2024-A96-prop-1`). -/
theorem isMPTQSet_union_neg_iff {A : Finset ℝ} (hpos : ∀ a ∈ A, 0 < a) :
    IsMPTQSet (A ∪ -A) ↔ IsMPTQSet A := by
  have hA : (0 : ℝ) ∉ A := fun h => (lt_irrefl 0) (hpos 0 h)
  have hA' : (0 : ℝ) ∉ A ∪ -A := by
    simpa only [Finset.mem_union, Finset.mem_neg', neg_zero, or_self] using hA
  have hprod : ∀ x ∈ A * A, 0 < x := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hx
    exact mul_pos (hpos a ha) (hpos b hb)
  have hquot : ∀ x ∈ A / A, 0 < x := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_div.mp hx
    exact div_pos (hpos a ha) (hpos b hb)
  have hinv : (A ∪ -A)⁻¹ = (A⁻¹) ∪ -(A⁻¹) := by
    ext x
    simp only [Finset.mem_inv', Finset.mem_union, Finset.mem_neg', inv_neg]
  have hdiv : (A ∪ -A) / (A ∪ -A) = (A / A) ∪ -(A / A) := by
    simp only [div_eq_mul_inv, hinv, union_neg_mul_union_neg]
  simp only [IsMPTQSet, hA, hA', not_false_eq_true, true_and, hdiv, union_neg_mul_union_neg,
    card_union_neg_of_pos hquot, card_union_neg_of_pos hprod]
  exact Nat.mul_lt_mul_left (by decide : 0 < 2)

/-- **At most one square is the product of the other two.**
Let $a$, $b$, $c$ be pairwise distinct positive real numbers. Then at most one
of the equations $a^2 = bc$, $b^2 = ac$ and $c^2 = ab$ holds; that is, no two of
them hold simultaneously.

Source: Anupriya Shetty and B. R. Shankar,
*On The Minimum Cardinality of MPTQ Sets*, INTEGERS 24 (2024), Article A96,
Lemma 3 (`integers-2024-A96-lem-3`). -/
theorem at_most_one_sq_eq_mul_of_distinct {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ (a ^ 2 = b * c ∧ b ^ 2 = a * c) ∧ ¬ (a ^ 2 = b * c ∧ c ^ 2 = a * b) ∧
      ¬ (b ^ 2 = a * c ∧ c ^ 2 = a * b) := by
  have incompatible {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
      (hxy : x ≠ y) : ¬ (x ^ 2 = y * z ∧ y ^ 2 = x * z) := by
    rintro ⟨hx_sq, hy_sq⟩
    apply hxy
    -- Both products with the same positive sum are equal.
    apply mul_right_cancel₀ (add_pos (add_pos hx hy) hz).ne'
    simp only [mul_add, ← pow_two, hx_sq, hy_sq]
    ac_rfl
  refine ⟨incompatible ha hb hc hab, ?_, ?_⟩
  · rintro ⟨ha_sq, hc_sq⟩
    exact incompatible ha hc hb hac
      ⟨by simpa only [mul_comm c b] using ha_sq, hc_sq⟩
  · rintro ⟨hb_sq, hc_sq⟩
    exact incompatible hb hc ha hbc
      ⟨by simpa only [mul_comm c a] using hb_sq,
        by simpa only [mul_comm b a] using hc_sq⟩

-- Three different powers of p give disjoint copies of a set of p-adic units.
private theorem card_padic_layers {p : ℕ} (hp : p.Prime) (C : Finset ℚ)
    (hC : ∀ q ∈ C, q ≠ 0 ∧ padicValRat p q = 0) (i j k : ℤ)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((({(p : ℚ) ^ i} * C) ∪ ({(p : ℚ) ^ j} * C)) ∪ ({(p : ℚ) ^ k} * C)).card =
      3 * C.card := by
  let : Fact p.Prime := ⟨hp⟩
  have hp₀ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let layer (n : ℤ) : Finset ℚ := {(p : ℚ) ^ n} * C
  change ((layer i ∪ layer j) ∪ layer k).card = 3 * C.card
  have val_layer (n : ℤ) {q : ℚ} (hq : q ∈ layer n) : padicValRat p q = n := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hq
    have hae : a = (p : ℚ) ^ n := Finset.mem_singleton.mp ha
    subst a
    rw [padicValRat.mul (zpow_ne_zero n hp₀) (hC b hb).1, padicValRat.zpow,
      padicValRat.self hp.one_lt, (hC b hb).2, mul_one, add_zero]
  have disj (u v : ℤ) (huv : u ≠ v) : Disjoint (layer u) (layer v) :=
    Finset.disjoint_left.mpr fun _ h₁ h₂ => huv ((val_layer u h₁).symm.trans (val_layer v h₂))
  have disj_union : Disjoint (layer i ∪ layer j) (layer k) := by
    rw [Finset.disjoint_left]
    intro q h₁ h₂
    rcases Finset.mem_union.mp h₁ with h | h
    · exact Finset.disjoint_left.mp (disj i k hik) h h₂
    · exact Finset.disjoint_left.mp (disj j k hjk) h h₂
  have card_layer (n : ℤ) : (layer n).card = C.card := by
    change (Finset.image₂ (· * ·) {(p : ℚ) ^ n} C).card = C.card
    rw [Finset.image₂_singleton_left]
    exact Finset.card_image_of_injective _ (mul_right_injective₀ (zpow_ne_zero n hp₀))
  rw [Finset.card_union_of_disjoint disj_union, Finset.card_union_of_disjoint (disj i j hij),
    card_layer, card_layer, card_layer]
  omega

private theorem ratCast_isMPTQ_iff (C : Finset ℚ) (hC : (0 : ℚ) ∉ C) :
    IsMPTQSet (C.image (Rat.castHom ℝ)) ↔ (C / C).card < (C * C).card := by
  have hz : (0 : ℝ) ∉ C.image (Rat.castHom ℝ) := by
    intro h
    obtain ⟨q, hq, hzero⟩ := Finset.mem_image.mp h
    change (q : ℝ) = 0 at hzero
    exact hC ((Rat.cast_eq_zero.mp hzero) ▸ hq)
  have hdiv : (C / C).image (Rat.castHom ℝ) =
      C.image (Rat.castHom ℝ) / C.image (Rat.castHom ℝ) :=
    Finset.image_image₂_distrib (map_div₀ (Rat.castHom ℝ))
  have hinj : Function.Injective (Rat.castHom ℝ) := Rat.cast_injective
  rw [IsMPTQSet, ← hdiv, ← Finset.image_mul (Rat.castHom ℝ),
    Finset.card_image_of_injective _ hinj, Finset.card_image_of_injective _ hinj]
  simp only [hz, not_false_eq_true, true_and]

/-- **Adjoining multiples by a coprime prime preserves the MPTQ property.** Let $A$ be a finite
set of integers and $p$ a prime number such that every element of $A$ is coprime to $p$, and let
$pA = \{pa : a \in A\}$. Regarding sets of integers as sets of real numbers, $A \cup pA$ is an
MPTQ set if and only if $A$ is an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 4 (`integers-2024-A96-thm-4`). -/
public theorem isMPTQSet_union_prime_mul_iff (A : Finset ℤ) {p : ℕ} (hp : p.Prime)
    (hcop : ∀ a ∈ A, IsCoprime a (p : ℤ)) :
    IsMPTQSet ((A ∪ A.image ((p : ℤ) * ·)).image ((↑) : ℤ → ℝ)) ↔
      IsMPTQSet (A.image ((↑) : ℤ → ℝ)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp₀ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let U := A.image ((↑) : ℤ → ℚ)
  let P : Finset ℚ := {(p : ℚ)}
  let V := U ∪ P * U
  have p_nonunit : ¬ IsUnit (p : ℤ) := (Nat.prime_iff_prime_int.mp hp).not_isUnit
  have units (q : ℚ) (hq : q ∈ U) : q ≠ 0 ∧ padicValRat p q = 0 := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    have hnd : ¬ (p : ℤ) ∣ z := fun h => p_nonunit ((hcop z hz).symm.isUnit_of_dvd h)
    have hnz : z ≠ 0 := fun h => hnd (h ▸ dvd_zero (p : ℤ))
    exact ⟨by exact_mod_cast hnz, by simp [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hnd]⟩
  have hU₀ : (0 : ℚ) ∉ U := fun h => (units 0 h).1 rfl
  have hV₀ : (0 : ℚ) ∉ V := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hU₀ h
    · obtain ⟨a, ha, q, hq, haq⟩ := Finset.mem_mul.mp h
      have hae : a = (p : ℚ) := Finset.mem_singleton.mp ha
      subst a
      exact mul_ne_zero hp₀ (units q hq).1 haq
  have prod_unit (q : ℚ) (hq : q ∈ U * U) : q ≠ 0 ∧ padicValRat p q = 0 := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hq
    exact ⟨mul_ne_zero (units a ha).1 (units b hb).1, by
      rw [padicValRat.mul (units a ha).1 (units b hb).1, (units a ha).2, (units b hb).2, zero_add]⟩
  have quot_unit (q : ℚ) (hq : q ∈ U / U) : q ≠ 0 ∧ padicValRat p q = 0 := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_div.mp hq
    exact ⟨div_ne_zero (units a ha).1 (units b hb).1, by
      rw [padicValRat.div (units a ha).1 (units b hb).1, (units a ha).2, (units b hb).2, sub_self]⟩
  have hprod : V * V = ((U * U) ∪ (P * (U * U))) ∪ ((P * P) * (U * U)) := by
    change (U ∪ P * U) * (U ∪ P * U) = _
    rw [Finset.union_mul, Finset.mul_union, Finset.mul_union,
      show U * (P * U) = P * (U * U) by ac_rfl,
      show P * U * U = P * (U * U) by ac_rfl,
      show P * U * (P * U) = (P * P) * (U * U) by ac_rfl]
    ext q
    simp only [Finset.mem_union]
    tauto
  have hquot : V / V = ((U / U) ∪ (P * (U / U))) ∪ (P⁻¹ * (U / U)) := by
    have inv_union : (U ∪ P * U)⁻¹ = U⁻¹ ∪ (P * U)⁻¹ := by
      ext q
      simp only [Finset.mem_inv', Finset.mem_union]
    have cancel : P * P⁻¹ = (1 : Finset ℚ) := by
      simp only [P, Finset.inv_singleton, Finset.singleton_mul_singleton,
        mul_inv_cancel₀ hp₀, Finset.singleton_one]
    change (U ∪ P * U) / (U ∪ P * U) = _
    simp only [div_eq_mul_inv, inv_union, mul_inv_rev, Finset.union_mul, Finset.mul_union]
    rw [show U * (U⁻¹ * P⁻¹) = P⁻¹ * (U * U⁻¹) by ac_rfl,
      show P * U * U⁻¹ = P * (U * U⁻¹) by ac_rfl,
      show P * U * (U⁻¹ * P⁻¹) = (P * P⁻¹) * (U * U⁻¹) by ac_rfl, cancel, one_mul]
    ext q
    simp only [Finset.mem_union]
    tauto
  have hprod_card : (V * V).card = 3 * (U * U).card := by
    rw [hprod]
    simpa [P, zpow_natCast, pow_two, Finset.singleton_mul_singleton, Finset.singleton_one] using
      card_padic_layers hp (U * U) prod_unit 0 1 2 (by decide) (by decide) (by decide)
  have hquot_card : (V / V).card = 3 * (U / U).card := by
    rw [hquot]
    simpa [P, Finset.inv_singleton, Finset.singleton_one] using
      card_padic_layers hp (U / U) quot_unit 0 1 (-1) (by decide) (by decide) (by decide)
  have hV : V = (A ∪ A.image ((p : ℤ) * ·)).image ((↑) : ℤ → ℚ) := by
    change U ∪ Finset.image₂ (· * ·) {(p : ℚ)} U = _
    rw [Finset.image_union, Finset.image₂_singleton_left, Finset.image_image, Finset.image_image]
    congr 2
    funext a
    simp
  have hcast (S : Finset ℤ) : (S.image ((↑) : ℤ → ℚ)).image (Rat.castHom ℝ) =
      S.image ((↑) : ℤ → ℝ) := by
    rw [Finset.image_image]
    congr 1
  rw [← hcast (A ∪ A.image ((p : ℤ) * ·)), ← hcast A, ← hV]
  change IsMPTQSet (V.image (Rat.castHom ℝ)) ↔ IsMPTQSet (U.image (Rat.castHom ℝ))
  rw [ratCast_isMPTQ_iff V hV₀, ratCast_isMPTQ_iff U hU₀, hprod_card, hquot_card]
  exact Nat.mul_lt_mul_left (by decide : 0 < 3)

end MetaMathlibExt
