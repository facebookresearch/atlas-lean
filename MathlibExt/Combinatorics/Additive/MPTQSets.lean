/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Ring.Pointwise.Finset
import Mathlib.Data.Finset.Sort
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

-- Product and quotient counting for four positive reals, for the proof below.
namespace not_isMPTQSet_of_card_five_one_neg_aux

private theorem card_mul_le_card_div_of_certificate (P : Finset ℝ) (S Q : List ℝ)
    (hne : P.Nonempty) (hpos : ∀ x ∈ P, 0 < x) (hS : ∀ x ∈ P, ∀ y ∈ P, x * y ∈ S)
    (hQ : ∀ q ∈ Q, 1 < q ∧ q ∈ P / P) (hQn : Q.Nodup)
    (hlen : S.length ≤ 2 * Q.length + 1) :
    (P * P).card ≤ (P / P).card := by
  obtain ⟨x0, hx0⟩ := hne
  have hx0ne : x0 ≠ 0 := (hpos x0 hx0).ne'
  have h1 : (1 : ℝ) ∈ P / P := by
    rw [Finset.mem_div]
    exact ⟨x0, hx0, x0, hx0, div_self hx0ne⟩
  have hsub : P * P ⊆ S.toFinset := by
    intro z hz
    rw [Finset.mem_mul] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    rw [List.mem_toFinset]
    exact hS x hx y hy
  have hub : (P * P).card ≤ S.length :=
    le_trans (Finset.card_le_card hsub) (List.toFinset_card_le S)
  have hLmem : ∀ q ∈ (1 :: (Q ++ Q.map (fun p => p⁻¹))), q ∈ P / P := by
    intro q hq
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hq
    rcases hq with rfl | hPmem | ⟨p, hpP, rfl⟩
    · exact h1
    · exact (hQ _ hPmem).2
    · obtain ⟨hposq, hmem⟩ := hQ p hpP
      rw [Finset.mem_div] at hmem ⊢
      obtain ⟨u, hu, v, hv, huv⟩ := hmem
      exact ⟨v, hv, u, hu, by rw [← huv]; exact (inv_div u v).symm⟩
  have h1not : (1 : ℝ) ∉ Q ++ Q.map (fun p => p⁻¹) := by
    simp only [List.mem_append, List.mem_map]
    rintro (hQ0 | ⟨p, hpP, hneg⟩)
    · exact absurd (hQ 1 hQ0).1 (lt_irrefl 1)
    · have hp1 : p = 1 := by
        have h2 := congrArg Inv.inv hneg
        simpa using h2
      have h1lt := (hQ p hpP).1
      rw [hp1] at h1lt
      exact absurd h1lt (lt_irrefl 1)
  have hmapnodup : (Q.map (fun p : ℝ => p⁻¹)).Nodup :=
    List.Nodup.map (fun a b hab => inv_injective hab) hQn
  have hdisj : ∀ a ∈ Q, ∀ b ∈ Q.map (fun p : ℝ => p⁻¹), a ≠ b := by
    intro q hq1 b hq2
    rw [List.mem_map] at hq2
    obtain ⟨p, hpP, hpq⟩ := hq2
    have hpos1 := (hQ q hq1).1
    have hpos2 := (hQ p hpP).1
    rw [← hpq]
    intro hEq
    have hlt : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpos2
    rw [← hEq] at hlt
    exact (not_lt_of_ge hpos1.le) hlt
  have hLnodup : (1 :: (Q ++ Q.map (fun p : ℝ => p⁻¹))).Nodup :=
    List.nodup_cons.mpr ⟨h1not, List.nodup_append.mpr ⟨hQn, hmapnodup, hdisj⟩⟩
  have hLcard : (1 :: (Q ++ Q.map (fun p : ℝ => p⁻¹))).toFinset.card
      = (1 :: (Q ++ Q.map (fun p : ℝ => p⁻¹))).length :=
    List.toFinset_card_of_nodup hLnodup
  have hLsub : (1 :: (Q ++ Q.map (fun p : ℝ => p⁻¹))).toFinset ⊆ P / P := by
    intro q hq
    rw [List.mem_toFinset] at hq
    exact hLmem q hq
  have hlb : (1 :: (Q ++ Q.map (fun p : ℝ => p⁻¹))).length ≤ (P / P).card := by
    have h := Finset.card_le_card hLsub
    rwa [hLcard] at h
  simp only [List.length_cons, List.length_append, List.length_map] at hlb
  omega

private theorem div_ne_div_of_mul_ne {p q r s : ℝ} (hq : q ≠ 0) (hs : s ≠ 0)
    (h : p * s ≠ r * q) : p / q ≠ r / s := by
  intro heq
  apply h
  rw [div_eq_div_iff hq hs] at heq
  exact heq

private theorem div_ne_of_ne_den {p r q : ℝ} (hq : q ≠ 0) (h : p ≠ r) :
    p / q ≠ r / q := by
  intro heq
  apply h
  have h' := (div_eq_div_iff hq hq).mp heq
  exact mul_right_cancel₀ hq h'

private theorem div_ne_of_ne_num {p q s : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hs : s ≠ 0)
    (h : q ≠ s) : p / q ≠ p / s := by
  intro heq
  apply h
  have h' := (div_eq_div_iff hq hs).mp heq
  exact (mul_left_cancel₀ hp h').symm

private theorem div_ne_div_of_mul_lt {p q r s : ℝ} (hq : q ≠ 0) (hs : s ≠ 0)
    (h : p * s < r * q) : p / q ≠ r / s := by
  intro heq
  rw [div_eq_div_iff hq hs] at heq
  exact absurd heq (ne_of_lt h)


private theorem card_mul_le_card_div_of_four_pos {a b c d : ℝ} (ha : 0 < a)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card ≤
      (({a, b, c, d} : Finset ℝ) / {a, b, c, d}).card := by
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  have hd : 0 < d := hc.trans hcd
  have hne : ({a, b, c, d} : Finset ℝ).Nonempty := ⟨a, by simp⟩
  have hpos : ∀ x ∈ ({a, b, c, d} : Finset ℝ), 0 < x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hS10 : ∀ x ∈ ({a, b, c, d} : Finset ℝ), ∀ y ∈ ({a, b, c, d} : Finset ℝ),
      x * y ∈ [a * a, a * b, a * c, a * d, b * b, b * c, b * d, c * c, c * d,
        d * d] := by
    intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, mul_comm, true_or, or_true, or_false]
  have case_none : b * b ≠ c * a → c * c ≠ d * a → c * c ≠ d * b →
      b * b ≠ d * a → b * c ≠ d * a →
      (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card ≤
        (({a, b, c, d} : Finset ℝ) / {a, b, c, d}).card := by
    intro hE1 hE2 hE3 hF1 hG
    refine card_mul_le_card_div_of_certificate _
      [a * a, a * b, a * c, a * d, b * b, b * c, b * d, c * c, c * d, d * d]
      [b / a, c / b, d / c, c / a, d / a] hne hpos hS10 ?_ ?_ ?_
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact ⟨(one_lt_div ha).mpr hab, Finset.mem_div.mpr ⟨b, by simp, a, by simp, rfl⟩⟩
      · exact ⟨(one_lt_div hb).mpr hbc, Finset.mem_div.mpr ⟨c, by simp, b, by simp, rfl⟩⟩
      · exact ⟨(one_lt_div hc).mpr hcd, Finset.mem_div.mpr ⟨d, by simp, c, by simp, rfl⟩⟩
      · exact ⟨(one_lt_div ha).mpr (hab.trans hbc),
          Finset.mem_div.mpr ⟨c, by simp, a, by simp, rfl⟩⟩
      · exact ⟨(one_lt_div ha).mpr ((hab.trans hbc).trans hcd),
          Finset.mem_div.mpr ⟨d, by simp, a, by simp, rfl⟩⟩
    · have h12 : b / a ≠ c / b := div_ne_div_of_mul_ne ha.ne' hb.ne' hE1
      have h13 : b / a ≠ d / c := div_ne_div_of_mul_ne ha.ne' hc.ne' hG
      have h14 : b / a ≠ c / a := div_ne_of_ne_den ha.ne' (ne_of_lt hbc)
      have h15 : b / a ≠ d / a :=
        div_ne_of_ne_den ha.ne' (ne_of_lt (hbc.trans hcd))
      have h23 : c / b ≠ d / c := div_ne_div_of_mul_ne hb.ne' hc.ne' hE3
      have hlt : c * a < d * b := by
        rw [mul_comm c a, mul_comm d b]
        exact lt_trans (mul_lt_mul_of_pos_right hab hc)
          (mul_lt_mul_of_pos_left hcd hb)
      have h24 : c / b ≠ c / a :=
        div_ne_of_ne_num hc.ne' hb.ne' ha.ne' (ne_of_lt hab).symm
      have h25 : c / b ≠ d / a := div_ne_div_of_mul_lt hb.ne' ha.ne' hlt
      have h34 : d / c ≠ c / a := by
        apply div_ne_div_of_mul_ne hc.ne' ha.ne'
        intro h
        exact hE2 h.symm
      have h35 : d / c ≠ d / a :=
        div_ne_of_ne_num hd.ne' hc.ne' ha.ne' (ne_of_lt (hab.trans hbc)).symm
      have h45 : c / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt hcd)
      simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or,
        not_false_eq_true, and_true]
      exact ⟨⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45, trivial, List.nodup_nil⟩
    · simp
  have hQ4a : ∀ q ∈ [b / a, c / a, d / a, d / c],
      1 < q ∧ q ∈ ({a, b, c, d} : Finset ℝ) / {a, b, c, d} := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨(one_lt_div ha).mpr hab, Finset.mem_div.mpr ⟨b, by simp, a, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div ha).mpr (hab.trans hbc),
        Finset.mem_div.mpr ⟨c, by simp, a, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div ha).mpr ((hab.trans hbc).trans hcd),
        Finset.mem_div.mpr ⟨d, by simp, a, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div hc).mpr hcd, Finset.mem_div.mpr ⟨d, by simp, c, by simp, rfl⟩⟩
  have hQ4b : ∀ q ∈ [b / a, c / b, d / a, d / b],
      1 < q ∧ q ∈ ({a, b, c, d} : Finset ℝ) / {a, b, c, d} := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨(one_lt_div ha).mpr hab, Finset.mem_div.mpr ⟨b, by simp, a, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div hb).mpr hbc, Finset.mem_div.mpr ⟨c, by simp, b, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div ha).mpr ((hab.trans hbc).trans hcd),
        Finset.mem_div.mpr ⟨d, by simp, a, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div hb).mpr (hbc.trans hcd),
        Finset.mem_div.mpr ⟨d, by simp, b, by simp, rfl⟩⟩
  have hQ4G : ∀ q ∈ [b / a, c / b, d / b, d / a],
      1 < q ∧ q ∈ ({a, b, c, d} : Finset ℝ) / {a, b, c, d} := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨(one_lt_div ha).mpr hab, Finset.mem_div.mpr ⟨b, by simp, a, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div hb).mpr hbc, Finset.mem_div.mpr ⟨c, by simp, b, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div hb).mpr (hbc.trans hcd),
        Finset.mem_div.mpr ⟨d, by simp, b, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div ha).mpr ((hab.trans hbc).trans hcd),
        Finset.mem_div.mpr ⟨d, by simp, a, by simp, rfl⟩⟩
  have hQ4c : ∀ q ∈ [b / a, c / a, d / b, d / a],
      1 < q ∧ q ∈ ({a, b, c, d} : Finset ℝ) / {a, b, c, d} := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨(one_lt_div ha).mpr hab, Finset.mem_div.mpr ⟨b, by simp, a, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div ha).mpr (hab.trans hbc),
        Finset.mem_div.mpr ⟨c, by simp, a, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div hb).mpr (hbc.trans hcd),
        Finset.mem_div.mpr ⟨d, by simp, b, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div ha).mpr ((hab.trans hbc).trans hcd),
        Finset.mem_div.mpr ⟨d, by simp, a, by simp, rfl⟩⟩
  have hQ4d : ∀ q ∈ [c / b, b / a, c / a, d / a],
      1 < q ∧ q ∈ ({a, b, c, d} : Finset ℝ) / {a, b, c, d} := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨(one_lt_div hb).mpr hbc, Finset.mem_div.mpr ⟨c, by simp, b, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div ha).mpr hab, Finset.mem_div.mpr ⟨b, by simp, a, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div ha).mpr (hab.trans hbc),
        Finset.mem_div.mpr ⟨c, by simp, a, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div ha).mpr ((hab.trans hbc).trans hcd),
        Finset.mem_div.mpr ⟨d, by simp, a, by simp, rfl⟩⟩
  have hQ3 : ∀ q ∈ [b / a, c / a, d / a],
      1 < q ∧ q ∈ ({a, b, c, d} : Finset ℝ) / {a, b, c, d} := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨(one_lt_div ha).mpr hab, Finset.mem_div.mpr ⟨b, by simp, a, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div ha).mpr (hab.trans hbc),
        Finset.mem_div.mpr ⟨c, by simp, a, by simp, rfl⟩⟩
    · exact ⟨(one_lt_div ha).mpr ((hab.trans hbc).trans hcd),
        Finset.mem_div.mpr ⟨d, by simp, a, by simp, rfl⟩⟩
  have case_E1 : b * b = c * a → c * c ≠ d * a → b * c ≠ d * a →
      (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card ≤
        (({a, b, c, d} : Finset ℝ) / {a, b, c, d}).card := by
    intro hE1 hE2 hG
    have hS : ∀ x ∈ ({a, b, c, d} : Finset ℝ), ∀ y ∈ ({a, b, c, d} : Finset ℝ),
        x * y ∈ [a * a, a * b, a * d, b * b, b * c, b * d, c * c, c * d, d * d] := by
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, mul_comm, hE1, true_or, or_true, or_false]
    refine card_mul_le_card_div_of_certificate _
      [a * a, a * b, a * d, b * b, b * c, b * d, c * c, c * d, d * d]
      [b / a, c / a, d / a, d / c] hne hpos hS hQ4a ?_ ?_
    · have h12 : b / a ≠ c / a := div_ne_of_ne_den ha.ne' (ne_of_lt hbc)
      have h13 : b / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt (hbc.trans hcd))
      have h14 : b / a ≠ d / c := div_ne_div_of_mul_ne ha.ne' hc.ne' hG
      have h23 : c / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt hcd)
      have h24 : c / a ≠ d / c := div_ne_div_of_mul_ne ha.ne' hc.ne' hE2
      have h34 : d / a ≠ d / c :=
        div_ne_of_ne_num hd.ne' ha.ne' hc.ne' (ne_of_lt (hab.trans hbc))
      simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or,
        not_false_eq_true, and_true]
      exact ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34, trivial, List.nodup_nil⟩
    · simp
  have case_E3 : c * c = d * b → c * c ≠ d * a → b * c ≠ d * a →
      (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card ≤
        (({a, b, c, d} : Finset ℝ) / {a, b, c, d}).card := by
    intro hE3 hE2 hG
    have hS : ∀ x ∈ ({a, b, c, d} : Finset ℝ), ∀ y ∈ ({a, b, c, d} : Finset ℝ),
        x * y ∈ [a * a, a * b, a * c, a * d, b * b, b * c, c * c, c * d, d * d] := by
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, mul_comm, hE3, true_or, or_true, or_false]
    refine card_mul_le_card_div_of_certificate _
      [a * a, a * b, a * c, a * d, b * b, b * c, c * c, c * d, d * d]
      [b / a, c / a, d / a, d / c] hne hpos hS hQ4a ?_ ?_
    · have h12 : b / a ≠ c / a := div_ne_of_ne_den ha.ne' (ne_of_lt hbc)
      have h13 : b / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt (hbc.trans hcd))
      have h14 : b / a ≠ d / c := div_ne_div_of_mul_ne ha.ne' hc.ne' hG
      have h23 : c / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt hcd)
      have h24 : c / a ≠ d / c := div_ne_div_of_mul_ne ha.ne' hc.ne' hE2
      have h34 : d / a ≠ d / c :=
        div_ne_of_ne_num hd.ne' ha.ne' hc.ne' (ne_of_lt (hab.trans hbc))
      simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or,
        not_false_eq_true, and_true]
      exact ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34, trivial, List.nodup_nil⟩
    · simp
  have case_F1 : b * b = d * a → c * c ≠ d * a → b * c ≠ d * a →
      (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card ≤
        (({a, b, c, d} : Finset ℝ) / {a, b, c, d}).card := by
    intro hF1 hE2 hG
    have hS : ∀ x ∈ ({a, b, c, d} : Finset ℝ), ∀ y ∈ ({a, b, c, d} : Finset ℝ),
        x * y ∈ [a * a, a * b, a * c, b * b, b * c, b * d, c * c, c * d, d * d] := by
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, mul_comm, hF1, true_or, or_true, or_false]
    refine card_mul_le_card_div_of_certificate _
      [a * a, a * b, a * c, b * b, b * c, b * d, c * c, c * d, d * d]
      [b / a, c / a, d / a, d / c] hne hpos hS hQ4a ?_ ?_
    · have h12 : b / a ≠ c / a := div_ne_of_ne_den ha.ne' (ne_of_lt hbc)
      have h13 : b / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt (hbc.trans hcd))
      have h14 : b / a ≠ d / c := div_ne_div_of_mul_ne ha.ne' hc.ne' hG
      have h23 : c / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt hcd)
      have h24 : c / a ≠ d / c := div_ne_div_of_mul_ne ha.ne' hc.ne' hE2
      have h34 : d / a ≠ d / c :=
        div_ne_of_ne_num hd.ne' ha.ne' hc.ne' (ne_of_lt (hab.trans hbc))
      simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or,
        not_false_eq_true, and_true]
      exact ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34, trivial, List.nodup_nil⟩
    · simp
  have case_E2 : c * c = d * a → b * b ≠ c * a → b * b ≠ d * a → b * c ≠ d * a →
      (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card ≤
        (({a, b, c, d} : Finset ℝ) / {a, b, c, d}).card := by
    intro hE2 hE1 hF1 hG
    have hS : ∀ x ∈ ({a, b, c, d} : Finset ℝ), ∀ y ∈ ({a, b, c, d} : Finset ℝ),
        x * y ∈ [a * a, a * b, a * c, b * b, b * c, b * d, c * c, c * d, d * d] := by
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, mul_comm, hE2, true_or, or_true, or_false]
    refine card_mul_le_card_div_of_certificate _
      [a * a, a * b, a * c, b * b, b * c, b * d, c * c, c * d, d * d]
      [b / a, c / b, d / a, d / b] hne hpos hS hQ4b ?_ ?_
    · have h12 : b / a ≠ c / b := div_ne_div_of_mul_ne ha.ne' hb.ne' hE1
      have h13 : b / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt (hbc.trans hcd))
      have h14 : b / a ≠ d / b := div_ne_div_of_mul_ne ha.ne' hb.ne' hF1
      have hlt : c * a < d * b := by
        rw [mul_comm c a, mul_comm d b]
        exact lt_trans (mul_lt_mul_of_pos_right hab hc)
          (mul_lt_mul_of_pos_left hcd hb)
      have h23 : c / b ≠ d / a := div_ne_div_of_mul_lt hb.ne' ha.ne' hlt
      have h24 : c / b ≠ d / b := div_ne_of_ne_den hb.ne' (ne_of_lt hcd)
      have h34 : d / a ≠ d / b :=
        div_ne_of_ne_num hd.ne' ha.ne' hb.ne' (ne_of_lt hab)
      simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or,
        not_false_eq_true, and_true]
      exact ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34, trivial, List.nodup_nil⟩
    · simp
  have case_G : b * c = d * a → b * b ≠ c * a → b * b ≠ d * a →
      (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card ≤
        (({a, b, c, d} : Finset ℝ) / {a, b, c, d}).card := by
    intro hG hE1 hF1
    have hS : ∀ x ∈ ({a, b, c, d} : Finset ℝ), ∀ y ∈ ({a, b, c, d} : Finset ℝ),
        x * y ∈ [a * a, a * b, a * c, b * b, b * c, b * d, c * c, c * d, d * d] := by
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, mul_comm, hG, true_or, or_true, or_false]
    refine card_mul_le_card_div_of_certificate _
      [a * a, a * b, a * c, b * b, b * c, b * d, c * c, c * d, d * d]
      [b / a, c / b, d / b, d / a] hne hpos hS hQ4G ?_ ?_
    · have h12 : b / a ≠ c / b := div_ne_div_of_mul_ne ha.ne' hb.ne' hE1
      have h13 : b / a ≠ d / b := div_ne_div_of_mul_ne ha.ne' hb.ne' hF1
      have h14 : b / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt (hbc.trans hcd))
      have h23 : c / b ≠ d / b := div_ne_of_ne_den hb.ne' (ne_of_lt hcd)
      have hlt : c * a < d * b := by
        rw [mul_comm c a, mul_comm d b]
        exact lt_trans (mul_lt_mul_of_pos_right hab hc)
          (mul_lt_mul_of_pos_left hcd hb)
      have h24 : c / b ≠ d / a := div_ne_div_of_mul_lt hb.ne' ha.ne' hlt
      have h34 : d / b ≠ d / a :=
        div_ne_of_ne_num hd.ne' hb.ne' ha.ne' (ne_of_lt hab).symm
      simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or,
        not_false_eq_true, and_true]
      exact ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34, trivial, List.nodup_nil⟩
    · simp
  have case_E1E2 : b * b = c * a → c * c = d * a → c * c ≠ d * b →
      b * b ≠ d * a → b * c ≠ d * a →
      (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card ≤
        (({a, b, c, d} : Finset ℝ) / {a, b, c, d}).card := by
    intro hE1 hE2 hE3 hF1 hG
    have hS : ∀ x ∈ ({a, b, c, d} : Finset ℝ), ∀ y ∈ ({a, b, c, d} : Finset ℝ),
        x * y ∈ [a * a, a * b, b * b, b * c, b * d, c * c, c * d, d * d] := by
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, mul_comm, hE1, hE2, true_or,
          or_true, or_false]
    refine card_mul_le_card_div_of_certificate _
      [a * a, a * b, b * b, b * c, b * d, c * c, c * d, d * d]
      [b / a, c / a, d / b, d / a] hne hpos hS hQ4c ?_ ?_
    · have h12 : b / a ≠ c / a := div_ne_of_ne_den ha.ne' (ne_of_lt hbc)
      have h13 : b / a ≠ d / b := div_ne_div_of_mul_ne ha.ne' hb.ne' hF1
      have h14 : b / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt (hbc.trans hcd))
      have h23 : c / a ≠ d / b := by
        apply div_ne_div_of_mul_ne ha.ne' hb.ne'
        intro h
        rw [mul_comm c b] at h
        exact hG h
      have h24 : c / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt hcd)
      have h34 : d / b ≠ d / a :=
        div_ne_of_ne_num hd.ne' hb.ne' ha.ne' (ne_of_lt hab).symm
      simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or,
        not_false_eq_true, and_true]
      exact ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34, trivial, List.nodup_nil⟩
    · simp
  have case_E3F1 : c * c = d * b → b * b = d * a → b * b ≠ c * a →
      b * c ≠ d * a →
      (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card ≤
        (({a, b, c, d} : Finset ℝ) / {a, b, c, d}).card := by
    intro hE3 hF1 hE1 hG
    have hS : ∀ x ∈ ({a, b, c, d} : Finset ℝ), ∀ y ∈ ({a, b, c, d} : Finset ℝ),
        x * y ∈ [a * a, a * b, a * c, b * b, b * c, c * c, c * d, d * d] := by
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, mul_comm, hE3, hF1, true_or,
          or_true, or_false]
    refine card_mul_le_card_div_of_certificate _
      [a * a, a * b, a * c, b * b, b * c, c * c, c * d, d * d]
      [c / b, b / a, c / a, d / a] hne hpos hS hQ4d ?_ ?_
    · have h12 : c / b ≠ b / a := by
        apply div_ne_div_of_mul_ne hb.ne' ha.ne'
        intro h
        exact hE1 h.symm
      have h13 : c / b ≠ c / a :=
        div_ne_of_ne_num hc.ne' hb.ne' ha.ne' (ne_of_lt hab).symm
      have hlt : c * a < d * b := by
        rw [mul_comm c a, mul_comm d b]
        exact lt_trans (mul_lt_mul_of_pos_right hab hc)
          (mul_lt_mul_of_pos_left hcd hb)
      have h14 : c / b ≠ d / a := div_ne_div_of_mul_lt hb.ne' ha.ne' hlt
      have h23 : b / a ≠ c / a := div_ne_of_ne_den ha.ne' (ne_of_lt hbc)
      have h24 : b / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt (hbc.trans hcd))
      have h34 : c / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt hcd)
      simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or,
        not_false_eq_true, and_true]
      exact ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34, trivial, List.nodup_nil⟩
    · simp
  have case_geom : b * b = c * a → c * c = d * b → b * c = d * a →
      (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card ≤
        (({a, b, c, d} : Finset ℝ) / {a, b, c, d}).card := by
    intro hE1 hE3 hG
    have hS : ∀ x ∈ ({a, b, c, d} : Finset ℝ), ∀ y ∈ ({a, b, c, d} : Finset ℝ),
        x * y ∈ [a * a, a * b, b * b, b * c, b * d, c * d, d * d] := by
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, mul_comm, hE1, hE3, hG, true_or,
          or_true, or_false]
    refine card_mul_le_card_div_of_certificate _
      [a * a, a * b, b * b, b * c, b * d, c * d, d * d]
      [b / a, c / a, d / a] hne hpos hS hQ3 ?_ ?_
    · have h12 : b / a ≠ c / a := div_ne_of_ne_den ha.ne' (ne_of_lt hbc)
      have h13 : b / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt (hbc.trans hcd))
      have h23 : c / a ≠ d / a := div_ne_of_ne_den ha.ne' (ne_of_lt hcd)
      simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or,
        not_false_eq_true, and_true]
      exact ⟨⟨h12, h13⟩, h23, trivial, List.nodup_nil⟩
    · simp
  have hpruneE1F1 : b * b = c * a → b * b = d * a → False := by
    intro h1 h2
    exact (ne_of_lt hcd) (mul_right_cancel₀ ha.ne' (h1.symm.trans h2))
  have hpruneE2F1 : c * c = d * a → b * b = d * a → False := by
    intro h1 h2
    have hsq : b * b = c * c := h2.trans h1.symm
    have hsq2 : b ^ 2 = c ^ 2 := by rw [pow_two, pow_two]; exact hsq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with h | h
    · exact (ne_of_lt hbc) h
    · exfalso; linarith
  have hpruneF1G : b * b = d * a → b * c = d * a → False := by
    intro h1 h2
    exact (ne_of_lt hbc) (mul_left_cancel₀ hb.ne' (h1.trans h2.symm))
  have hderiveG : b * b = c * a → c * c = d * b → b * c = d * a := by
    intro h1 h2
    have r1 : b / a = c / b := (div_eq_div_iff ha.ne' hb.ne').mpr h1
    have r2 : c / b = d / c := (div_eq_div_iff hb.ne' hc.ne').mpr h2
    exact (div_eq_div_iff ha.ne' hc.ne').mp (r1.trans r2)
  have hderiveE1 : b * c = d * a → c * c = d * b → b * b = c * a := by
    intro hG hE3
    have rG : b / a = d / c := (div_eq_div_iff ha.ne' hc.ne').mpr hG
    have rE3 : c / b = d / c := (div_eq_div_iff hb.ne' hc.ne').mpr hE3
    exact (div_eq_div_iff ha.ne' hb.ne').mp (rG.trans rE3.symm)
  have hderiveE3 : b * b = c * a → b * c = d * a → c * c = d * b := by
    intro hE1 hG
    have rE1 : b / a = c / b := (div_eq_div_iff ha.ne' hb.ne').mpr hE1
    have rG : b / a = d / c := (div_eq_div_iff ha.ne' hc.ne').mpr hG
    exact (div_eq_div_iff hb.ne' hc.ne').mp (rE1.symm.trans rG)
  by_cases hE1 : b * b = c * a <;> by_cases hE2 : c * c = d * a <;>
    by_cases hE3 : c * c = d * b <;> by_cases hF1 : b * b = d * a <;>
    by_cases hG : b * c = d * a <;>
    first
      | exact case_none hE1 hE2 hE3 hF1 hG
      | exact case_E1 hE1 hE2 hG
      | exact case_E3 hE3 hE2 hG
      | exact case_F1 hF1 hE2 hG
      | exact case_E2 hE2 hE1 hF1 hG
      | exact case_G hG hE1 hF1
      | exact case_E1E2 hE1 hE2 hE3 hF1 hG
      | exact case_E3F1 hE3 hF1 hE1 hG
      | exact case_geom hE1 hE3 hG
      | exact absurd (hderiveG hE1 hE3) hG
      | exact absurd (hderiveE1 hG hE3) hE1
      | exact absurd (hderiveE3 hE1 hG) hE3
      | exact False.elim (hpruneE1F1 hE1 hF1)
      | exact False.elim (hpruneE2F1 hE2 hF1)
      | exact False.elim (hpruneF1G hF1 hG)

private theorem exists_sorted_of_card_eq_four_real (A : Finset ℝ) (h : A.card = 4) :
    ∃ a b c d : ℝ, a < b ∧ b < c ∧ c < d ∧ A = {a, b, c, d} := by
  let f := A.orderEmbOfFin h
  refine ⟨f 0, f 1, f 2, f 3, ?_, ?_, ?_, ?_⟩
  · exact f.strictMono (by decide)
  · exact f.strictMono (by decide)
  · exact f.strictMono (by decide)
  · have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
    have himg := Finset.image_orderEmbOfFin_univ A h
    rw [huniv, Finset.image_insert, Finset.image_insert, Finset.image_insert,
      Finset.image_singleton] at himg
    rw [← himg]

end not_isMPTQSet_of_card_five_one_neg_aux

/-- **Five-element sets with one negative element are not MPTQ sets.** If $A$ is a set of five
real numbers exactly one of which is negative, then $A$ is not an MPTQ set.

The source assumes the elements are nonzero; this is not needed, since a set containing $0$ is
never an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 4 (`integers-2024-A96-lem-4`). -/
public theorem not_isMPTQSet_of_card_five_one_neg {A : Finset ℝ} (hcard : A.card = 5)
    (hneg : (A.filter (· < 0)).card = 1) : ¬ IsMPTQSet A := by
  by_cases h0 : (0 : ℝ) ∈ A
  · exact not_isMPTQSet_of_zero_mem h0
  · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hneg
    have hzmem : z ∈ A := by
      have hmem : z ∈ A.filter (· < 0) := hz ▸ Finset.mem_singleton_self z
      exact (Finset.mem_filter.mp hmem).1
    have hzneg : z < 0 := by
      have hmem : z ∈ A.filter (· < 0) := hz ▸ Finset.mem_singleton_self z
      exact (Finset.mem_filter.mp hmem).2
    have hPcard : (A.erase z).card = 4 := by
      rw [Finset.card_erase_of_mem hzmem, hcard]
    obtain ⟨a, b, c, d, hab, hbc, hcd, hPeq⟩ :=
      not_isMPTQSet_of_card_five_one_neg_aux.exists_sorted_of_card_eq_four_real (A.erase z) hPcard
    have hAeq : A = insert z {a, b, c, d} := by
      rw [← hPeq]
      exact (Finset.insert_erase hzmem).symm
    have hcard4 : ({a, b, c, d} : Finset ℝ).card = 4 := by
      rw [← hPeq]; exact hPcard
    have hPpos : ∀ p ∈ ({a, b, c, d} : Finset ℝ), 0 < p := by
      intro p hp
      have hpA : p ∈ A := by
        have hmem : p ∈ A.erase z := by rw [hPeq]; exact hp
        exact Finset.mem_of_mem_erase hmem
      have hpne : p ≠ z := by
        intro hpe
        have hmem : p ∈ A.erase z := by rw [hPeq]; exact hp
        exact Finset.ne_of_mem_erase hmem hpe
      have hple : ¬ p < 0 := by
        intro hlt
        have hmem : p ∈ A.filter (· < 0) := Finset.mem_filter.mpr ⟨hpA, hlt⟩
        rw [hz] at hmem
        exact hpne (Finset.mem_singleton.mp hmem)
      rcases lt_or_ge p 0 with hlt | hge
      · exact absurd hlt hple
      · rcases eq_or_lt_of_le hge with heq | hgt
        · exact absurd (heq ▸ hpA) h0
        · exact hgt
    have ha : 0 < a := hPpos a (by simp)
    have hb : 0 < b := hPpos b (by simp)
    have hc : 0 < c := hPpos c (by simp)
    have hd : 0 < d := hPpos d (by simp)
    have hPnot : ¬ IsMPTQSet ({a, b, c, d} : Finset ℝ) := by
      intro h
      have hle :=
        not_isMPTQSet_of_card_five_one_neg_aux.card_mul_le_card_div_of_four_pos ha hab hbc hcd
      exact absurd h.2 (not_lt_of_ge hle)
    rw [hAeq]
    have hquot_pos : ∀ w ∈ ({a, b, c, d} : Finset ℝ) / {a, b, c, d}, 0 < w := by
      intro w hw
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_div.mp hw
      exact div_pos (hPpos u hu) (hPpos v hv)
    have hzS : z ∈ insert z ({a, b, c, d} : Finset ℝ) := Finset.mem_insert_self _ _
    have hsubS : ({a, b, c, d} : Finset ℝ) ⊆ insert z {a, b, c, d} :=
      fun _ hp => Finset.mem_insert_of_mem hp
    by_cases hsq : z * z ∈ ({a, b, c, d} : Finset ℝ) * {a, b, c, d}
    · apply not_isMPTQSet_insert_of_le (A := ({a, b, c, d} : Finset ℝ)) (x := z)
        (n := 4) (m := 4) hPnot ?_ ?_ (le_refl 4)
      · have hsub : insert z ({a, b, c, d} : Finset ℝ) * insert z {a, b, c, d} ⊆
            (({a, b, c, d} : Finset ℝ) * {a, b, c, d}) ∪
              ({a, b, c, d} : Finset ℝ).image (fun p => z * p) := by
          intro w hw
          obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp hw
          rcases Finset.mem_insert.mp hu with hu_eq | hu
          · rcases Finset.mem_insert.mp hv with hv_eq | hv
            · rw [hu_eq, hv_eq]
              exact Finset.mem_union_left _ hsq
            · rw [hu_eq]
              exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
          · rcases Finset.mem_insert.mp hv with hv_eq | hv
            · rw [hv_eq, mul_comm u z]
              exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
            · exact Finset.mem_union_left _
                (Finset.mem_mul.mpr ⟨u, hu, v, hv, rfl⟩)
        calc (insert z ({a, b, c, d} : Finset ℝ) * insert z {a, b, c, d}).card
            ≤ ((({a, b, c, d} : Finset ℝ) * {a, b, c, d}) ∪
              ({a, b, c, d} : Finset ℝ).image (fun p => z * p)).card :=
              Finset.card_le_card hsub
          _ ≤ (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card +
              (({a, b, c, d} : Finset ℝ).image (fun p => z * p)).card :=
              Finset.card_union_le _ _
          _ ≤ (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card + 4 := by
              have hle : (({a, b, c, d} : Finset ℝ).image (fun p => z * p)).card ≤
                  ({a, b, c, d} : Finset ℝ).card := Finset.card_image_le
              rw [hcard4] at hle
              exact Nat.add_le_add_left hle _
      · have hneg1 : ∀ w ∈ ({a, b, c, d} : Finset ℝ).image (fun p => z / p), w < 0 := by
          intro w hw
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
          exact div_neg_of_neg_of_pos hzneg (hPpos p hp)
        have hdisj : Disjoint (({a, b, c, d} : Finset ℝ) / {a, b, c, d})
            (({a, b, c, d} : Finset ℝ).image (fun p => z / p)) := by
          rw [Finset.disjoint_left]
          intro w hw1 hw2
          exact absurd (hquot_pos w hw1) (not_lt_of_ge (hneg1 w hw2).le)
        have hsub : (({a, b, c, d} : Finset ℝ) / {a, b, c, d}) ∪
            (({a, b, c, d} : Finset ℝ).image (fun p => z / p)) ⊆
            insert z ({a, b, c, d} : Finset ℝ) / insert z {a, b, c, d} := by
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_div.mp hw
            exact Finset.mem_div.mpr ⟨u, hsubS hu, v, hsubS hv, rfl⟩
          · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
            exact Finset.mem_div.mpr ⟨z, hzS, p, hsubS hp, rfl⟩
        have hinj : Set.InjOn (fun p : ℝ => z / p) ↑({a, b, c, d} : Finset ℝ) := by
          intro p hp q hq h
          have hp0 := (hPpos p hp).ne'
          have hq0 := (hPpos q hq).ne'
          rw [div_eq_div_iff hp0 hq0] at h
          exact mul_left_cancel₀ hzneg.ne h.symm
        calc (({a, b, c, d} : Finset ℝ) / {a, b, c, d}).card + 4
            = ((({a, b, c, d} : Finset ℝ) / {a, b, c, d}) ∪
              (({a, b, c, d} : Finset ℝ).image (fun p => z / p))).card := by
              rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj,
                hcard4]
          _ ≤ (insert z ({a, b, c, d} : Finset ℝ) /
              insert z {a, b, c, d}).card := Finset.card_le_card hsub
    · apply not_isMPTQSet_insert_of_le (A := ({a, b, c, d} : Finset ℝ)) (x := z)
        (n := 5) (m := 8) hPnot ?_ ?_ (by norm_num)
      · have hsub : insert z ({a, b, c, d} : Finset ℝ) * insert z {a, b, c, d} ⊆
            ((({a, b, c, d} : Finset ℝ) * {a, b, c, d}) ∪
              ({a, b, c, d} : Finset ℝ).image (fun p => z * p)) ∪ {z * z} := by
          intro w hw
          obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp hw
          rcases Finset.mem_insert.mp hu with hu_eq | hu
          · rcases Finset.mem_insert.mp hv with hv_eq | hv
            · rw [hu_eq, hv_eq]
              exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
            · rw [hu_eq]
              exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
          · rcases Finset.mem_insert.mp hv with hv_eq | hv
            · rw [hv_eq, mul_comm u z]
              exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨u, hu, rfl⟩))
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_mul.mpr ⟨u, hu, v, hv, rfl⟩))
        calc (insert z ({a, b, c, d} : Finset ℝ) * insert z {a, b, c, d}).card
            ≤ (((( {a, b, c, d} : Finset ℝ) * {a, b, c, d}) ∪
              ({a, b, c, d} : Finset ℝ).image (fun p => z * p)) ∪ {z * z}).card :=
              Finset.card_le_card hsub
          _ ≤ ((({a, b, c, d} : Finset ℝ) * {a, b, c, d}) ∪
              ({a, b, c, d} : Finset ℝ).image (fun p => z * p)).card + 1 := by
              refine le_trans (Finset.card_union_le _ _) ?_
              rw [Finset.card_singleton]
          _ ≤ (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card + 4 + 1 := by
              refine Nat.add_le_add_right ?_ 1
              refine le_trans (Finset.card_union_le _ _) ?_
              have hle : (({a, b, c, d} : Finset ℝ).image (fun p => z * p)).card ≤
                  ({a, b, c, d} : Finset ℝ).card := Finset.card_image_le
              rw [hcard4] at hle
              exact Nat.add_le_add_left hle _
          _ = (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card + 5 := by omega
      · have hneg1 : ∀ w ∈ ({a, b, c, d} : Finset ℝ).image (fun p => z / p), w < 0 := by
          intro w hw
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
          exact div_neg_of_neg_of_pos hzneg (hPpos p hp)
        have hneg2 : ∀ w ∈ ({a, b, c, d} : Finset ℝ).image (fun p => p / z), w < 0 := by
          intro w hw
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
          exact div_neg_of_pos_of_neg (hPpos p hp) hzneg
        have hdisj1 : Disjoint (({a, b, c, d} : Finset ℝ) / {a, b, c, d})
            ((({a, b, c, d} : Finset ℝ).image (fun p => z / p)) ∪
              (({a, b, c, d} : Finset ℝ).image (fun p => p / z))) := by
          rw [Finset.disjoint_left]
          intro w hw1 hw2
          rcases Finset.mem_union.mp hw2 with hw2 | hw2
          · exact absurd (hquot_pos w hw1) (not_lt_of_ge (hneg1 w hw2).le)
          · exact absurd (hquot_pos w hw1) (not_lt_of_ge (hneg2 w hw2).le)
        have hdisj12 : Disjoint (({a, b, c, d} : Finset ℝ).image (fun p => z / p))
            (({a, b, c, d} : Finset ℝ).image (fun p => p / z)) := by
          rw [Finset.disjoint_left]
          intro w hw1 hw2
          obtain ⟨p, hp, hpw⟩ := Finset.mem_image.mp hw1
          obtain ⟨q, hq, hqw⟩ := Finset.mem_image.mp hw2
          have hEq : z / p = q / z := hpw.trans hqw.symm
          rw [div_eq_div_iff (hPpos p hp).ne' hzneg.ne] at hEq
          exact hsq (by rw [hEq]; exact Finset.mem_mul.mpr ⟨q, hq, p, hp, rfl⟩)
        have hsub : (({a, b, c, d} : Finset ℝ) / {a, b, c, d}) ∪
            ((({a, b, c, d} : Finset ℝ).image (fun p => z / p)) ∪
              (({a, b, c, d} : Finset ℝ).image (fun p => p / z))) ⊆
            insert z ({a, b, c, d} : Finset ℝ) / insert z {a, b, c, d} := by
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_div.mp hw
            exact Finset.mem_div.mpr ⟨u, hsubS hu, v, hsubS hv, rfl⟩
          · rcases Finset.mem_union.mp hw with hw | hw
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
              exact Finset.mem_div.mpr ⟨z, hzS, p, hsubS hp, rfl⟩
            · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
              exact Finset.mem_div.mpr ⟨p, hsubS hp, z, hzS, rfl⟩
        have hinj1 : Set.InjOn (fun p : ℝ => z / p) ↑({a, b, c, d} : Finset ℝ) := by
          intro p hp q hq h
          rw [div_eq_div_iff (hPpos p hp).ne' (hPpos q hq).ne'] at h
          exact mul_left_cancel₀ hzneg.ne h.symm
        have hinj2 : Set.InjOn (fun p : ℝ => p / z) ↑({a, b, c, d} : Finset ℝ) := by
          intro p hp q hq h
          rw [div_eq_div_iff hzneg.ne hzneg.ne] at h
          exact mul_right_cancel₀ hzneg.ne h
        calc (({a, b, c, d} : Finset ℝ) / {a, b, c, d}).card + 8
            = ((({a, b, c, d} : Finset ℝ) / {a, b, c, d}) ∪
              ((({a, b, c, d} : Finset ℝ).image (fun p => z / p)) ∪
                (({a, b, c, d} : Finset ℝ).image (fun p => p / z)))).card := by
              rw [Finset.card_union_of_disjoint hdisj1,
                Finset.card_union_of_disjoint hdisj12, Finset.card_image_of_injOn hinj1,
                Finset.card_image_of_injOn hinj2, hcard4]
          _ ≤ (insert z ({a, b, c, d} : Finset ℝ) /
              insert z {a, b, c, d}).card := Finset.card_le_card hsub

end MetaMathlibExt
