/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Prod
public import MathlibExt.Combinatorics.Additive.Sidon
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod

/-!
# Isolated sums of finite Sidon sets

The sumset of a sufficiently large finite Sidon set contains arbitrarily many isolated elements.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosSidonIsolatedSumsWanted

/-! Source record `EP-152`. -/

/-- **Finite Sidon sets of natural numbers.** A finite set $A$ of natural numbers is a Sidon set
when every equality $a + b = c + d$ with $a, b, c, d \in A$ is trivial, that is, $a = c$ and
$b = d$, or $a = d$ and $b = c$. -/
def IsSidon (A : Finset ℕ) : Prop :=
  Set.IsSidon (A : Set ℕ)

/-- **Sumset of a finite set of natural numbers.** For a finite set $A$ of natural numbers, the
sumset $A + A$ is the finite set of all sums $x + y$ with $x, y \in A$. -/
def Sumset (A : Finset ℕ) : Finset ℕ :=
  (A.product A).image (fun p => p.1 + p.2)

/-- **Isolated elements of a set of natural numbers.** Let $S$ be a finite set of natural numbers.
A natural number $a$ is isolated in $S$ when $a \in S$, $a + 1 \notin S$, and either $a = 0$ or
$a - 1 \notin S$.

For $a = 0$ the condition on the predecessor is vacuous, since $0$ has no predecessor among the
natural numbers. -/
def IsIsolated (S : Finset ℕ) (a : ℕ) : Prop :=
  a ∈ S ∧ a + 1 ∉ S ∧ (a = 0 ∨ a - 1 ∉ S)

/-- **Number of isolated elements.** For a finite set $S$ of natural numbers, the isolated count
of $S$ is the number of elements $a \in S$ with $a + 1 \notin S$ and either $a = 0$ or
$a - 1 \notin S$. -/
def IsolatedCount (S : Finset ℕ) : ℕ :=
  (S.filter (fun a => a + 1 ∉ S ∧ (a = 0 ∨ a - 1 ∉ S))).card

/-- **Erdős Problem 152 on isolated sums of Sidon sets.** A finite set $A$ of natural numbers is
a Sidon set when $a + b = c + d$ with $a, b, c, d \in A$ implies $\{a, b\} = \{c, d\}$, and its
sumset is $A + A = \{x + y : x, y \in A\}$. An element $s$ of a finite set $S$ of natural numbers
is isolated in $S$ when $s + 1 \notin S$ and either $s = 0$ or $s - 1 \notin S$. The proposition
asserts that for every natural number $M \ge 1$ there is a natural number $K$ such that every
finite Sidon set $A$ of natural numbers with at least $K$ elements has at least $M$ isolated
elements in $A + A$. -/
def conjecture : Prop :=
  ∀ M : ℕ, 1 ≤ M →
    ∃ K : ℕ, ∀ A : Finset ℕ,
      IsSidon A → K ≤ A.card → M ≤ IsolatedCount (Sumset A)

open Finset
open scoped BigOperators Pointwise

/-- Translate by `-k`, so membership at `x` tests the original set at `x + k`. -/
private def shift (X : Finset ℤ) (k : ℤ) : Finset ℤ :=
  X.map ⟨(· - k), fun a b h ↦ by
    change a - k = b - k at h
    omega⟩

private lemma mem_shift {X : Finset ℤ} {k x : ℤ} : x ∈ shift X k ↔ x + k ∈ X := by
  rw [shift, Finset.mem_map]
  change (∃ y ∈ X, y - k = x) ↔ x + k ∈ X
  simp [sub_eq_iff_eq_add]

@[simp] private lemma card_shift (X : Finset ℤ) (k : ℤ) :
    (shift X k).card = X.card := card_map _

/-- The starting points of pairs in `X` at distance `k`. -/
private def gap (X : Finset ℤ) (k : ℤ) : Finset ℤ := X ∩ shift X k

private lemma mem_gap {X : Finset ℤ} {k x : ℤ} : x ∈ gap X k ↔ x ∈ X ∧ x + k ∈ X := by
  simp [gap, mem_shift]

private def isolated (X : Finset ℤ) : Finset ℤ :=
  X \ (gap X 1 ∪ shift (gap X 1) (-1))

private lemma mem_isolated {X : Finset ℤ} {x : ℤ} :
    x ∈ isolated X ↔ x ∈ X ∧ x + 1 ∉ X ∧ x - 1 ∉ X := by
  simp only [isolated, mem_sdiff, mem_union, mem_shift, mem_gap, ← sub_eq_add_neg,
    sub_add_cancel]
  tauto

private def interior (X : Finset ℤ) : Finset ℤ :=
  gap X 1 ∩ shift (gap X 1) (-1)

private lemma mem_interior {X : Finset ℤ} {x : ℤ} :
    x ∈ interior X ↔ x ∈ X ∧ x + 1 ∈ X ∧ x - 1 ∈ X := by
  simp only [interior, mem_inter, mem_shift, mem_gap, ← sub_eq_add_neg, sub_add_cancel]
  tauto

private lemma card_isolated_add_twice_gap (X : Finset ℤ) :
    (isolated X).card + 2 * (gap X 1).card = X.card + (interior X).card := by
  have hsub : gap X 1 ∪ shift (gap X 1) (-1) ⊆ X := by
    intro x hx
    simp only [mem_union, mem_shift, mem_gap, ← sub_eq_add_neg, sub_add_cancel] at hx
    exact hx.elim And.left And.right
  have h₁ := card_sdiff_add_card_eq_card hsub
  have h₂ := card_union_add_card_inter (gap X 1) (shift (gap X 1) (-1))
  rw [card_shift] at h₂
  change (isolated X).card + _ = _ at h₁
  change _ + (interior X).card = _ at h₂
  omega

private lemma four_mul_card_gap_one_add_card_gap_three (X : Finset ℤ) :
    4 * (gap X 1).card + (gap X 3).card ≤ 3 * X.card + 2 * (gap X 2).card := by
  let U := X ∪ shift X 1 ∪ shift X 2
  have h₀ : X ⊆ U := by intro x hx; simp [U, hx]
  have h₁ : shift X 1 ⊆ U := by intro x hx; simp [U, hx]
  have h₂ : shift X 2 ⊆ U := by intro x hx; simp [U, hx]
  have hgap (i : ℤ) : gap X i ⊆ U := inter_subset_left.trans h₀
  have hshift {i j : ℤ} (h : shift X i ⊆ U) : shift (gap X j) i ⊆ U := by
    intro x hx
    have hx' := (mem_gap.mp (mem_shift.mp hx)).1
    exact h (mem_shift.mpr hx')
  let indicator (Y : Finset ℤ) (x : ℤ) : ℕ := if x ∈ Y then 1 else 0
  have hcount {Y : Finset ℤ} (h : Y ⊆ U) : (∑ x ∈ U, indicator Y x) = Y.card :=
    (card_eq_sum_ite h).symm
  have hpoint (x : ℤ) :
      indicator (gap X 1) x + 2 * indicator (shift (gap X 1) 1) x +
        indicator (shift (gap X 1) 2) x + indicator (gap X 3) x ≤
      indicator X x + indicator (shift X 1) x + indicator (shift X 2) x +
        indicator (gap X 2) x + indicator (shift (gap X 2) 1) x := by
    have e₁ : x + 1 + 1 = x + 2 := by omega
    have e₂ : x + 2 + 1 = x + 3 := by omega
    have e₃ : x + 1 + 2 = x + 3 := by omega
    by_cases h0 : x ∈ X <;> by_cases h1 : x + 1 ∈ X <;>
      by_cases h2 : x + 2 ∈ X <;> by_cases h3 : x + 3 ∈ X <;>
      simp [indicator, mem_shift, mem_gap, e₁, e₂, e₃, h0, h1, h2, h3]
  have hsum := sum_le_sum (s := U) fun x _ ↦ hpoint x
  simp only [sum_add_distrib, ← mul_sum, hcount h₀, hcount h₁, hcount h₂,
    hcount (hgap 1), hcount (hgap 2), hcount (hgap 3), hcount (hshift (j := 1) h₁),
    hcount (hshift (j := 1) h₂), hcount (hshift (j := 2) h₁), card_shift] at hsum
  omega

private lemma twice_card_gap_two (X : Finset ℤ) :
    2 * (gap X 2).card ≤ (gap X 3).card + 2 * (interior X).card + 2 * (isolated X).card := by
  let G := gap X 2 \ shift X 1
  let L := G ∩ shift X (-1)
  let R := G ∩ shift X 3
  have memG {x : ℤ} : x ∈ G ↔ (x ∈ X ∧ x + 2 ∈ X) ∧ x + 1 ∉ X := by
    simp [G, mem_gap, mem_shift]
  have hmid : shift (gap X 2 ∩ shift X 1) (-1) = interior X := by
    ext x
    have e : x - 1 + 2 = x + 1 := by omega
    simp only [mem_interior, mem_shift, mem_gap, mem_inter, ← sub_eq_add_neg, sub_add_cancel, e]
    tauto
  have hpart := card_sdiff_add_card_inter (gap X 2) (shift X 1)
  rw [← card_shift (gap X 2 ∩ shift X 1) (-1), hmid] at hpart
  change G.card + _ = _ at hpart
  -- The two extensions of a gap give disjoint subsets of the distance-three pairs.
  have hsub : shift L 1 ∪ R ⊆ gap X 3 := by
    intro x hx
    have e : x + 1 + 2 = x + 3 := by omega
    simp only [L, R, mem_union, mem_shift, mem_inter, memG, ← sub_eq_add_neg,
      add_sub_cancel_right, e] at hx
    exact mem_gap.mpr (hx.elim (fun h ↦ ⟨h.2, h.1.1.2⟩) (fun h ↦ ⟨h.1.1.1, h.2⟩))
  have hdisj : Disjoint (shift L 1) R := by
    rw [disjoint_left]
    intro x hl hr
    exact (memG.mp (mem_inter.mp hr).1).2 (memG.mp (mem_inter.mp (mem_shift.mp hl)).1).1.1
  have hext := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_shift] at hext
  -- If the gap does not extend on a side, the endpoint on that side is isolated.
  have hleft : G \ L ⊆ isolated X := by
    intro x hx
    simp only [L, mem_sdiff, mem_inter, mem_shift, ← sub_eq_add_neg] at hx
    exact mem_isolated.mpr ⟨(memG.mp hx.1).1.1, (memG.mp hx.1).2, fun h ↦ hx.2 ⟨hx.1, h⟩⟩
  have hright : shift (G \ R) (-2) ⊆ isolated X := by
    intro x hx
    have e₁ : x + -2 + 2 = x := by omega
    have e₂ : x + -2 + 1 = x - 1 := by omega
    have e₃ : x + -2 + 3 = x + 1 := by omega
    simp only [R, mem_shift, mem_sdiff, mem_inter, e₃] at hx
    have hg := memG.mp hx.1
    rw [e₁, e₂] at hg
    exact mem_isolated.mpr ⟨hg.1.2, fun h ↦ hx.2 ⟨hx.1, h⟩, hg.2⟩
  have hleft' := card_le_card hleft
  have hright' := card_le_card hright
  rw [card_shift] at hright'
  have hl := card_sdiff_add_card_eq_card (show L ⊆ G from inter_subset_left)
  have hr := card_sdiff_add_card_eq_card (show R ⊆ G from inter_subset_left)
  omega

/-- The sum and the order of the summands recover a pair from a Sidon set. -/
private def encodePair (p : ℤ × ℤ) : ℤ × Bool :=
  (p.1 + p.2, decide (p.1 ≤ p.2))

private lemma encodePair_injOn {A : Finset ℤ} (hA : (A : Set ℤ).IsSidon) :
    Set.InjOn encodePair (↑(A ×ˢ A) : Set (ℤ × ℤ)) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
  obtain ⟨ha, hb⟩ := mem_product.mp hab
  obtain ⟨hc, hd⟩ := mem_product.mp hcd
  have hsum : a + b = c + d := congrArg Prod.fst heq
  rcases hA a ha b hb c hc d hd hsum with ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · exact Prod.ext hac hbd
  · have hord : decide (a ≤ b) = decide (c ≤ d) := congrArg Prod.snd heq
    rw [← had, ← hbc, decide_eq_decide] at hord
    have hab : a = b := by omega
    exact Prod.ext (hab.trans hbc) (hab.symm.trans had)

private lemma card_product_le_twice_card_sum (A : Finset ℤ) (hA : (A : Set ℤ).IsSidon) :
    A.card * A.card ≤ 2 * (A + A).card := by
  have h := card_le_card_of_injOn (t := (A + A) ×ˢ (univ : Finset Bool)) encodePair
    (fun p hp ↦ mem_product.mpr ⟨Finset.mem_add.mpr
      ⟨p.1, (mem_product.mp hp).1, p.2, (mem_product.mp hp).2, rfl⟩, mem_univ _⟩)
    (encodePair_injOn hA)
  simpa [card_product, Fintype.card_bool, Nat.mul_comm] using h

private lemma eq_of_sub_eq {A : Finset ℤ} (hA : (A : Set ℤ).IsSidon)
    {a b c d : ℤ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (h : a - b = c - d) (hne : a ≠ b) : a = c ∧ b = d := by
  rcases hA a ha d hd c hc b hb (by omega) with ⟨hac, hdb⟩ | ⟨hab, _⟩
  · exact ⟨hac, hdb.symm⟩
  · exact (hne hab).elim

private def quadruples (A : Finset ℤ) (k : ℤ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun q ↦ q.1.1 + q.1.2 + k = q.2.1 + q.2.2)

private lemma mem_quadruples {A : Finset ℤ} {k : ℤ} {a b c d : ℤ} :
    ((a, b), (c, d)) ∈ quadruples A k ↔
      (a ∈ A ∧ b ∈ A) ∧ (c ∈ A ∧ d ∈ A) ∧ a + b + k = c + d := by
  simp [quadruples, and_assoc]

private lemma card_gap_diff_le_card_quadruples (A : Finset ℤ) (k : ℤ) :
    (gap (A - A) k).card ≤ (quadruples A k).card := by
  apply card_le_card_of_surjOn (fun q ↦ q.1.1 - q.2.1)
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := mem_gap.mp hx
  obtain ⟨a, ha, c, hc, he₁⟩ := Finset.mem_sub.mp hx₁
  obtain ⟨d, hd, b, hb, he₂⟩ := Finset.mem_sub.mp hx₂
  exact ⟨((a, b), (c, d)), mem_quadruples.mpr ⟨⟨ha, hb⟩, ⟨hc, hd⟩, by omega⟩, he₁⟩

private lemma card_quadruples_le_card_gap_diff {A : Finset ℤ} (hA : (A : Set ℤ).IsSidon)
    {k : ℤ} (hk : k ≠ 0) :
    (quadruples A k).card ≤ (gap (A - A) k).card + 2 * A.card := by
  let Q := quadruples A k
  let Q₀ := Q.filter (fun q ↦ q.1.1 = q.2.1)
  let Q₁ := Q.filter (fun q ↦ q.1.2 = q.2.2)
  let Q' := Q.filter (fun q ↦ q.1.1 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2)
  have h₀ : Q₀.card ≤ A.card := by
    apply card_le_card_of_injOn (fun q ↦ q.1.1)
    · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq
      exact (mem_quadruples.mp (mem_filter.mp hq).1).1.1
    · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ hq' he
      obtain ⟨hq, hac⟩ := mem_filter.mp hq
      obtain ⟨hq', hac'⟩ := mem_filter.mp hq'
      obtain ⟨⟨_, hb⟩, ⟨_, hd⟩, hsum⟩ := mem_quadruples.mp hq
      obtain ⟨⟨_, hb'⟩, ⟨_, hd'⟩, hsum'⟩ := mem_quadruples.mp hq'
      change a = c at hac
      change a' = c' at hac'
      change a = a' at he
      obtain ⟨rfl, rfl⟩ := eq_of_sub_eq hA hd hb hd' hb' (by omega) (by omega)
      have hcc : c = c' := by omega
      exact Prod.ext (Prod.ext he rfl) (Prod.ext hcc rfl)
  have h₁ : Q₁.card ≤ A.card := by
    apply card_le_card_of_injOn (fun q ↦ q.1.2)
    · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq
      exact (mem_quadruples.mp (mem_filter.mp hq).1).1.2
    · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ hq' he
      obtain ⟨hq, hbd⟩ := mem_filter.mp hq
      obtain ⟨hq', hbd'⟩ := mem_filter.mp hq'
      obtain ⟨⟨ha, _⟩, ⟨hc, _⟩, hsum⟩ := mem_quadruples.mp hq
      obtain ⟨⟨ha', _⟩, ⟨hc', _⟩, hsum'⟩ := mem_quadruples.mp hq'
      change b = d at hbd
      change b' = d' at hbd'
      change b = b' at he
      obtain ⟨rfl, rfl⟩ := eq_of_sub_eq hA hc ha hc' ha' (by omega) (by omega)
      have hdd : d = d' := by omega
      exact Prod.ext (Prod.ext rfl he) (Prod.ext rfl hdd)
  have hgood : Q'.card ≤ (gap (A - A) k).card := by
    apply card_le_card_of_injOn (fun q ↦ q.1.1 - q.2.1)
    · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq
      obtain ⟨⟨ha, hb⟩, ⟨hc, hd⟩, hsum⟩ := mem_quadruples.mp (mem_filter.mp hq).1
      change a - c ∈ gap (A - A) k
      exact mem_gap.mpr ⟨Finset.mem_sub.mpr ⟨a, ha, c, hc, rfl⟩,
        Finset.mem_sub.mpr ⟨d, hd, b, hb, by omega⟩⟩
    · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ hq' he
      obtain ⟨hq, hac, hbd⟩ := mem_filter.mp hq
      obtain ⟨⟨ha, hb⟩, ⟨hc, hd⟩, hsum⟩ := mem_quadruples.mp hq
      obtain ⟨⟨ha', hb'⟩, ⟨hc', hd'⟩, hsum'⟩ := mem_quadruples.mp (mem_filter.mp hq').1
      obtain ⟨rfl, rfl⟩ := eq_of_sub_eq hA ha hc ha' hc' he hac
      obtain ⟨rfl, rfl⟩ := eq_of_sub_eq hA hd hb hd' hb' (by omega) (Ne.symm hbd)
      rfl
  have hcover : Q ⊆ Q' ∪ Q₀ ∪ Q₁ := by
    intro q hq
    by_cases ha : q.1.1 = q.2.1 <;> by_cases hb : q.1.2 = q.2.2 <;>
      simp [Q₀, Q₁, Q', hq, ha, hb]
  have hcard := card_le_card hcover
  have hu := card_union_le (Q' ∪ Q₀) Q₁
  have hu' := card_union_le Q' Q₀
  change Q.card ≤ _
  omega

private def encodeQuadruple (q : (ℤ × ℤ) × (ℤ × ℤ)) : ℤ × (Bool × Bool) :=
  ((encodePair q.1).1, (encodePair q.1).2, (encodePair q.2).2)

private lemma encodeQuadruple_injOn {A : Finset ℤ} (hA : (A : Set ℤ).IsSidon) (k : ℤ) :
    Set.InjOn encodeQuadruple (↑(quadruples A k) : Set ((ℤ × ℤ) × (ℤ × ℤ))) := by
  rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ hq' he
  obtain ⟨hab, hcd, hsum⟩ := mem_quadruples.mp hq
  obtain ⟨hab', hcd', hsum'⟩ := mem_quadruples.mp hq'
  have hstart : a + b = a' + b' := congrArg Prod.fst he
  exact Prod.ext
    (encodePair_injOn hA (mem_product.mpr hab) (mem_product.mpr hab')
      (Prod.ext hstart (congrArg (fun p ↦ p.2.1) he)))
    (encodePair_injOn hA (mem_product.mpr hcd) (mem_product.mpr hcd')
      (Prod.ext (show c + d = c' + d' by omega) (congrArg (fun p ↦ p.2.2) he)))

private lemma card_quadruples_le_four_card_gap_sum {A : Finset ℤ} (hA : (A : Set ℤ).IsSidon)
    (k : ℤ) : (quadruples A k).card ≤ 4 * (gap (A + A) k).card := by
  have h := card_le_card_of_injOn (t := gap (A + A) k ×ˢ (univ : Finset (Bool × Bool)))
    encodeQuadruple (by
      rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq
      obtain ⟨⟨ha, hb⟩, ⟨hc, hd⟩, hsum⟩ := mem_quadruples.mp hq
      exact mem_product.mpr ⟨mem_gap.mpr ⟨Finset.mem_add.mpr ⟨a, ha, b, hb, rfl⟩,
        Finset.mem_add.mpr ⟨c, hc, d, hd, hsum.symm⟩⟩, mem_univ _⟩)
    (encodeQuadruple_injOn hA k)
  simpa [card_product, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using h

private lemma exists_pair_with_order {A : Finset ℤ} {s : ℤ} (hs : s ∈ A + A)
    (hdouble : s ∉ A.image (fun a ↦ a + a)) (o : Bool) :
    ∃ a ∈ A, ∃ b ∈ A, a + b = s ∧ decide (a ≤ b) = o := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
  have hne : a ≠ b := by
    rintro rfl
    exact hdouble (mem_image_of_mem _ hb)
  by_cases hle : decide (a ≤ b) = o
  · exact ⟨a, ha, b, hb, rfl, hle⟩
  · refine ⟨b, hb, a, ha, add_comm b a, ?_⟩
    cases o <;> simp at hle ⊢ <;> omega

private lemma four_card_gap_sum_le_card_quadruples (A : Finset ℤ) (k : ℤ) :
    4 * (gap (A + A) k).card ≤ (quadruples A k).card + 8 * A.card := by
  let D := A.image (fun a ↦ a + a)
  let G := gap (A + A) k
  let B := D ∪ shift D k
  have hbad : B.card ≤ 2 * A.card := by
    have hu := card_union_le D (shift D k)
    rw [card_shift] at hu
    have hd : D.card ≤ A.card := card_image_le
    change (D ∪ shift D k).card ≤ _
    omega
  have hgood : 4 * (G \ B).card ≤ (quadruples A k).card := by
    have h := card_le_card_of_surjOn
      (s := quadruples A k) (t := (G \ B) ×ˢ (univ : Finset (Bool × Bool))) encodeQuadruple (by
        rintro ⟨s, o, p⟩ hsp
        obtain ⟨hs, hn⟩ := mem_sdiff.mp (mem_product.mp hsp).1
        obtain ⟨hs₁, hs₂⟩ := mem_gap.mp hs
        have hn₁ : s ∉ D := fun h ↦ hn (mem_union_left _ h)
        have hn₂ : s + k ∉ D := fun h ↦ hn (mem_union_right _ (mem_shift.mpr h))
        obtain ⟨a, ha, b, hb, he₁, ho⟩ := exists_pair_with_order hs₁ hn₁ o
        obtain ⟨c, hc, d, hd, he₂, hp⟩ := exists_pair_with_order hs₂ hn₂ p
        refine ⟨((a, b), (c, d)), mem_quadruples.mpr ⟨⟨ha, hb⟩, ⟨hc, hd⟩, by omega⟩, ?_⟩
        exact Prod.ext he₁ (Prod.ext ho hp))
    simpa [card_product, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using h
  have hpart := card_sdiff_add_card_inter G B
  have hinter : (G ∩ B).card ≤ B.card := card_le_card inter_subset_right
  change 4 * G.card ≤ _
  omega

private lemma sq_card_le_isolated_add_linear (A : Finset ℤ) (hA : (A : Set ℤ).IsSidon) :
    A.card * A.card ≤ 16 * (isolated (A + A)).card + 50 * A.card := by
  have transfer (k : ℤ) (hk : k ≠ 0) :
      4 * (gap (A + A) k).card ≤ (gap (A - A) k).card + 10 * A.card := by
    have h₁ := four_card_gap_sum_le_card_quadruples A k
    have h₂ := card_quadruples_le_card_gap_diff hA hk
    omega
  -- Apply the four-point inequality to differences, then transfer back to the sumset.
  have h₁ := transfer 1 (by decide)
  have h₂ := (card_gap_diff_le_card_quadruples A 2).trans
    (card_quadruples_le_four_card_gap_sum hA 2)
  have h₃ := transfer 3 (by decide)
  have hd := four_mul_card_gap_one_add_card_gap_three (A - A)
  have hs := twice_card_gap_two (A + A)
  have hi := card_isolated_add_twice_gap (A + A)
  have hsum := card_product_le_twice_card_sum A hA
  have hdiff : (A - A).card ≤ A.card * A.card := Finset.card_sub_le
  omega

private lemma isSidon_image_int {A : Finset ℕ} (hA : IsSidon A) :
    ((A.image Int.ofNat : Finset ℤ) : Set ℤ).IsSidon := by
  intro a ha b hb c hc d hd hsum
  obtain ⟨a', ha', rfl⟩ := mem_image.mp ha
  obtain ⟨b', hb', rfl⟩ := mem_image.mp hb
  obtain ⟨c', hc', rfl⟩ := mem_image.mp hc
  obtain ⟨d', hd', rfl⟩ := mem_image.mp hd
  change (a' : ℤ) + (b' : ℤ) = (c' : ℤ) + (d' : ℤ) at hsum
  have h : a' + b' = c' + d' := by exact_mod_cast hsum
  simpa using hA a' ha' b' hb' c' hc' d' hd' h

private lemma sumset_image_int (A : Finset ℕ) :
    (Sumset A).image Int.ofNat = A.image Int.ofNat + A.image Int.ofNat := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp hy
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    exact Finset.mem_add.mpr ⟨a, mem_image_of_mem _ ha, b, mem_image_of_mem _ hb, by simp⟩
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨a', ha', rfl⟩ := mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := mem_image.mp hb
    refine mem_image.mpr ⟨a' + b', ?_, by simp⟩
    have hp : (a', b') ∈ A ×ˢ A := mem_product.mpr ⟨ha', hb'⟩
    exact mem_image_of_mem (fun p : ℕ × ℕ ↦ p.1 + p.2) hp

private lemma card_isolated_image_int (S : Finset ℕ) :
    (isolated (S.image Int.ofNat)).card = IsolatedCount S := by
  let T := S.filter (fun a ↦ a + 1 ∉ S ∧ (a = 0 ∨ a - 1 ∉ S))
  have hmem (a : ℕ) : (a : ℤ) ∈ S.image Int.ofNat ↔ a ∈ S := by simp
  have hsucc (a : ℕ) : (a : ℤ) + 1 ∈ S.image Int.ofNat ↔ a + 1 ∈ S := by
    simpa using hmem (a + 1)
  have hpred (a : ℕ) : (a : ℤ) - 1 ∉ S.image Int.ofNat ↔ a = 0 ∨ a - 1 ∉ S := by
    by_cases ha : a = 0
    · subst a
      refine iff_of_true (fun h ↦ ?_) (Or.inl rfl)
      obtain ⟨b, _, hb⟩ := mem_image.mp h
      change (b : ℤ) = (0 : ℤ) - 1 at hb
      omega
    · have he : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
      rw [← he, hmem, or_iff_right ha]
  have himage : isolated (S.image Int.ofNat) = T.image Int.ofNat := by
    have h (a : ℕ) : (a : ℤ) ∈ isolated (S.image Int.ofNat) ↔ a ∈ T := by
      simp only [T, mem_isolated, hmem, hsucc, hpred, mem_filter]
    ext x
    constructor
    · intro hx
      obtain ⟨a, _, rfl⟩ := mem_image.mp (mem_isolated.mp hx).1
      exact mem_image_of_mem _ ((h a).mp hx)
    · intro hx
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
      exact (h a).mpr ha
  rw [himage, card_image_of_injective _ Int.ofNat_injective]
  rfl

/--
**Large Sidon sets have many isolated sums.** For every natural number $M \ge 1$ there is a
natural number $K$ such that every finite Sidon set $A$ of natural numbers with at least $K$
elements has at least $M$ isolated elements in its sumset $A + A = \{x + y : x, y \in A\}$. Here
$A$ is a Sidon set when $a + b = c + d$ with $a, b, c, d \in A$ implies $\{a, b\} = \{c, d\}$,
and an element $s$ of $A + A$ is isolated when $s + 1 \notin A + A$ and either $s = 0$ or
$s - 1 \notin A + A$.

This answers Erdős Problem 152 affirmatively: Tsoukalas et al. show, with a Lean proof, that
every Sidon set $A$ of $n$ natural numbers has at least $(n^2 - 100n - 16)/16$ isolated elements
in $A + A$.

Source: George
Tsoukalas et al., Advancing Mathematics Research with AI-Driven Formal Proof Search, arXiv
preprint (2026), arXiv:2605.22763, https://arxiv.org/abs/2605.22763. Moved from
`OpenConjectures/Combinatorics/ErdosSidonIsolatedSums`.
-/
public theorem conjecture_holds : conjecture := by
  intro M _
  refine ⟨max 51 (16 * M), fun A hA hK ↦ ?_⟩
  have h := sq_card_le_isolated_add_linear (A.image Int.ofNat) (isSidon_image_int hA)
  rw [← sumset_image_int, card_isolated_image_int,
    card_image_of_injective _ Int.ofNat_injective] at h
  have h₁ := Nat.mul_le_mul_right A.card ((le_max_left 51 (16 * M)).trans hK)
  have h₂ := (le_max_right 51 (16 * M)).trans hK
  omega

end MathlibExt.Combinatorics.ErdosSidonIsolatedSumsWanted
