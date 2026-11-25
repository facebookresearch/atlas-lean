/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Almost-palindromic width of the rank-two free group

We prove that the almost-palindromic width of the free group on two generators is infinite
for every fixed number of allowed letter changes, answering Kourovka Notebook Problem 19.8.

As in Staiger's formulation, the words representing the almost palindromes may be unreduced.
We count signed transitions between adjacent letters after free reduction. Reversal negates
the count, and multiplication has defect at most three. Thus each letter change in a palindrome
has bounded effect, while the count grows linearly on powers of the commutator.

## Record carried over from the retired wanted module

From `WantedExt/GroupTheory/AlmostPalindromicWidthKourovka19Problem8Wanted.lean`:

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.8 (V. G. Bardakov). UnsolvedMath record
UM-00701556 (`KOU-19.8`), dataset ulamai/UnsolvedMath v1.8.0.

Words are lists of letters `(i, b)` (`i : Fin 2`, `b = false` for an inverse letter), not
necessarily reduced, as in Staiger's paper, and represent elements via `FreeGroup.mk`. Allowing
unreduced words gives more almost palindromes than reduced words do, so the refutation also covers
the reduced reading.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.AlmostPalindromicWidthKourovka19Problem8Wanted

/-- **Almost palindromes.** For a natural number $m$, a word $w$ in the letters $x^{\pm 1}$ and
$y^{\pm 1}$ is an almost $m$-palindrome if there is a palindrome $p$ in the same letters with the
same length as $w$ such that $w$ and $p$ differ in at most $m$ positions. The word $w$ need not be
reduced. -/
def IsAlmostPalindrome (m : ℕ) (w : List (Fin 2 × Bool)) : Prop :=
  ∃ p : List (Fin 2 × Bool), p.length = w.length ∧ p.reverse = p ∧
    (List.zip w p).countP (fun q => q.1 ≠ q.2) ≤ m

/-- **Finite almost-palindromic width of $F_2$ (Kourovka 19.8).** The proposition that there are
positive integers $m$ and $c$ such that every element of the free group $F_2$ on generators $x, y$
is a product of at most $c$ elements, each represented by an almost $m$-palindrome, that is, by a
word in $x^{\pm 1}, y^{\pm 1}$ (not necessarily reduced) that differs from a palindrome of the
same length in at most $m$ positions.

This is the question posed by V. G. Bardakov as Kourovka Problem 19.8. -/
def almostPalindromicWidthFinite : Prop :=
  ∃ m c : ℕ, 0 < m ∧ 0 < c ∧ ∀ g : FreeGroup (Fin 2), ∃ ws : List (List (Fin 2 × Bool)),
    ws.length ≤ c ∧ (∀ w ∈ ws, IsAlmostPalindrome m w) ∧ (ws.map FreeGroup.mk).prod = g

open FreeGroup

private abbrev Letter := Fin 2 × Bool
private abbrev Word := List Letter

-- Count a transition from x to y with weight +1 and the reverse transition with weight -1,
-- provided the letters have the same sign. Missing endpoints have weight zero.
private def turn : Option Letter → Option Letter → ℤ
  | some a, some b => if a.2 = b.2 then (b.1.val : ℤ) - a.1.val else 0
  | _, _ => 0

private theorem turn_bounds (a b : Option Letter) : -1 ≤ turn a b ∧ turn a b ≤ 1 := by
  cases a with
  | none => simp [turn]
  | some a =>
    cases b with
    | none => simp [turn]
    | some b =>
      have := a.1.isLt
      have := b.1.isLt
      simp only [turn]
      split <;> omega

private theorem turn_swap (a b : Option Letter) : turn a b = -turn b a := by
  cases a <;> cases b <;> simp [turn, eq_comm]
  split <;> omega

private def weight : Word → ℤ
  | [] => 0
  | a :: w => turn (some a) w.head? + weight w

private theorem weight_append (u v : Word) :
    weight (u ++ v) = weight u + weight v + turn u.getLast? v.head? := by
  induction u with
  | nil => simp [weight, turn]
  | cons a u ih =>
    cases u with
    | nil => simp [weight, turn, add_comm]
    | cons b u =>
      simp only [List.cons_append, weight, List.head?_cons, List.getLast?_cons_cons] at ih ⊢
      omega

private theorem weight_reverse (w : Word) : weight w.reverse = -weight w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [List.reverse_cons, weight_append, ih, weight]
    simp only [List.head?_cons, List.getLast?_reverse]
    rw [turn_swap w.head?]
    simp [weight, turn]

private theorem weight_invRev (w : Word) : weight (invRev w) = -weight w := by
  rw [invRev, weight_reverse]
  congr 1
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, weight, ih]
    cases w <;> simp [turn]

-- Multiplying two reduced words cancels a suffix of the first against its inverse in
-- the second. The words on either side of that cancellation survive intact.
private theorem cancellation {u v : Word} (hu : IsReduced u) (hv : IsReduced v) :
    ∃ l s r : Word, u = l ++ s ∧ v = invRev s ++ r ∧ reduce (u ++ v) = l ++ r := by
  induction u using List.reverseRecOn generalizing v with
  | nil => exact ⟨[], [], v, rfl, rfl, by simpa using hv.reduce_eq⟩
  | append_singleton u a ih =>
    cases v with
    | nil => exact ⟨u ++ [a], [], [], by simp, rfl, by simpa using hu.reduce_eq⟩
    | cons b v =>
      by_cases h : a.1 = b.1 → a.2 = b.2
      · have hred : IsReduced ((u ++ [a]) ++ b :: v) := by
          simpa only [List.append_assoc, List.singleton_append, IsReduced,
            List.isChain_append_cons_cons] using And.intro hu (And.intro h hv)
        exact ⟨_, [], _, by simp, rfl, hred.reduce_eq⟩
      · obtain ⟨i, e⟩ := a
        obtain ⟨j, f⟩ := b
        simp only [not_imp] at h
        obtain ⟨rfl, h⟩ := h
        have hf : f = !e := by cases f <;> cases e <;> simp_all
        subst f
        obtain ⟨l, s, r, hl, hr, hred⟩ := ih (v := v) hu.left_of_append hv.tail
        refine ⟨l, s ++ [(i, e)], r, by simp [hl], by rw [hr, invRev_append]; rfl, ?_⟩
        simpa only [List.append_assoc, List.singleton_append] using
          (reduce.Step.eq (Red.Step.not (L₁ := u) (L₂ := v) (x := i) (b := e))).trans hred

private def score (g : FreeGroup (Fin 2)) : ℤ := weight g.toWord

private theorem score_mul (g h : FreeGroup (Fin 2)) :
    -3 ≤ score (g * h) - (score g + score h) ∧ score (g * h) - (score g + score h) ≤ 3 := by
  obtain ⟨l, s, r, hg, hh, hred⟩ := cancellation (isReduced_toWord (x := g))
    (isReduced_toWord (x := h))
  unfold score
  rw [toWord_mul, hred, hg, hh]
  simp only [weight_append, weight_invRev]
  have := turn_bounds l.getLast? r.head?
  have := turn_bounds l.getLast? s.head?
  have := turn_bounds (invRev s).getLast? r.head?
  omega

private theorem reduce_reverse (w : Word) : reduce w.reverse = (reduce w).reverse := by
  have step {u v : Word} (h : Red.Step u v) : Red.Step u.reverse v.reverse := by
    obtain @⟨l, r, i, b⟩ := h
    simp [List.append_assoc]
  have h := Relation.ReflTransGen.lift List.reverse (fun _ _ => step) _ _ (reduce.red (L := w))
  have hred : IsReduced (reduce w).reverse := by
    apply List.isChain_reverse.mpr
    exact (IsReduced.of_reduce_eq (reduce.idem (L := w))).imp fun _ _ h e => (h e.symm).symm
  exact (reduce.eq_of_red h).trans hred.reduce_eq

private theorem score_palindrome {p : Word} (hp : p.reverse = p) : score (mk p) = 0 := by
  have h : weight (reduce p.reverse) = weight (reduce p) := congrArg (weight ∘ reduce) hp
  rw [reduce_reverse, weight_reverse] at h
  change weight (reduce p) = 0
  omega

-- Replacing one letter in any context changes the score by at most four product defects.
private theorem score_substitution (l r : Word) (a b : Letter) :
    score (mk (l ++ a :: r)) ≤ score (mk (l ++ b :: r)) + 12 := by
  have split (x : Letter) :
      -6 ≤ score (mk (l ++ x :: r)) - (score (mk l) + score (mk r)) ∧
      score (mk (l ++ x :: r)) - (score (mk l) + score (mk r)) ≤ 6 := by
    have h₁ := score_mul (mk l) (mk (x :: r))
    have h₂ := score_mul (mk [x]) (mk r)
    have hx : score (mk [x]) = 0 := rfl
    rw [mul_mk] at h₁
    rw [mul_mk, List.singleton_append, hx] at h₂
    omega
  have := split a
  have := split b
  omega

private theorem score_edits (l w p : Word) (hlen : p.length = w.length) :
    score (mk (l ++ w)) ≤ score (mk (l ++ p)) +
      12 * ((w.zip p).countP (fun q => q.1 ≠ q.2) : ℕ) := by
  induction w generalizing l p with
  | nil =>
    obtain rfl : p = [] := List.length_eq_zero_iff.mp hlen
    simp
  | cons a w ih =>
    cases p with
    | nil => simp at hlen
    | cons b p =>
      have h := ih (l ++ [a]) p (by simpa using hlen)
      simp only [List.append_assoc, List.singleton_append] at h
      by_cases hab : a = b
      · subst b
        simpa using h
      · have := score_substitution l p a b
        rw [List.zip_cons_cons, List.countP_cons_of_pos (by simpa using hab)]
        omega

private theorem score_prod_bound (m : ℕ) (ws : List Word)
    (hall : ∀ w ∈ ws, IsAlmostPalindrome m w) :
    score (ws.map mk).prod ≤ (12 * (m : ℤ) + 3) * ws.length := by
  induction ws with
  | nil => simp [score, weight]
  | cons w ws ih =>
    obtain ⟨p, hlen, hp, hm⟩ := hall w List.mem_cons_self
    have hw := score_edits [] w p hlen
    simp only [List.nil_append, score_palindrome hp, zero_add] at hw
    have hm' : score (mk w) ≤ 12 * (m : ℤ) :=
      hw.trans (Int.mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr hm) (by decide))
    have ht := ih (fun v hv => hall v (List.mem_cons_of_mem _ hv))
    have := (score_mul (mk w) (ws.map mk).prod).2
    simp only [List.map_cons, List.prod_cons, List.length_cons, Int.natCast_succ,
      Int.mul_add, Int.mul_one]
    omega

-- Each copy of the cyclically reduced commutator contributes two positive turns. The
-- transition from its final inverse letter to the first letter of the next copy contributes zero.
private def commutatorWord : Word := [(0, true), (1, true), (0, false), (1, false)]

private theorem score_commutator_pow (n : ℕ) : score (mk commutatorWord ^ n) = 2 * (n : ℤ) := by
  have hc : IsCyclicallyReduced commutatorWord := by
    simp [commutatorWord, IsCyclicallyReduced, isReduced_cons_cons]
  rw [score, toWord_pow, toWord_mk, hc.isReduced.reduce_eq,
    (hc.flatten_replicate n).isReduced.reduce_eq]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, weight_append, ih]
    have h : turn commutatorWord.getLast? (List.replicate n commutatorWord).flatten.head? = 0 := by
      cases n <;> rfl
    rw [h, show weight commutatorWord = 2 from rfl]
    omega

/--
**The almost-palindromic width of $F_2$ is infinite (Kourovka 19.8).** There are no positive
integers $m$ and $c$ such that every element of the free group $F_2$ on generators $x, y$ is a
product of at most $c$ elements, each represented by an almost $m$-palindrome, that is, by a word
in $x^{\pm 1}, y^{\pm 1}$ (not necessarily reduced) that differs from a palindrome of the same
length in at most $m$ positions. So the question of Kourovka Problem 19.8 has a negative answer.

Staiger proved more: for every $m \ge 0$, the $m$-almost-palindromic width of every non-abelian
free group is infinite.

Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Problem 19.8 (V. G. Bardakov); resolution: M. Staiger, On the almost-palindromic width of
free groups, J. Algebra 659 (2024), 475-481 (arXiv:2306.15752), Section 1: m-almost-palindromes are
words of the free monoid on the letters x^{±1}, y^{±1} (not necessarily reduced) within Hamming
distance m of a palindrome, and the width is taken for the group elements they represent; Theorem 1:
for a non-abelian free group F and every m ≥ 0 the m-almost-palindromic width of F is infinite; the
Kourovka Notebook (21st issue) marks 19.8 solved: No, there are no such integers,
https://arxiv.org/abs/2306.15752.
-/
theorem almostPalindromicWidthFinite_refuted : ¬ almostPalindromicWidthFinite := by
  rintro ⟨m, c, _, _, h⟩
  let bound : ℤ := (12 * (m : ℤ) + 3) * c
  obtain ⟨ws, hlen, hall, hprod⟩ := h (mk commutatorWord ^ (bound.toNat + 1))
  have hscore := score_prod_bound m ws hall
  rw [hprod, score_commutator_pow] at hscore
  have hc : (12 * (m : ℤ) + 3) * ws.length ≤ bound :=
    Int.mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr hlen) (by omega)
  have := hscore.trans hc
  omega

end MathlibExt.GroupTheory.AlmostPalindromicWidthKourovka19Problem8Wanted
