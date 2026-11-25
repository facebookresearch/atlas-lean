/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Finite.Sum
import Mathlib.Tactic.Ring

/-!
# Binomial sum for compositions with colors 1 and 2

For total size `n + 2`, partition by the first part: remove a leading `(1, 1)` or `(2, 2)`,
or shorten the first part by one if its size exceeds its color. This gives two copies of the
compositions of `n + 1` and one of those of `n`. Pascal's identity gives the same recurrence
for the even-indexed binomial sum. This is an alternative to the endpoint selection proof
of Hopkins and Wang, Theorem 3.

The public definitions and theorem keep their original `NColorCompositionsWanted` namespace.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted

/-- **n-color compositions with two allowed consecutive colors.** For natural numbers $b$ and $n$,
$\mathrm{CCo}_{b,b+1}(n)$ is the set of $n$-color compositions of $n$ that use only the colors $b$
and $b+1$: finite sequences of pairs $(k_1, c_1), \dots, (k_m, c_m)$ of natural numbers (part
$k_i$ with color $c_i$) such that $1 \le c_i \le k_i$ and $c_i \in \{b, b+1\}$ for every $i$, and
$k_1 + \dots + k_m = n$. -/
def ColorCompAllowed (b n : ℕ) : Type :=
  { l : List (ℕ × ℕ) //
    (∀ pc ∈ l, 1 ≤ pc.2 ∧ pc.2 ≤ pc.1 ∧ (pc.2 = b ∨ pc.2 = b + 1)) ∧
      (l.map Prod.fst).sum = n }

/-- **Count of n-color compositions with two consecutive colors.** An $n$-color composition of a
natural number $n$ is a finite sequence of parts, each a positive integer $k$ carrying a color
$c$ with $1 \le c \le k$, whose sizes sum to $n$. For natural numbers $b$ and $n$,
$\operatorname{cco}_{b,b+1}(n)$ is the number of $n$-color compositions of $n$ in which every
part has color $b$ or $b+1$. -/
noncomputable def ccoAllowed (b n : ℕ) : ℕ :=
  Nat.card (ColorCompAllowed b n)

private def prepend {n k c m : ℕ} (h : 1 ≤ c ∧ c ≤ k ∧ (c = 1 ∨ c = 2))
    (p : ColorCompAllowed 1 n) (hs : k + n = m) : ColorCompAllowed 1 m :=
  ⟨(k, c) :: p.val, by
    simp only [List.forall_mem_cons, List.map_cons, List.sum_cons]
    exact ⟨⟨h, p.property.1⟩, (congrArg (k + ·) p.property.2).trans hs⟩⟩

private def grow {n : ℕ} : ColorCompAllowed 1 (n + 1) → ColorCompAllowed 1 (n + 2)
  | ⟨[], h⟩ => False.elim (by simpa using h.2)
  | ⟨(k, c) :: l, h⟩ => ⟨(k + 1, c) :: l, by
    simp only [List.forall_mem_cons, List.map_cons, List.sum_cons] at h ⊢
    obtain ⟨⟨⟨hcpos, hcle, hcolor⟩, hparts⟩, hsum⟩ := h
    exact ⟨⟨⟨hcpos, by omega, hcolor⟩, hparts⟩, by omega⟩⟩

private def splitLeading {n : ℕ} : ColorCompAllowed 1 (n + 2) →
    ColorCompAllowed 1 (n + 1) ⊕ (ColorCompAllowed 1 (n + 1) ⊕ ColorCompAllowed 1 n)
  | ⟨[], h⟩ => False.elim (by simpa using h.2)
  | ⟨(k, c) :: l, h⟩ => by
    simp only [List.forall_mem_cons, List.map_cons, List.sum_cons] at h
    obtain ⟨⟨⟨hcpos, hcle, hcolor⟩, hparts⟩, hsum⟩ := h
    if hkc : k = c then
      if hc : c = 1 then
        exact .inl ⟨l, hparts, by omega⟩
      else
        exact .inr (.inr ⟨l, hparts, by omega⟩)
    else
      exact .inr (.inl ⟨(k - 1, c) :: l, by
        simp only [List.forall_mem_cons, List.map_cons, List.sum_cons]
        exact ⟨⟨⟨hcpos, by omega, hcolor⟩, hparts⟩, by omega⟩⟩)

private def joinLeading {n : ℕ} :
    ColorCompAllowed 1 (n + 1) ⊕ (ColorCompAllowed 1 (n + 1) ⊕ ColorCompAllowed 1 n) →
      ColorCompAllowed 1 (n + 2)
  | .inl p => prepend (k := 1) (c := 1) (by decide) p (by omega)
  | .inr (.inl p) => grow p
  | .inr (.inr p) => prepend (k := 2) (c := 2) (by decide) p (by omega)

private def leadingEquiv (n : ℕ) : ColorCompAllowed 1 (n + 2) ≃
    ColorCompAllowed 1 (n + 1) ⊕ (ColorCompAllowed 1 (n + 1) ⊕ ColorCompAllowed 1 n) where
  toFun := splitLeading
  invFun := joinLeading
  left_inv := by
    rintro ⟨l, h⟩
    cases l with
    | nil => exact False.elim (by simpa using h.2)
    | cons p l =>
      obtain ⟨k, c⟩ := p
      have hp := h.1 (k, c) (by simp)
      change 1 ≤ c ∧ c ≤ k ∧ (c = 1 ∨ c = 2) at hp
      by_cases hkc : k = c
      · rcases hp.2.2 with hc | hc
        · subst k; subst c; rfl
        · subst k; subst c; rfl
      · apply Subtype.ext
        simp [splitLeading, joinLeading, grow, hkc, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  right_inv := by
    rintro (p | p | p)
    · cases p; rfl
    · obtain ⟨l, h⟩ := p
      cases l with
      | nil => exact False.elim (by simpa using h.2)
      | cons p l =>
        obtain ⟨k, c⟩ := p
        have hp := (h.1 (k, c) (by simp)).2.1
        change c ≤ k at hp
        simp [joinLeading, grow, splitLeading, show k + 1 ≠ c by omega]
    · cases p; rfl

private def zeroEquiv : ColorCompAllowed 1 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], by simp⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases l with
    | nil => rfl
    | cons p l =>
      have hp := h.1 p (by simp)
      have hs := h.2
      simp only [List.map_cons, List.sum_cons] at hs
      omega
  right_inv := by intro u; cases u; rfl

private def oneEquiv : ColorCompAllowed 1 1 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[(1, 1)], by simp⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases l with
    | nil => exact False.elim (by simpa using h.2)
    | cons p l =>
      have hp := h.1 p (by simp)
      cases l with
      | nil =>
        obtain ⟨k, c⟩ := p
        have hs : k = 1 := h.2
        have hc : c = 1 := by omega
        subst k
        subst c
        rfl
      | cons q l =>
        have hq := h.1 q (by simp)
        have hs := h.2
        simp only [List.map_cons, List.sum_cons] at hs
        omega
  right_inv := by intro u; cases u; rfl

private theorem allowedFinite (n : ℕ) : Finite (ColorCompAllowed 1 n) := by
  induction n using Nat.twoStepInduction with
  | zero => exact Finite.of_equiv Unit zeroEquiv.symm
  | one => exact Finite.of_equiv Unit oneEquiv.symm
  | more n ih₀ ih₁ =>
    have : Finite (ColorCompAllowed 1 n) := ih₀
    have : Finite (ColorCompAllowed 1 (n + 1)) := ih₁
    exact Finite.of_equiv _ (leadingEquiv n).symm

private theorem ccoAllowed_step (n : ℕ) :
    ccoAllowed 1 (n + 2) = ccoAllowed 1 (n + 1) + (ccoAllowed 1 (n + 1) + ccoAllowed 1 n) := by
  have := allowedFinite n
  have := allowedFinite (n + 1)
  unfold ccoAllowed
  simpa only [Nat.card_sum] using Nat.card_congr (leadingEquiv n)

private def evenSum (n r : ℕ) : ℕ := ∑ m ∈ Finset.range r, 2 ^ m * n.choose (2 * m)

private def oddSum (n r : ℕ) : ℕ := ∑ m ∈ Finset.range r, 2 ^ m * n.choose (2 * m + 1)

private theorem oddSum_step (n r : ℕ) : oddSum (n + 1) r = evenSum n r + oddSum n r := by
  unfold evenSum oddSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by rw [Nat.choose_succ_succ', mul_add]

private theorem evenSum_step (n r : ℕ) :
    evenSum (n + 1) (r + 1) = evenSum n (r + 1) + 2 * oddSum n r := by
  unfold evenSum oddSum
  rw [Finset.sum_range_succ' (f := fun m => 2 ^ m * (n + 1).choose (2 * m)),
    Finset.sum_range_succ' (f := fun m => 2 ^ m * n.choose (2 * m))]
  simp only [mul_zero, Nat.choose_zero_right, pow_zero, one_mul]
  rw [add_right_comm _ 1, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Nat.choose_succ_succ', pow_succ]
  ring

private theorem evenSum_of_le_one (n r : ℕ) (hn : n ≤ 1) : evenSum n (r + 1) = 1 := by
  unfold evenSum
  rw [Finset.sum_range_succ']
  have hzero (m : ℕ) : n.choose (2 * (m + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [hzero]

-- Keeping the upper limit variable lets Pascal's identity use the same cutoff in both parities.
private theorem ccoAllowed_eq_evenSum (n r : ℕ) (hr : n / 2 < r) :
    ccoAllowed 1 n = evenSum n r := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  induction n using Nat.twoStepInduction generalizing r with
  | zero =>
    rw [ccoAllowed, Nat.card_congr zeroEquiv, Nat.card_unique, evenSum_of_le_one 0 r (by decide)]
  | one =>
    rw [ccoAllowed, Nat.card_congr oneEquiv, Nat.card_unique, evenSum_of_le_one 1 r (by decide)]
  | more n ih₀ ih₁ =>
    -- At this cutoff the last summand for `n` is already zero.
    have hpad : evenSum n (r + 1) = evenSum n r := by
      unfold evenSum
      rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (by omega : n < 2 * r), mul_zero,
        add_zero]
    have hstep := evenSum_step n r
    rw [ccoAllowed_step, ih₁ r (by omega), ih₀ r (by omega), evenSum_step (n + 1), oddSum_step]
    change evenSum (n + 1) (r + 1) + (evenSum (n + 1) (r + 1) + evenSum n (r + 1)) =
      evenSum (n + 1) (r + 1) + 2 * (evenSum n r + oddSum n r)
    omega

/-- **Binomial sum for n-color compositions with colors 1 and 2.** For every natural number
$n \ge 1$, the number $\operatorname{cco}_{1,2}(n)$ of $n$-color compositions of $n$ in which
every part has color $1$ or $2$ satisfies
$$\operatorname{cco}_{1,2}(n) = \sum_{m=0}^{\lfloor n/2 \rfloor} 2^m \binom{n}{2m}.$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 3. -/
theorem ccoAllowed_one_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    ccoAllowed 1 n =
      ∑ m ∈ Finset.range (n / 2 + 1), 2 ^ m * Nat.choose n (2 * m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact ccoAllowed_eq_evenSum (k + 1) _ (Nat.lt_succ_self _)

end MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted
