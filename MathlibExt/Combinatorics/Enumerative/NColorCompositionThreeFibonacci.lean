/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.Combinatorics.Enumerative.NColorCompositionBinomialSum
import Mathlib.Basic.Finite.Sum

/-!
# Fibonacci identity for compositions with colors 3 and 4

Partition the compositions of `k + 4` by the first part. Shortening a part whose size exceeds
its color leaves weight `k + 3`; removing a leading `(3, 3)` or `(4, 4)` leaves weight `k + 1`
or `k`, respectively. Thus if `c` is the composition count, the shifted sum
`c (k + 2) + c k` satisfies the Fibonacci recurrence. This is a recurrence proof of
Hopkins and Wang, Proposition 10, in place of their bijection with uncolored compositions.
-/

set_option autoImplicit false

namespace MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted

private def prependExactColor {n m : ℕ} (c : ℕ) (hc : c = 3 ∨ c = 4)
    (p : ColorCompAllowed 3 n) (hs : c + n = m) : ColorCompAllowed 3 m :=
  ⟨(c, c) :: p.val, by
    simp only [List.forall_mem_cons, List.map_cons, List.sum_cons]
    exact ⟨⟨⟨by omega, le_rfl, hc⟩, p.property.1⟩, (congrArg (c + ·) p.property.2).trans hs⟩⟩

private def growLeadingPart {k : ℕ} : ColorCompAllowed 3 (k + 3) → ColorCompAllowed 3 (k + 4)
  | ⟨[], h⟩ => False.elim (by simpa using h.2)
  | ⟨(s, c) :: l, h⟩ => ⟨(s + 1, c) :: l, by
    simp only [List.forall_mem_cons, List.map_cons, List.sum_cons] at h ⊢
    obtain ⟨⟨⟨hcpos, hcs, hc⟩, htail⟩, hsum⟩ := h
    exact ⟨⟨⟨hcpos, by omega, hc⟩, htail⟩, by omega⟩⟩

private def splitThreeLeading {k : ℕ} : ColorCompAllowed 3 (k + 4) →
    ColorCompAllowed 3 (k + 3) ⊕ (ColorCompAllowed 3 (k + 1) ⊕ ColorCompAllowed 3 k)
  | ⟨[], h⟩ => False.elim (by simpa using h.2)
  | ⟨(s, c) :: l, h⟩ => by
    simp only [List.forall_mem_cons, List.map_cons, List.sum_cons] at h
    obtain ⟨⟨⟨hcpos, hcs, hc⟩, htail⟩, hsum⟩ := h
    if hsc : s = c then
      if h : c = 3 then
        exact .inr (.inl ⟨l, htail, by omega⟩)
      else
        exact .inr (.inr ⟨l, htail, by omega⟩)
    else
      exact .inl ⟨(s - 1, c) :: l, by
        simp only [List.forall_mem_cons, List.map_cons, List.sum_cons]
        exact ⟨⟨⟨hcpos, by omega, hc⟩, htail⟩, by omega⟩⟩

private def joinThreeLeading {k : ℕ} :
    ColorCompAllowed 3 (k + 3) ⊕ (ColorCompAllowed 3 (k + 1) ⊕ ColorCompAllowed 3 k) →
      ColorCompAllowed 3 (k + 4)
  | .inl p => growLeadingPart p
  | .inr (.inl p) => prependExactColor 3 (Or.inl rfl) p (by omega)
  | .inr (.inr p) => prependExactColor 4 (Or.inr rfl) p (by omega)

private def threeLeadingEquiv (k : ℕ) : ColorCompAllowed 3 (k + 4) ≃
    ColorCompAllowed 3 (k + 3) ⊕ (ColorCompAllowed 3 (k + 1) ⊕ ColorCompAllowed 3 k) where
  toFun := splitThreeLeading
  invFun := joinThreeLeading
  left_inv := by
    rintro ⟨l, h⟩
    cases l with
    | nil => exact False.elim (by simpa using h.2)
    | cons p l =>
      obtain ⟨s, c⟩ := p
      have hp := h.1 (s, c) (by simp)
      change 1 ≤ c ∧ c ≤ s ∧ (c = 3 ∨ c = 4) at hp
      by_cases hsc : s = c
      · rcases hp.2.2 with hc | hc
        · subst s; subst c; rfl
        · subst s; subst c; rfl
      · apply Subtype.ext
        simp [splitThreeLeading, joinThreeLeading, growLeadingPart, hsc,
          Nat.sub_add_cancel (by omega : 1 ≤ s)]
  right_inv := by
    rintro (p | p | p)
    · obtain ⟨l, h⟩ := p
      cases l with
      | nil => exact False.elim (by simpa using h.2)
      | cons p l =>
        obtain ⟨s, c⟩ := p
        have hcs : c ≤ s := (h.1 (s, c) (by simp)).2.1
        simp [joinThreeLeading, growLeadingPart, splitThreeLeading, show s + 1 ≠ c by omega]
    · cases p; rfl
    · cases p; rfl

private theorem eq_nil_of_lt_three {n : ℕ} (hn : n < 3) (p : ColorCompAllowed 3 n) :
    p.val = [] := by
  obtain ⟨l, hparts, hsum⟩ := p
  cases l with
  | nil => rfl
  | cons p l =>
    obtain ⟨s, c⟩ := p
    have hp : 1 ≤ c ∧ c ≤ s ∧ (c = 3 ∨ c = 4) := hparts (s, c) (by simp)
    simp only [List.map_cons, List.sum_cons] at hsum
    omega

private def emptyThreeEquiv : ColorCompAllowed 3 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], by simp⟩
  left_inv p := Subtype.ext (eq_nil_of_lt_three (by decide) p).symm
  right_inv := by intro u; cases u; rfl

private theorem shortIsEmpty {n : ℕ} (hpos : 0 < n) (hn : n < 3) :
    IsEmpty (ColorCompAllowed 3 n) := by
  refine ⟨fun p => ?_⟩
  have hs := p.property.2
  rw [eq_nil_of_lt_three hn p] at hs
  simp at hs
  omega

private def singletonThreeEquiv : ColorCompAllowed 3 3 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[(3, 3)], by simp⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases l with
    | nil => exact False.elim (by simpa using h.2)
    | cons p l =>
      obtain ⟨s, c⟩ := p
      have hp : 1 ≤ c ∧ c ≤ s ∧ (c = 3 ∨ c = 4) := h.1 (s, c) (by simp)
      have hs := h.2
      simp only [List.map_cons, List.sum_cons] at hs
      have hl : l = [] := eq_nil_of_lt_three (n := 0) (by decide)
        ⟨l, (fun p hp => h.1 p (List.mem_cons_of_mem _ hp)), by omega⟩
      have hsize : s = 3 := by omega
      have hcolor : c = 3 := by omega
      apply Subtype.ext
      simp [hsize, hcolor, hl]
  right_inv := by intro u; cases u; rfl

private theorem allowedThreeFinite (n : ℕ) : Finite (ColorCompAllowed 3 n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n < 4
    · obtain rfl | rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
      · exact Finite.of_equiv Unit emptyThreeEquiv.symm
      · have := shortIsEmpty (n := 1) (by decide) (by decide)
        infer_instance
      · have := shortIsEmpty (n := 2) (by decide) (by decide)
        infer_instance
      · exact Finite.of_equiv Unit singletonThreeEquiv.symm
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have := ih (k + 3) (by omega)
      have := ih (k + 1) (by omega)
      have := ih k (by omega)
      exact Finite.of_equiv _ (threeLeadingEquiv k).symm

private theorem ccoAllowed_three_step (k : ℕ) : ccoAllowed 3 (k + 4) =
    ccoAllowed 3 (k + 3) + (ccoAllowed 3 (k + 1) + ccoAllowed 3 k) := by
  have := allowedThreeFinite (k + 3)
  have := allowedThreeFinite (k + 1)
  have := allowedThreeFinite k
  unfold ccoAllowed
  simpa only [Nat.card_sum] using Nat.card_congr (threeLeadingEquiv k)

private theorem ccoAllowed_small {n : ℕ} (hpos : 0 < n) (hn : n < 3) : ccoAllowed 3 n = 0 := by
  exact @Nat.card_of_isEmpty _ (shortIsEmpty hpos hn)

private theorem ccoAllowed_add_fib (k : ℕ) :
    ccoAllowed 3 (k + 2) + ccoAllowed 3 k = Nat.fib (k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [ccoAllowed_small (by decide) (by decide), ccoAllowed, Nat.card_congr emptyThreeEquiv,
      Nat.card_unique]
    decide
  | one =>
    rw [ccoAllowed_small (n := 1) (by decide) (by decide), ccoAllowed,
      Nat.card_congr singletonThreeEquiv, Nat.card_unique]
    decide
  | more k ih₀ ih₁ =>
    change ccoAllowed 3 (k + 4) + ccoAllowed 3 (k + 2) = Nat.fib ((k + 1) + 2)
    calc
      _ = (ccoAllowed 3 (k + 2) + ccoAllowed 3 k) +
          (ccoAllowed 3 (k + 3) + ccoAllowed 3 (k + 1)) := by
        rw [ccoAllowed_three_step]
        omega
      _ = _ := by rw [Nat.fib_add_two, ih₀, ← ih₁]

/-- **Fibonacci identity for n-color compositions with colors 3 and 4.** For a natural number
$m$, let $\operatorname{cco}_{3,4}(m)$ be the number of $n$-color compositions of $m$ in which
every part has color $3$ or $4$, and let $F_k$ be the Fibonacci numbers with $F_0 = 0$ and
$F_1 = 1$. Then for every natural number $n \ge 3$,
$\operatorname{cco}_{3,4}(n) + \operatorname{cco}_{3,4}(n-2) = F_{n-1}$.

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Proposition 10. -/
public theorem ccoAllowed_three_add (n : ℕ) (hn : 3 ≤ n) :
    ccoAllowed 3 n + ccoAllowed 3 (n - 2) = Nat.fib (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  exact ccoAllowed_add_fib k

end MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted
