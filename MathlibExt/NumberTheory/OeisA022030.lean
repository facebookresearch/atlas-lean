/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/OEIS/22030.lean` (Formal Conjectures):
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
Adapted portions: the definition of the sequence `a`, the definition of the conjecture and the
statement that it holds.
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# OEIS A022030 satisfies Barker's linear recurrence

The sequence `a` (OEIS A022030) starts with `a 0 = 4` and `a 1 = 16`. Its terms are positive,
and `a (n + 2)` is the largest integer below `a (n + 1) ^ 2 / a n` when `n` is even and the
smallest integer above it when `n` is odd: with natural-number division, the definition computes
`⌈a (n + 1) ^ 2 / a n⌉ - 1` as `(a (n + 1) ^ 2 + a n - 1) / a n - 1` and
`⌊a (n + 1) ^ 2 / a n⌋ + 1` as `a (n + 1) ^ 2 / a n + 1`. `conjecture_holds` proves Barker's
conjecture that `a n = 4 a (n - 1) - a (n - 3) + a (n - 4)` for every `n ≥ 4`.

## Proof outline

* Let `b` be the integer sequence with first terms `4, 16, 63, 249` that satisfies the linear
  recurrence, and let `D n = b (n + 1) ^ 2 - b n * b (n + 2)`. Given `b n` and `b (n + 1)`, the
  step of `a` produces `b (n + 2)` exactly when `0 < D n ≤ b n` for even `n` and
  `-b n ≤ D n < 0` for odd `n`, that is, when `g n = (-1) ^ n D n` satisfies `0 < g n ≤ b n`.
  Once this is shown, `a = b` by induction.
* Since `b` satisfies a linear recurrence of order four, `D` satisfies one of order six, whose
  characteristic roots are the products of two roots of `x ^ 4 - 4 x ^ 3 + x - 1`. Hence
  `g (n + 6) = g n - 3 g (n + 2) + 15 g (n + 3) + 3 g (n + 4)`.
* The characteristic polynomial `x ^ 6 - 3 x ^ 4 - 15 x ^ 3 + 3 x ^ 2 - 1` of `g` has a simple
  positive root `ρ ≈ 2.8207`, two complex roots of modulus about `2.3532` and three roots of
  modulus less than `1/2`. Six integer linear forms (`InCone`) cut out an open simplicial cone
  around the eigenvector of `ρ` that the four-step map
  `(g n, …, g (n + 5)) ↦ (g (n + 4), …, g (n + 9))` sends into itself: each form of the image is
  a positive combination of the six forms. The states for `n = 5, …, 8` lie in the cone, hence so
  does every state from `n = 5` on. On the cone, `g n` and `231 g n - g (n + 4)` are positive
  combinations of the six forms.
* Since `39 b n ≤ 10 b (n + 1)`, `231 b n ≤ b (n + 4)`, so `g n ≤ b n` passes from `n` to `n + 4`
  for `n ≥ 5`; it is checked directly for `n ≤ 8`.
* The recurrence of `b` then gives the statement. Its natural-number subtraction does not
  truncate, since `b` is increasing.

## Implementation notes

The definitions and the statement keep the full names they had in the former wanted module, so
the namespace still ends in `OeisA022030Wanted`.

The cone was found numerically from the real Jordan form of the four-step map, which turns the
complex eigenplane by about `159°` and shrinks it by the factor `0.48` relative to `ρ`, and its
forms were rounded to integers. The proof only checks it: `linarith` finds the positive
combinations.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.OeisA022030Wanted

/-! Source record `FC-OeisA022030`, ported from FormalConjectures
`OEIS/22030.lean` and checked against oeis.org/A022030. A nonlinear
recurrence sequence (core Lean only). Test evaluations omitted (proofs
live upstream). Status: resolved true (Barker's linear recurrence holds;
formal proof upstream). -/

/-- **The sequence OEIS A022030.** The sequence of natural numbers with $a(0) = 4$, $a(1) = 16$ and,
for every natural number $n$, $a(n + 2) = \lfloor (a(n + 1)^2 + a(n) - 1) / a(n) \rfloor - 1$ if
$n$ is even and $a(n + 2) = \lfloor a(n + 1)^2 / a(n) \rfloor + 1$ if $n$ is odd. -/
def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 4
  | 1 => 16
  | n + 2 =>
    if Even n then
      (a (n + 1) ^ 2 + a n - 1) / a n - 1
    else
      (a (n + 1) ^ 2) / a n + 1

/-- **Barker's linear recurrence for A022030.** The statement that for every natural number
$n \ge 4$, the sequence $a$ of OEIS A022030 satisfies $a(n) = 4a(n - 1) - a(n - 3) + a(n - 4)$,
with the subtraction taken in the natural numbers (truncated at $0$). -/
def conjecture : Prop :=
  ∀ (n : ℕ) (_hn : 4 ≤ n),
    a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

/-- The integer sequence with the first four terms of `a` that satisfies Barker's recurrence. -/
private def b : ℕ → ℤ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | 3 => 249
  | n + 4 => 4 * b (n + 3) - b (n + 1) + b n

private lemma b_add_four (n : ℕ) : b (n + 4) = 4 * b (n + 3) - b (n + 1) + b n := by
  rw [b]

/-- The Hankel defect of `b`, whose sign and size decide the steps of `a`. -/
private def D (n : ℕ) : ℤ := b (n + 1) ^ 2 - b n * b (n + 2)

/-- The linear recurrence of order six satisfied by `D`. -/
private lemma D_add_six (n : ℕ) :
    D (n + 6) = D n - 3 * D (n + 2) - 15 * D (n + 3) + 3 * D (n + 4) := by
  have h4 := b_add_four n
  have h5 := b_add_four (n + 1)
  have h6 := b_add_four (n + 2)
  have h7 := b_add_four (n + 3)
  have h8 := b_add_four (n + 4)
  simp only [D, Nat.add_assoc, Nat.reduceAdd] at h5 h6 h7 h8 ⊢
  rw [h8, h7, h6, h5, h4]
  ring

/-- The signed Hankel defect `(-1) ^ n * D n` (see `g_eq`), defined by its own recurrence. -/
private def g : ℕ → ℤ
  | 0 => 4
  | 1 => 15
  | 2 => 9
  | 3 => 105
  | 4 => 241
  | 5 => 405
  | n + 6 => g n - 3 * g (n + 2) + 15 * g (n + 3) + 3 * g (n + 4)

private lemma g_add_six (n : ℕ) :
    g (n + 6) = g n - 3 * g (n + 2) + 15 * g (n + 3) + 3 * g (n + 4) := by
  rw [g]

private lemma g_eq (n : ℕ) : g n = (-1) ^ n * D n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | 4, _ => decide
    | 5, _ => decide
    | m + 6, ih =>
      rw [g_add_six, ih m (by omega), ih (m + 2) (by omega), ih (m + 3) (by omega),
        ih (m + 4) (by omega), D_add_six]
      ring

/-- Six integer linear forms, positive on an open simplicial cone of states
`(g n, …, g (n + 5))` that the four-step map sends into itself. -/
private def InCone (x0 x1 x2 x3 x4 x5 : ℤ) : Prop :=
  0 < -2358 * x0 - 2566 * x1 - 10000 * x2 - 1031 * x3 + 50 * x4 + 641 * x5 ∧
  0 < -2381 * x0 - 2543 * x1 - 10000 * x2 - 1358 * x3 + 516 * x4 + 517 * x5 ∧
  0 < -2495 * x0 - 2597 * x1 - 10000 * x2 - 2368 * x3 + 288 * x4 + 727 * x5 ∧
  0 < 3189 * x0 + 5724 * x1 - 10000 * x2 - 2329 * x3 - 194 * x4 + 700 * x5 ∧
  0 < -263 * x0 + 2576 * x1 + 10000 * x2 + 1782 * x3 - 282 * x4 - 608 * x5 ∧
  0 < 2018 * x0 - 5691 * x1 + 10000 * x2 + 2059 * x3 + 255 * x4 - 715 * x5

/-- The four-step map of the recurrence of `g` sends the cone into itself. -/
private lemma InCone.step {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℤ}
    (h6 : x6 = x0 - 3 * x2 + 15 * x3 + 3 * x4)
    (h7 : x7 = x1 - 3 * x3 + 15 * x4 + 3 * x5)
    (h8 : x8 = x2 - 3 * x4 + 15 * x5 + 3 * x6)
    (h9 : x9 = x3 - 3 * x5 + 15 * x6 + 3 * x7)
    (H : InCone x0 x1 x2 x3 x4 x5) : InCone x4 x5 x6 x7 x8 x9 := by
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := H
  subst h9 h8 h7 h6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- On the cone, the first coordinate is positive and the fifth is less than `231` times it. -/
private lemma InCone.pos {x0 x1 x2 x3 x4 x5 : ℤ} (H : InCone x0 x1 x2 x3 x4 x5) :
    0 < x0 ∧ x4 < 231 * x0 := by
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := H
  constructor <;> linarith

/-- Every state of `g` from `n = 5` on lies in the cone. -/
private lemma g_inCone (n : ℕ) :
    InCone (g (n + 5)) (g (n + 6)) (g (n + 7)) (g (n + 8)) (g (n + 9)) (g (n + 10)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp only [InCone]; decide
    | 1, _ => simp only [InCone]; decide
    | 2, _ => simp only [InCone]; decide
    | 3, _ => simp only [InCone]; decide
    | m + 4, ih =>
      have h := ih m (by omega)
      have h6 := g_add_six (m + 5)
      have h7 := g_add_six (m + 6)
      have h8 := g_add_six (m + 7)
      have h9 := g_add_six (m + 8)
      simp only [Nat.add_assoc, Nat.reduceAdd] at h h6 h7 h8 h9 ⊢
      exact InCone.step h6 h7 h8 h9 h

private lemma g_pos (n : ℕ) : 0 < g n := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | m + 5 => exact (g_inCone m).pos.1

private lemma g_add_nine_lt (n : ℕ) : g (n + 9) < 231 * g (n + 5) := by
  have h := (g_inCone n).pos.2
  simpa only [Nat.add_assoc, Nat.reduceAdd] using h

private lemma b_growth (n : ℕ) :
    (0 < b n ∧ 39 * b n ≤ 10 * b (n + 1)) ∧ (0 < b (n + 1) ∧ 39 * b (n + 1) ≤ 10 * b (n + 2)) ∧
      (0 < b (n + 2) ∧ 39 * b (n + 2) ≤ 10 * b (n + 3)) := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := ih
    have h4 := b_add_four n
    refine ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩, ⟨by linarith, ?_⟩⟩
    simp only [Nat.add_assoc, Nat.reduceAdd]
    rw [h4]
    linarith

private lemma b_pos (n : ℕ) : 0 < b n := (b_growth n).1.1

private lemma b_le_b_add_one (n : ℕ) : 39 * b n ≤ 10 * b (n + 1) := (b_growth n).1.2

private lemma g_le_b (n : ℕ) : g n ≤ b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | 4, _ => decide
    | 5, _ => decide
    | 6, _ => decide
    | 7, _ => decide
    | 8, _ => decide
    | m + 9, ih =>
      have h1 := ih (m + 5) (by omega)
      have h2 := g_add_nine_lt m
      have e0 := b_le_b_add_one (m + 5)
      have e1 := b_le_b_add_one (m + 6)
      have e2 := b_le_b_add_one (m + 7)
      have e3 := b_le_b_add_one (m + 8)
      have hp := b_pos (m + 5)
      simp only [Nat.add_assoc, Nat.reduceAdd] at e0 e1 e2 e3
      linarith

/-- The terms of `a` are those of `b`. -/
private lemma a_eq_b (n : ℕ) : (a n : ℤ) = b n ∧ (a (n + 1) : ℤ) = b (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨hn, hn1⟩ := ih
    refine ⟨hn1, ?_⟩
    have hgD := g_eq n
    have hg := g_pos n
    have hgb := g_le_b n
    have hy := b_pos n
    have hz := b_pos (n + 2)
    obtain ⟨z, hz'⟩ : ∃ z : ℕ, (z : ℤ) = b (n + 2) := ⟨(b (n + 2)).toNat, by omega⟩
    have hD : D n = b (n + 1) ^ 2 - b n * b (n + 2) := rfl
    rw [show n + 1 + 1 = n + 2 by omega, a, ← hz']
    rw [← hn, ← hn1, ← hz'] at hD
    rw [← hn] at hy hgb
    rcases Nat.even_or_odd n with he | ho
    · -- the ceiling step: `0 < D n ≤ b n`
      rw [ite_eq_left he]
      rw [he.neg_one_pow, one_mul] at hgD
      have hy' : 0 < a n := by exact_mod_cast hy
      have key : (a (n + 1) ^ 2 + a n - 1) / a n = z + 1 := by
        apply Nat.div_eq_of_lt_le
        · zify [show 1 ≤ a (n + 1) ^ 2 + a n by omega]
          nlinarith
        · zify [show 1 ≤ a (n + 1) ^ 2 + a n by omega]
          nlinarith
      rw [key]
      simp
    · -- the floor step: `-b n ≤ D n < 0`
      rw [ite_eq_right (Nat.not_even_iff_odd.mpr ho)]
      rw [ho.neg_one_pow, neg_one_mul] at hgD
      have hz1 : 1 ≤ z := by omega
      have key : a (n + 1) ^ 2 / a n = z - 1 := by
        apply Nat.div_eq_of_lt_le
        · zify [hz1]
          nlinarith
        · zify [hz1]
          nlinarith
      rw [key]
      push_cast [hz1]
      ring

/--
**Barker's linear recurrence for A022030 holds.** For every natural number $n \ge 4$, the
sequence $a$ of OEIS A022030 satisfies $a(n) = 4a(n - 1) - a(n - 3) + a(n - 4)$, with the
subtraction taken in the natural numbers (truncated at $0$).

Source: Kenta
Kitamura, Lean formal proof of Barker's linear recurrence,
https://github.com/KitaKen1/oeis-a022030-lean/blob/f74afc2/lean/OeisA022030FC.lean#L270-L275.
Moved from `OpenConjectures/NumberTheory/OeisA022030`.
-/
public theorem conjecture_holds : conjecture := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h0 := (a_eq_b m).1
  have h1 := (a_eq_b (m + 1)).1
  have h3 := (a_eq_b (m + 3)).1
  have h4 := (a_eq_b (m + 4)).1
  have hrec := b_add_four m
  have e1 := b_le_b_add_one (m + 1)
  have e2 := b_le_b_add_one (m + 2)
  have p1 := b_pos (m + 1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at e1 e2
  simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 3 = m + 1 by omega,
    show m + 4 - 4 = m by omega]
  omega

end MathlibExt.NumberTheory.OeisA022030Wanted
