/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.NumberTheory.Real.Irrational

/-!
# The union of two arithmetic progressions is not an MSTD set

Statements from Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic
Progressions with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026),
Article A58.

A finite set `A ⊆ ℝ` is an MSTD (more sums than differences) set when `|A + A| > |A - A|`. The
paper normalizes the first progression to `I_n = {0, 1, …, n - 1}` and the second to
`J(x, m, d) = {x + i d : i ∈ [0, m]}`. The paper's `ℕ` is the positive integers; membership in
`ℕ` is written here as `y ∈ Set.range ((↑) : ℕ → ℝ)`, which also admits `0`. Where this is used,
either the hypotheses already exclude `0` or the claim holds for every integer value; the one
case where `0` matters, `d ∈ ℚ ∖ ℕ` in Lemma 19 (i), is written with positive integers.
-/

namespace MetaMathlibExt

open Pointwise

@[expose] public section

/-- The interval `I_n = {0, 1, …, n - 1}` as a finite set of reals.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
noncomputable def realIntervalSet (n : ℕ) : Finset ℝ :=
  (Finset.range n).image fun i : ℕ => (i : ℝ)

/-- `I_n` has `n` elements.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
theorem card_realIntervalSet (n : ℕ) : (realIntervalSet n).card = n := by
  rw [realIntervalSet, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]

/-- The arithmetic progression `J(x, m, d) = {x + i d : i ∈ [0, m]}`.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
noncomputable def realAPSet (x : ℝ) (m : ℕ) (d : ℝ) : Finset ℝ :=
  (Finset.range (m + 1)).image fun i : ℕ => x + i * d

/-- `J(x, m, d)` has `m + 1` elements when `d ≠ 0`.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
theorem card_realAPSet (x : ℝ) (m : ℕ) {d : ℝ} (hd : d ≠ 0) :
    (realAPSet x m d).card = m + 1 := by
  rw [realAPSet, Finset.card_image_of_injective, Finset.card_range]
  intro i j h
  have : (i : ℝ) * d = j * d := by simpa using h
  exact_mod_cast mul_right_cancel₀ hd this

/-- A finite set of reals is an MSTD set when it has more sums than differences:
`|A - A| < |A + A|`.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
def IsMSTDSet (A : Finset ℝ) : Prop :=
  (A - A).card < (A + A).card

/-- A singleton is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
theorem not_isMSTDSet_singleton (a : ℝ) : ¬ IsMSTDSet {a} := by
  simp [IsMSTDSet]

/-- **Theorem 1.** The union of two finite arithmetic progressions `X₁ = J(a, m₁, d₁)` and `X₂ =
J(b, m₂, d₂)` (positive common differences) with `max X₁ < min X₂` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Theorem 1
(`integers-2026-A58-thm-1`). -/
public theorem_wanted not_isMSTDSet_union_two_ap (a b d₁ d₂ : ℝ) (m₁ m₂ : ℕ) (hd₁ : 0 < d₁)
    (hd₂ : 0 < d₂)
    (hlt : a + m₁ * d₁ < b) :
    ¬ IsMSTDSet (realAPSet a m₁ d₁ ∪ realAPSet b m₂ d₂)

/-- **Lemma 1.** For integers `n ≥ 3`, `m ≥ 2`, `d ≥ 2` and natural `x ∈ [n + 1, 2n - 2]`, `I_n ∪
J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 1
(`integers-2026-A58-lem-1`). -/
public theorem_wanted not_isMSTDSet_intervalAP_nat_of_le_two_mul_sub_two (n m d x : ℕ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd : 2 ≤ d)
    (hx₁ : n + 1 ≤ x) (hx₂ : x ≤ 2 * n - 2) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ))

/-- **Lemma 2.** For integers `n ≥ 3`, `m ≥ 2`, `d ≥ 2` and natural `x ≥ 2n - 1`, `I_n ∪ J(x, m, d)`
is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 2
(`integers-2026-A58-lem-2`). -/
public theorem_wanted not_isMSTDSet_intervalAP_nat_of_two_mul_sub_one_le (n m d x : ℕ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd : 2 ≤ d)
    (hx : 2 * n - 1 ≤ x) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ))

/-- **Lemma 3.** For integers `n ≥ 3`, `m ≥ 2`, `d ≥ 2` and natural `x > n - 1`, `I_n ∪ J(x, m, d)`
is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 3
(`integers-2026-A58-lem-3`). -/
public theorem_wanted not_isMSTDSet_intervalAP_nat_of_lt (n m d x : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hd : 2 ≤ d)
    (hx : n - 1 < x) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ))

/-- **Lemma 4.** For `n ≥ 3`, `m ≥ 2`, a positive irrational `d` and natural `x ≥ n + 1`, `I_n ∪
J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 4
(`integers-2026-A58-lem-4`). -/
public theorem_wanted not_isMSTDSet_intervalAP_irrational_diff (n m x : ℕ) (d : ℝ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hirr : Irrational d)
    (hd : 0 < d) (hx : n + 1 ≤ x) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m d)

/-- **Lemma 5.** For `n ≥ 3`, `d = s + p/q` with `0 < p < q` coprime, natural `x ≥ n + 1`, and
either `m ∈ [2, q - 1]` or (`m ≥ q` and `qd > n - 1`), `I_n ∪ J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 5
(`integers-2026-A58-lem-5`). -/
public theorem_wanted not_isMSTDSet_intervalAP_rat_diff (n m x : ℕ) (d : ℝ) (hn : 3 ≤ n) (s p q : ℕ)
    (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (hd : d = s + (p : ℝ) / q)
    (hx : n + 1 ≤ x) (hm : (2 ≤ m ∧ m ≤ q - 1) ∨ (q ≤ m ∧ (n : ℝ) - 1 < q * d)) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m d)

/-- **Lemma 6.** For `n ≥ 3`, `d = s + p/q` with `0 < p < q` coprime and `qd ≤ n - 1`, natural `x ≥
n + 1` and `m ≥ q`, `I_n ∪ J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 6
(`integers-2026-A58-lem-6`). -/
public theorem_wanted not_isMSTDSet_intervalAP_rat_diff_of_le (n m x : ℕ) (d : ℝ) (hn : 3 ≤ n)
    (s p q : ℕ) (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (hd : d = s + (p : ℝ) / q)
    (hqd : q * d ≤ (n : ℝ) - 1) (hx : n + 1 ≤ x) (hm : q ≤ m) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m d)

/-- **Lemma 7.** For `n ≥ 3`, real `x ∉ ℕ` with `x > n - 1`, a positive irrational `d`, and `x + id
∉ ℕ` for `i ∈ [0, m]`, `I_n ∪ J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 7
(`integers-2026-A58-lem-7`). -/
public theorem_wanted not_isMSTDSet_intervalAP_irrational_of_forall_not_nat (n m : ℕ) (x d : ℝ)
    (hn : 3 ≤ n) (hxN : x ∉ Set.range ((↑) : ℕ → ℝ))
    (hirr : Irrational d) (hd : 0 < d) (hx : (n : ℝ) - 1 < x)
    (hnat : ∀ i ≤ m, x + i * d ∉ Set.range ((↑) : ℕ → ℝ)) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **Lemma 8.** For irrational `d`, at most one index `i` has `x + id ∈ ℕ`.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 8
(`integers-2026-A58-lem-8`). -/
public theorem_wanted eq_of_add_mul_irrational_mem_nat (x d : ℝ) (hirr : Irrational d) (i j : ℕ)
    (hi : x + i * d ∈ Set.range ((↑) : ℕ → ℝ)) (hj : x + j * d ∈ Set.range ((↑) : ℕ → ℝ)) :
    i = j

/-- **Lemma 9.** For `n ≥ 3`, real `x ∉ ℕ` with `x > n - 1`, a positive irrational `d`, and `x + jd
∈ ℕ` for some `j ∈ [1, m]`, `I_n ∪ J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 9
(`integers-2026-A58-lem-9`). -/
public theorem_wanted not_isMSTDSet_intervalAP_irrational_of_exists_nat (n m : ℕ) (x d : ℝ)
    (hn : 3 ≤ n) (hxN : x ∉ Set.range ((↑) : ℕ → ℝ))
    (hirr : Irrational d) (hd : 0 < d) (hx : (n : ℝ) - 1 < x)
    (hnat : ∃ j, 1 ≤ j ∧ j ≤ m ∧ x + j * d ∈ Set.range ((↑) : ℕ → ℝ)) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **Lemma 10.** For `n ≥ 3`, real `x ∉ ℕ` with `x > n - 1`, `d = s + p/q` with `0 < p < q`
coprime, `x + id ∉ ℕ` for `i ∈ [0, m]`, and either `m ∈ [2, q - 1]` or (`m ≥ q` and `qd > n - 1`),
`I_n ∪ J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 10
(`integers-2026-A58-lem-10`). -/
public theorem_wanted not_isMSTDSet_intervalAP_real_rat_diff_of_forall_not_nat (n m : ℕ) (x d : ℝ)
    (hn : 3 ≤ n) (hxN : x ∉ Set.range ((↑) : ℕ → ℝ))
    (s p q : ℕ) (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (hd : d = s + (p : ℝ) / q)
    (hx : (n : ℝ) - 1 < x) (hnat : ∀ i ≤ m, x + i * d ∉ Set.range ((↑) : ℕ → ℝ))
    (hm : (2 ≤ m ∧ m ≤ q - 1) ∨ (q ≤ m ∧ (n : ℝ) - 1 < q * d)) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **Lemma 11.** For `d = s + p/q` with `0 < p < q` coprime, at most one `i ∈ [1, q - 1]` has `x +
id ∈ ℕ`.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 11
(`integers-2026-A58-lem-11`). -/
public theorem_wanted eq_of_add_mul_rat_mem_nat (x d : ℝ) (s p q : ℕ) (hp : 0 < p) (hpq : p < q)
    (hcop : Nat.Coprime p q)
    (hd : d = s + (p : ℝ) / q) (i j : ℕ)
    (hi₁ : 1 ≤ i) (hi₂ : i ≤ q - 1) (hj₁ : 1 ≤ j) (hj₂ : j ≤ q - 1)
    (hxi : x + i * d ∈ Set.range ((↑) : ℕ → ℝ)) (hxj : x + j * d ∈ Set.range ((↑) : ℕ → ℝ)) :
    i = j

/-- **Lemma 12.** For `n ≥ 3`, real `x ∉ ℕ` with `x > n - 1`, `d = s + p/q` with `0 < p < q`
coprime, `x + jd ∈ ℕ` for some `j ∈ [1, q - 1]`, and either `m ∈ [2, q - 1]` or (`m ≥ q` and `qd > n
- 1`), `I_n ∪ J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 12
(`integers-2026-A58-lem-12`). -/
public theorem_wanted not_isMSTDSet_intervalAP_real_rat_diff_of_exists_nat (n m : ℕ) (x d : ℝ)
    (hn : 3 ≤ n) (hxN : x ∉ Set.range ((↑) : ℕ → ℝ))
    (s p q : ℕ) (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (hd : d = s + (p : ℝ) / q)
    (hx : (n : ℝ) - 1 < x) (hnat : ∃ j, 1 ≤ j ∧ j ≤ q - 1 ∧ x + j * d ∈ Set.range ((↑) : ℕ → ℝ))
    (hm : (2 ≤ m ∧ m ≤ q - 1) ∨ (q ≤ m ∧ (n : ℝ) - 1 < q * d)) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **Lemma 13.** For `n ≥ 3`, real `x ∉ ℕ` with `x > n - 1`, `d = s + p/q` with `0 < p < q` coprime
and `qd ≤ n - 1`, and `m ≥ q`, `I_n ∪ J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 13
(`integers-2026-A58-lem-13`). -/
public theorem_wanted not_isMSTDSet_intervalAP_real_rat_diff_of_le (n m : ℕ) (x d : ℝ) (hn : 3 ≤ n)
    (hxN : x ∉ Set.range ((↑) : ℕ → ℝ))
    (s p q : ℕ) (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (hd : d = s + (p : ℝ) / q)
    (hqd : q * d ≤ (n : ℝ) - 1) (hx : (n : ℝ) - 1 < x) (hm : q ≤ m) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **Lemma 14.** For integers `n ≥ 3`, `m ≥ 2`, `d ≥ 2` and natural `x ≤ n - 1`, `I_n ∪ J(x, m, d)`
is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 14
(`integers-2026-A58-lem-14`). -/
public theorem_wanted not_isMSTDSet_intervalAP_nat_of_le_sub_one (n m d x : ℕ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd : 2 ≤ d)
    (hx : x ≤ n - 1) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ))

/-- **Lemma 15.** For integers `n ≥ 3`, `m ≥ 2`, `2 ≤ d ≤ n - 1` and `0 < x < n - 1` with `x`
irrational or `x = s + p/q` (`0 < p < q`, coprime, `q ≠ 2`), `I_n ∪ J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 15
(`integers-2026-A58-lem-15`). -/
public theorem_wanted not_isMSTDSet_intervalAP_overlap_of_den_ne_two (n m d : ℕ) (x : ℝ)
    (hn : 3 ≤ n) (hm : 2 ≤ m) (hd₁ : 2 ≤ d)
    (hd₂ : d ≤ n - 1)
    (hxform : Irrational x ∨ ∃ s p q : ℕ, 0 < p ∧ p < q ∧ q ≠ 2 ∧ Nat.Coprime p q ∧
      x = s + (p : ℝ) / q)
    (hx₀ : 0 < x) (hx₁ : x < (n : ℝ) - 1) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m (d : ℝ))

/-- **Lemma 16.** For integers `n ≥ 3`, `m ≥ 2`, `2 ≤ d ≤ n - 1` and `x = s + 1/2` with `0 < x < n -
1`, `I_n ∪ J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 16
(`integers-2026-A58-lem-16`). -/
public theorem_wanted not_isMSTDSet_intervalAP_overlap_half (n m d s : ℕ) (x : ℝ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd₁ : 2 ≤ d)
    (hd₂ : d ≤ n - 1) (hxs : x = s + 1 / 2) (hx : x < (n : ℝ) - 1) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m (d : ℝ))

/-- **Lemma 17.** For integers `n ≥ 3`, `m ≥ 2`, `d ≥ n` and real `x ∉ ℕ` with `0 < x < n - 1`, `I_n
∪ J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 17
(`integers-2026-A58-lem-17`). -/
public theorem_wanted not_isMSTDSet_intervalAP_overlap_large_diff (n m d : ℕ) (x : ℝ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd : n ≤ d)
    (hxN : x ∉ Set.range ((↑) : ℕ → ℝ)) (hx₀ : 0 < x) (hx₁ : x < (n : ℝ) - 1) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m (d : ℝ))

/-- **Lemma 19.** For `n ≥ 3`, `m ≥ 2` and `0 < x < n - 1`, if (i) `x` is irrational and `d ∈ ℚ ∖
ℕ`, or (ii) `x ∈ ℚ ∖ ℕ` and `d` is irrational, or (iii) `x = s₁ + p₁/q₁`, `d = s₂ + p₂/q₂` (reduced,
with `gcd(q₁, q₂) = 1`, `q₁ ≥ 3`, and `d ∉ ℕ`), then `I_n ∪ J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 19
(`integers-2026-A58-lem-19`). -/
public theorem_wanted not_isMSTDSet_intervalAP_overlap_of_coprime_den (n m : ℕ) (x d : ℝ)
    (hn : 3 ≤ n) (hm : 2 ≤ m) (hx₀ : 0 < x)
    (hx₁ : x < (n : ℝ) - 1)
    (hcase : (Irrational x ∧ d ∈ Set.range ((↑) : ℚ → ℝ) ∧ ∀ k : ℕ, 0 < k → d ≠ k) ∨
      (x ∈ Set.range ((↑) : ℚ → ℝ) ∧ x ∉ Set.range ((↑) : ℕ → ℝ) ∧ Irrational d) ∨
      (∃ s₁ s₂ p₁ p₂ q₁ q₂ : ℕ, 0 < p₁ ∧ 0 < p₂ ∧ Nat.Coprime p₁ q₁ ∧ Nat.Coprime p₂ q₂ ∧
        Nat.Coprime q₁ q₂ ∧ 3 ≤ q₁ ∧ x = s₁ + (p₁ : ℝ) / q₁ ∧ d = s₂ + (p₂ : ℝ) / q₂ ∧
        d ∉ Set.range ((↑) : ℕ → ℝ))) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **Lemma 20.** For reduced `x = s₁ + p₁/q₁` and `d = s₂ + p₂/q₂` with `gcd(q₁, q₂) > 1`, at most
one `i ∈ [1, q₂ - 1]` has `x + id ∈ ℕ`, at most one `j ∈ [1, q₂ - 1]` has `2x + jd ∈ ℕ`, and such
`i` and `j` differ.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 20
(`integers-2026-A58-lem-20`). -/
public theorem_wanted add_mul_mem_nat_unique_of_one_lt_gcd (x d : ℝ) (s₁ s₂ p₁ p₂ q₁ q₂ : ℕ)
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hc₁ : Nat.Coprime p₁ q₁) (hc₂ : Nat.Coprime p₂ q₂) (hl : 1 < Nat.gcd q₁ q₂)
    (hx : x = s₁ + (p₁ : ℝ) / q₁) (hd : d = s₂ + (p₂ : ℝ) / q₂) :
    (∀ i i' : ℕ, 1 ≤ i → i ≤ q₂ - 1 → 1 ≤ i' → i' ≤ q₂ - 1 →
      x + i * d ∈ Set.range ((↑) : ℕ → ℝ) → x + i' * d ∈ Set.range ((↑) : ℕ → ℝ) → i = i') ∧
    (∀ j j' : ℕ, 1 ≤ j → j ≤ q₂ - 1 → 1 ≤ j' → j' ≤ q₂ - 1 →
      2 * x + j * d ∈ Set.range ((↑) : ℕ → ℝ) → 2 * x + j' * d ∈ Set.range ((↑) : ℕ → ℝ) → j = j') ∧
    (∀ i j : ℕ, 1 ≤ i → i ≤ q₂ - 1 → 1 ≤ j → j ≤ q₂ - 1 →
      x + i * d ∈ Set.range ((↑) : ℕ → ℝ) → 2 * x + j * d ∈ Set.range ((↑) : ℕ → ℝ) → i ≠ j)

/-- **Lemma 21.** For `n ≥ 3`, `m ≥ 2`, `0 < x < n - 1`, `d > n - 1`, and reduced `x = s₁ + p₁/q₁`,
`d = s₂ + p₂/q₂` with `gcd(q₁, q₂) > 1`, `I_n ∪ J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 21
(`integers-2026-A58-lem-21`). -/
public theorem_wanted not_isMSTDSet_intervalAP_overlap_of_one_lt_gcd (n m : ℕ) (x d : ℝ)
    (s₁ s₂ p₁ p₂ q₁ q₂ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hc₁ : Nat.Coprime p₁ q₁) (hc₂ : Nat.Coprime p₂ q₂)
    (hl : 1 < Nat.gcd q₁ q₂) (hx : x = s₁ + (p₁ : ℝ) / q₁) (hd : d = s₂ + (p₂ : ℝ) / q₂)
    (hx₁ : x < (n : ℝ) - 1) (hdn : (n : ℝ) - 1 < d) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **Lemma 22.** For `x = s₁ + 1/2` and `d = s₂ + p₂/q₂` with `q₂` odd, `x + id ∉ ℕ` for every `i ≥
0`.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 22
(`integers-2026-A58-lem-22`). -/
public theorem_wanted add_mul_not_mem_nat_of_half (x d : ℝ) (s₁ s₂ p₂ q₂ : ℕ)
    (hq₂ : Nat.Coprime 2 q₂)
    (hx : x = s₁ + 1 / 2) (hd : d = s₂ + (p₂ : ℝ) / q₂) (i : ℕ) :
    x + i * d ∉ Set.range ((↑) : ℕ → ℝ)

/-- **Lemma 23.** For `n ≥ 3`, `m ≥ 2`, `x = s₁ + 1/2` with `x < n - 1`, `d > n - 1`, and `d = s₂ +
p₂/q₂` with `q₂` odd, `I_n ∪ J(x, m, d)` is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 23
(`integers-2026-A58-lem-23`). -/
public theorem_wanted not_isMSTDSet_intervalAP_overlap_half_odd_den (n m : ℕ) (x d : ℝ)
    (s₁ s₂ p₂ q₂ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hq₂ : Nat.Coprime 2 q₂) (hx : x = s₁ + 1 / 2) (hd : d = s₂ + (p₂ : ℝ) / q₂)
    (hx₁ : x < (n : ℝ) - 1) (hdn : (n : ℝ) - 1 < d) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **Theorem 2.** Let `X₁ = J(x₁, m₁, d₁)` and `X₂ = J(x₂, m₂, d₂)` with `d₁ > 0` and
`min X₂ < max X₁`, and suppose `(x₂ - x₁)/d₁ = s₁ + p₁/q₁` and `d₂/d₁ = s₂ + p₂/q₂` with
`sᵢ ≥ 0` and `pᵢ, qᵢ` positive and coprime. Then `X₁ ∪ X₂` is not an MSTD set, except in the
two cases the paper leaves open: (i) `gcd(q₁, q₂) > 1` and `0 < d₂ < (m₁ - 1) d₁`, and
(ii) `q₁ = 2`, `gcd(2, q₂) = 1` and `0 < d₂ < (m₁ - 1) d₁`; these are excluded by hypothesis.
`min X₂ < max X₁` is written `x₂ < x₁ + m₁ d₁` (here `d₂ > 0` follows from `d₁ > 0`).

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Theorem 2
(`integers-2026-A58-thm-2`). -/
public theorem_wanted not_isMSTDSet_union_two_ap_overlap (x₁ x₂ d₁ d₂ : ℝ) (m₁ m₂ : ℕ)
    (hd₁ : 0 < d₁) (s₁ s₂ p₁ p₂ q₁ q₂ : ℕ) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hq₁ : 0 < q₁)
    (hq₂ : 0 < q₂) (hcop₁ : Nat.Coprime p₁ q₁) (hcop₂ : Nat.Coprime p₂ q₂)
    (hx : (x₂ - x₁) / d₁ = s₁ + (p₁ : ℝ) / q₁) (hd : d₂ / d₁ = s₂ + (p₂ : ℝ) / q₂)
    (hlt : x₂ < x₁ + m₁ * d₁)
    (hexc₁ : ¬ (1 < Nat.gcd q₁ q₂ ∧ 0 < d₂ ∧ d₂ < ((m₁ : ℝ) - 1) * d₁))
    (hexc₂ : ¬ (q₁ = 2 ∧ Nat.Coprime 2 q₂ ∧ 0 < d₂ ∧ d₂ < ((m₁ : ℝ) - 1) * d₁)) :
    ¬ IsMSTDSet (realAPSet x₁ m₁ d₁ ∪ realAPSet x₂ m₂ d₂)

/-- **Lemma 18 (i).** If `x` is irrational and `d` is rational, then `x + i d` and `2x + j d` are
not natural numbers for any `i, j ≥ 0`. The paper assumes `d ∈ ℚ ∖ ℕ`; the claim holds for every
rational `d`, so that restriction is not stated.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 18
(`integers-2026-A58-lem-18`). -/
public theorem_wanted add_mul_not_mem_nat_of_irrational_of_rat (x d : ℝ) (hx : Irrational x)
    (hd : d ∈ Set.range ((↑) : ℚ → ℝ)) (i j : ℕ) :
    x + i * d ∉ Set.range ((↑) : ℕ → ℝ) ∧ 2 * x + j * d ∉ Set.range ((↑) : ℕ → ℝ)

/-- **Lemma 18 (ii), corrected.** If `x ∈ ℚ ∖ ℕ` and `d` is irrational, then `x + i d` is not a
natural number for any `i ≥ 0`, and `2x + j d` is not a natural number for any `j ≥ 1`. As printed
the lemma also claims `2x + 0 · d ∉ ℕ`, which fails at `x = 1/2` (`2x = 1`); the paper's proof
("then `d ∈ ℚ`") covers only `j ≥ 1`, and the condition `q₁ ≥ 3` that excludes this case is
attached only to (iii).

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 18
(`integers-2026-A58-lem-18`). -/
public theorem_wanted add_mul_not_mem_nat_of_rat_of_irrational (x d : ℝ)
    (hx : x ∈ Set.range ((↑) : ℚ → ℝ)) (hxn : x ∉ Set.range ((↑) : ℕ → ℝ)) (hd : Irrational d)
    (i j : ℕ) (hj : 1 ≤ j) :
    x + i * d ∉ Set.range ((↑) : ℕ → ℝ) ∧ 2 * x + j * d ∉ Set.range ((↑) : ℕ → ℝ)

/-- **Lemma 18 (iii).** If `x = s₁ + p₁/q₁` and `d = s₂ + p₂/q₂` with `s₁, s₂, p₁, p₂, q₁, q₂ ∈ ℕ`,
`gcd(p₁, q₁) = 1`, `gcd(q₁, q₂) = 1` and `q₁ ≥ 3`, then `x + i d` and `2x + j d` are not natural
numbers for any `i, j ≥ 0`. The paper's further hypotheses (`p₁, p₂, q₂ > 0`, `gcd(p₂, q₂) = 1`,
`d ∉ ℕ`) are not needed and are not stated (`p₁ > 0` and `q₂ > 0` already follow from the two
coprimality conditions and `q₁ ≥ 3`).

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 18
(`integers-2026-A58-lem-18`). -/
public theorem_wanted add_mul_not_mem_nat_of_coprime_den (x d : ℝ) (s₁ s₂ p₁ p₂ q₁ q₂ : ℕ)
    (hc₁ : Nat.Coprime p₁ q₁) (hq : Nat.Coprime q₁ q₂) (hq₁ : 3 ≤ q₁)
    (hx : x = s₁ + (p₁ : ℝ) / q₁) (hd : d = s₂ + (p₂ : ℝ) / q₂) (i j : ℕ) :
    x + i * d ∉ Set.range ((↑) : ℕ → ℝ) ∧ 2 * x + j * d ∉ Set.range ((↑) : ℕ → ℝ)

end

end MetaMathlibExt
