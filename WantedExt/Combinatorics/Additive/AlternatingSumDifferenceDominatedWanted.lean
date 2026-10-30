/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Alternating sequences of sum- and difference-dominated sets

Statements from Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller
and Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88 (arXiv:2509.12829). Journal labels: Lemma 1,
Theorems 1-3 are arXiv Lemma 2.4 and Theorems 2.1, 2.3, 2.5.

A finite set `A ⊆ ℤ` is MSTD (sum-dominated) when `|A + A| > |A - A|` and MDTS
(difference-dominated) when `|A - A| > |A + A|`; both are written out with Mathlib's pointwise
`Finset` operations.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Int.Interval

namespace MetaMathlibExt

@[expose] public section

open Pointwise

/-- Lemma 1 (quoted from Nathanson): for `m ≥ 4` and `2 ≤ r ≤ m - 3`, the set
`B = [0, m - 1] ∖ {r}` has `B + B = [0, 2m - 2]` and `B - B = [-(m - 1), m - 1]`.

Source: Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and
Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88, Lemma 1 (`integers-2026-A88-lem-1`). -/
public theorem_wanted interval_erase_add_sub {m r : ℤ} (hm : 4 ≤ m) (hr : 2 ≤ r)
    (hrm : r ≤ m - 3) :
    (Finset.Icc 0 (m - 1)).erase r + (Finset.Icc 0 (m - 1)).erase r = Finset.Icc 0 (2 * m - 2) ∧
      (Finset.Icc 0 (m - 1)).erase r - (Finset.Icc 0 (m - 1)).erase r =
        Finset.Icc (-(m - 1)) (m - 1)

/-- Theorem 1: let `A₁` be an MSTD set of nonnegative integers with `0 ∈ A₁` (so
`0 = min A₁`, as the paper's proof uses when it counts every sum `a + b + 2n` as new) and let
`n > max A₁` be such that
(a) `A₁ + A₁` and `A₁ - A₁` have the same number of residues modulo `n`, and (b) with
`x = #{a ∈ A₁ : n + a ∉ A₁ + A₁}` and `y = #{b ∈ A₁ : n - b ∉ A₁ - A₁}`,
`2y - x - 1 > |A₁ + A₁| - |A₁ - A₁|`. Define `A_{2l} = A_{2l-1} ∪ {ln}` and
`A_{2l+1} = A_{2l-1} ∪ (A₁ + ln)` for `l ≥ 1`. Then `A_{2l}` is MDTS, `A_{2l+1}` is MSTD, and
the sequence is strictly increasing.

Source: Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and
Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88, Theorem 1 (`integers-2026-A88-thm-1`). -/
public theorem_wanted alternating_sequence_of_copies (A₁ : Finset ℤ) (n : ℤ)
    (hmstd : (A₁ - A₁).card < (A₁ + A₁).card) (h0 : 0 ∈ A₁) (hn : ∀ a ∈ A₁, 0 ≤ a ∧ a < n)
    (hmod : ((A₁ + A₁).image (· % n)).card = ((A₁ - A₁).image (· % n)).card)
    (hxy : 2 * ((A₁.filter fun b => n - b ∉ A₁ - A₁).card : ℤ) -
        (A₁.filter fun a => n + a ∉ A₁ + A₁).card - 1 >
      ((A₁ + A₁).card : ℤ) - (A₁ - A₁).card)
    (A : ℕ → Finset ℤ) (h1 : A 1 = A₁)
    (heven : ∀ l ≥ 1, A (2 * l) = A (2 * l - 1) ∪ {(l : ℤ) * n})
    (hodd : ∀ l ≥ 1, A (2 * l + 1) = A (2 * l - 1) ∪ (A₁ + {(l : ℤ) * n})) :
    ∀ l ≥ 1, (A (2 * l) + A (2 * l)).card < (A (2 * l) - A (2 * l)).card ∧
      (A (2 * l + 1) - A (2 * l + 1)).card < (A (2 * l + 1) + A (2 * l + 1)).card ∧
      A (2 * l - 1) ⊂ A (2 * l) ∧ A (2 * l) ⊂ A (2 * l + 1)

/-- Theorem 2 (quoted from Nathanson): let `m ≥ 4`, `1 ≤ d ≤ m - 1`, `d ≠ m / 2`, and
`k ≥ 3` if `d < m / 2`, `k ≥ 4` if `d > m / 2`. With `B = [0, m - 1] ∖ {d}`,
`L = {m - d, 2m - d, …, km - d}`, `a* = (k + 1)m - 2d`, `A* = B ∪ L ∪ (a* - B)` and
`A = A* ∪ {m}`, the set `A` is MSTD, `2m ∈ (A + A) ∖ (A* + A*)`, and
`A* - {m} ⊆ A* - A*`. (`d ≠ m / 2` is written `2d ≠ m`.)

Source: Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and
Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88, Theorem 2 (`integers-2026-A88-thm-2`). -/
public theorem_wanted nathanson_mstd_construction {m d k : ℤ} (hm : 4 ≤ m) (hd : 1 ≤ d)
    (hdm : d ≤ m - 1) (hd2 : 2 * d ≠ m) (hk3 : 2 * d < m → 3 ≤ k) (hk4 : m < 2 * d → 4 ≤ k) :
    let B := (Finset.Icc 0 (m - 1)).erase d
    let As := B ∪ (Finset.Icc 1 k).image (fun j => j * m - d) ∪
      B.image (fun b => (k + 1) * m - 2 * d - b)
    let A := insert m As
    (A - A).card < (A + A).card ∧ 2 * m ∈ A + A ∧ 2 * m ∉ As + As ∧ As - {m} ⊆ As - As

/-- Theorem 3: let `A = A* ∪ {m}` be as in Theorem 2 with `m ≡ 0 (mod 4)` and
`d ∈ {m / 4, 3m / 4}`. Then `A₁ = A ∪ {-d, (k + 1)m - d}` is MSTD. For `r ≥ 1` define
`A_{2r} = A_{2r-1} ∪ {(k + r + 1)m - d}` and `A_{2r+1} = A_{2r-1} ∪ {-rm - d, (k + r + 1)m - d}`.
Then `A_{2r}` is MDTS, `A_{2r+1}` is MSTD, the sequence is strictly increasing, and with
`A*_i = A_i ∖ {m}`: `m + A*_{2r-1} ⊆ A*_{2r-1} + A*_{2r-1}`,
`m - A*_{2r-1} ⊆ A*_{2r-1} - A*_{2r-1}`, `|A_{2r-1} + A_{2r-1}| = |A_{2r-1} - A_{2r-1}| + 1`,
and `|A_{2r} + A_{2r}| ≤ |A_{2r} - A_{2r}| - m + 3`. The extracted condition on `d` (control
glyphs in the record) is read as `d ∈ {m/4, 3m/4}`, as in the paper's proof, which treats
exactly these two values; the lost cardinality bars in items 3 and 4 are restored.

Source: Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and
Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88, Theorem 3 (`integers-2026-A88-thm-3`). -/
public theorem_wanted alternating_sequence_from_nathanson {m d k : ℤ} (hm : 4 ≤ m)
    (hm4 : m % 4 = 0) (hd : 4 * d = m ∨ 4 * d = 3 * m) (hk3 : 2 * d < m → 3 ≤ k)
    (hk4 : m < 2 * d → 4 ≤ k) (A : ℕ → Finset ℤ)
    (h1 : A 1 = insert (-d) (insert ((k + 1) * m - d) (insert m
      ((Finset.Icc 0 (m - 1)).erase d ∪ (Finset.Icc 1 k).image (fun j => j * m - d) ∪
        ((Finset.Icc 0 (m - 1)).erase d).image (fun b => (k + 1) * m - 2 * d - b)))))
    (heven : ∀ r ≥ 1, A (2 * r) = insert ((k + r + 1) * m - d) (A (2 * r - 1)))
    (hodd : ∀ r ≥ 1, A (2 * r + 1) =
      insert (-(r : ℤ) * m - d) (insert ((k + r + 1) * m - d) (A (2 * r - 1)))) :
    (A 1 - A 1).card < (A 1 + A 1).card ∧
    ∀ r ≥ 1, (A (2 * r) + A (2 * r)).card < (A (2 * r) - A (2 * r)).card ∧
      (A (2 * r + 1) - A (2 * r + 1)).card < (A (2 * r + 1) + A (2 * r + 1)).card ∧
      A (2 * r - 1) ⊂ A (2 * r) ∧ A (2 * r) ⊂ A (2 * r + 1) ∧
      {m} + (A (2 * r - 1)).erase m ⊆ (A (2 * r - 1)).erase m + (A (2 * r - 1)).erase m ∧
      {m} - (A (2 * r - 1)).erase m ⊆ (A (2 * r - 1)).erase m - (A (2 * r - 1)).erase m ∧
      (A (2 * r - 1) + A (2 * r - 1)).card = (A (2 * r - 1) - A (2 * r - 1)).card + 1 ∧
      ((A (2 * r) + A (2 * r)).card : ℤ) ≤ (A (2 * r) - A (2 * r)).card - m + 3

end

end MetaMathlibExt
