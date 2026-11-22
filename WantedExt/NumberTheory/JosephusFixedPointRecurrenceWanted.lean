/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.Combinatorics.Enumerative.JosephusFunction

/-!
# A recurrence formula for the fixed points of the Josephus function `J₃`

Statements from Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula
for Fixed Points of the Josephus Function*, INTEGERS 24 (2024), Article A115 (preprint
arXiv:2310.12984, from which the definitions are taken). `J₃` is the existing
`MetaMathlibExt.josephus 3`. A *high extremal point* is an `n ≥ 1` with
`J₃(n) ∈ {n - 1, n}`, a *fixed point* one with `J₃(n) = n`, and a *pure* high extremal point
one with `J₃(n) = n - 1`. The paper's sequences `n_e^{(i)}` and `n_p^{(ℓ)}` (`i, ℓ ≥ 1`,
increasing) are `Nat.nth` of the corresponding predicates at the zero-based index `i - 1`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- `n` is a high extremal point of the Josephus function `J₃`: `n ≥ 1` and
`J₃(n) ∈ {n - 1, n}`.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 1, Definition
(Extremal and Fixed points). -/
public def IsJosephusThreeHighExtremal (n : ℕ) : Prop :=
  1 ≤ n ∧ (josephus 3 n = n ∨ josephus 3 n + 1 = n)

/-- `n` is a fixed point of the Josephus function `J₃`: `n ≥ 1` and `J₃(n) = n`.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 1, Definition
(Extremal and Fixed points). -/
public def IsJosephusThreeFixedPoint (n : ℕ) : Prop :=
  1 ≤ n ∧ josephus 3 n = n

/-- `3` is a high extremal point of `J₃` (`J₃(3) = 2`) but not a fixed point.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 1, Definition
(Extremal and Fixed points). -/
public theorem isJosephusThreeHighExtremal_three :
    IsJosephusThreeHighExtremal 3 ∧ ¬ IsJosephusThreeFixedPoint 3 := by
  unfold IsJosephusThreeHighExtremal IsJosephusThreeFixedPoint
  decide

/-- `4` is not a high extremal point of `J₃` (`J₃(4) = 1`).

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 1, Definition
(Extremal and Fixed points). -/
public theorem not_isJosephusThreeHighExtremal_four : ¬ IsJosephusThreeHighExtremal 4 := by
  unfold IsJosephusThreeHighExtremal
  decide

/-- `13` is a fixed point of `J₃` (the third one, after `1` and `2`).

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 2, Table 1. -/
public theorem isJosephusThreeFixedPoint_thirteen : IsJosephusThreeFixedPoint 13 := by
  unfold IsJosephusThreeFixedPoint
  decide

/-- The four cases for consecutive high extremal points `a = n_e^{(i)}`, `b = n_e^{(i+1)}`
of `J₃`, with `f = a - J₃(a)` and `r = a mod 2`: `(f, r) = (1, 0)` gives `2b = 3a + 2` and
`f' = 0`; `(1, 1)` gives `2b = 3a + 1`, `f' = 1`; `(0, 0)` gives `2b = 3a`, `f' = 1`;
`(0, 1)` gives `2b = 3a + 1`, `f' = 0`, where `f' = b - J₃(b)`.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Theorem 1
(`integers-2024-A115-thm-1`). -/
public theorem_wanted josephusThree_highExtremal_succ_cases (i : ℕ) :
    let a := Nat.nth IsJosephusThreeHighExtremal i
    let b := Nat.nth IsJosephusThreeHighExtremal (i + 1)
    (a - josephus 3 a = 1 → a % 2 = 0 → 2 * b = 3 * a + 2 ∧ b - josephus 3 b = 0) ∧
    (a - josephus 3 a = 1 → a % 2 = 1 → 2 * b = 3 * a + 1 ∧ b - josephus 3 b = 1) ∧
    (a - josephus 3 a = 0 → a % 2 = 0 → 2 * b = 3 * a ∧ b - josephus 3 b = 1) ∧
    (a - josephus 3 a = 0 → a % 2 = 1 → 2 * b = 3 * a + 1 ∧ b - josephus 3 b = 0)

/-- The unified recurrences (1)-(4) for consecutive high extremal points
`a = n_e^{(i)}`, `b = n_e^{(i+1)}` of `J₃`, with `r = a mod 2`, `f = a - J₃(a)` and
`s = ((3a + 2 - r)/2) mod 2`: `2b = 3a + 1 + (1-r)(2f-1)`, `2J₃(b) = 3a + (2-3r)(2f-1)`,
`b - J₃(b) = f - (1-r)(2f-1)` and `b mod 2 = s - (1-r)(1-f)(2s-1)`.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Lemma 1
(`integers-2024-A115-lem-1`). -/
public theorem_wanted josephusThree_highExtremal_recurrences (i : ℕ) :
    let a := Nat.nth IsJosephusThreeHighExtremal i
    let b := Nat.nth IsJosephusThreeHighExtremal (i + 1)
    let r : ℤ := (a : ℤ) % 2
    let f : ℤ := (a : ℤ) - josephus 3 a
    let s : ℤ := ((3 * (a : ℤ) + 2 - r) / 2) % 2
    2 * (b : ℤ) = 3 * a + 1 + (1 - r) * (2 * f - 1) ∧
      2 * (josephus 3 b : ℤ) = 3 * a + (2 - 3 * r) * (2 * f - 1) ∧
      (b : ℤ) - josephus 3 b = f - (1 - r) * (2 * f - 1) ∧
      (b : ℤ) % 2 = s - (1 - r) * (1 - f) * (2 * s - 1)

/-- For consecutive fixed points `a = n_p^{(ℓ)}`, `b = n_p^{(ℓ+1)}` of `J₃`, the number
`m` of pure high extremal points strictly between them is the `2`-adic valuation of
`3a + 2` (the paper's `max {m | 2^m ∣ 3a + 2}`), and
`b = (3^m (3a + 2) - 2^m) / 2^{m+1}`, stated as `2^{m+1} b + 2^m = 3^m (3a + 2)`.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Theorem 2
(`integers-2024-A115-thm-2`). -/
public theorem_wanted josephusThree_fixedPoint_recurrence (ℓ : ℕ) :
    let a := Nat.nth IsJosephusThreeFixedPoint ℓ
    let b := Nat.nth IsJosephusThreeFixedPoint (ℓ + 1)
    ((Finset.Ioo a b).filter (fun n => josephus 3 n + 1 = n)).card =
        padicValNat 2 (3 * a + 2) ∧
      2 ^ (padicValNat 2 (3 * a + 2) + 1) * b + 2 ^ padicValNat 2 (3 * a + 2) =
        3 ^ padicValNat 2 (3 * a + 2) * (3 * a + 2)

/-- For consecutive fixed points `a = n_p^{(ℓ)}`, `b = n_p^{(ℓ+1)}` of `J₃` and
`a + 1 ≤ n ≤ b`, with `m_ℓ = v₂(3a + 2)` and `𝔪 = ⌈log_{3/2}((2n+1)/(3a+2))⌉`,
`J₃(n) = 3n + 1 - (2/3)^{m_ℓ - 𝔪} (2b + 1)`.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Theorem 3
(`integers-2024-A115-thm-3`). -/
public theorem_wanted josephusThree_eq_of_mem_fixedPoint_interval (ℓ n : ℕ)
    (hn₁ : Nat.nth IsJosephusThreeFixedPoint ℓ + 1 ≤ n)
    (hn₂ : n ≤ Nat.nth IsJosephusThreeFixedPoint (ℓ + 1)) :
    (josephus 3 n : ℝ) =
      3 * n + 1 -
        (2 / 3 : ℝ) ^
            ((padicValNat 2 (3 * Nat.nth IsJosephusThreeFixedPoint ℓ + 2) : ℤ) -
              ⌈Real.logb (3 / 2)
                ((2 * n + 1) / (3 * Nat.nth IsJosephusThreeFixedPoint ℓ + 2))⌉) *
          (2 * Nat.nth IsJosephusThreeFixedPoint (ℓ + 1) + 1)

end

end MetaMathlibExt
