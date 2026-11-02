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

/-- **High extremal points of the Josephus function $J_3$.** A natural number $n$ is a high
extremal point of the Josephus function $J_3$ (elimination step $3$) when $n \ge 1$ and either
$J_3(n) = n$ or $J_3(n) = n - 1$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 1, Definition
(Extremal and Fixed points). -/
public def IsJosephusThreeHighExtremal (n : ℕ) : Prop :=
  1 ≤ n ∧ (josephus 3 n = n ∨ josephus 3 n + 1 = n)

/-- **Fixed points of the Josephus function $J_3$.** A natural number $n$ is a fixed point of the
Josephus function $J_3$ (elimination step $3$) when $n \ge 1$ and $J_3(n) = n$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 1, Definition
(Extremal and Fixed points). -/
public def IsJosephusThreeFixedPoint (n : ℕ) : Prop :=
  1 ≤ n ∧ josephus 3 n = n

/-- **$3$ is a high extremal point but not a fixed point of $J_3$.** The number $3$ is a high
extremal point of the Josephus function $J_3$ (elimination step $3$) and is not a fixed point of
$J_3$; indeed $J_3(3) = 2$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 1, Definition
(Extremal and Fixed points). -/
public theorem isJosephusThreeHighExtremal_three :
    IsJosephusThreeHighExtremal 3 ∧ ¬ IsJosephusThreeFixedPoint 3 := by
  unfold IsJosephusThreeHighExtremal IsJosephusThreeFixedPoint
  decide

/-- **$4$ is not a high extremal point of $J_3$.** The number $4$ is not a high extremal point of
the Josephus function $J_3$ (elimination step $3$).

Indeed $J_3(4) = 1$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 1, Definition
(Extremal and Fixed points). -/
public theorem not_isJosephusThreeHighExtremal_four : ¬ IsJosephusThreeHighExtremal 4 := by
  unfold IsJosephusThreeHighExtremal
  decide

/-- **$13$ is a fixed point of $J_3$.** The number $13$ is a fixed point of the Josephus function
$J_3$ (elimination step $3$), that is, $J_3(13) = 13$.

It is the third fixed point of $J_3$, after $1$ and $2$; the statement records only that $13$ is
a fixed point.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 2, Table 1. -/
public theorem isJosephusThreeFixedPoint_thirteen : IsJosephusThreeFixedPoint 13 := by
  unfold IsJosephusThreeFixedPoint
  decide

/-- **Successive high extremal points of $J_3$.** For every natural number $i$, let $a$ and $b$ be
the $(i+1)$-th and $(i+2)$-th smallest high extremal points of the Josephus function $J_3$, and
put $f = a - J_3(a)$, $f' = b - J_3(b)$ and $r = a \bmod 2$. If $(f, r) = (1, 0)$, then
$2b = 3a + 2$ and $f' = 0$; if $(f, r) = (1, 1)$, then $2b = 3a + 1$ and $f' = 1$; if
$(f, r) = (0, 0)$, then $2b = 3a$ and $f' = 1$; if $(f, r) = (0, 1)$, then $2b = 3a + 1$ and
$f' = 0$.

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

/-- **Unified recurrences for consecutive high extremal points of $J_3$.** For every natural
number $i$, let $a$ and $b$ be the $(i+1)$-th and $(i+2)$-th smallest high extremal points of the
Josephus function $J_3$. In the integers, put $r = a \bmod 2$, $f = a - J_3(a)$ and
$s = \lfloor (3a + 2 - r)/2 \rfloor \bmod 2$. Then
$$2b = 3a + 1 + (1 - r)(2f - 1), \qquad 2J_3(b) = 3a + (2 - 3r)(2f - 1),$$
$$b - J_3(b) = f - (1 - r)(2f - 1), \qquad b \bmod 2 = s - (1 - r)(1 - f)(2s - 1).$$

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

/-- **Recurrence for consecutive fixed points of $J_3$.** For every natural number $\ell$, let $a$
and $b$ be the $(\ell+1)$-th and $(\ell+2)$-th smallest fixed points of the Josephus function
$J_3$, and let $m = \nu_2(3a + 2)$ be the $2$-adic valuation of $3a + 2$. Then exactly $m$
natural numbers $n$ with $a < n < b$ satisfy $J_3(n) = n - 1$ (the pure high extremal points
between $a$ and $b$), and $2^{m+1} b + 2^m = 3^m (3a + 2)$, that is,
$b = (3^m (3a + 2) - 2^m) / 2^{m+1}$.

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

/-- **The Josephus function between consecutive fixed points.** For every natural number $\ell$,
let $a$ and $b$ be the $(\ell+1)$-th and $(\ell+2)$-th smallest fixed points of the Josephus
function $J_3$, and let $m = \nu_2(3a + 2)$ be the $2$-adic valuation of $3a + 2$. For every
natural number $n$ with $a + 1 \le n \le b$, put
$\mathfrak{m} = \lceil \log_{3/2}((2n + 1)/(3a + 2)) \rceil$; then, in the real numbers,
$$J_3(n) = 3n + 1 - \left(\tfrac{2}{3}\right)^{m - \mathfrak{m}} (2b + 1).$$

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
