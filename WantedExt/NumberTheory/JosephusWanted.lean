/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Analytical study and efficient evaluation of the Josephus function

Statements from Yunier Bello-Cruz and Roy
Quintero-Contreras, "Analytical Study and Efficient
Evaluation of the Josephus Function", *Journal of Integer
Sequences* 27 (2024), Article 24.3.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Cruz/cruz4.html>).
The statement `josephus_add_eq_of_le` is proved in
`MathlibExt.NumberTheory.JosephusJosephusAddEqOfLe`.

The statements use the existing Josephus survivor
function `MetaMathlibExt.josephus` (`J_k(1) = 1`,
`J_k(n+1) = (J_k(n) + k - 1) % (n+1) + 1`). Following the
paper's usage (Lemma 8: "`j ∈ [[1, k-1]]`, i.e., `n+1` is
a low extremal point"; Corollary 7: "`n_e` is a high
extremal point and `n_e + 1` is a low extremal point"), a
point `m` is *low extremal* if `J_k(m) ∈ [1, k - 1]` and
*high extremal* if `m + 1` is low extremal. The
bounded-instance statements were verified by
simulation for `2 ≤ k ≤ 9`, `n ≤ 400`; for Theorem 13
the simulation only exhibits initial fixed points
(for `n ≤ 3000`) and does not verify infinitude.

Lemma 6(b) is stated with the additional single-wrap
hypothesis `J_k(n) + k * m ≤ 2 * (n + m)`: as extracted it
fails at `k = 4`, `n = 1`, `m = 1`, where the printed
formula gives `3 > n + m` but `J_4(2) = 1` (two wraps);
with the hypothesis it holds on the whole simulation
grid. Proposition 4 carries the domain hypothesis
`1 ≤ n_p`: at `n_p = 0` the recursion anchor
`J_k(0) = 0` is a spurious fixed point for which the
fourth case fails (`J_k(1) = 1 ≠ 0`). Not stated (see the
source audit table): Lemma 8(b), 8(c), Theorem 9(b),
9(c), 9(d). Corollaries 10 and 11 ("next" extremal point
= the least extremal point beyond the given one) use
`IsHighExtremal`, which for `m ≥ 2k - 3` agrees with the
paper's Definition 1 (`J_k(m) ∈ [[m - k + 2, m]]`; checked
for `k ≤ 9`, `m < 3000`); Corollary 11's last formula is
omitted, false as printed (`k = 2`, `ň = 1`, `n = 2`:
`J_2(2) = 1`, the formula gives `3`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.NumberTheory.JosephusFixedPointIff
public import MathlibExt.NumberTheory.JosephusFixedSuccCases
public import MathlibExt.NumberTheory.JosephusHighExtremal
public import MathlibExt.NumberTheory.JosephusWrapAround
public import MathlibExt.NumberTheory.JosephusExtremalTwoMulSub
public import MathlibExt.NumberTheory.JosephusJosephusAddEqOfLe

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.JosephusWanted

/-- **The Josephus function at the first wrap-around.** Let $k \ge 2$, $n \ge 1$ and $m$ be
natural numbers and let $J_k$ be the Josephus function. Suppose that $m$ is the least natural
number with $J_k(n) + km > n + m$, and that moreover $J_k(n) + km \le 2(n + m)$. Then
$J_k(n + m) = J_k(n) + km - (n + m)$.

The second hypothesis, which allows only one wrap-around, is not in the printed lemma; without it
the statement fails at $k = 4$, $n = 1$, $m = 1$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Lemma 6. -/
theorem_wanted josephus_add_eq_sub_of_minimal (k n m : ℕ)
    (hk : 2 ≤ k) (hn : 1 ≤ n)
    (hmin : (∀ m' : ℕ, m' < m →
        MetaMathlibExt.josephus k n + k * m' ≤ n + m') ∧
      n + m < MetaMathlibExt.josephus k n + k * m)
    (hwrap : MetaMathlibExt.josephus k n + k * m ≤ 2 * (n + m)) :
    MetaMathlibExt.josephus k (n + m) =
      MetaMathlibExt.josephus k n + k * m - (n + m)

/-- **Linear-step bound at a low extremal point.** Let $k \ge 2$ and $n$ be natural numbers, let
$J_k$ be the Josephus function, write $j = J_k(n+1)$, and suppose $j \le k - 1$. Then for every
natural number $m$, $j + km \le n + 1 + m$ holds if and only if
$m \le \lfloor (n - (j - 1)) / (k - 1) \rfloor$. Moreover, if $k - 2 + j \le n$, then
$\lfloor (n - (j - 1)) / (k - 1) \rfloor \ge 1$.

Since $1 \le J_k(n+1) \le n + 1$, the hypothesis says $j \in [1, k - 1]$, that is, $n + 1$ is a
low extremal point in the paper's sense, and none of the subtractions above is truncated.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Lemma 8. -/
theorem_wanted shift_le_iff_le_div (k n : ℕ) (hk : 2 ≤ k)
    (hj : MetaMathlibExt.josephus k (n + 1) ≤ k - 1) :
    (∀ m : ℕ, MetaMathlibExt.josephus k (n + 1) + k * m ≤ n + 1 + m ↔
      m ≤ (n - (MetaMathlibExt.josephus k (n + 1) - 1)) / (k - 1)) ∧
    (k - 2 + MetaMathlibExt.josephus k (n + 1) ≤ n →
      1 ≤ (n - (MetaMathlibExt.josephus k (n + 1) - 1)) / (k - 1))

/-- **The Josephus function has infinitely many fixed points.** For every natural number
$k \ge 2$, the set of natural numbers $n$ with $J_k(n) = n$ is infinite, where $J_k$ is the
Josephus function.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Theorem 13. -/
theorem_wanted infinite_fixedPoints (k : ℕ) (hk : 2 ≤ k) :
    {n : ℕ | MetaMathlibExt.josephus k n = n}.Infinite

/-- **Corollary 10**: for a high extremal point `n_e ≥ 2k - 3`, with
`r = n_e mod (k - 1)` and `c = 1` if `r < k - 2 - n_e + J_k(n_e)`, else `0`,
the next high extremal point is
`n_e' = (k(n_e + 1) - (r + 1))/(k - 1) - c`, with
`J_k(n_e') = (k - 1) - n_e + J_k(n_e) + k⌊(2n_e - J_k(n_e) - (k - 2))/(k - 1)⌋`,
and `J_k(n) = k(n - n_e') + J_k(n_e')` for `n ∈ [[n_e + 1, n_e']]`
(integer division by the positive `k - 1` is the floor).

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the Josephus
Function", Journal of Integer Sequences 27 (2024), Article
24.3.8, Corollary 10. -/
theorem_wanted josephus_next_high_extremal (k ne : ℕ) (hk : 2 ≤ k) (hne : 2 * k - 3 ≤ ne)
    (hh : IsHighExtremal k ne) :
    let r := ne % (k - 1)
    let c : ℕ := if (r : ℤ) < (k : ℤ) - 2 - ne + MetaMathlibExt.josephus k ne then 1 else 0
    let ne' := (k * (ne + 1) - (r + 1)) / (k - 1) - c
    ne < ne' ∧ IsHighExtremal k ne' ∧ (∀ m, ne < m → m < ne' → ¬ IsHighExtremal k m) ∧
      (MetaMathlibExt.josephus k ne' : ℤ) =
        ((k : ℤ) - 1) - ne + MetaMathlibExt.josephus k ne +
          k * ((2 * (ne : ℤ) - MetaMathlibExt.josephus k ne - ((k : ℤ) - 2)) / ((k : ℤ) - 1)) ∧
      ∀ n, ne + 1 ≤ n → n ≤ ne' →
        (MetaMathlibExt.josephus k n : ℤ) = k * ((n : ℤ) - ne') + MetaMathlibExt.josephus k ne'

/-- **Corollary 11** (first two formulas): for a low extremal point `ň ≥ 2k - 3`, with
`ř = ň mod (k - 1)` and `č = 1` if `ř < J_k(ň)`, else `0`, the next low extremal
point is `ň' = (kň - ř)/(k - 1) - č + 1`, with
`J_k(ň') = k - ň' + J_k(ň) + k⌊(ň - J_k(ň))/(k - 1)⌋`. The corollary's last
formula is omitted: false as printed (`k = 2`, `ň = 1`, `n = 2`).

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the Josephus
Function", Journal of Integer Sequences 27 (2024), Article
24.3.8, Corollary 11. -/
theorem_wanted josephus_next_low_extremal (k ne : ℕ) (hk : 2 ≤ k) (hne : 2 * k - 3 ≤ ne)
    (hl : IsLowExtremal k ne) :
    let r := ne % (k - 1)
    let c : ℕ := if r < MetaMathlibExt.josephus k ne then 1 else 0
    let ne' := (k * ne - r) / (k - 1) - c + 1
    ne < ne' ∧ IsLowExtremal k ne' ∧ (∀ m, ne < m → m < ne' → ¬ IsLowExtremal k m) ∧
      (MetaMathlibExt.josephus k ne' : ℤ) =
        (k : ℤ) - ne' + MetaMathlibExt.josephus k ne +
          k * (((ne : ℤ) - MetaMathlibExt.josephus k ne) / ((k : ℤ) - 1))

end MathlibExt.NumberTheory.JosephusWanted
