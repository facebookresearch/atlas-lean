/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Intervals of N-expansions with many gaps

Jaap de Jonge's *Intervals of N-Expansions with Many Gaps* (INTEGERS 26 (2026), Article A75)
studies the N-expansion map `T_α(x) = N/x - d_α(x)` on the interval `[α, α + 1]`, whose digit
`d_α(x) = ⌊N/x - α⌋` is lowered by one at `x = α` when `N/α - α` is an integer. This file holds
the map and its digit with three basic properties, the fact that orbits with the same digits
alternate in order, and the ideal period words `d_n` of Definition 7: finite lists of blocks of
partial quotients, each block being `a = 2, 1, 1` or `b = 2, 2`. It gives the first values, the
length of each digit string, and the counts of both kinds of blocks. The paper's other statements
are in `WantedExt.Dynamics.NExpansionGapsWanted`.

## Main declarations

* `MetaMathlibExt.nExpansionDigit` and `MetaMathlibExt.nExpansionMap`: the digit `d_α` and the
  N-expansion map `T_α`.
* `MetaMathlibExt.nExpansion_orbit_gt_iff_odd`: for `N > 0` and `0 < α < α'`, if the orbits of
  `α` under `T_α` and of `α'` under `T_α'` have the same digits up to step `m`, then their points
  of index `m` are in reverse order exactly when `m` is odd; likewise for the orbits of `α + 1`
  and `α' + 1`.
* `MetaMathlibExt.idealPeriodWord`: the ideal period word `d_n`, a list of blocks.
* `MetaMathlibExt.idealPeriodWord_flatten_length` gives the digit length `2^(n+1) - (-1)^n`
  for `n ≥ 1`.
* `MetaMathlibExt.idealPeriodWord_count_blocks` (Lemma 8): for `n ≥ 1`, `d_n` has `2^(n-1)`
  blocks `2, 2`, and its number `c_n` of blocks `2, 1, 1` satisfies `3 c_n = 2^n - (-1)^n`.

## Proof outline

Orbits with the same digits: the digit of `x` is at most `⌊N/x - α⌋ ≤ N/x - α`, so every value of
`T_α` is at least `α`, and for `α > 0` the orbits of positive points stay positive. If the orbits
of `x < x'` have the same digit `d` at step `j`, their next points are `N/x_j - d` and
`N/x'_j - d`. Since `y ↦ N/y` is strictly decreasing on `(0, ∞)` for `N > 0`, each step reverses
the order of the two points.

Block counts: write lists of blocks as in Definition 7. From `n = 4` on, `d_n = [j, abb]` for
some list `j` when `n` is even, and `d_n = [j, ab, ab]` when `n` is odd. In the first case the
recursion gives `d_(n+1) = [j, abb, j, ab, ab]`, in the second `d_(n+1) = [j, ab, ab, j, abb]`, so
the pattern carries over to `n + 1`. In both cases the number of blocks `2, 2` doubles, and the
number of blocks `2, 1, 1` goes from `c_n` to `2 c_n + (-1)^n`, the recursion of
`(2^n - (-1)^n) / 3`. The words `d_1`, `d_2`, `d_3` and `d_4` are checked by computation.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped Classical in
/-- **Digit of the N-expansion map.** Let $N$ be a natural number and $\alpha$ a real number, and
write $I_\alpha = [\alpha, \alpha + 1]$. The digit of a real number $x$ is
$d(x) = \lfloor N/x - \alpha \rfloor$, except that when $N/\alpha - \alpha$ is an integer, the
digit of $\alpha$ itself is $d(\alpha) = N/\alpha - \alpha - 1$.

With this choice the $N$-expansion map $T_\alpha(x) = N/x - d(x)$ sends $\alpha$ to $\alpha + 1$
in the integer case, every other point of $I_\alpha$ lands in $[\alpha, \alpha + 1)$, and no
cylinder is a single point.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 1. -/
public noncomputable def nExpansionDigit (N : ℕ) (α x : ℝ) : ℤ :=
  if x = α ∧ ∃ k : ℤ, (N : ℝ) / α - α = k then ⌊(N : ℝ) / x - α⌋ - 1 else ⌊(N : ℝ) / x - α⌋

/-- **The $N$-expansion map.** For a natural number $N$ and a real number $\alpha$, the
$N$-expansion map is $T_\alpha(x) = N/x - d_\alpha(x)$ for real $x$, where $d_\alpha(x)$ is the
$N$-expansion digit: $d_\alpha(x) = \lfloor N/x - \alpha \rfloor$, except that
$d_\alpha(\alpha) = \lfloor N/\alpha - \alpha \rfloor - 1$ when $N/\alpha - \alpha$ is an integer.
The map is meant to act on the interval $I_\alpha = [\alpha, \alpha + 1]$, but it is defined for
every real $x$, with the convention $N/0 = 0$.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 1. -/
public noncomputable def nExpansionMap (N : ℕ) (α x : ℝ) : ℝ :=
  (N : ℝ) / x - nExpansionDigit N α x

/-- **The digit away from the left endpoint.** Let $N$ be a natural number and let $\alpha$ and
$x$ be real numbers with $x \ne \alpha$. Then the digit of $x$ for the $N$-expansion map on
$[\alpha, \alpha + 1]$ is $\lfloor N/x - \alpha \rfloor$.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 1. -/
public theorem nExpansionDigit_of_ne {N : ℕ} {α x : ℝ} (hx : x ≠ α) :
    nExpansionDigit N α x = ⌊(N : ℝ) / x - α⌋ := by
  simp [nExpansionDigit, hx]

/-- **The N-expansion map away from the left endpoint.** Let $N$ be a natural number and let
$\alpha$ and $x$ be real numbers with $x \ne \alpha$. Then the $N$-expansion map $T_\alpha$
satisfies $\alpha \le T_\alpha(x) < \alpha + 1$.

Indeed $T_\alpha(x) = \alpha + \{N/x - \alpha\}$, where $\{\cdot\}$ denotes the fractional part.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 1. -/
public theorem nExpansionMap_mem_Ico_of_ne {N : ℕ} {α x : ℝ} (hx : x ≠ α) :
    nExpansionMap N α x ∈ Set.Ico α (α + 1) := by
  have h : nExpansionMap N α x = α + Int.fract ((N : ℝ) / x - α) := by
    rw [nExpansionMap, nExpansionDigit_of_ne hx, Int.fract]
    ring
  rw [h]
  exact ⟨le_add_of_nonneg_right (Int.fract_nonneg _),
    by linarith [Int.fract_lt_one ((N : ℝ) / x - α)]⟩

/-- **The left endpoint goes to the right endpoint when $N/\alpha - \alpha$ is an integer.** Let
$N$ be a natural number and $\alpha$ a real number such that $N/\alpha - \alpha$ is an integer,
with the convention $N/0 = 0$. Then the $N$-expansion map $T_\alpha$ satisfies
$T_\alpha(\alpha) = \alpha + 1$.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 1. -/
public theorem nExpansionMap_self_of_int {N : ℕ} {α : ℝ} {k : ℤ} (hk : (N : ℝ) / α - α = k) :
    nExpansionMap N α α = α + 1 := by
  have hd : nExpansionDigit N α α = k - 1 := by
    simp [nExpansionDigit, hk]
  rw [nExpansionMap, hd]
  push_cast
  linarith

/-- The digit of `x` is at most `⌊N/x - α⌋`, so the N-expansion map never takes a value below
`α`. -/
private theorem le_nExpansionMap (N : ℕ) (α x : ℝ) : α ≤ nExpansionMap N α x := by
  have hd : nExpansionDigit N α x ≤ ⌊(N : ℝ) / x - α⌋ := by
    unfold nExpansionDigit
    split_ifs <;> omega
  have h : (nExpansionDigit N α x : ℝ) ≤ (N : ℝ) / x - α :=
    (Int.cast_le.mpr hd).trans (Int.floor_le _)
  rw [nExpansionMap]
  linarith

/-- For `α > 0`, the orbit of a positive point under the N-expansion map stays positive. -/
private theorem nExpansionMap_iterate_pos {N : ℕ} {α x : ℝ} (hα : 0 < α) (hx : 0 < x) (j : ℕ) :
    0 < (nExpansionMap N α)^[j] x := by
  cases j with
  | zero => exact hx
  | succ j =>
    rw [Function.iterate_succ_apply']
    exact hα.trans_le (le_nExpansionMap N α _)

/-- Let `N > 0`, `α, α' > 0` and `0 < x < x'`. If the orbits of `x` under `T_α` and of `x'` under
`T_α'` have the same digits at the steps `j < m`, then at step `m` the orbit of `x'` is below the
orbit of `x` exactly when `m` is odd, and above it exactly when `m` is even. -/
private theorem nExpansionMap_iterate_lt_iff {N : ℕ} (hN : 0 < N) {α α' x x' : ℝ} (hα : 0 < α)
    (hα' : 0 < α') (hx : 0 < x) (hxx' : x < x') (m : ℕ)
    (hd : ∀ j < m, nExpansionDigit N α ((nExpansionMap N α)^[j] x) =
      nExpansionDigit N α' ((nExpansionMap N α')^[j] x')) :
    ((nExpansionMap N α')^[m] x' < (nExpansionMap N α)^[m] x ↔ Odd m) ∧
      ((nExpansionMap N α)^[m] x < (nExpansionMap N α')^[m] x' ↔ Even m) := by
  induction m with
  | zero => simpa using ⟨hxx'.le, hxx'⟩
  | succ m ih =>
    obtain ⟨ih₁, ih₂⟩ := ih fun j hj => hd j (by omega)
    have hy := nExpansionMap_iterate_pos (N := N) hα hx m
    have hy' := nExpansionMap_iterate_pos (N := N) hα' (hx.trans hxx') m
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    -- Both orbits subtract the same digit, and `y ↦ N / y` reverses the order of positive reals.
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', nExpansionMap,
      nExpansionMap, hd m (by omega), sub_lt_sub_iff_right, sub_lt_sub_iff_right,
      div_lt_div_iff_of_pos_left hN' hy hy', div_lt_div_iff_of_pos_left hN' hy' hy, ih₁, ih₂,
      Nat.odd_add_one, Nat.even_add_one, Nat.not_odd_iff_even, Nat.not_even_iff_odd]
    exact ⟨Iff.rfl, Iff.rfl⟩

/-- **Orbits with the same digits alternate in order.** Let $N$ be a positive integer and let
$0 < \alpha < \alpha'$ be real numbers. Write $T_\alpha$ for the $N$-expansion map and $d_\alpha$
for the $N$-expansion digit with parameter $\alpha$, and let $m$ be a natural number. If the
orbits $\alpha_j = T_\alpha^j(\alpha)$ and $\alpha'_j = T_{\alpha'}^j(\alpha')$ satisfy
$d_\alpha(\alpha_j) = d_{\alpha'}(\alpha'_j)$ for all $j \in \{0, \dots, m\}$, then
$\alpha'_m < \alpha_m$ if and only if $m$ is odd. Likewise, if the orbits
$\beta_j = T_\alpha^j(\alpha + 1)$ and $\beta'_j = T_{\alpha'}^j(\alpha' + 1)$ satisfy
$d_\alpha(\beta_j) = d_{\alpha'}(\beta'_j)$ for all $j \in \{0, \dots, m\}$, then
$\beta'_m < \beta_m$ if and only if $m$ is odd.

The paper assumes $\alpha$ and $\alpha'$ in Phase I (so in particular $\alpha' \le \sqrt N - 1$);
for $N > 0$ neither assumption is needed (the orbits stay in $[\alpha, \alpha + 1]$ and
$[\alpha', \alpha' + 1]$, where $x \mapsto N/x$ is strictly decreasing), so both are replaced by
$N > 0$. For $N = 0$ the claim fails ($\alpha = 1/5$, $\alpha' = 3/10$, $m = 1$).

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Lemma 2 (`integers-2026-A75-lem-2`). -/
public theorem nExpansion_orbit_gt_iff_odd {N : ℕ} (hN : 0 < N) {α α' : ℝ} (hα : 0 < α)
    (hαα' : α < α') (m : ℕ) :
    ((∀ j ≤ m, nExpansionDigit N α ((nExpansionMap N α)^[j] α) =
        nExpansionDigit N α' ((nExpansionMap N α')^[j] α')) →
      ((nExpansionMap N α')^[m] α' < (nExpansionMap N α)^[m] α ↔ Odd m)) ∧
    ((∀ j ≤ m, nExpansionDigit N α ((nExpansionMap N α)^[j] (α + 1)) =
        nExpansionDigit N α' ((nExpansionMap N α')^[j] (α' + 1))) →
      ((nExpansionMap N α')^[m] (α' + 1) < (nExpansionMap N α)^[m] (α + 1) ↔ Odd m)) := by
  have hα' : 0 < α' := hα.trans hαα'
  exact ⟨fun hd => (nExpansionMap_iterate_lt_iff hN hα hα' hα hαα' m fun j hj => hd j hj.le).1,
    fun hd => (nExpansionMap_iterate_lt_iff hN hα hα' (by linarith) (by linarith) m
      fun j hj => hd j hj.le).1⟩

/-- **Ideal period words.** For $n \ge 1$, the ideal period word $d_n$ is a finite list of blocks
of partial quotients, each block being $a = 2, 1, 1$ or $b = 2, 2$. Writing lists of blocks by
juxtaposition, with commas between parts, $d_1 = [ab]$, $d_2 = [abb]$, $d_3 = [abb, ab, ab]$ and
$d_4 = [abb, ab, ab, abb, abb]$; for $n \ge 5$, if $d_{n-1} = [j, ab, ab]$ for a list $j$ then
$d_n = [j, ab, ab, j, abb]$, and if $d_{n-1} = [j, abb]$ then $d_n = [j, abb, j, ab, ab]$. The
digit string of $d_n$ is the concatenation of its blocks. For $n = 0$ the list is empty, a
placeholder.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 7. -/
public def idealPeriodWord : ℕ → List (List ℕ)
  | 0 => []
  | 1 => [[2, 1, 1], [2, 2]]
  | 2 => [[2, 1, 1], [2, 2], [2, 2]]
  | 3 => [[2, 1, 1], [2, 2], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2]]
  | 4 => [[2, 1, 1], [2, 2], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2],
      [2, 2], [2, 1, 1], [2, 2], [2, 2]]
  | n + 5 =>
    let w := idealPeriodWord (n + 4)
    if w.drop (w.length - 4) = [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] then
      w ++ w.take (w.length - 4) ++ [[2, 1, 1], [2, 2], [2, 2]]
    else if w.drop (w.length - 3) = [[2, 1, 1], [2, 2], [2, 2]] then
      w ++ w.take (w.length - 3) ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]]
    else w

/-- **The fifth ideal period word.** Writing $a$ for the block $2, 1, 1$ and $b$ for the block
$2, 2$ of partial quotients, the ideal period word $d_5$ is $d_4$ followed by the blocks
$abb\,ab\,ab\,abb\,ab\,ab$, in this order.

This is the second recursion rule applied to $d_4 = [j, abb]$ with $j = [abb, ab, ab, abb]$.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 7. -/
public theorem idealPeriodWord_five :
    idealPeriodWord 5 = idealPeriodWord 4 ++
      [[2, 1, 1], [2, 2], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2], [2, 2],
        [2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] := by
  decide

/-- **Lengths of the first ideal period words.** The digit strings of the ideal period words
$d_1, d_2, d_3, d_4, d_5$ have lengths $5, 7, 17, 31, 65$ respectively.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 7. -/
public theorem idealPeriodWord_flatten_length_small :
    ((List.range 5).map fun n => (idealPeriodWord (n + 1)).flatten.length) =
      [5, 7, 17, 31, 65] := by
  decide

/-- The recursion step of the ideal period words, unfolded for an index `n + 5`. -/
private theorem idealPeriodWord_add_five (n : ℕ) :
    idealPeriodWord (n + 5) =
      let w := idealPeriodWord (n + 4)
      if w.drop (w.length - 4) = [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] then
        w ++ w.take (w.length - 4) ++ [[2, 1, 1], [2, 2], [2, 2]]
      else if w.drop (w.length - 3) = [[2, 1, 1], [2, 2], [2, 2]] then
        w ++ w.take (w.length - 3) ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]]
      else w :=
  rfl

/-- If the ideal period word $d_{n+4}$ is $[j, ab, ab]$, then $d_{n+5} = [j, ab, ab, j, abb]$. -/
private theorem idealPeriodWord_add_five_of_abab {n : ℕ} {j : List (List ℕ)}
    (h : idealPeriodWord (n + 4) = j ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]]) :
    idealPeriodWord (n + 5) = idealPeriodWord (n + 4) ++ j ++ [[2, 1, 1], [2, 2], [2, 2]] := by
  rw [idealPeriodWord_add_five]
  simp [h]

/-- If the ideal period word $d_{n+4}$ is $[j, abb]$, then $d_{n+5} = [j, abb, j, ab, ab]$. -/
private theorem idealPeriodWord_add_five_of_abb {n : ℕ} {j : List (List ℕ)}
    (h : idealPeriodWord (n + 4) = j ++ [[2, 1, 1], [2, 2], [2, 2]]) :
    idealPeriodWord (n + 5) =
      idealPeriodWord (n + 4) ++ j ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] := by
  -- The last four blocks are `[x, a, b, b]` (or there are only three), never `[a, b, a, b]`.
  have h4 : (idealPeriodWord (n + 4)).drop ((idealPeriodWord (n + 4)).length - 4) ≠
      [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] := by
    rw [h]
    rcases List.eq_nil_or_concat j with rfl | ⟨L, x, rfl⟩
    · decide
    · simp
  rw [idealPeriodWord_add_five]
  simp only [h4, ite_false]
  simp [h]

/-- From $d_4$ on, the ideal period word $d_{k+4}$ ends with the blocks $abb$ when $k$ is even
and with the blocks $ab, ab$ when $k$ is odd. -/
private theorem idealPeriodWord_add_four_shape (k : ℕ) :
    (Even k → ∃ j, idealPeriodWord (k + 4) = j ++ [[2, 1, 1], [2, 2], [2, 2]]) ∧
      (Odd k → ∃ j, idealPeriodWord (k + 4) = j ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]]) := by
  induction k with
  | zero =>
    exact ⟨fun _ => ⟨[[2, 1, 1], [2, 2], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1],
      [2, 2], [2, 2]], rfl⟩, fun h => absurd h (by decide)⟩
  | succ k ih =>
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨j, hj⟩ := ih.2 (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hk))
      exact ⟨idealPeriodWord (k + 4) ++ j, idealPeriodWord_add_five_of_abab hj⟩
    · obtain ⟨j, hj⟩ := ih.1 (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hk))
      exact ⟨idealPeriodWord (k + 4) ++ j, idealPeriodWord_add_five_of_abb hj⟩

/-- **Length of the ideal period words.** For every $n \ge 1$, the digit string of the ideal
period word $d_n$ (the concatenation of its blocks of partial quotients) has length
$|d_n| = 2^{n+1} - (-1)^n$.

The source derives this from the recursion $|d_n| = 2|d_{n-1}| - 3(-1)^n$.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Lemma 7 (`integers-2026-A75-lem-7`). -/
public theorem idealPeriodWord_flatten_length {n : ℕ} (hn : 1 ≤ n) :
    ((idealPeriodWord n).flatten.length : ℤ) = 2 ^ (n + 1) - (-1) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    suffices ((idealPeriodWord (n + 1)).flatten.length : ℤ) =
        2 * (idealPeriodWord n).flatten.length + 3 * (-1) ^ n by
      rw [this, ih]
      ring
    match n, hn with
    | 1, _ | 2, _ | 3, _ => decide
    | k + 4, _ =>
      rcases Nat.even_or_odd k with hk | hk
      · obtain ⟨j, hj⟩ := (idealPeriodWord_add_four_shape k).1 hk
        rw [idealPeriodWord_add_five_of_abb hj, hj, pow_add, hk.neg_one_pow]
        simp [List.flatten_append]
        omega
      · obtain ⟨j, hj⟩ := (idealPeriodWord_add_four_shape k).2 hk
        rw [idealPeriodWord_add_five_of_abab hj, hj, pow_add, hk.neg_one_pow]
        simp [List.flatten_append]
        omega

/-- From $d_4$ to $d_5$ and onwards, the number of blocks $2, 2$ doubles, and the number $c$ of
blocks $2, 1, 1$ of $d_{k+4}$ becomes $2c + (-1)^k$ in $d_{k+5}$. -/
private theorem idealPeriodWord_add_five_count (k : ℕ) :
    (idealPeriodWord (k + 5)).count [2, 2] = 2 * (idealPeriodWord (k + 4)).count [2, 2] ∧
      ((idealPeriodWord (k + 5)).count [2, 1, 1] : ℤ) =
        2 * (idealPeriodWord (k + 4)).count [2, 1, 1] + (-1) ^ k := by
  rcases Nat.even_or_odd k with hk | hk
  · obtain ⟨j, hj⟩ := (idealPeriodWord_add_four_shape k).1 hk
    rw [idealPeriodWord_add_five_of_abb hj, hj, hk.neg_one_pow]
    simp
    omega
  · obtain ⟨j, hj⟩ := (idealPeriodWord_add_four_shape k).2 hk
    rw [idealPeriodWord_add_five_of_abab hj, hj, hk.neg_one_pow]
    simp
    omega

/-- The block counts of the ideal period word $d_{k+4}$. -/
private theorem idealPeriodWord_add_four_count (k : ℕ) :
    (idealPeriodWord (k + 4)).count [2, 2] = 2 ^ (k + 3) ∧
      3 * ((idealPeriodWord (k + 4)).count [2, 1, 1] : ℤ) = 2 ^ (k + 4) - (-1) ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨hb, ha⟩ := idealPeriodWord_add_five_count k
    refine ⟨?_, ?_⟩
    · rw [show k + 1 + 4 = k + 5 from rfl, hb, ih.1]
      ring
    · rw [show k + 1 + 4 = k + 5 from rfl, ha]
      linear_combination 2 * ih.2

/-- **Block counts of the ideal period words.** For every $n \ge 1$, the ideal period word $d_n$
contains exactly $2^{n-1}$ blocks $2, 2$, and the number $c_n$ of its blocks $2, 1, 1$ satisfies
$3 c_n = 2^n - (-1)^n$; that is, $c_n = (2^n + 1)/3$ for odd $n$ and $c_n = (2^n - 1)/3$ for even
$n$.

In this lemma the source names the blocks $a = 2, 2$ and $b = 2, 1, 1$, the reverse of its
Definition 7; the counts are stated by block, so the naming does not matter.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Lemma 8 (`integers-2026-A75-lem-8`). -/
public theorem idealPeriodWord_count_blocks {n : ℕ} (hn : 1 ≤ n) :
    (idealPeriodWord n).count [2, 2] = 2 ^ (n - 1) ∧
      3 * ((idealPeriodWord n).count [2, 1, 1] : ℤ) = 2 ^ n - (-1) ^ n := by
  match n, hn with
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | k + 4, _ =>
    obtain ⟨hb, ha⟩ := idealPeriodWord_add_four_count k
    refine ⟨hb, ?_⟩
    rw [ha]
    ring

end

end MetaMathlibExt
