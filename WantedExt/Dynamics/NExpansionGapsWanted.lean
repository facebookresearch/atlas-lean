/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring
public import MathlibExt.Dynamics.NExpansionGaps

/-!
# Intervals of N-expansions with many gaps

Statements from Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026),
Article A75. The ideal period words (Definition 7), their first values and their block counts
(Lemma 8) are in `MathlibExt.Dynamics.NExpansionGaps`, which this module imports.
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
public theorem_wanted nExpansion_orbit_gt_iff_odd {N : ℕ} (hN : 0 < N) {α α' : ℝ} (hα : 0 < α)
    (hαα' : α < α') (m : ℕ) :
    ((∀ j ≤ m, nExpansionDigit N α ((nExpansionMap N α)^[j] α) =
        nExpansionDigit N α' ((nExpansionMap N α')^[j] α')) →
      ((nExpansionMap N α')^[m] α' < (nExpansionMap N α)^[m] α ↔ Odd m)) ∧
    ((∀ j ≤ m, nExpansionDigit N α ((nExpansionMap N α)^[j] (α + 1)) =
        nExpansionDigit N α' ((nExpansionMap N α')^[j] (α' + 1))) →
      ((nExpansionMap N α')^[m] (α' + 1) < (nExpansionMap N α)^[m] (α + 1) ↔ Odd m))

/-- **The ideal periodic points decrease.** Let $N$ be a natural number, let $\alpha$ be a real
number with $0 < \alpha \le \sqrt N - 1$, and let $T_\alpha$ be the $N$-expansion map on
$I_\alpha = [\alpha, \alpha + 1]$. For $m \ge 1$ write $|d_m|$ for the length of the digit string
of the ideal period word $d_m$. Let $k, \ell \ge 1$ and let $x, y \in I_\alpha$ be such that for
every $i \ge 0$ the digit of $T_\alpha^i(x)$ is entry $i \bmod |d_k|$ (counting from $0$) of the
digit string of $d_k$, and the digit of $T_\alpha^i(y)$ is entry $i \bmod |d_\ell|$ of the digit
string of $d_\ell$; that is, the expansions of $x$ and $y$ are purely periodic with period words
$d_k$ and $d_\ell$. Then $x < y$ if and only if $\ell < k$.

The source works in Phase I; only the assumption $0 < \alpha \le \sqrt N - 1$ is kept here, which
makes $T_\alpha$ expanding, so that a digit sequence determines its point.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Lemma 4 (`integers-2026-A75-lem-4`). -/
public theorem_wanted idealPeriodWord_point_lt_iff {N : ℕ} {α : ℝ} (hα : 0 < α)
    (hαN : α ≤ Real.sqrt N - 1) {k ℓ : ℕ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) {x y : ℝ}
    (hx : x ∈ Set.Icc α (α + 1)) (hy : y ∈ Set.Icc α (α + 1))
    (hxd : ∀ i, nExpansionDigit N α ((nExpansionMap N α)^[i] x) =
      ((idealPeriodWord k).flatten.getD (i % (idealPeriodWord k).flatten.length) 0 : ℤ))
    (hyd : ∀ i, nExpansionDigit N α ((nExpansionMap N α)^[i] y) =
      ((idealPeriodWord ℓ).flatten.getD (i % (idealPeriodWord ℓ).flatten.length) 0 : ℤ)) :
    x < y ↔ ℓ < k

/-- **The ideal periodic point is the least point of its orbit.** Let $N$ be a natural number,
let $\alpha$ be a real number with $0 < \alpha \le \sqrt N - 1$, and let $T_\alpha$ be the
$N$-expansion map on $I_\alpha = [\alpha, \alpha + 1]$. Let $n \ge 1$, write $|d_n|$ for the
length of the digit string of the ideal period word $d_n$, and let $x \in I_\alpha$ be such that
for every $i \ge 0$ the digit of $T_\alpha^i(x)$ is entry $i \bmod |d_n|$ (counting from $0$) of
that digit string, so that the expansion of $x$ is purely periodic with period word $d_n$. Then
$x \le T_\alpha^j(x)$ for every $j \ge 0$.

The source assumes Phase I; only the assumption $0 < \alpha \le \sqrt N - 1$ is kept here.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Lemma 5 (`integers-2026-A75-lem-5`). -/
public theorem_wanted idealPeriodWord_point_le_orbit {N : ℕ} {α : ℝ} (hα : 0 < α)
    (hαN : α ≤ Real.sqrt N - 1) {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc α (α + 1))
    (hxd : ∀ i, nExpansionDigit N α ((nExpansionMap N α)^[i] x) =
      ((idealPeriodWord n).flatten.getD (i % (idealPeriodWord n).flatten.length) 0 : ℤ))
    (j : ℕ) :
    x ≤ (nExpansionMap N α)^[j] x

/-- **Length of the ideal period words.** For every $n \ge 1$, the digit string of the ideal
period word $d_n$ (the concatenation of its blocks of partial quotients) has length
$|d_n| = 2^{n+1} - (-1)^n$.

The source derives this from the recursion $|d_n| = 2|d_{n-1}| - 3(-1)^n$.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Lemma 7 (`integers-2026-A75-lem-7`). -/
public theorem_wanted idealPeriodWord_flatten_length {n : ℕ} (hn : 1 ≤ n) :
    ((idealPeriodWord n).flatten.length : ℤ) = 2 ^ (n + 1) - (-1) ^ n

end

end MetaMathlibExt
