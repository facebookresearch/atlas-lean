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

namespace MetaMathlibExt

@[expose] public section

open scoped Classical in
/-- The digit `d(x)` of the `N`-expansion map on `I_α = [α, α + 1]`: `d(x) = ⌊N / x - α⌋`, except
that `d(α) = N / α - α - 1` when `N / α - α` is an integer (then `T_α(α) = α + 1`; every other
point of `I_α` lands in `[α, α + 1)`, and no cylinder is a single point).

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 1. -/
public noncomputable def nExpansionDigit (N : ℕ) (α x : ℝ) : ℤ :=
  if x = α ∧ ∃ k : ℤ, (N : ℝ) / α - α = k then ⌊(N : ℝ) / x - α⌋ - 1 else ⌊(N : ℝ) / x - α⌋

/-- The `N`-expansion map `T_α(x) = N / x - d(x)` on `I_α = [α, α + 1]`.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 1. -/
public noncomputable def nExpansionMap (N : ℕ) (α x : ℝ) : ℝ :=
  (N : ℝ) / x - nExpansionDigit N α x

/-- Away from the left endpoint `α`, the digit is `⌊N / x - α⌋`.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 1. -/
public theorem nExpansionDigit_of_ne {N : ℕ} {α x : ℝ} (hx : x ≠ α) :
    nExpansionDigit N α x = ⌊(N : ℝ) / x - α⌋ := by
  simp [nExpansionDigit, hx]

/-- For `x ≠ α` the `N`-expansion map lands in `[α, α + 1)`: `T_α(x) = α + fract(N / x - α)`.

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

/-- When `N / α - α` is an integer, the left endpoint is mapped to the right endpoint:
`T_α(α) = α + 1`.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 1. -/
public theorem nExpansionMap_self_of_int {N : ℕ} {α : ℝ} {k : ℤ} (hk : (N : ℝ) / α - α = k) :
    nExpansionMap N α α = α + 1 := by
  have hd : nExpansionDigit N α α = k - 1 := by
    simp [nExpansionDigit, hk]
  rw [nExpansionMap, hd]
  push_cast
  linarith

/-- The periodic words `d_n` of Definition 7, as lists of the blocks `a = 2, 1, 1` and
`b = 2, 2` of partial quotients: `d₁ = [ab]`, `d₂ = [abb]`, `d₃ = [abb, ab, ab]`,
`d₄ = [abb, ab, ab, abb, abb]`, and for `n ≥ 5`: if `d_{n-1} = [j, ab, ab]` then
`d_n = [j, ab, ab, j, abb]`, and if `d_{n-1} = [j, abb]` then `d_n = [j, abb, j, ab, ab]`.
The digit string of `d_n` is `(idealPeriodWord n).flatten`; `idealPeriodWord 0 = []` is a
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

/-- `d₅ = [d₄, abb, ab, ab, abb, ab, ab]`, obtained from `d₄ = [j, abb]` by the second rule.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 7. -/
public theorem idealPeriodWord_five :
    idealPeriodWord 5 = idealPeriodWord 4 ++
      [[2, 1, 1], [2, 2], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2], [2, 2],
        [2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] := by
  decide

/-- The digit lengths of `d₁, …, d₅` are `5, 7, 17, 31, 65`.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 7. -/
public theorem idealPeriodWord_flatten_length_small :
    ((List.range 5).map fun n => (idealPeriodWord (n + 1)).flatten.length) = [5, 7, 17, 31, 65] := by
  decide

/-- Lemma 2: let `0 < α < α'`. If the orbits `α_j = T_α^j(α)` and `α'_j = T_{α'}^j(α')`
have the same digits for `j ∈ {0, …, m}`, then `α_m > α'_m` if and only if `m` is odd; the same
holds for the orbits of `β = α + 1` and `β' = α' + 1`.

The paper assumes `α, α'` in Phase I (so in particular `α' ≤ √N - 1`); for `N > 0` neither
assumption is needed (orbits stay in `[α, α + 1]` and `[α', α' + 1]`, where `x ↦ N / x` is strictly
decreasing), so both are replaced by `0 < N`. For `N = 0` the claim fails (`α = 1/5`, `α' = 3/10`,
`m = 1`).

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

/-- Lemma 4: the periodic points `d₁, d₂, …` decrease: for `k, ℓ ≥ 1`, `d_k < d_ℓ` if and only if
`k > ℓ`. Here `x` and `y` are points of `I_α` whose `N`-expansions are purely periodic with
period words `d_k` and `d_ℓ` respectively (digit `i` of `x` is entry `i mod |d_k|` of the digit
string of `d_k`).

The paper works in Phase I; the ordering only needs the standing assumption `0 < α ≤ √N - 1` of
Definition 1 (which makes `T_α` expanding, so a digit sequence determines its point), so Phase I
is dropped.

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

/-- Lemma 5: for `n ≥ 1`, the periodic point `d_n` is the smallest point of its orbit: if
`x ∈ I_α` has purely periodic `N`-expansion with period word `d_n`, then `x ≤ T_α^j(x)` for
all `j`.

As for Lemma 4, Phase I is dropped; the standing assumptions of Definition 1 are kept.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Lemma 5 (`integers-2026-A75-lem-5`). -/
public theorem_wanted idealPeriodWord_point_le_orbit {N : ℕ} {α : ℝ} (hα : 0 < α)
    (hαN : α ≤ Real.sqrt N - 1) {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc α (α + 1))
    (hxd : ∀ i, nExpansionDigit N α ((nExpansionMap N α)^[i] x) =
      ((idealPeriodWord n).flatten.getD (i % (idealPeriodWord n).flatten.length) 0 : ℤ))
    (j : ℕ) :
    x ≤ (nExpansionMap N α)^[j] x

/-- Lemma 7: for `n ≥ 1` the period length of `d_n` is `|d_n| = 2^{n+1} - (-1)^n`.

`|d_n|` is read as the number of partial quotients in the defining word of Definition 7 (the
paper derives it from `|d_n| = 2|d_{n-1}| - 3(-1)^n`).

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Lemma 7 (`integers-2026-A75-lem-7`). -/
public theorem_wanted idealPeriodWord_flatten_length {n : ℕ} (hn : 1 ≤ n) :
    ((idealPeriodWord n).flatten.length : ℤ) = 2 ^ (n + 1) - (-1) ^ n

/-- Lemma 8: for `n ≥ 1`, the number `a(n)` of blocks `2, 2` in `d_n` is `2^{n-1}`, and the
number `b(n)` of blocks `2, 1, 1` is `(2^n + 1)/3` for odd `n` and `(2^n - 1)/3` for even `n`
(written `3 b(n) = 2^n - (-1)^n`).

In this lemma the paper names the blocks `a = 2, 2` and `b = 2, 1, 1`, the reverse of
Definition 7; the counts are stated by block, so the naming does not matter.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Lemma 8 (`integers-2026-A75-lem-8`). -/
public theorem_wanted idealPeriodWord_count_blocks {n : ℕ} (hn : 1 ≤ n) :
    (idealPeriodWord n).count [2, 2] = 2 ^ (n - 1) ∧
      3 * ((idealPeriodWord n).count [2, 1, 1] : ℤ) = 2 ^ n - (-1) ^ n

end

end MetaMathlibExt
