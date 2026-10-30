/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.Set.Card

/-!
# Positional colored compositions (statements)

Statement-only targets from Andrew Li and Hua Wang, *Combinatorics of Positional Colored
Compositions*, INTEGERS 26 (2026), Article A49. In an `(m, k)`-`n`-colored composition the
parts at positions `≡ k (mod m)` (positions counted from `1`) carry a color from `1` to the part,
the other parts are uncolored; `c_{m,k}(ℓ)` is `positionalColoredCompositionCount m k ℓ`. EVEN
colored compositions are the case `(2, 0)` (count `e(ℓ)`) and ODD colored compositions the
case `(2, 1)` (count `o(ℓ)`). Ternary and binary strings are lists over `Fin 3` and `Bool`; a
string avoids `01` and `12` when neither occurs as a contiguous factor (`List.IsInfix`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- `c_{m,k}(ℓ)`: the number of `(m, k)`-`n`-colored compositions of `ℓ`, i.e. the sum over
compositions of `ℓ` of the product of the parts at positions `≡ k (mod m)` (each such part `p`
has `p` colors; the position of the `i`-th block, `0`-indexed, is `i + 1`). The paper takes
`m ≥ 1`; the definition is total, and at `m = 0` (where `x % 0 = x`) it colors only the part at
position exactly `k`. The statements below that vary `m` assume `1 ≤ m`.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Definition 1. -/
public def positionalColoredCompositionCount (m k ℓ : ℕ) : ℕ :=
  ∑ c : Composition ℓ, (c.blocks.mapIdx fun i p => if (i + 1) % m = k % m then p else 1).prod

/-- Characteristic value `c_{m,k}(0) = 1` (the empty composition).

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Definition 1. -/
public theorem positionalColoredCompositionCount_zero (m k : ℕ) :
    positionalColoredCompositionCount m k 0 = 1 := by
  have h : (Finset.univ : Finset (Composition 0)) = {Composition.ones 0} := by decide
  simp [positionalColoredCompositionCount, h, Composition.ones]

/-- For `k ≥ 0`, the number of `n`-color compositions of `k` restricting the color `2` (a part
`p ≥ 2` has the `p - 1` colors other than `2`, a part `1` its single color) equals the number
`e(k)` of EVEN colored compositions of `k`. Stated for all `k ≥ 0` (both sides are `1` at
`k = 0`); the paper says `k` positive.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 1 (`integers-2026-A49-thm-1`). -/
public theorem_wanted colorTwoRestrictedCompositions_eq_even (k : ℕ) :
    ∑ c : Composition k, (c.blocks.map fun p => if 2 ≤ p then p - 1 else p).prod =
      positionalColoredCompositionCount 2 0 k

/-- For `k ≥ 1`, the number `o(k)` of ODD colored compositions of `k` equals the number of
`C(n, 2)`-color compositions of `k + 1` (a part `p` has `C(p, 2)` colors).

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 2 (`integers-2026-A49-thm-2`). -/
public theorem_wanted odd_eq_choose_two_colorCompositions (k : ℕ) (hk : 1 ≤ k) :
    positionalColoredCompositionCount 2 1 k =
      ∑ c : Composition (k + 1), (c.blocks.map fun p => p.choose 2).prod

/-- For `k ≥ 1`, the number `o(k)` of ODD colored compositions of `k` equals the number of
ternary strings of length `k - 1` avoiding the factors `01` and `12`.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Corollary 1 (`integers-2026-A49-cor-1`). -/
public theorem_wanted odd_eq_ternaryStrings_avoiding (k : ℕ) (hk : 1 ≤ k) :
    positionalColoredCompositionCount 2 1 k =
      {w : List (Fin 3) | w.length = k - 1 ∧ ¬ [0, 1] <:+: w ∧ ¬ [1, 2] <:+: w}.ncard

/-- For `k ≥ 0`, the number `e(k)` of EVEN colored compositions of `k` equals the number of
ternary strings of length `k` avoiding the factors `01` and `12` that do not begin with `2` and
do not end with `0`. Stated for all `k ≥ 0` (both sides are `1` at `k = 0`).

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 3 (`integers-2026-A49-thm-3`). -/
public theorem_wanted even_eq_ternaryStrings_avoiding (k : ℕ) :
    positionalColoredCompositionCount 2 0 k =
      {w : List (Fin 3) | w.length = k ∧ ¬ [0, 1] <:+: w ∧ ¬ [1, 2] <:+: w ∧
        w.head? ≠ some 2 ∧ w.getLast? ≠ some 0}.ncard

/-- For `k ≥ 0`, `e(k + 1)` equals the sum over all binary strings of length `k` of the product
of the lengths of their runs of `1`s (`true`s); the all-`0` string contributes the empty
product `1`.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 4 (`integers-2026-A49-thm-4`). -/
public theorem_wanted even_succ_eq_sum_runLength_prod (k : ℕ) :
    positionalColoredCompositionCount 2 0 (k + 1) =
      ∑ f : Fin k → Bool,
        ((((List.ofFn f).splitOn false).map List.length).filter (· ≠ 0)).prod

/-- For `k ≥ 1`, `o(k)` equals the sum over the binary strings of length `k` that start with
`1` (`true`) of the product of the lengths of their runs of `1`s.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 5 (`integers-2026-A49-thm-5`). -/
public theorem_wanted odd_eq_sum_runLength_prod (k : ℕ) (hk : 1 ≤ k) :
    positionalColoredCompositionCount 2 1 k =
      ∑ f ∈ (Finset.univ : Finset (Fin k → Bool)).filter (fun f => (List.ofFn f).head? = some true),
        ((((List.ofFn f).splitOn false).map List.length).filter (· ≠ 0)).prod

/-- For `ℓ ≥ 1` and `m ∤ k`, `c_{m,k+1}(ℓ + 1) = c_{m,k+1}(ℓ) + c_{m,k}(ℓ)`. Corrected reading:
the printed hypotheses `k ≥ 1`, `ℓ ≥ 2`, `1 ≤ m ≤ ℓ - 1` admit `m ∣ k`, where the identity fails
(`m = 1`, `k = 1`, `ℓ = 2`: `c_{1,2}(3) = 8` but `c_{1,2}(2) + c_{1,1}(2) = 6`); the paper's
argument (remove a first part `1` or decrease the first part) needs the first part uncolored,
i.e. `m ∤ k`, which is the hypothesis here (the identity holds for every `ℓ ≥ 1`). The
paper's `1 ≤ m` is kept.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 6 (`integers-2026-A49-thm-6`). -/
public theorem_wanted positionalColoredCompositionCount_succ (m k ℓ : ℕ) (hm : 1 ≤ m)
    (hmk : ¬ m ∣ k) (hℓ : 1 ≤ ℓ) :
    positionalColoredCompositionCount m (k + 1) (ℓ + 1) =
      positionalColoredCompositionCount m (k + 1) ℓ + positionalColoredCompositionCount m k ℓ

/-- For `k ≥ 0`, `e(k)` equals the number of permutations of `{1, …, k}` avoiding the patterns
`321`, `2413` and `3142` (the `321`-avoiding separable permutations). Stated for all `k ≥ 0`
(both sides are `1` at `k = 0`).

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 7 (`integers-2026-A49-thm-7`). -/
public theorem_wanted even_eq_card_separable_321_avoiding (k : ℕ) :
    positionalColoredCompositionCount 2 0 k =
      Nat.card {σ : Equiv.Perm (Fin k) //
        (¬ ∃ a b c : Fin k, a < b ∧ b < c ∧ σ c < σ b ∧ σ b < σ a) ∧
        (¬ ∃ a b c d : Fin k, a < b ∧ b < c ∧ c < d ∧ σ c < σ a ∧ σ a < σ d ∧ σ d < σ b) ∧
        (¬ ∃ a b c d : Fin k, a < b ∧ b < c ∧ c < d ∧ σ b < σ d ∧ σ d < σ a ∧ σ a < σ c)}

end

end MetaMathlibExt
