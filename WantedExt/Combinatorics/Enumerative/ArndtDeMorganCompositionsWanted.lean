/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Arndt and De Morgan compositions

Statements from Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*,
INTEGERS 26 (2026), Article A64.

The permutations `U` and `V` act on Mathlib's `Composition n`; the counts are over tuples of
positive integers, as in `kArndtCompositionCount`. The number `a(n, k)` of generalized Arndt
compositions of `n` (pairwise condition `c_{2i-1} > c_{2i} + k`) is `kArndtTotalCount k n`, the
sum over the number of parts of `kArndtCompositionCount k n m`
(`WantedExt/Combinatorics/Enumerative/ArndtCompositionsGeneratingFunctionsWanted.lean`).
`c^{2k}_o(n)` and `c^{2k+1}_e(n)` are `oddOrSmallEvenCompositionCount k n` and
`evenOrSmallOddCompositionCount k n`. The permutations `U` and `V` of the paper act on the list of
parts pair by pair; a final unpaired part `c` is the pair `(c, 0)` and maps to `c` parts `1`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.NumberTheory.PadovanSequence
public import WantedExt.Combinatorics.Enumerative.ArndtCompositionsGeneratingFunctionsWanted

namespace MetaMathlibExt

@[expose] public section

/-- The number `a(n, k)` of generalized Arndt compositions of `n`: compositions with
`c_{2i-1} > c_{2i} + k` for every pair of consecutive positions `2i - 1, 2i`, summed over the
number of parts. The empty composition gives `a(0, k) = 1`.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Definition 4. -/
def kArndtTotalCount (k : ℤ) (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), kArndtCompositionCount k n m

/-- Values from Table 9: `a(5, 0) = 5`, `a(5, -1) = 10`, `a(5, -2) = 14`, `a(5, 1) = 3`.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 9. -/
theorem kArndtTotalCount_five :
    kArndtTotalCount 0 5 = 5 ∧ kArndtTotalCount (-1) 5 = 10 ∧ kArndtTotalCount (-2) 5 = 14 ∧
      kArndtTotalCount 1 5 = 3 := by
  decide

/-- `c^{2k}_o(n)`: the number of compositions of `n` whose parts are odd or even and at most
`2k`, counted as `m`-tuples of positive integers summing to `n` over all `m` (as in
`kArndtCompositionCount`). For `k = 0` these are De Morgan's compositions into odd parts.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Definitions 2 and 5. -/
def oddOrSmallEvenCompositionCount (k n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    ∀ i, 0 < c i ∧ (Odd (c i) ∨ c i ≤ 2 * k)).card

/-- `c^0_o(5) = 5` and `c^2_o(5) = 14` (Table 3 of the paper lists these compositions).

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 3 and the discussion after Theorem 5. -/
theorem oddOrSmallEvenCompositionCount_five :
    oddOrSmallEvenCompositionCount 0 5 = 5 ∧ oddOrSmallEvenCompositionCount 1 5 = 14 := by
  decide

/-- `c^{2k+1}_e(n)`: the number of compositions of `n` whose parts are even or odd and at most
`2k + 1`, counted as `m`-tuples of positive integers summing to `n` over all `m`.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Definition 5. -/
def evenOrSmallOddCompositionCount (k n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    ∀ i, 0 < c i ∧ (Even (c i) ∨ c i ≤ 2 * k + 1)).card

/-- `c^1_e(5) = 10` and `c^3_e(5) = 15` (Table 6 of the paper lists these compositions).

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 6 and the discussion after Theorem 6. -/
theorem evenOrSmallOddCompositionCount_five :
    evenOrSmallOddCompositionCount 0 5 = 10 ∧ evenOrSmallOddCompositionCount 1 5 = 15 := by
  decide

/-- The map `U` on lists of parts, pair by pair:
`(c₁, c₂) ↦ (1^{c₁ - c₂ - 1}, 2c₂ + 1)` if `c₂ < c₁`, and
`(c₁, c₂) ↦ (1^{c₁ + c₂ - 2k}, 2k)` if `2k - 2 ≤ c₂ - c₁ < 2k` with `k ≥ 1`
(that is, `k = (c₂ - c₁)/2 + 1`); a final unpaired part `c` (the pair `(c, 0)`) maps to `c`
parts `1`.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 2 and its proof. -/
def arndtU : List ℕ → List ℕ
  | [] => []
  | [a] => List.replicate a 1
  | a :: b :: rest =>
      (if b < a then List.replicate (a - b - 1) 1 ++ [2 * b + 1]
        else List.replicate (a + b - 2 * ((b - a) / 2 + 1)) 1 ++ [2 * ((b - a) / 2 + 1)]) ++
        arndtU rest

/-- Entries of Table 3: `U(2,3) = (1,1,1,2)`, `U(1,4) = (1,4)`, `U(3,2) = (5)`,
`U(1,1,1,2) = (2,1,2)`, `U(1,3,1) = (4,1)`.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 3. -/
theorem arndtU_examples :
    arndtU [2, 3] = [1, 1, 1, 2] ∧ arndtU [1, 4] = [1, 4] ∧ arndtU [3, 2] = [5] ∧
      arndtU [1, 1, 1, 2] = [2, 1, 2] ∧ arndtU [1, 3, 1] = [4, 1] := by
  decide

/-- The map `V` on lists of parts, pair by pair:
`(c₁, c₂) ↦ (1^{c₁ - c₂}, 2c₂)` if `c₂ - c₁ < 1`, and
`(c₁, c₂) ↦ (1^{c₁ + c₂ - 2k - 1}, 2k + 1)` if `2k - 1 ≤ c₂ - c₁ < 2k + 1` with `k ≥ 1`
(that is, `k = (c₂ - c₁ + 1)/2`); a final unpaired part `c` (the pair `(c, 0)`) maps to `c`
parts `1`.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 3 and its proof. -/
def arndtV : List ℕ → List ℕ
  | [] => []
  | [a] => List.replicate a 1
  | a :: b :: rest =>
      (if b ≤ a then List.replicate (a - b) 1 ++ [2 * b]
        else List.replicate (a + b - 2 * ((b - a + 1) / 2) - 1) 1 ++
          [2 * ((b - a + 1) / 2) + 1]) ++
        arndtV rest

/-- Entries of Table 6: `V(2,3) = (1,1,3)`, `V(1,4) = (5)`, `V(4,1) = (1,1,1,2)`,
`V(1,3,1) = (1,3,1)`, `V(2,2,1) = (4,1)`.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 6. -/
theorem arndtV_examples :
    arndtV [2, 3] = [1, 1, 3] ∧ arndtV [1, 4] = [5] ∧ arndtV [4, 1] = [1, 1, 1, 2] ∧
      arndtV [1, 3, 1] = [1, 3, 1] ∧ arndtV [2, 2, 1] = [4, 1] := by
  decide

/-- Arndt's compositions of `n` are equinumerous with De Morgan's compositions of `n` into odd
parts: `a(n) = c_o(n)`. The bijection `A(n) ≅ C_o(n)` is stated as equality of the cardinalities
of these finite sets; `n = 0` (both counts `1`) is included.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 1 (`integers-2026-A64-thm-1`). -/
public theorem_wanted kArndtTotalCount_zero_eq_odd_compositions (n : ℕ) :
    kArndtTotalCount 0 n = oddOrSmallEvenCompositionCount 0 n

/-- The pairwise map `U` sends compositions of `n` to compositions of `n` and is a permutation of
the compositions of `n`.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 2 (`integers-2026-A64-thm-2`). -/
public theorem_wanted exists_perm_composition_blocks_eq_arndtU (n : ℕ) :
    ∃ σ : Equiv.Perm (Composition n), ∀ c, (σ c).blocks = arndtU c.blocks

/-- The pairwise map `V` sends compositions of `n` to compositions of `n` and is a permutation of
the compositions of `n`.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 3 (`integers-2026-A64-thm-3`). -/
public theorem_wanted exists_perm_composition_blocks_eq_arndtV (n : ℕ) :
    ∃ σ : Equiv.Perm (Composition n), ∀ c, (σ c).blocks = arndtV c.blocks

/-- The compositions fixed by `U` are those whose odd-indexed parts (1-based) are `1` and whose
even-indexed parts are even (0-based: even positions hold `1`, odd positions hold even parts).
Their number `c_U(n)` satisfies `c_U(n) = c_U(n - 2) + c_U(n - 3)` for `n ≥ 4` with
`c_U(1) = 1`, `c_U(2) = 0`, `c_U(3) = 1`, and `c_U(n)` is the Padovan number
`shiftedPadovanSequence (n - 1)` (OEIS A000931, shifted) for `n ≥ 1`.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Proposition 1 (`integers-2026-A64-prop-1`). -/
public theorem_wanted arndtU_fixed_iff_and_count :
    (∀ (n : ℕ) (c : Composition n), arndtU c.blocks = c.blocks ↔
      ∀ (i : ℕ) (h : i < c.blocks.length),
        if i % 2 = 0 then c.blocks[i] = 1 else Even c.blocks[i]) ∧
    (∀ n : ℕ, 4 ≤ n →
      (Finset.univ.filter fun c : Composition n => arndtU c.blocks = c.blocks).card =
        (Finset.univ.filter fun c : Composition (n - 2) => arndtU c.blocks = c.blocks).card +
          (Finset.univ.filter fun c : Composition (n - 3) => arndtU c.blocks = c.blocks).card) ∧
    (Finset.univ.filter fun c : Composition 1 => arndtU c.blocks = c.blocks).card = 1 ∧
    (Finset.univ.filter fun c : Composition 2 => arndtU c.blocks = c.blocks).card = 0 ∧
    (Finset.univ.filter fun c : Composition 3 => arndtU c.blocks = c.blocks).card = 1 ∧
    ∀ n : ℕ, 1 ≤ n →
      (Finset.univ.filter fun c : Composition n => arndtU c.blocks = c.blocks).card =
        shiftedPadovanSequence (n - 1)

/-- The compositions fixed by `V` are those whose odd-indexed parts (1-based) are `1` and whose
even-indexed parts are odd and at least `3`. Their number `c_V(n)` satisfies
`c_V(n) = c_V(n - 2) + c_V(n - 4)` for `n ≥ 5` with `c_V(1) = c_V(4) = 1` and
`c_V(2) = c_V(3) = 0`, and `c_V(2j) = c_V(2j + 1) = F_{j-1}` for `j ≥ 1`.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Proposition 2 (`integers-2026-A64-prop-2`). -/
public theorem_wanted arndtV_fixed_iff_and_count :
    (∀ (n : ℕ) (c : Composition n), arndtV c.blocks = c.blocks ↔
      ∀ (i : ℕ) (h : i < c.blocks.length),
        if i % 2 = 0 then c.blocks[i] = 1 else Odd c.blocks[i] ∧ 3 ≤ c.blocks[i]) ∧
    (∀ n : ℕ, 5 ≤ n →
      (Finset.univ.filter fun c : Composition n => arndtV c.blocks = c.blocks).card =
        (Finset.univ.filter fun c : Composition (n - 2) => arndtV c.blocks = c.blocks).card +
          (Finset.univ.filter fun c : Composition (n - 4) => arndtV c.blocks = c.blocks).card) ∧
    (Finset.univ.filter fun c : Composition 1 => arndtV c.blocks = c.blocks).card = 1 ∧
    (Finset.univ.filter fun c : Composition 4 => arndtV c.blocks = c.blocks).card = 1 ∧
    (Finset.univ.filter fun c : Composition 2 => arndtV c.blocks = c.blocks).card = 0 ∧
    (Finset.univ.filter fun c : Composition 3 => arndtV c.blocks = c.blocks).card = 0 ∧
    ∀ j : ℕ, 1 ≤ j →
      (Finset.univ.filter fun c : Composition (2 * j) => arndtV c.blocks = c.blocks).card =
          Nat.fib (j - 1) ∧
        (Finset.univ.filter fun c : Composition (2 * j + 1) =>
          arndtV c.blocks = c.blocks).card = Nat.fib (j - 1)

/-- For `k = -j ≤ 0`, `a(n, k) = a(n - 1, k) + 2a(n - 2, k) - a(n - 2 + k, k)`, and for `k ≥ 0`,
`a(n, k) = a(n - 1, k) + a(n - 2, k) - a(n - 3, k) + a(n - 3 - k, k)`, for `n ≥ 3`, with
`a(0, k) = 1` (the empty composition) and `a(m, k) = 0` for `m < 0` (the `if` terms). The paper
sets `a(n - 2 + k, k) = 0` whenever `n - 2 + k ≤ 0`; at `n - 2 + k = 0` that is false
(`k = -1`, `n = 3`: `a(3, -1) = 3`, while `a(2, -1) + 2a(1, -1) - 0 = 4`), and its own bijection
uses the empty composition there. At `n = 2` the recurrences fail for every `k`
(`a(2, k) ≠ a(1, k) + 2a(0, k)`), so `n ≥ 3` is assumed.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 4 (`integers-2026-A64-thm-4`). -/
public theorem_wanted kArndtTotalCount_recurrence :
    (∀ j n : ℕ, 3 ≤ n →
      (kArndtTotalCount (-(j : ℤ)) n : ℤ) =
        kArndtTotalCount (-(j : ℤ)) (n - 1) + 2 * kArndtTotalCount (-(j : ℤ)) (n - 2) -
          if j + 2 ≤ n then (kArndtTotalCount (-(j : ℤ)) (n - 2 - j) : ℤ) else 0) ∧
    ∀ k n : ℕ, 3 ≤ n →
      (kArndtTotalCount k n : ℤ) =
        kArndtTotalCount k (n - 1) + kArndtTotalCount k (n - 2) - kArndtTotalCount k (n - 3) +
          if k + 3 ≤ n then (kArndtTotalCount k (n - 3 - k) : ℤ) else 0

/-- For `k = -2j` a negative even number, `a(n, k) = c^{-k}_o(n)`; `n = 0` is included.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 5 (`integers-2026-A64-thm-5`). -/
public theorem_wanted kArndtTotalCount_neg_even (j n : ℕ) (hj : 1 ≤ j) :
    kArndtTotalCount (-(2 * j : ℤ)) n = oddOrSmallEvenCompositionCount j n

/-- For `k = -2j - 1` a negative odd number (`j ≥ 0`), `a(n, k) = c^{-k}_e(n)`; `n = 0` is
included.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 6 (`integers-2026-A64-thm-6`). -/
public theorem_wanted kArndtTotalCount_neg_odd (j n : ℕ) :
    kArndtTotalCount (-(2 * j + 1 : ℤ)) n = evenOrSmallOddCompositionCount j n

/-- For `k ≥ 1` and `n ≥ 3`,
`c^{2k+1}_e(n) = c^{2k+1}_e(n - 1) + 2c^{2k+1}_e(n - 2) - c^{2k+1}_e(n - 2 - 2k - 1)` and
`c^{2k}_o(n) = c^{2k}_o(n - 1) + 2c^{2k}_o(n - 2) - c^{2k}_o(n - 2 - 2k)`, with counts at
negative arguments `0` (the `if` terms) and at `0` equal to `1`; at `n = 2` both fail.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Corollary 1 (`integers-2026-A64-cor-1`). -/
public theorem_wanted evenOrSmallOdd_oddOrSmallEven_recurrence (k n : ℕ) (hk : 1 ≤ k)
    (hn : 3 ≤ n) :
    ((evenOrSmallOddCompositionCount k n : ℤ) =
        evenOrSmallOddCompositionCount k (n - 1) + 2 * evenOrSmallOddCompositionCount k (n - 2) -
          if 2 * k + 3 ≤ n then (evenOrSmallOddCompositionCount k (n - 3 - 2 * k) : ℤ)
          else 0) ∧
      (oddOrSmallEvenCompositionCount k n : ℤ) =
        oddOrSmallEvenCompositionCount k (n - 1) + 2 * oddOrSmallEvenCompositionCount k (n - 2) -
          if 2 * k + 2 ≤ n then (oddOrSmallEvenCompositionCount k (n - 2 - 2 * k) : ℤ) else 0

end

end MetaMathlibExt
