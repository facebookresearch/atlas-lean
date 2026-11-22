/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Strachey-type magic squares of singly even order

Statements from Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even
Orders*, Journal of Integer Sequences 27 (2024), Article 24.1.4, Theorems 1 and 2.

A square of order `2(2m+1)` is built from a radix-digit square `A` with entries in
`{0, 1, 2, 3}` and a unit-digit square `B` whose blocks are reduced magic squares of order
`2m+1`; the entry of the superposition `[A; B]` is `A i j * (2m+1)² + B i j`. Arrays are
`Matrix (Fin n) (Fin n) ℕ`, the anti-diagonal of `M` is `i ↦ M i i.rev`, and block squares are
assembled with `Matrix.fromBlocks` and reindexed along `finSumFinEquiv`.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- A square array of natural numbers is a *magic square* when every row, every column, the
main diagonal and the anti-diagonal have one common sum.

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Section 1. -/
def IsMagicSquare {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∃ s : ℕ, (∀ i, ∑ j, M i j = s) ∧ (∀ j, ∑ i, M i j = s) ∧ ∑ i, M i i = s ∧
    ∑ i, M i i.rev = s

/-- A *reduced magic square of order `n`* is a magic square whose entries are
`0, 1, …, n² - 1`, each exactly once (a magic square of order `n` with every entry reduced
by `1`); "each exactly once" is stated as: entries are below `n²` and pairwise distinct.

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Section 3. -/
def IsReducedMagicSquare {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  IsMagicSquare M ∧ (∀ i j, M i j < n ^ 2) ∧
    Function.Injective (fun p : Fin n × Fin n => M p.1 p.2)

/-- The reduced Lo Shu square is a reduced magic square of order `3` (magic sum `12`).

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Section 3 (reduced magic squares). -/
theorem isReducedMagicSquare_loShu :
    IsReducedMagicSquare !![7, 0, 5; 2, 4, 6; 3, 8, 1] := by
  refine ⟨⟨12, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    first | decide | (intro i j; fin_cases i <;> fin_cases j <;> decide)

/-- The square `[[0, 1], [2, 3]]` has all entries `0, …, 3` once but is not magic (row sums
`1` and `5`).

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Section 3 (reduced magic squares). -/
theorem not_isReducedMagicSquare_zero_one_two_three :
    ¬ IsReducedMagicSquare !![0, 1; 2, 3] := by
  rintro ⟨⟨s, hrow, -, -, -⟩, -, -⟩
  have h0 := hrow 0
  have h1 := hrow 1
  simp [Fin.sum_univ_two] at h0 h1
  omega

/-- Theorem 1 (the extended Strachey construction). Let `A₀` be a `(2m+1) × (2m+1)` array with
entries in `{0, 3}`, each row having exactly `m + 1` zeros and each diagonal exactly `m + 1`
threes; let `A₁` have entries in `{1, 2}`, each row and each diagonal having exactly `m + 2`
ones; and let `B₁`, `B₂` be reduced magic squares of order `2m+1`. With `A₂ = 3J - A₁`,
`A₃ = 3J - A₀`, `A = [[A₀, A₂], [A₃, A₁]]` and `B = [[B₁, B₂], [B₁, B₂]]`, the superposition
`[A; B]`, read in base `(2m+1)²`, is a reduced magic square of order `2(2m+1)`. At `m = 0` no `A₁`
satisfies `hA₁row` (a row of length `1` cannot hold `2` ones), so the statement is vacuous there.

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Theorem 1, with Definitions 1-3
(`jis-2024-24.1.4-thm-1`). -/
public theorem_wanted isReducedMagicSquare_extendedStrachey (m : ℕ)
    (A₀ A₁ B₁ B₂ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℕ)
    (hA₀ : ∀ i j, A₀ i j = 0 ∨ A₀ i j = 3)
    (hA₀row : ∀ i, #{j | A₀ i j = 0} = m + 1)
    (hA₀diag : #{i | A₀ i i = 3} = m + 1) (hA₀anti : #{i | A₀ i i.rev = 3} = m + 1)
    (hA₁ : ∀ i j, A₁ i j = 1 ∨ A₁ i j = 2)
    (hA₁row : ∀ i, #{j | A₁ i j = 1} = m + 2)
    (hA₁diag : #{i | A₁ i i = 1} = m + 2) (hA₁anti : #{i | A₁ i i.rev = 1} = m + 2)
    (hB₁ : IsReducedMagicSquare B₁) (hB₂ : IsReducedMagicSquare B₂) :
    IsReducedMagicSquare
      ((Matrix.fromBlocks
          (fun i j => A₀ i j * (2 * m + 1) ^ 2 + B₁ i j)
          (fun i j => (3 - A₁ i j) * (2 * m + 1) ^ 2 + B₂ i j)
          (fun i j => (3 - A₀ i j) * (2 * m + 1) ^ 2 + B₁ i j)
          (fun i j => A₁ i j * (2 * m + 1) ^ 2 + B₂ i j)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm)

/-- Theorem 2 (self-complementary squares). Let `A₀`, `A₁` satisfy the hypotheses of Theorem 1
and, in addition, be invariant under the horizontal reflection `ρ` (`A i.rev j = A i j`) with
middle row `m` symmetric about its central cell. Let `M` be a reduced ro-symmetric magic square
of order `2m+1` (`M i j + M i.rev j.rev = (2m+1)² - 1`). Let `B₁` be `M` with its bottom `m`
rows reversed (`π(M₃)`), `B₁*` be `B₁` with its middle row also reversed, and
`B = [[B₁, π(B₁)], [B₁*, π(B₁*)]]` where `π` reverses every row. Then the superposition
`[A*; B]` is a reduced magic square of order `n = 2(2m+1)` that is ref-symmetrical:
`S i j + S i.rev j = n² - 1`, the reduced form of the paper's `a_{i,j} + a_{n+1-i,j} = n² + 1`.
As in Theorem 1, the statement is vacuous at `m = 0`, where no `A₁` satisfies `hA₁row`.

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Theorem 2, with Definitions 4-6
(`jis-2024-24.1.4-thm-2`). -/
public theorem_wanted isReducedMagicSquare_refSymmetric_strachey (m : ℕ)
    (A₀ A₁ M : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℕ)
    (hA₀ : ∀ i j, A₀ i j = 0 ∨ A₀ i j = 3)
    (hA₀row : ∀ i, #{j | A₀ i j = 0} = m + 1)
    (hA₀diag : #{i | A₀ i i = 3} = m + 1) (hA₀anti : #{i | A₀ i i.rev = 3} = m + 1)
    (hA₁ : ∀ i j, A₁ i j = 1 ∨ A₁ i j = 2)
    (hA₁row : ∀ i, #{j | A₁ i j = 1} = m + 2)
    (hA₁diag : #{i | A₁ i i = 1} = m + 2) (hA₁anti : #{i | A₁ i i.rev = 1} = m + 2)
    (hA₀ρ : ∀ i j, A₀ i.rev j = A₀ i j) (hA₁ρ : ∀ i j, A₁ i.rev j = A₁ i j)
    (hA₀mid : ∀ j, A₀ ⟨m, by omega⟩ j.rev = A₀ ⟨m, by omega⟩ j)
    (hA₁mid : ∀ j, A₁ ⟨m, by omega⟩ j.rev = A₁ ⟨m, by omega⟩ j)
    (hM : IsReducedMagicSquare M)
    (hMro : ∀ i j, M i j + M i.rev j.rev = (2 * m + 1) ^ 2 - 1) :
    let B₁ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℕ :=
      fun i j => if m < (i : ℕ) then M i j.rev else M i j
    let B₁' : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℕ :=
      fun i j => if m ≤ (i : ℕ) then M i j.rev else M i j
    let S := (Matrix.fromBlocks
          (fun i j => A₀ i j * (2 * m + 1) ^ 2 + B₁ i j)
          (fun i j => (3 - A₁ i j) * (2 * m + 1) ^ 2 + B₁ i j.rev)
          (fun i j => (3 - A₀ i j) * (2 * m + 1) ^ 2 + B₁' i j)
          (fun i j => A₁ i j * (2 * m + 1) ^ 2 + B₁' i j.rev)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm
    IsReducedMagicSquare S ∧
      ∀ i j, S i j + S i.rev j = (2 * m + 1 + (2 * m + 1)) ^ 2 - 1

end

end MetaMathlibExt
