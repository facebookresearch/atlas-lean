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

/-- **Magic squares.** An $n \times n$ array $M$ of natural numbers, with rows and columns
indexed by $0, 1, \dots, n - 1$, is a *magic square* when there is a natural number $s$ such
that every row of $M$ and every column of $M$ sums to $s$, and also $\sum_i M_{i,i} = s$ (the
main diagonal) and $\sum_i M_{i,n-1-i} = s$ (the anti-diagonal).

No condition is imposed on the entries themselves.

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Section 1. -/
def IsMagicSquare {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∃ s : ℕ, (∀ i, ∑ j, M i j = s) ∧ (∀ j, ∑ i, M i j = s) ∧ ∑ i, M i i = s ∧
    ∑ i, M i i.rev = s

/-- **Reduced magic squares.** An $n \times n$ array $M$ of natural numbers is a *reduced magic
square of order $n$* when it is a magic square and its entries are $0, 1, \dots, n^2 - 1$, each
exactly once; equivalently, every entry of $M$ is less than $n^2$ and distinct cells of $M$
hold distinct entries.

These are the magic squares of order $n$ with entries $1, 2, \dots, n^2$, each exactly once,
with every entry reduced by $1$.

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Section 3. -/
def IsReducedMagicSquare {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  IsMagicSquare M ∧ (∀ i j, M i j < n ^ 2) ∧
    Function.Injective (fun p : Fin n × Fin n => M p.1 p.2)

/-- **The reduced Lo Shu square.** The $3 \times 3$ square with rows $(7, 0, 5)$, $(2, 4, 6)$ and
$(3, 8, 1)$, a form of the Lo Shu square with every entry reduced by $1$, is a reduced magic
square of order $3$; its magic sum is $12$.

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Section 3 (reduced magic squares). -/
theorem isReducedMagicSquare_loShu :
    IsReducedMagicSquare !![7, 0, 5; 2, 4, 6; 3, 8, 1] := by
  refine ⟨⟨12, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    first | decide | (intro i j; fin_cases i <;> fin_cases j <;> decide)

/-- **A 2×2 square that is not a reduced magic square.** The $2 \times 2$ square with rows
$(0, 1)$ and $(2, 3)$ is not a reduced magic square.

Its entries are $0, 1, 2, 3$, each once, but its row sums are $1$ and $5$, so it is not magic.

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Section 3 (reduced magic squares). -/
theorem not_isReducedMagicSquare_zero_one_two_three :
    ¬ IsReducedMagicSquare !![0, 1; 2, 3] := by
  rintro ⟨⟨s, hrow, -, -, -⟩, -, -⟩
  have h0 := hrow 0
  have h1 := hrow 1
  simp [Fin.sum_univ_two] at h0 h1
  omega

/-- **Extended Strachey construction.** Let $m$ be a natural number, let $q = (2m+1)^2$, and let
$A_0$, $A_1$, $B_1$, $B_2$ be $(2m+1) \times (2m+1)$ arrays of natural numbers. Suppose that every
entry of $A_0$ is $0$ or $3$, every row of $A_0$ has exactly $m+1$ zeros, and the main diagonal
and the anti-diagonal of $A_0$ each have exactly $m+1$ threes; that every entry of $A_1$ is $1$
or $2$, every row of $A_1$ has exactly $m+2$ ones, and the main diagonal and the anti-diagonal
of $A_1$ each have exactly $m+2$ ones; and that $B_1$ and $B_2$ are reduced magic squares. Then
the square of order $2(2m+1)$ made of four $(2m+1) \times (2m+1)$ blocks, whose $(i, j)$ entries
are $q A_0(i,j) + B_1(i,j)$ in the top left block, $q (3 - A_1(i,j)) + B_2(i,j)$ in the top
right block, $q (3 - A_0(i,j)) + B_1(i,j)$ in the bottom left block and
$q A_1(i,j) + B_2(i,j)$ in the bottom right block, is a reduced magic square.

At $m = 0$ no array $A_1$ satisfies the row condition (a row of length $1$ cannot hold two
ones), so the statement is vacuous there.

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

/-- **Ref-symmetric squares from the Strachey construction.** Let $m$ be a natural number, let
$q = (2m+1)^2$, and let $A_0$, $A_1$ and $M$ be $(2m+1) \times (2m+1)$ arrays of natural
numbers, with rows and columns indexed by $0, 1, \dots, 2m$; write $\bar\imath = 2m - i$ and
$\bar\jmath = 2m - j$. Suppose that every entry of $A_0$ is $0$ or $3$, every row of $A_0$ has
exactly $m+1$ zeros, and the main diagonal and the anti-diagonal of $A_0$ each have exactly
$m+1$ threes; that every entry of $A_1$ is $1$ or $2$, every row of $A_1$ has exactly $m+2$
ones, and the main diagonal and the anti-diagonal of $A_1$ each have exactly $m+2$ ones; that
$A_k(\bar\imath, j) = A_k(i, j)$ and $A_k(m, \bar\jmath) = A_k(m, j)$ for $k = 0, 1$ and all
$i$, $j$; that $M$ is a reduced magic square; and that
$M(i, j) + M(\bar\imath, \bar\jmath) = q - 1$ for all $i$, $j$. Let $B_1(i, j) = M(i, \bar\jmath)$
if $i > m$ and $B_1(i, j) = M(i, j)$ otherwise, and let $B_1^*(i, j) = M(i, \bar\jmath)$ if
$i \ge m$ and $B_1^*(i, j) = M(i, j)$ otherwise. Let $n = 2(2m+1)$ and let $S$ be the square of
order $n$, with rows and columns indexed by $0, 1, \dots, n-1$, made of four
$(2m+1) \times (2m+1)$ blocks whose $(i, j)$ entries are $q A_0(i, j) + B_1(i, j)$ in the top
left block, $q (3 - A_1(i, j)) + B_1(i, \bar\jmath)$ in the top right block,
$q (3 - A_0(i, j)) + B_1^*(i, j)$ in the bottom left block and
$q A_1(i, j) + B_1^*(i, \bar\jmath)$ in the bottom right block. Then $S$ is a reduced magic
square, and $S(i, j) + S(n - 1 - i, j) = n^2 - 1$ for all $i$, $j$.

The last identity is the reduced form of the paper's condition $a_{i,j} + a_{n+1-i,j} = n^2 + 1$.
As in the extended Strachey construction, the statement is vacuous at $m = 0$, where no array
$A_1$ satisfies the row condition.

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
