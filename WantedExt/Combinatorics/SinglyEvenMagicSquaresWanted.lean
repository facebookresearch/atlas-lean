/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SinglyEvenMagicSquares

/-!
# Strachey-type magic squares of singly even order

The ref-symmetric construction of Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic
Squares of Singly Even Orders*, Journal of Integer Sequences 27 (2024), Article 24.1.4.

A square of order `2(2m+1)` is built from a radix-digit square `A` with entries in
`{0, 1, 2, 3}` and a unit-digit square `B` whose blocks are reduced magic squares of order
`2m+1`; the entry of the superposition `[A; B]` is `A i j * (2m+1)² + B i j`. Arrays are
`Matrix (Fin n) (Fin n) ℕ`, the anti-diagonal of `M` is `i ↦ M i i.rev`, and block squares are
assembled with `Matrix.fromBlocks` and reindexed along `finSumFinEquiv`.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

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
