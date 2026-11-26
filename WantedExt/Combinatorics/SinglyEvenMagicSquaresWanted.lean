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
