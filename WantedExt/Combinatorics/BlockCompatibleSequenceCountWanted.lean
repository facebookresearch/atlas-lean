/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
OWR-14299518-002, question (2): many block-size sequences are realizable by
pairwise balanced designs.

A descending sequence `n ≥ x₁ ≥ ... ≥ x_m ≥ 2` is block-compatible when some
pairwise balanced design (blocks of size at least 2, each pair of points in
exactly one block, following the convention of `ErdosProblem665PairwiseBalancedDesign`)
has exactly those block sizes. The conjecture: an absolute `c > 0` exists
such that for all large `n`, at least `exp(c√n log n)` sequences are
block-compatible. "At least K" is stated as the existence of a finite
subfamily of that cardinality, avoiding any enumeration bound.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Card
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.BlockCompatibleSequenceCountWanted

/-! Source record `OWR-14299518-002`, question (2). -/

/-- **Pairwise balanced design.** For a natural number $n$, a finite list of blocks
$B_1, \ldots, B_m \subseteq \{0, \ldots, n - 1\}$ is a pairwise balanced design on these $n$ points
when the blocks are pairwise distinct, every block has at least two points, and every two distinct
points lie in exactly one common block. -/
def IsPBD (n : ℕ) (blocks : List (Finset (Fin n))) : Prop :=
  blocks.Nodup ∧
  (∀ B ∈ blocks, 2 ≤ B.card) ∧
    ∀ x y : Fin n, x ≠ y →
      ∃! B : Finset (Fin n), B ∈ blocks ∧ x ∈ B ∧ y ∈ B

/-- **Block-compatible sequences.** For a natural number $n$, a finite sequence
$(x_1, \ldots, x_m)$ of natural numbers is block-compatible for $n$ when
$x_1 \ge x_2 \ge \cdots \ge x_m$, every $x_k$ satisfies $2 \le x_k \le n$, and there is a pairwise
balanced design on the point set $\{0, \ldots, n - 1\}$ whose blocks, listed in order as
$B_1, \ldots, B_m$, have sizes $|B_k| = x_k$ for every $k$. -/
def BlockCompatible (n : ℕ) (l : List ℕ) : Prop :=
  List.Pairwise (· ≥ ·) l ∧ (∀ x ∈ l, 2 ≤ x ∧ x ≤ n) ∧
    ∃ blocks : List (Finset (Fin n)),
      blocks.map Finset.card = l ∧ IsPBD n blocks

/-- **Many block-compatible sequences.** The statement that there are a real number $c > 0$ and a
natural number $N$ such that for every $n \ge N$ there is a finite set of at least
$\exp(c \sqrt{n} \log n)$ distinct finite sequences of natural numbers, each of which is
block-compatible for $n$. Here $\log$ is the natural logarithm.

Source: OWR-14299518-002, question (2). -/
def conjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ S : Finset (List ℕ), (∀ l ∈ S, BlockCompatible n l) ∧
      Real.exp (c * Real.sqrt n * Real.log n) ≤ (S.card : ℝ)

/--
**Many block-compatible sequences (Erdős Problem 732).** There are a real number $c > 0$ and a
natural number $N$ such that for every $n \ge N$ there is a finite set of at least
$\exp(c \sqrt{n} \log n)$ distinct finite sequences of natural numbers, each of which is
block-compatible for $n$. Here $\log$ is the natural logarithm.

Alon proved the stronger bound that at least $2^{(1/2 + o(1)) \sqrt{n} \log n}$ sequences are
block-compatible for $n$ (Oberwolfach Report 42/2025, Theorem 4; also Theorem 2.3 of his note
'Blocking partial designs and block-compatible sequences').

Source: N. Alon, On designs and
partial designs, extended abstract in Oberwolfach Report 42/2025 (Combinatorics, Probability and
Computing), pp. 2249-2250, Theorem 4, https://doi.org/10.4171/owr/2025/42; N. Alon, Blocking
partial designs and block-compatible sequences, note, Theorem 2.3,
https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf; T. F. Bloom, Erdős Problem #732,
erdosproblems.com (status PROVED), https://www.erdosproblems.com/732. Moved from
`OpenConjectures/Combinatorics/BlockCompatibleSequenceCount`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.BlockCompatibleSequenceCountWanted
