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

/-- A pairwise balanced design given as an ordered block list: blocks are
pairwise distinct, every block has at least two points, and every pair of
distinct points lies in exactly one block. -/
def IsPBD (n : ℕ) (blocks : List (Finset (Fin n))) : Prop :=
  blocks.Nodup ∧
  (∀ B ∈ blocks, 2 ≤ B.card) ∧
    ∀ x y : Fin n, x ≠ y →
      ∃! B : Finset (Fin n), B ∈ blocks ∧ x ∈ B ∧ y ∈ B

/-- A descending size sequence realizable as the block sizes of a pairwise
balanced design on `Fin n`. -/
def BlockCompatible (n : ℕ) (l : List ℕ) : Prop :=
  List.Pairwise (· ≥ ·) l ∧ (∀ x ∈ l, 2 ≤ x ∧ x ≤ n) ∧
    ∃ blocks : List (Finset (Fin n)),
      blocks.map Finset.card = l ∧ IsPBD n blocks

/-- [OWR-14299518-002(2)] At least `exp(c√n log n)` block-size sequences are
realizable for all large `n`. -/
def conjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ S : Finset (List ℕ), (∀ l ∈ S, BlockCompatible n l) ∧
      Real.exp (c * Real.sqrt n * Real.log n) ≤ (S.card : ℝ)

/--
Resolved true: Answered affirmatively by Alon in the source report (Oberwolfach Report 42/2025,
pp. 2249-2250, Theorem 4; also Theorem 2.3 of his note 'Blocking partial designs and
block-compatible sequences'), recorded on erdosproblems.com/732 (PROVED): at least 2^((1/2 +
o(1)) n^(1/2) log n) sequences are block-compatible for n. Source: N. Alon, On designs and
partial designs, extended abstract in Oberwolfach Report 42/2025 (Combinatorics, Probability and
Computing), pp. 2249-2250, Theorem 4, https://doi.org/10.4171/owr/2025/42; N. Alon, Blocking
partial designs and block-compatible sequences, note, Theorem 2.3,
https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf; T. F. Bloom, Erdős Problem #732,
erdosproblems.com (status PROVED), https://www.erdosproblems.com/732. Moved from
`OpenConjectures/Combinatorics/BlockCompatibleSequenceCount`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.BlockCompatibleSequenceCountWanted
