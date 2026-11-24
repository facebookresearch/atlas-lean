/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.FiniteSumsWitness
public import MathlibExt.Combinatorics.InterleavedSequencesTensor
public import MathlibExt.Combinatorics.PairwiseSumTheorem
public import MathlibExt.Combinatorics.PairwiseSumsWitness
public import MathlibExt.Combinatorics.PartitionRegularUltrafilter
public import MathlibExt.Combinatorics.RamseyWitnessTensorSquare

/-!
# From Schur's theorem to the pairwise sum theorem

Statements from Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum
Theorem*, INTEGERS 25 (2025), Article A105.

A finite coloring is a map `c : S → Fin r`; a set `F` is monochromatic when `c` is constant on
`F` with some value `k : Fin r`. `FS(A)` is the set of sums of nonempty finite subsets of `A`.
Ultrafilters on `ℕ+` carry Mathlib's sum `Ultrafilter.add` (`A ∈ U + V` iff
`{n | {m | n + m ∈ A} ∈ V} ∈ U`) and the Stone–Čech topology. The tensor product of ultrafilters
on `ℕ` is `X ∈ U ⊗ V ↔ {n | {m | (n, m) ∈ X} ∈ V} ∈ U`.

The characterization of Ramsey's witnesses on `ℕ × ℕ` as the closure of the tensor squares
`U ⊗ U` of non-principal ultrafilters (`ramseyWitness_iff_mem_closure_tensor_squares`) is
proved in `MathlibExt.Combinatorics.RamseyWitnessTensorSquare`, which this module imports.
The pairwise sum theorem (`exists_infinite_pairwiseSums_monochromatic`) is proved in
`MathlibExt.Combinatorics.PairwiseSumTheorem` using Hindman's finite sums theorem.
The characterization of the sets `X ⊆ ℕ × ℕ` that contain interleaved sequences by the tensor
products `V₁ ⊗ V₂` and `V₂ ⊗ V₁` of non-principal ultrafilters
(`exists_interleaved_sequences_iff_mem_tensor`) is proved in
`MathlibExt.Combinatorics.InterleavedSequencesTensor`, which this module imports.
-/

open Filter

namespace MetaMathlibExt

@[expose] public section

/-- **Disjoint infinite sets with monochromatic union and sumset.** For every finite coloring of
$\mathbb{N} = \{0, 1, 2, \dots\}$ there are disjoint infinite sets $A, B \subseteq \mathbb{N}$ such
that $A \cup B \cup (A + B)$ is monochromatic, where $A + B = \{a + b : a \in A, b \in B\}$.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Theorem 2.2 (`integers-2025-A105-thm-2-2`). -/
public theorem_wanted exists_disjoint_infinite_union_add_monochromatic {r : ℕ} (c : ℕ → Fin r) :
    ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧ Disjoint A B ∧ ∃ k : Fin r,
      (∀ a ∈ A, c a = k) ∧ (∀ b ∈ B, c b = k) ∧ ∀ a ∈ A, ∀ b ∈ B, c (a + b) = k

end

end MetaMathlibExt
