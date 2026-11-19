/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lines through two points avoiding a blocking set (Erdős Problem 105)

Erdős Problem 105 (Erdős and Purdy): let `A, B ⊆ ℝ²` be disjoint sets of size `n` and `n - 3`, with
`A` not contained in a line. Is there a line which contains at least two points of `A` and no point
of `B`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section

namespace MathlibExt.Geometry.LineAvoidingBlockersErdosProblem105Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #105, https://www.erdosproblems.com/105 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006722 (`EP-105`), dataset ulamai/UnsolvedMath v1.8.0.

`|B| = n - 3` is written `|A| = |B| + 3`, which excludes the degenerate `n < 3`. Lines are `line[ℝ,
p, q]` for distinct `p, q ∈ A`. Compared with the formal-conjectures statement
`ErdosProblems/105.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 105: if `A, B ⊆ ℝ²` are disjoint finite sets with `|A| = n`, `|B| = n - 3` and `A`
not contained in a line, then some line through two points of `A` contains no point of `B`. -/
def lineAvoidingBlockers : Prop :=
  ∀ A B : Finset (EuclideanSpace ℝ (Fin 2)), Disjoint A B → A.card = B.card + 3 →
    ¬ Collinear ℝ (A : Set (EuclideanSpace ℝ (Fin 2))) →
    ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ ∀ b ∈ B, b ∉ line[ℝ, p, q]

/--
Resolved false: erdosproblems.com/105 lists the problem as disproved (Lean), by three explicit
configurations of Xichuan in which every line through two points of `A` meets `B`; a formal proof is
in plby/lean-proofs (`Erdos105.lean`). Source: T. F. Bloom, Erdős Problems, Problem #105,
https://www.erdosproblems.com/105 (status DISPROVED (LEAN)); resolution: Xichuan, three explicit
counterexamples in the erdosproblems.com/105 comments; formal proof plby/lean-proofs,
src/v4.29.1/ErdosProblems/Erdos105.lean, erdosproblems.com/105: 'This has been disproved by Xichuan
in the comments, who has found three explicit counterexamples',
https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos105.lean.
-/
public theorem_wanted lineAvoidingBlockers_refuted : ¬ lineAvoidingBlockers

end MathlibExt.Geometry.LineAvoidingBlockersErdosProblem105Wanted
