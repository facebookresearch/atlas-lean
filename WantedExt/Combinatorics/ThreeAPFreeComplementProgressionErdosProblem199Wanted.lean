/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Complements of 3-AP-free sets of reals (Erdős Problem 199)

Erdős Problem 199: if `A ⊆ ℝ` contains no three-term arithmetic progression, must `ℝ \ A` contain an
infinite arithmetic progression?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Additive.AP.Three.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.ThreeAPFreeComplementProgressionErdosProblem199Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #199, https://www.erdosproblems.com/199 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006761 (`EP-199`), dataset ulamai/UnsolvedMath v1.8.0.

Three-term progressions use Mathlib's `ThreeAPFree`. An infinite progression is one-sided, `a, a +
d, a + 2d, …` with `d ≠ 0`; a two-sided progression contains a one-sided one, so this is the
stronger refutation. Compared with the formal-conjectures statement `ErdosProblems/199.lean`
(equivalent; no code imported).
-/

/-- Erdős Problem 199: if `A ⊆ ℝ` contains no three-term arithmetic progression, then `ℝ \ A`
contains an infinite arithmetic progression `a, a + d, a + 2d, …` with `d ≠ 0`. -/
def threeAPFreeComplementContainsProgression : Prop :=
  ∀ A : Set ℝ, ThreeAPFree A → ∃ a d : ℝ, d ≠ 0 ∧ ∀ n : ℕ, a + n * d ∉ A

/--
Resolved false: Baumgartner constructed, with the axiom of choice (a basis of `ℝ` over `ℚ`), a set
`A ⊆ ℝ` with no three-term progression whose complement contains no infinite arithmetic progression;
erdosproblems.com/199 lists the problem as disproved, with a formal proof in plby/lean-proofs
(`Erdos199.lean`). Source: T. F. Bloom, Erdős Problems, Problem #199,
https://www.erdosproblems.com/199 (status DISPROVED (LEAN)); resolution: J. E. Baumgartner,
Partitioning vector spaces, J. Combin. Theory Ser. A 18 (1975), 231-233; formal proof
plby/lean-proofs, src/v4.29.1/ErdosProblems/Erdos199.lean, erdosproblems.com/199: answered no by
Baumgartner (construction using a Hamel basis), https://doi.org/10.1016/0097-3165(75)90011-8.
-/
public theorem_wanted threeAPFreeComplementContainsProgression_refuted :
    ¬ threeAPFreeComplementContainsProgression

end MathlibExt.Combinatorics.ThreeAPFreeComplementProgressionErdosProblem199Wanted
