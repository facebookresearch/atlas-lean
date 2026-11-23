/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.MaxNTimesCoverage
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Maximum `n`-times coverage tests

Three overlays and two elements of weights `2` and `3`: overlay `0` covers element `0` twice,
overlay `1` covers both elements once, overlay `2` covers element `1` once. The `2`-times
coverage of `{0, 1}` is `2`, of `{1, 2}` is `3`, of all three `5`; the empty set covers nothing.
Theorem 1 is instantiated at `n = 2` and `n = 5`, and the `n = 1` submodularity at this
instance. `n = 0` is the boundary: every element counts.
-/

namespace Cslib.Algorithms.Lean.MaxNTimesCoverage

open Finset

private def wt : Fin 2 → ℝ := ![2, 3]

private def cov : Fin 3 → Fin 2 → ℕ := ![![2, 0], ![1, 1], ![0, 1]]

example : coverCount cov {0, 1} 0 = 3 := by simp [coverCount, cov]

example : nCoverage wt cov 2 {0, 1} = 2 := by
  simp [nCoverage, coverCount, cov, wt, Fin.sum_univ_two]

example : nCoverage wt cov 2 {1, 2} = 3 := by
  simp [nCoverage, coverCount, cov, wt, Fin.sum_univ_two]

example : nCoverage wt cov 2 univ = 5 := by
  simp [nCoverage, coverCount, cov, wt, Fin.sum_univ_two, Fin.sum_univ_three]; norm_num

example : nCoverage wt cov 2 ∅ = 0 := by
  simp [nCoverage, coverCount]

/-- Boundary `n = 0`: every element counts, even for the empty set. -/
example : nCoverage wt cov 0 ∅ = 5 := by
  simp [nCoverage, wt, Fin.sum_univ_two]; norm_num

example : ¬IsSubmodular (nCoverage (fun _ : Unit => (1 : ℝ)) (fun (_ : Fin 2) _ => 1) 2) :=
  not_isSubmodular_nCoverage le_rfl

example : ¬IsSubmodular (nCoverage (fun _ : Unit => (1 : ℝ)) (fun (_ : Fin 5) _ => 1) 5) :=
  not_isSubmodular_nCoverage (by norm_num)

example : IsSubmodular (nCoverage wt cov 1) :=
  isSubmodular_nCoverage_one (fun i => by fin_cases i <;> simp [wt]) cov

example : nCoverage wt cov 2 {0, 1} ≤ nCoverage wt cov 2 univ :=
  nCoverage_mono (fun i => by fin_cases i <;> simp [wt]) cov 2 (subset_univ _)

end Cslib.Algorithms.Lean.MaxNTimesCoverage
