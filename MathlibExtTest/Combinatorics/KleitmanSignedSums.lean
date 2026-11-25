/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.KleitmanSignedSums
import Mathlib.Algebra.BigOperators.Fin

open MathlibExt.Combinatorics.StrongLittlewoodOffordErdosProblem498Wanted

-- Opposite signs on two equal vectors give the same sum twice, attaining the bound.
example :
    {ε : Fin 2 → Bool | ∑ i, (if ε i then (1 : ℂ) else -1) * 1 ∈ Metric.ball 0 1}.ncard = 2 := by
  refine le_antisymm (signedSumsInUnitDiscBound_holds 2 (fun _ => 1) (by simp) 0) ?_
  have h : {ε : Fin 2 → Bool | ε 0 ≠ ε 1} ⊆
      {ε : Fin 2 → Bool | ∑ i, (if ε i then (1 : ℂ) else -1) * 1 ∈ Metric.ball 0 1} := by
    intro ε hε
    change ε 0 ≠ ε 1 at hε
    change ∑ i, (if ε i then (1 : ℂ) else -1) * 1 ∈ Metric.ball 0 1
    cases h₀ : ε 0 <;> cases h₁ : ε 1 <;> simp_all [Fin.sum_univ_two]
  refine le_trans ?_ (Set.ncard_le_ncard h)
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  decide

-- Both signs of the imaginary unit lie on the boundary of the open disc at zero.
example :
    {ε : Fin 1 → Bool |
      ∑ i, (if ε i then (1 : ℂ) else -1) * Complex.I ∈ Metric.ball 0 1}.ncard = 0 := by
  rw [Set.ncard_eq_zero]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ε
  cases h : ε 0 <;> simp [h, Metric.mem_ball]
