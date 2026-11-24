/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Admixture.QpAdmCounterexamples
import Domains.Biology.PopulationGenetics.Admixture.ConditionalNegDef

/-! Tests for the qpAdm counterexamples: each explicit graph is realized on a probability
space (the counterexamples are non-vacuous), and the ghost and reversed fits at concrete
parameter values give the out-of-range weights `(-1/2, 3/2)` and `(-1, 2)`. -/

open MeasureTheory Matrix MathlibExt.Biology.PopulationGenetics
  MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.QpAdmCounterexamples

open MathlibExt.Biology.PopulationGenetics.Admixture

/-! ### Realized graphs and boundary cases -/

section Acceptance

-- Each graph is realized on a probability space (all three statements are non-vacuous).
example (α : ℝ) : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
    (M : DriftModel μ (Fin 8) (Fin 7)), M.weight = proxyWeight α ∧ M.len = fun _ => 1 :=
  exists_driftModel _ _ fun _ => zero_le_one
example (α : ℝ) : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
    (M : DriftModel μ (Fin 8) (Fin 7)), M.weight = ghostWeight α ∧ M.len = fun _ => 1 :=
  exists_driftModel _ _ fun _ => zero_le_one
example (β : ℝ) : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
    (M : DriftModel μ (Fin 8) (Fin 6)), M.weight = reversedWeight β ∧ M.len = fun _ => 1 :=
  exists_driftModel _ _ fun _ => zero_le_one

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

-- Out-of-range weights: the ghost graph at `α = 3/4` gives qpAdm weights `(-1/2, 3/2)`; the
-- reversed graph at `β = 1/2` gives `(-1, 2)`.
example (M : DriftModel μ (Fin 8) (Fin 7)) (hw : M.weight = ghostWeight (3 / 4))
    (hl : M.len = fun _ => 1) :
    ADMIXTOOLS.qpAdmSourceMatrix μ M.freq ![0, 1] ![4, 5, 6] *ᵥ ![3 / 2] =
      ADMIXTOOLS.qpAdmTargetVector μ M.freq 3 ![0, 1] ![4, 5, 6] := by
  have := ((ghost_counterexample (by norm_num) M hw hl).2.1 ![3 / 2]).2 (by norm_num)
  exact this
example (M : DriftModel μ (Fin 8) (Fin 6)) (hw : M.weight = reversedWeight (1 / 2))
    (hl : M.len = fun _ => 1) :
    ADMIXTOOLS.qpAdmSourceMatrix μ M.freq ![0, 2] ![3, 4, 5] *ᵥ ![2] =
      ADMIXTOOLS.qpAdmTargetVector μ M.freq 1 ![0, 2] ![3, 4, 5] := by
  have := ((reversed_counterexample (by norm_num) M hw hl).1 ![2]).2 (by norm_num)
  exact this

-- The general ghost statement applies to the ghost graph with span coefficient `c = 2`.
example {α : ℝ} (M : DriftModel μ (Fin 8) (Fin 7)) (hw : M.weight = ghostWeight α)
    (hl : M.len = fun _ => 1) :
    ADMIXTOOLS.qpAdmSourceMatrix μ M.freq ![0, 1] ![4, 5, 6] *ᵥ (α • ![2]) =
      ADMIXTOOLS.qpAdmTargetVector μ M.freq 3 ![0, 1] ![4, 5, 6] := by
  refine qpAdm_mulVec_eq_of_ghost M (T := 3) (G := 2) ![0, 1] ![4, 5, 6] ![2] (fun e j => ?_)
    (fun j => ?_)
  · rw [hw]
    fin_cases e <;> fin_cases j <;> simp [ghostWeight]
  · fin_cases j <;> simp [M.f4_freq, hw, hl, ghostWeight, Fin.sum_univ_succ] <;> norm_num

-- Boundary `α = 0` of the proxy graph: `T = S₀`, the qpAdm weight is `0`, and `T` is then a
-- (trivial) mixture of the proxy and `S₀`, so the hypothesis `α ≠ 0` of
-- `proxy_counterexample` is needed for its last clause.
example (M : DriftModel μ (Fin 8) (Fin 7)) (hw : M.weight = proxyWeight 0) :
    M.weight 3 = (0 : ℝ) • M.weight 2 + (1 - 0 : ℝ) • M.weight 0 := by
  rw [hw]; funext e; fin_cases e <;> simp [proxyWeight]

-- Boundary `β = 0` of the reversed graph: the source carries no ancestry from `T`, its right
-- contrasts vanish, and the qpAdm source matrix is zero, so no weight fits (`T` has a nonzero
-- target vector): the hypothesis `β ≠ 0` is needed.
example (M : DriftModel μ (Fin 8) (Fin 6)) (hw : M.weight = reversedWeight 0)
    (hl : M.len = fun _ => 1) :
    ADMIXTOOLS.qpAdmSourceMatrix μ M.freq ![0, 2] ![3, 4, 5] = 0 ∧
      ADMIXTOOLS.qpAdmTargetVector μ M.freq 1 ![0, 2] ![3, 4, 5] ≠ 0 := by
  refine ⟨?_, fun h => ?_⟩
  · ext j l
    fin_cases j <;> fin_cases l <;>
      simp [ADMIXTOOLS.qpAdmSourceMatrix, M.f4_freq, hw, hl, reversedWeight, Fin.sum_univ_succ]
  · have h0 := congrFun h 0
    simp [ADMIXTOOLS.qpAdmTargetVector, M.f4_freq, hw, hl, reversedWeight, Fin.sum_univ_succ] at h0

end Acceptance

end MathlibExtTest.Biology.PopulationGenetics.Admixture.QpAdmCounterexamples
