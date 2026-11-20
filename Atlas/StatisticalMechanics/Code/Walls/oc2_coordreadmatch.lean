/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.OSSS.Coding
import Code.OSSS.CovLowerBound
import Code.OSSS.Lindeberg

open scoped BigOperators
open Finset

set_option linter.style.longLine false

namespace StatMech.Walls

open StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]









omit [Fintype E] [DecidableEq E] in




theorem oc2_coord_eq_coordI (e : E) (ω : ConfigSpace E) :
    OSSS.Lindeberg.coord e ω = CovLowerBound.coordI e ω := rfl

omit [Fintype E] [DecidableEq E] in

theorem oc2_coord_eq_indicator (e : E) (ω : ConfigSpace E) :
    OSSS.Lindeberg.coord e ω = (if ω e = true then (1 : ℝ) else 0) := by
  simp only [OSSS.Lindeberg.coord]

omit [Fintype E] [DecidableEq E] in


theorem oc2_coordI_eq_indicator (e : E) (ω : ConfigSpace E) :
    CovLowerBound.coordI e ω = (if ω e = true then (1 : ℝ) else 0) := by
  simp only [CovLowerBound.coordI]














theorem oc2_coord_read_match (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u : Fin n → ℝ) (e : E) :
    OSSS.Lindeberg.coord e (OSSS.Coding.codeMap μ σ u)
        = CovLowerBound.coordI e (OSSS.Coding.codeMap μ σ u)
      ∧ OSSS.Lindeberg.coord e (OSSS.Coding.codeMap μ σ u)
        = (if (OSSS.Coding.codeMap μ σ u) e = true then (1 : ℝ) else 0)
      ∧ CovLowerBound.coordI e (OSSS.Coding.codeMap μ σ u)
        = (if (OSSS.Coding.codeMap μ σ u) e = true then (1 : ℝ) else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact oc2_coord_eq_coordI e (OSSS.Coding.codeMap μ σ u)
  · exact oc2_coord_eq_indicator e (OSSS.Coding.codeMap μ σ u)
  · exact oc2_coordI_eq_indicator e (OSSS.Coding.codeMap μ σ u)






theorem oc2_coord_read_match_sum (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u : Fin n → ℝ) :
    (∑ e, OSSS.Lindeberg.coord e (OSSS.Coding.codeMap μ σ u))
      = ∑ e, CovLowerBound.coordI e (OSSS.Coding.codeMap μ σ u) :=
  Finset.sum_congr rfl
    (fun e _ => oc2_coord_eq_coordI e (OSSS.Coding.codeMap μ σ u))

end StatMech.Walls
