/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.ExpanderChernoff
import Mathlib.Tactic.NormNum

open Finset
open MathlibExt.Combinatorics.SpectralExpander
open MathlibExt.GraphTheory.SpectralExpanderWanted

private noncomputable def spike (v : Fin 3) : ℝ := if v = 0 then 1 else 0

private lemma triangle : IsSpectralExpander (⊤ : SimpleGraph (Fin 3)) 2 (1 / 2) := by
  have h := isSpectralExpander_top (V := Fin 3) (by decide)
  norm_num at h ⊢
  exact h

-- A zero-step walk samples one vertex. The spike reaches the threshold exactly there.
example : ∃ C : ℝ, 0 < C ∧ (1 / 3 : ℝ) ≤ 2 * Real.exp (-(C * (1 / 6) ^ 2)) := by
  obtain ⟨C, hC, hbound⟩ := chernoff_bound_expander_walk
  have hf (v : Fin 3) : 0 ≤ spike v ∧ spike v ≤ 1 := by
    by_cases hv : v = 0 <;> simp [spike, hv]
  have h := hbound (Fin 3) ⊤ 2 (1 / 2) triangle (by decide) spike hf 0 (1 / 6) (by norm_num)
  have hevent (w : Fin (0 + 1) → Fin 3) :
      (1 / 2 : ℝ) + 1 / 6 ≤
          |(1 / (0 + 1 : ℝ)) * ∑ i, spike (w i) - (1 / Fintype.card (Fin 3) : ℝ) *
            ∑ v, spike v| ↔ w 0 = 0 := by
    have hsum : ∑ v, spike v = 1 := by simp [spike]
    rw [hsum, Fin.sum_univ_one]
    by_cases hw : w 0 = 0 <;> norm_num [spike, hw, abs_of_nonneg, abs_of_nonpos]
  have hprob :
      walkProb ⊤ 2 triangle.1 (by decide) 0 (fun w => (1 / 2 : ℝ) + 1 / 6 ≤
          |(1 / (0 + 1 : ℝ)) * ∑ i, spike (w i) - (1 / Fintype.card (Fin 3) : ℝ) *
            ∑ v, spike v|) = 1 / 3 := by
    unfold walkProb
    simp only [hevent]
    rw [← (Fin.consEquiv fun _ => Fin 3).sum_comp, Fintype.sum_prod_type]
    simp
  simp only [Nat.cast_zero] at h
  rw [hprob] at h
  exact ⟨C, hC, by simpa using h⟩
