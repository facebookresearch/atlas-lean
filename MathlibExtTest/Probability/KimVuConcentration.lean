/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.KimVuConcentration

open MeasureTheory unitInterval MathlibExt.Probability.Combinatorics.RandomSubset
open MathlibExt.Probability.KimVuConcentrationWanted

namespace MathlibExtTest.Probability.KimVuConcentration

private noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

private def fullEdge : Finset (Finset (Fin 2)) := {Finset.univ}

-- The second derivative of the two-variable monomial is one, even at the all-false outcome.
example : truncatedPoly fullEdge (fun _ => 1) Finset.univ (fun _ => false) = 1 := by
  simp [truncatedPoly, fullEdge, Finset.filter_singleton]

-- There are no subsets of size three on two vertices.
example : maxAverageEffect (fun _ => half) fullEdge (fun _ => 1) 3 = 0 := by
  have : IsEmpty {A : Finset (Fin 2) // A.card = 3} := ⟨fun ⟨A, h⟩ => by
    have hle : A.card ≤ 2 := by simpa using A.card_le_univ
    omega⟩
  simp [maxAverageEffect, iSup_of_empty', Real.sSup_empty]

-- Apply the concentration theorem to the product of two independent fair bits.
example :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 1 < lam →
      (randomSubsetLaw (fun _ : Fin 2 => half)).real
        {ω | (8 : ℝ) ^ (2 : ℕ) * Real.sqrt (Nat.factorial 2 : ℝ) *
              Real.sqrt ((max (maxAverageEffect (fun _ => half) fullEdge (fun _ => 1) 0)
                  (⨆ j : Fin 2, maxAverageEffect (fun _ => half) fullEdge (fun _ => 1) (j + 1))) *
                (⨆ j : Fin 2, maxAverageEffect (fun _ => half) fullEdge (fun _ => 1) (j + 1))) *
                lam ^ (2 : ℕ) <
            |truncatedPoly fullEdge (fun _ => 1) ∅ ω -
              ∫ ω', truncatedPoly fullEdge (fun _ => 1) ∅ ω'
                ∂(randomSubsetLaw (fun _ : Fin 2 => half))|} ≤
        C * Real.exp (-lam + Real.log 2) := by
  obtain ⟨C, hC, htail⟩ := kim_vu_concentration 2
  refine ⟨C, hC, fun lam hlam => ?_⟩
  have hdeg (e : Finset (Fin 2)) (_ : e ∈ fullEdge) : e.card ≤ 2 := by
    simpa using e.card_le_univ
  simpa [show (2 : ℝ) - 1 = 1 by norm_num] using
    htail 2 (fun _ => half) fullEdge (fun _ => 1) (by simp) hdeg lam hlam

end MathlibExtTest.Probability.KimVuConcentration
