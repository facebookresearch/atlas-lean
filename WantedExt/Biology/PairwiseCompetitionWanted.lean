/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Selection coefficient from a pairwise competition assay

The resistant-to-susceptible abundance ratio under constant haploid relative fitness.
-/

@[expose] public section

namespace WantedExt.Biology.PairwiseCompetitionWanted

/-- In serial batch competition between two asexual strains with positive abundances,
constant, frequency-independent relative fitness `w_R / w_S = exp s` per generation makes the
logarithm of the resistant-to-susceptible abundance ratio linear in the generation count, with
slope `s`. At every positive generation count, `s` is the logarithm of the ratio's fold change
from its initial value, divided by the generation count.

Source: E. Gullberg et al., *Selection of resistant bacteria at very low antibiotic
concentrations*, PLoS Pathogens 7 (2011), e1002158, Results and Materials and Methods,
"Competition experiments", https://doi.org/10.1371/journal.ppat.1002158. -/
public theorem_wanted selection_coefficient_pairwise_competition
    (N_R N_S : ℕ → ℝ) (w_R w_S s : ℝ)
    (hR : ∀ t, 0 < N_R t) (hS : ∀ t, 0 < N_S t)
    (hwR : 0 < w_R) (hwS : 0 < w_S)
    (hfitness : w_R / w_S = Real.exp s)
    (hselection : ∀ t, N_R (t + 1) / N_S (t + 1) =
      (w_R / w_S) * (N_R t / N_S t)) :
    ∀ t : ℕ,
      Real.log (N_R t / N_S t) = Real.log (N_R 0 / N_S 0) + s * (t : ℝ) ∧
      (0 < t → s = Real.log ((N_R t / N_S t) / (N_R 0 / N_S 0)) / (t : ℝ))

end WantedExt.Biology.PairwiseCompetitionWanted
