/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Coalescent.VariableSFSExistsNeAeFirstCoalMeanEq

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.VariableSFS

open MeasureTheory ProbabilityTheory

theorem exists_distinct_histories_same_three_means :
    ∃ η₁ η₂ : ℝ → ℝ,
      ¬ (η₁ =ᵐ[volume.restrict (Set.Ici 0)] η₂) ∧
      meanWaitingTime (fun t => (η₁ t)⁻¹) 1 = meanWaitingTime (fun t => (η₂ t)⁻¹) 1 ∧
      meanWaitingTime (fun t => (η₁ t)⁻¹) 3 = meanWaitingTime (fun t => (η₂ t)⁻¹) 3 ∧
      meanWaitingTime (fun t => (η₁ t)⁻¹) 6 = meanWaitingTime (fun t => (η₂ t)⁻¹) 6 := by
  obtain ⟨η₁, η₂, _, _, _, hne, hmeans⟩ :=
    MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFSWanted.exists_ne_ae_firstCoalMean_eq
  refine ⟨η₁, η₂, hne, ?_, ?_, ?_⟩
  · simpa using hmeans 2 (by decide)
  · simpa using hmeans 3 (by decide)
  · have h := hmeans 4 (by decide)
    norm_num [Nat.choose] at h
    exact h

#check @MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFSWanted.exists_ne_ae_firstCoalMean_eq
#print axioms MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFSWanted.exists_ne_ae_firstCoalMean_eq
#print axioms exists_distinct_histories_same_three_means

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.VariableSFS
