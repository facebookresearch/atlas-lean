/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Admixture.ConditionalNegDef

/-!
# Tests for conditional negative definiteness and f2 realizability

The examples restate the characterizations and evaluate the separating matrices.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.FStatisticsCovariance
  MathlibExt.Biology.Phylogenetics.Buneman
open MathlibExt.Biology.PopulationGenetics.Admixture

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.ConditionalNegDef

universe u

example : IsF2Realizable twoF2 := isF2Realizable_twoF2
example : ¬ IsF2RealizableUnit twoF2 := not_isF2RealizableUnit_twoF2
example : IsF2Realizable squareF2 := isF2Realizable_squareF2
example : ¬ IsTreeMetric squareF2 := not_isTreeMetric_squareF2
example : ¬ IsF2Realizable nonCndF2 := not_isF2Realizable_nonCndF2

example {P : Type u} [Fintype P] {D : P → P → ℝ} :
    IsF2Realizable D ↔ (∀ i j, D i j = D j i) ∧ (∀ i, D i i = 0) ∧ IsCondNegSemidef D :=
  isF2Realizable_iff

#print axioms MathlibExt.Biology.PopulationGenetics.Admixture.f2_isCondNegSemidef
#print axioms MathlibExt.Biology.PopulationGenetics.Admixture.isF2Realizable_iff
#print axioms MathlibExt.Biology.PopulationGenetics.Admixture.isF2RealizableUnit_iff
#print axioms MathlibExt.Biology.PopulationGenetics.Admixture.exists_driftModel_admix_three
#print axioms MathlibExt.Biology.PopulationGenetics.Admixture.not_isTreeMetric_squareF2

end MathlibExtTest.Biology.PopulationGenetics.Admixture.ConditionalNegDef
