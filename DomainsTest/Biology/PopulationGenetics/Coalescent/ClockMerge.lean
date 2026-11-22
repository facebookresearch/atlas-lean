/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.ClockMerge

/-!
# Tests for the clock/merge decomposition

Boundary instances of `KingmanTimes.ofGenealogy`: the concrete genealogy at
`n = 2` has expected TMRCA `1` and expected total length `2`; at `n = 1` the
TMRCA is `0`; the empty and singleton samples still carry a `KingmanTimes`
(empty epoch index). The marginal and one-step uniformity statements are
exercised at `n = 2`, where the single merging pair is forced.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.ClockMerge

open MathlibExt.Biology.PopulationGenetics.Coalescent

/-- The concrete genealogy carries a `KingmanTimes` already at `n = 0`. -/
example : KingmanTimes (kingmanGenealogyMeasure 0) 0 := KingmanTimes.ofGenealogy 0

/-- Two genes on the concrete genealogy: `E[T_MRCA] = 1`. -/
example : (kingmanGenealogyMeasure 2)[(KingmanTimes.ofGenealogy 2).tmrca] = 1 := by
  rw [(KingmanTimes.ofGenealogy 2).integral_tmrca (by norm_num)]
  norm_num

/-- One gene on the concrete genealogy: the TMRCA expectation is `0`. -/
example : (kingmanGenealogyMeasure 1)[(KingmanTimes.ofGenealogy 1).tmrca] = 0 := by
  rw [(KingmanTimes.ofGenealogy 1).integral_tmrca le_rfl]
  norm_num

/-- Two genes on the concrete genealogy: `E[L] = 2`. -/
example : (kingmanGenealogyMeasure 2)[(KingmanTimes.ofGenealogy 2).totalLength] = 2 := by
  rw [(KingmanTimes.ofGenealogy 2).integral_totalLength]
  norm_num [harmonic]

/-- The history marginal of the two-gene genealogy is `randomJoining 2`:
its pushforward of the whole space is `1`. -/
example : Measure.map Prod.snd (kingmanGenealogyMeasure 2) = randomJoining 2 :=
  (MathlibExt.Biology.PopulationGenetics.Coalescent.ClockMerge.measurePreserving_snd_genealogy
    2).map_eq

/-- At `n = 2` the single random-joining step is uniform over the (unique) pair. -/
example (i : Fin (2 - 1)) :
    HasLaw (fun h : RankedHistory 2 => h i)
      (ProbabilityTheory.uniformOn (Set.univ : Set (LineagePair (2 - i))))
      (randomJoining 2) :=
  MathlibExt.Biology.PopulationGenetics.Coalescent.ClockMerge.hasLaw_step_randomJoining 2 i

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.ClockMerge
