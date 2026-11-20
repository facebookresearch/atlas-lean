/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.RandomWalkHighDimensionalReduction
import Code.Lattice.HypercubicLattice

open Filter Finset Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Lattice


def latticeOriginDelta (d : ℕ) : Site d → ℝ :=
  fun x => if x = 0 then 1 else 0


noncomputable def latticeEuclideanRadius (d : ℕ) (x : Site d) : ℝ :=
  Real.sqrt (∑ i, (x i : ℝ) ^ 2)





structure HighDimensionalRandomWalkHypotheses
    (d : ℕ) (betaC epsilon sigma C c : ℝ)
    (twoPoint : ℝ → Site d → ℝ) (xi : ℝ → ℝ) : Type where
  dimension : 2 < d
  epsilon_pos : 0 < epsilon
  sigma_pos : 0 < sigma
  C_pos : 0 < C
  c_pos : 0 < c
  correlationLength_pos : ∀ beta, beta ≤ betaC → 0 < xi beta
  transfer : ℝ → PositiveAdditiveOperator (Site d)
  effectiveGreen : ℝ → Site d → ℝ
  twoPoint_nonneg : ∀ beta x, 0 ≤ twoPoint beta x
  renewal : ∀ beta, beta ≤ betaC → ∀ x,
    twoPoint beta x ≤ latticeOriginDelta d x + transfer beta (twoPoint beta) x
  partial_tendsto : ∀ beta, beta ≤ betaC → ∀ x,
    Tendsto
      (fun n => randomWalkPartial (transfer beta) (latticeOriginDelta d) n x)
      atTop (nhds (effectiveGreen beta x))
  remainder_tendsto : ∀ beta, beta ≤ betaC → ∀ x,
    Tendsto (fun n => randomWalkIterate (transfer beta) n (twoPoint beta) x)
      atTop (nhds 0)
  effectiveGreen_bound : ∀ beta, beta ≤ betaC → ∀ x,
    effectiveGreen beta x ≤ latticeOriginDelta d x +
      highDimensionalRandomWalkTail d epsilon sigma C c (xi beta)
        (latticeEuclideanRadius d x)



theorem highDimensionalRandomWalk_bound
    {d : ℕ} {betaC epsilon sigma C c : ℝ}
    {twoPoint : ℝ → Site d → ℝ} {xi : ℝ → ℝ}
    (H : HighDimensionalRandomWalkHypotheses
      d betaC epsilon sigma C c twoPoint xi)
    {beta : ℝ} (hbeta : beta ≤ betaC) (x : Site d) :
    twoPoint beta x ≤ latticeOriginDelta d x +
      highDimensionalRandomWalkTail d epsilon sigma C c (xi beta)
        (latticeEuclideanRadius d x) := by
  exact renewal_to_highDimensionalRandomWalk_bound
    (H.transfer beta) d epsilon sigma C c (xi beta)
    (latticeOriginDelta d) (twoPoint beta) (H.effectiveGreen beta)
    (latticeEuclideanRadius d) (H.renewal beta hbeta)
    (H.partial_tendsto beta hbeta) (H.remainder_tendsto beta hbeta)
    (H.effectiveGreen_bound beta hbeta) x

end StatMech.FrontierA
