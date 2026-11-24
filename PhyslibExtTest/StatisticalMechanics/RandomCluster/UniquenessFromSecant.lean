/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.UniquenessFromSecant
import PhyslibExt.StatisticalMechanics.RandomCluster.TiltSecant

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FKUniquenessClose3`

* `freeEdgeDensity` and `wiredEdgeDensity` (from `FKUniquenessFull`) are `0` outside
  `p ∈ (0, 1)`;
* `freeEdgeDensity_q2_le_wiredEdgeDensity` on `ℤ²` at `p = 1/2`: the free edge density is at most
  the wired one, for every edge of `Λ_1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKUniquenessClose3

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

-- The densities are set to `0` at `p = 1`.
example (e : Sym2 (Site 2)) : freeEdgeDensity 2 2 e 1 = 0 ∧ wiredEdgeDensity 2 2 e 1 = 0 := by
  simp [freeEdgeDensity, wiredEdgeDensity]

-- Free density `≤` wired density at `p = 1/2`, for an edge of `Λ_1`.
example (eb : Sym2 (boxVerts 2 1)) :
    freeEdgeDensity 2 2 (edgeIncl 2 1 eb) (1 / 2)
      ≤ wiredEdgeDensity 2 2 (edgeIncl 2 1 eb) (1 / 2) :=
  freeEdgeDensity_q2_le_wiredEdgeDensity 2 1 eb (by norm_num) (by norm_num)

-- The cutoff may depend on the parameter pair and tolerance.
open Filter Topology Set in
example (d N : ℕ) (eb : Sym2 (boxVerts d N)) :
    FKSecantData d N eb ↔
      ∃ S V : ℕ → ℝ, (∀ n, 0 < V n)
        ∧ Tendsto (fun n => S n / V n) atTop (𝓝 0)
        ∧ Tendsto V atTop atTop
        ∧ ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p → ∀ ε > 0,
          ∃ n₀ : ℕ, ∀ n ≥ n₀,
            ε ≤ (2 : ℝ) ^ (S n) * (tiltFactor p p') ^
              ((wiredEdgeDensity d 2 (edgeIncl d N eb) p' -
                freeEdgeDensity d 2 (edgeIncl d N eb) p - 2 * ε) * V n) / ε := by
  simp only [FKSecantData, eventually_atTop]

-- The comparison alone suffices, with no hypothesis about finite boxes.
open Set in
example (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (h : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p) :
    FKSecantData d N eb :=
  (fkSecantData_iff_secant d N eb).mpr h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKUniquenessClose3
