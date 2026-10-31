/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.PoincareApp

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.PoincareApp`

* `fk_poincare_covSum_ge` on the complete graph on `Fin 2` at `p = 1/2`, `q = 2`, for the
  explicit increasing event "edge `s(0, 1)` is open";
* `poincare_covSum_indicator_ge` for the FK mass on `K₂` (positivity, normalization and the FKG
  lattice condition supplied by the library), same event;
* `var_indicator_eq`: the variance of an indicator is `θ (1 - θ)`, for the FK mass on `K₂`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.PoincareApp

open _root_.StatMech _root_.StatMech.OSSS

/-- The event that the edge `s(0, 1)` of `K₂` is open. -/
def edgeOpen : Set (ConfigSpace (Sym2 (Fin 2))) := {ω | ω s(0, 1) = true}

/-- The event `edgeOpen` is increasing. -/
theorem isIncreasing_edgeOpen : IsIncreasing edgeOpen := by
  intro x y hxy hx
  simp only [edgeOpen, Set.mem_ofPred_eq] at hx ⊢
  have hle := hxy s(0, 1)
  rw [hx] at hle
  exact le_antisymm (by simp) hle

-- The FK Poincaré bound for the event "edge `s(0, 1)` is open" on `K₂`.
example :
    FK.fkProbOf (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 edgeOpen
        * (1 - FK.fkProbOf (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 edgeOpen)
      ≤ ∑ e, FK.fkCov (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2
          (edgeOpen.indicator (fun _ => (1 : ℝ))) (FK.coord e) :=
  MonotonicFK.fk_poincare_covSum_ge ⊤ (by norm_num) (by norm_num) (by norm_num)
    isIncreasing_edgeOpen

-- The abstract indicator bound, instantiated at the FK mass on `K₂`.
example :
    Lindeberg.mean (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
        (edgeOpen.indicator (fun _ => (1 : ℝ)))
        * (1 - Lindeberg.mean (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
          (edgeOpen.indicator (fun _ => (1 : ℝ))))
      ≤ ∑ e, Lindeberg.cov (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
          (edgeOpen.indicator (fun _ => (1 : ℝ))) (Lindeberg.coord e) :=
  PoincareApp.poincare_covSum_indicator_ge
    (MonotonicFK.fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (MonotonicFK.fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num))
    (FK.fkProb_FKGLatticeCondition ⊤ (by norm_num) (by norm_num) (by norm_num))
    isIncreasing_edgeOpen

-- The variance of an indicator is `θ (1 - θ)`.
example (A : Set (ConfigSpace (Sym2 (Fin 2)))) :
    Lindeberg.var (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
        (A.indicator (fun _ => (1 : ℝ)))
      = Lindeberg.mean (MonotonicFK.fkMass ⊤ (1 / 2) 2) (A.indicator (fun _ => (1 : ℝ)))
        * (1 - Lindeberg.mean (MonotonicFK.fkMass ⊤ (1 / 2) 2)
          (A.indicator (fun _ => (1 : ℝ)))) :=
  PoincareApp.var_indicator_eq _ A

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.PoincareApp
