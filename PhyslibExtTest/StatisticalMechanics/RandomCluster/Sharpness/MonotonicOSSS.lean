/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.MonotonicOSSS

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.MonotonicOSSS`

* `fkMass_pos` and `fkMass_sum_eq_one` on the complete graph on `Fin 2` at `p = 1/2`, `q = 2`;
* `fkMass_isMonotonic` (the headline, unconditional) on the same instance;
* `fkVar_indicator` for the event "edge `s(0, 1)` is open";
* non-vacuity of `MonotonicOSSSBound`: it holds trivially with `N = 0`, `D = 0`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.MonotonicOSSS

open _root_.StatMech _root_.StatMech.OSSS

-- The random-cluster mass on `K₂` at `p = 1/2`, `q = 2` is strictly positive and sums to one.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    0 < MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 ω ∧
      ∑ ω' : ConfigSpace (Sym2 (Fin 2)), MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 ω'
        = 1 :=
  ⟨MonotonicFK.fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num) ω,
    MonotonicFK.fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)⟩

-- Monotonicity of the random-cluster mass for `q = 2 ≥ 1` on `K₂`.
example : Monotonic.IsMonotonicMeasure (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) :=
  MonotonicFK.fkMass_isMonotonic ⊤ (by norm_num) (by norm_num) (by norm_num)

-- The variance of the indicator of "`s(0, 1)` is open" is `P (1 - P)`.
example :
    MonotonicMeasure.genVar (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
        ({ω | ω (s(0, 1) : Sym2 (Fin 2)) = true}.indicator (fun _ => (1 : ℝ)))
      = FK.fkProbOf (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 {ω | ω s(0, 1) = true}
          * (1 - FK.fkProbOf (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 {ω | ω s(0, 1) = true}) :=
  MonotonicFK.fkVar_indicator ⊤ (1 / 2) 2 _

-- `MonotonicOSSSBound` is satisfiable: with `N = 0` and `D = 0` both sides vanish.
example (f : ConfigSpace (Sym2 (Fin 2)) → ℝ) (c₀ : ℝ) :
    MonotonicMeasure.MonotonicOSSSBound
      (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) Finset.univ f 0 c₀ 0 := by
  simp [MonotonicMeasure.MonotonicOSSSBound]

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.MonotonicOSSS
