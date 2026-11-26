/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.ThermodynamicDuality

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.ThermodynamicDuality`

* `dualConfigEquiv` flips the all-open configuration on two edges to the all-closed one;
* `dualConfigEquiv_symm` with `Equiv.symm_apply_apply`: dualizing twice is the identity;
* `weakLimit_dual_event` on the image measure `nu.map (dualConfigEquiv e)` and the sure event;
* `exists_common_weak_dual_limits` for a constant sequence and its dual image.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.ThermodynamicDuality

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory

-- The dual of the all-open configuration is all-closed.
example : dualConfigEquiv (Equiv.refl (Fin 2)) (fun _ => true) = fun _ => false := by
  funext f
  simp only [dualConfigEquiv_apply, Bool.not_true]

-- Dualizing along `e` and then along `e.symm` is the identity.
example (omega : ConfigSpace (Fin 3)) (e : Fin 3 ≃ Fin 3) :
    dualConfigEquiv e.symm (dualConfigEquiv e omega) = omega := by
  rw [dualConfigEquiv_symm, Equiv.symm_apply_apply]

-- The dual event formula for the sure event under an image measure.
example (nu : ProbabilityMeasure (ConfigSpace (Fin 2))) (e : Fin 2 ≃ Fin 2) :
    ((nu.map (dualConfigEquiv e) : ProbabilityMeasure _) :
        Measure (ConfigSpace (Fin 2))) Set.univ =
      (nu : Measure (ConfigSpace (Fin 2))) ((dualConfigEquiv e) ⁻¹' Set.univ) :=
  weakLimit_dual_event e nu _ rfl MeasurableSet.univ

-- Common dual weak limits for a constant sequence.
example (nu : ProbabilityMeasure (ConfigSpace (Fin 2))) (e : Fin 2 ≃ Fin 2) :
    ∃ (phi : ℕ → ℕ) (lim : ProbabilityMeasure (ConfigSpace (Fin 2)))
      (limDual : ProbabilityMeasure (ConfigSpace (Fin 2))),
      StrictMono phi ∧ WeakConvergesTo (fun n => (fun _ => nu) (phi n)) lim ∧
      WeakConvergesTo
        (fun n => (fun _ => nu.map (dualConfigEquiv e)) (phi n))
        limDual ∧
      limDual = lim.map (dualConfigEquiv e) :=
  exists_common_weak_dual_limits e (fun _ => nu) (fun _ => nu.map (dualConfigEquiv e))
    fun _ => rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.ThermodynamicDuality
