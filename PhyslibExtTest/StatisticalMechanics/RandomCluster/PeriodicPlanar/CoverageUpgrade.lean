/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CoverageUpgrade

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CoverageUpgrade`

* the Dirac mass at the all-open configuration of `ℤ²` has finite energy (a non-vacuity witness
  for the `HasFiniteEnergy` hypothesis);
* `clusterInfinite_real_pos_iff` for that measure on the square lattice transports positivity
  from the origin to `(1, 0)` (conditional on connectivity of the lattice);
* `dualConfigEquiv_setClosed_setOpen` for an arbitrary dual pair, evaluated at the opened edge;
* `bidirectionalSubcriticalCoverage_of_exponentialDecay` in its conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CoverageUpgrade

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.Lattice MeasureTheory

/-- The all-open configuration of `ℤ²`. -/
def allOpen : ConfigSpace (Sym2 (Site 2)) := fun _ => true

/-- The Dirac mass at the all-open configuration has finite energy. -/
theorem allOpen_hasFiniteEnergy : HasFiniteEnergy (Measure.dirac allOpen) := by
  intro F
  have h : forceOpenFinset F allOpen = allOpen := by
    funext e
    by_cases he : e ∈ F <;> simp [forceOpenFinset, allOpen, he]
  rw [Measure.map_dirac' (measurable_forceOpenFinset F), h]

-- Positivity of an infinite cluster moves between vertices (given connectivity).
example (hconn : square.graph.Connected)
    (h0 : 0 < (Measure.dirac allOpen).real {omega | (square.cluster omega 0).Infinite}) :
    0 < (Measure.dirac allOpen).real {omega | (square.cluster omega ![1, 0]).Infinite} :=
  (square.clusterInfinite_real_pos_iff hconn _ allOpen_hasFiniteEnergy 0 _).1 h0

-- Opening a dual edge is closing its primal edge, read at that dual edge.
example {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
    {P : PeriodicGraph V} {Pdual : PeriodicGraph W} (D : PeriodicPlanarDualPair P Pdual)
    (e : Sym2 W) (omega : ConfigSpace (Sym2 V)) :
    dualConfigEquiv D.edgeDual (setClosed (D.edgeDual.symm e) omega) e = true := by
  rw [← D.dualConfigEquiv_setClosed_setOpen e omega]
  exact setOpen_self e _

-- Two-sided coverage from two-sided exponential decay (conditional form).
example {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
    {P : PeriodicGraph V} {Pdual : PeriodicGraph W} (D : PeriodicPlanarDualPair P Pdual)
    (H : PeriodicPlanarDualPair.PolynomialConnectionShells D)
    (Hdual : PeriodicPlanarDualPair.PolynomialConnectionShells D.swap)
    {q pc pcDual : ℝ} (hq : 1 ≤ q) (hdecay : SubcriticalTwoPointExponentialDecay P q pc)
    (hdecayDual : SubcriticalTwoPointExponentialDecay Pdual q pcDual) :
    DualSubcriticalCoverage (fun r => P.wiredPercolates r q) pcDual q :=
  (D.bidirectionalSubcriticalCoverage_of_exponentialDecay H Hdual hq hdecay hdecayDual).2

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CoverageUpgrade
