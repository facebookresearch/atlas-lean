/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.DualPair

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.DualPair`

* the orbit box of radius `1` of the hexagonal lattice has at most `18` vertices
  (`orbitBox_card_le_quadratic` with the two-point fundamental domain);
* `probabilityMeasure_eq_of_finiteCylinder_real_eq` recovers `mu = mu` from equal cylinders;
* for any dual pair, the free dual percolation probability vanishes at `p = 2` (outside
  `(0, 1)`), so `FreeDualPercolates 2 q` fails;
* `swap` exchanges the embeddings, and the conditional `dualCritical_relation_of_freeDual`
  instantiated for an arbitrary dual pair.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.DualPair

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.BeffaraDC
open _root_.StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair

-- Quadratic orbit-box growth on the hexagonal lattice at radius `1`.
example : (hexagonal.orbitBox 1).card ≤ 18 := by
  have h := PeriodicPlanarDualPair.PeriodicGraph.orbitBox_card_le_quadratic hexagonal 1
  have hcard : hexagonal.fundamentalDomain.card = 2 := by decide
  rw [hcard] at h
  simpa using h

-- Equal finite cylinders: the reflexive case.
example {E : Type*} [Countable E] (mu : MeasureTheory.ProbabilityMeasure (ConfigSpace E)) :
    mu = mu :=
  probabilityMeasure_eq_of_finiteCylinder_real_eq mu mu fun _ _ => rfl

-- Free dual percolation never holds at the out-of-range parameter `p = 2`.
example {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
    {P : PeriodicGraph V} {Pdual : PeriodicGraph W} (D : PeriodicPlanarDualPair P Pdual)
    (q : ℝ) : ¬ D.FreeDualPercolates 2 q := by
  have h : D.freeDualPercolationProbability 2 q = 0 := by
    unfold freeDualPercolationProbability
    split_ifs with h2
    · exact absurd h2.1.2 (by norm_num)
    · rfl
  simp only [FreeDualPercolates, h, lt_irrefl, not_false_eq_true]

-- `swap` exchanges the embeddings; the critical relation in its conditional form.
example {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
    {P : PeriodicGraph V} {Pdual : PeriodicGraph W} (D : PeriodicPlanarDualPair P Pdual)
    {q : ℝ} (hpc : P.criticalPoint q ∈ Set.Ioo (0 : ℝ) 1)
    (hpcDual : Pdual.criticalPoint q ∈ Set.Ioo (0 : ℝ) 1) (hq : 1 ≤ q)
    (hcov : ∀ p ∈ Set.Ioo (0 : ℝ) 1, p < P.criticalPoint q → D.FreeDualPercolates p q)
    (hnc : ∀ p ∈ Set.Ioo (0 : ℝ) 1, ¬(P.wiredPercolates p q ∧ D.FreeDualPercolates p q)) :
    D.swap.primalEmbedding = D.dualEmbedding ∧
      dualParam (P.criticalPoint q) q = Pdual.criticalPoint q :=
  ⟨D.swap_primalEmbedding, (D.dualCritical_relation_of_freeDual hpc hpcDual hq hcov hnc).1⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.DualPair
