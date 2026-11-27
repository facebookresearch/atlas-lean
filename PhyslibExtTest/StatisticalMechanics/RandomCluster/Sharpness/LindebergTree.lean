/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.LindebergTree

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.LindebergTree`

* `treeDepth` and `pathPrefix` on an explicit one-query decision tree;
* non-vacuity of `StepCovBound`: it holds for a leaf tree (nothing is ever revealed);
* `fk_tree_osss` on the complete graph on `Fin 2` at `p = 1/2`, `q = 2`, applied to the leaf tree;
* `tree_osss_revealment_le` for an arbitrary FKG weight, conditional on `StepCovBound`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.LindebergTree

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.LindebergTree
open _root_.StatMech.OSSS.DecisionTree

-- The tree querying edge `0` once has depth `1`, and its one-step path prefix is `{0}`.
example (ω : ConfigSpace (Fin 2)) :
    treeDepth (node (0 : Fin 2) (leaf true) (leaf false)) = 1 ∧
      pathPrefix (node (0 : Fin 2) (leaf true) (leaf false)) ω 1 = {0} := by
  constructor
  · rfl
  · cases h : ω 0 <;> simp [pathPrefix, h]

-- `StepCovBound` is satisfiable: a leaf tree reveals nothing, so both sides vanish.
example {E : Type*} [Fintype E] [DecidableEq E] (μ : ConfigSpace E → ℝ)
    (f : ConfigSpace E → ℝ) (b : Bool) :
    StepCovBound μ (leaf b) f := by
  intro t e
  simp [freshAt, Lindeberg.mean]

-- The tree OSSS inequality on `K₂` for the constant leaf tree.
example :
    Lindeberg.var (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) (leaf true).evalR
      ≤ ∑ e, revealmentMu (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) (leaf true) e
          * Lindeberg.cov (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
            (leaf true).evalR
            (Lindeberg.coord e) :=
  fk_tree_osss ⊤ (by norm_num) (by norm_num) (by norm_num) (leaf true) (by
    intro t e
    simp [freshAt, Lindeberg.mean])

-- `Var f ≤ D ∑ Cov` from the step bound and a uniform revealment bound `D`.
example {E : Type*} [Fintype E] [DecidableEq E] {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (T : DecisionTree E)
    (hfmono : Monotone T.evalR) (hStep : StepCovBound μ T T.evalR) (D : ℝ)
    (hD : ∀ e, revealmentMu μ T e ≤ D) :
    Lindeberg.var μ T.evalR ≤ D * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) :=
  tree_osss_revealment_le hpos hμ1 hFKG T hfmono hStep D hD

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.LindebergTree
