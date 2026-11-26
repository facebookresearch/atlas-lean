/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.QueriedCrossTree

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.QueriedCrossTree`

* `covSum_ge_crossTree` applied in its conditional form, with the edge set `Fin 2` and all
  geometric-embedding and connection hypotheses as binders, at the single scale `n = 1`;
* `covSum_ge_crossTree` stated by name.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.QueriedCrossTree

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.QueriedCrossTreeClose
open _root_.StatMech.OSSS.DecisionTree _root_.StatMech.OSSS.Revealment
open _root_.StatMech.OSSS.RevealmentConstruction _root_.StatMech.OSSS.CovLowerBound
open _root_.StatMech.OSSS.SharpnessFK _root_.StatMech.Lattice

open Classical in
-- The crossing-tree covariance lower bound at scale `1`, for two edges.
example {d : ℕ} {ν : Fin 2 → Bool → ℝ} (hν : IsProbWeight ν)
    {edge : Fin 2 → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : Fin 2 → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
    (disc₀ : ℕ → Finset (Site d))
    (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
    (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
    (hoB : ∀ k, o ∉ disc₀ k)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDnn : 0 ≤ D)
    (hD : ∀ e,
      (∑ k ∈ Finset.Icc 1 1,
        (expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k)
            then (1 : ℝ) else 0)
          + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k)
              then (1 : ℝ) else 0))) ≤ D) :
    ((1 : ℕ) : ℝ) * c₀
        * (expect ν ((crossEvent edge o (vertexBoundary d 1)).indicator (fun _ => (1 : ℝ)))
          * (1 - expect ν ((crossEvent edge o (vertexBoundary d 1)).indicator
            (fun _ => (1 : ℝ)))))
      ≤ D * ∑ e, cov ν (coordI e)
          ((crossEvent edge o (vertexBoundary d 1)).indicator (fun _ => (1 : ℝ))) :=
  covSum_ge_crossTree le_rfl hν hinj hcoh hadj o ho [0, 1] (by decide) disc₀ hdisc₀sub
    hdisc₀sup hoB c₀ hc₀nn hc₀ D hDnn hD

-- The headline lemma exists with the expected name.
example := @covSum_ge_crossTree

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.QueriedCrossTree
