/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.LocalizedCrossTree

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.LocalizedCrossTree`

* `revealment_sum_bound_lattice_map` on an explicit instance: one edge, `d = 1`, the uniform
  weight on `ConfigSpace (Fin 1)`, `Λ = {0}`, `u = 0`, `n = 2`;
* `revealment_sum_bound_lattice_map` for arbitrary data;
* `hcov_reindexed_crossTree_mass`, the conditional covariance lower bound, stated as a term.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.LocalizedCrossTree

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.OSSS
open _root_.StatMech.OSSS.LocalizedCrossTree _root_.StatMech.OSSS.RevealmentConstruction
open _root_.StatMech.OSSS.RevealmentTranslation

-- The revealment sum bound for one edge at the origin of `ℤ`, with `n = 2`.
open Classical in
example :
    (∑ k ∈ Finset.Icc 1 2,
      Lindeberg.mean (fun _ : ConfigSpace (Fin 1) => (1 / 2 : ℝ)) (fun ω =>
        if ConnectedToSet 1 (liftCfg (fun _ : Fin 1 => s((0 : Site 1), 0)) ω) 0
          (vertexBoundary 1 k) then (1 : ℝ) else 0))
      ≤ 2 * ({0} : Finset (Site 1)).sup' (Finset.singleton_nonempty _)
          (fun x => ∑ j ∈ Finset.range 2,
            Lindeberg.mean (fun _ : ConfigSpace (Fin 1) => (1 / 2 : ℝ)) (fun ω =>
              if ConnectedToSet 1 (liftCfg (fun _ : Fin 1 => s((0 : Site 1), 0)) ω) x
                (centeredBoundary x j) then (1 : ℝ) else 0)) :=
  revealment_sum_bound_lattice_map (n := 2) (fun _ => (1 / 2 : ℝ)) (fun _ => by norm_num) id
    (fun _ => s((0 : Site 1), 0)) {0} (Finset.singleton_nonempty _) 0
    (Finset.mem_singleton_self _) (by simp [box])

-- The bound for arbitrary weights, configuration maps and centers.
open Classical in
example {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E] {d n : ℕ}
    (μ : ConfigSpace E → ℝ) (hμ0 : ∀ ω, 0 ≤ μ ω) (cfg : ConfigSpace E → ConfigSpace I)
    (edge : I → Sym2 (Site d)) (Λ : Finset (Site d)) (hne : Λ.Nonempty) (u : Site d)
    (hu : u ∈ Λ) (hubox : u ∈ box d n) :
    (∑ k ∈ Finset.Icc 1 n,
      Lindeberg.mean μ (fun ω => if ConnectedToSet d (liftCfg edge (cfg ω)) u
        (vertexBoundary d k) then (1 : ℝ) else 0))
      ≤ 2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n,
          Lindeberg.mean μ (fun ω => if ConnectedToSet d (liftCfg edge (cfg ω)) x
            (centeredBoundary x j) then (1 : ℝ) else 0)) :=
  revealment_sum_bound_lattice_map μ hμ0 cfg edge Λ hne u hu hubox

-- The localized covariance lower bound elaborates with its hypotheses.
example := @hcov_reindexed_crossTree_mass

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.LocalizedCrossTree
