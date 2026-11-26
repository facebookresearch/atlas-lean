/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.IndexedEdgeLumping

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.IndexedEdgeLumping`

For two parallel edges `Fin 2` lumped onto a single edge (`f : Fin 2 → Unit`), at `p = 1/2`:
* `indexedEffectiveParam` evaluates to `1 - (1 - p)^2 = 3/4`;
* `sum_indexedEdgeProduct_bundleSupport` applied to the indicator "the lumped edge is open";
* `sum_indexedEdgeProduct_restrictActive_bundleSupport` for the one-edge graph `⊤` on `Fin 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.IndexedEdgeLumping

open _root_.StatMech _root_.StatMech.FK

-- The effective parameter of a bundle of two edges.
example : indexedEffectiveParam (fun _ : Fin 2 => ()) (1 / 2) () = 3 / 4 := by
  have h : (indexedBundle (fun _ : Fin 2 => ()) ()).card = 2 := by decide
  rw [indexedEffectiveParam, h]
  norm_num

-- Lumping identity for "the lumped edge is open".
example := sum_indexedEdgeProduct_bundleSupport (1 / 2) (fun _ : Fin 2 => ())
  (fun ρ => if ρ () then 1 else 0)

-- Lumping identity through `restrictActive` for the one-edge graph.
example := sum_indexedEdgeProduct_restrictActive_bundleSupport (⊤ : SimpleGraph (Fin 2))
  (1 / 2) (fun _ : Fin 2 => s(0, 1)) (fun _ => 1)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.IndexedEdgeLumping
