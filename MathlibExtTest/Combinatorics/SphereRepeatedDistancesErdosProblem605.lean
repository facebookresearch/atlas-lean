/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SphereRepeatedDistancesErdosProblem605

open MathlibExt.Combinatorics.SphereRepeatedDistancesErdosProblem605Wanted

open Classical in
example (P : Finset (EuclideanSpace ℝ (Fin 3))) : pairsAtDistance P 0 = 0 := by
  simp [pairsAtDistance]

open Classical in
example (p q : EuclideanSpace ℝ (Fin 3)) (hpq : p ≠ q) :
    pairsAtDistance {p, q} (dist p q) = 1 := by
  have h : p ∉ ({q} : Finset _) := by simpa
  norm_num [pairsAtDistance, Finset.offDiag_insert h, Finset.filter_insert,
    Finset.filter_singleton, dist_comm q p, hpq]
