/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.InducedDensity

/-!
# Tests for induced densities and the averaging identity

The double count and the superset count on `Fin 4`, checked by evaluation against the
theorems, and the averaging identity instantiated with `k = 2 ≤ l = 3 ≤ n = 4`.
-/

open Finset MathlibExt.Combinatorics.SimpleGraph.InducedDensity

namespace MathlibExtTest.Combinatorics.SimpleGraph.InducedDensity

/-- The vertex `0` of `Fin 4` lies in `C(3, 1) = 3` pairs. -/
example : #{L ∈ (univ : Finset (Fin 4)).powersetCard 2 | ({0} : Finset (Fin 4)) ⊆ L} = 3 := by
  decide

example : #{L ∈ (univ : Finset (Fin 4)).powersetCard 2 | ({0} : Finset (Fin 4)) ⊆ L} =
    (4 - 1).choose (2 - 1) :=
  card_superset_powersetCard (K := ({0} : Finset (Fin 4))) (by decide)

/-- Singletons containing `0`, counted inside the `6` pairs of `Fin 4`: each of the `1` such
singleton lies in `3` pairs. -/
example : ∑ L ∈ (univ : Finset (Fin 4)).powersetCard 2,
    #{K ∈ L.powersetCard 1 | (0 : Fin 4) ∈ K} = 3 := by decide

example : ∑ L ∈ (univ : Finset (Fin 4)).powersetCard 2,
    #{K ∈ L.powersetCard 1 | (0 : Fin 4) ∈ K} =
      (4 - 1).choose (2 - 1) * #{K ∈ (univ : Finset (Fin 4)).powersetCard 1 | (0 : Fin 4) ∈ K} :=
  sum_card_filter_powersetCard (fun K : Finset (Fin 4) => (0 : Fin 4) ∈ K) (by decide)

/-- The edge density of `K₄` is the average of the edge densities of its four triangles. -/
example : inducedDensity (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 4)) =
    (∑ L ∈ (univ : Finset (Fin 4)).powersetCard 3,
      inducedDensityIn (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 4)) L) /
        ((Fintype.card (Fin 4)).choose 3 : ℚ) :=
  inducedDensity_eq_average _ _ (by decide) (by simp)

end MathlibExtTest.Combinatorics.SimpleGraph.InducedDensity
