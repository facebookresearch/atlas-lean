/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.EquivalenceReflection
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Fibration
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.QuasicategoryFibrations

/-!
# The original cocartesian projection is a genuine categorical fibration

Its source-prescribed cocartesian lifts of actual base equivalences are
proved equivalences in the original total space. The native Joyal criterion
then applies to that same original projection.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace SSet

/-- Original cocartesian lifts of base equivalences retain both their endpoints and full base image. -/
theorem CocartesianFibration.hasStrictEquivalenceLifting {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] [Quasicategory B] : HasStrictEquivalenceLifting p where
  exists_lift {x} {b} g hg := by
    obtain ⟨y, hy, a, ha, hmap⟩ := CocartesianFibration.lift (p := p) x b g
    have hmapEq : (a.map p).IsEquivalence := (Edge.isEquivalence_iff_of_edge_eq hmap).mpr hg
    exact ⟨y, hy, a, CocartesianEdge.isEquivalence_of_map p a ha hmapEq, hmap⟩

/-- An actual cocartesian fibration over a quasicategory lies in the genuine Joyal fibration class. -/
theorem CocartesianFibration.categoricalFibration {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] [Quasicategory B] : categoricalFibrations p :=
  (categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting p).mpr
    ⟨inferInstance, CocartesianFibration.hasStrictEquivalenceLifting p⟩

end SSet
