/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.QuasiIdentitiesGeometricEquivalenceKourovka14Problem71

open MathlibExt.GroupTheory.QuasiIdentitiesGeometricEquivalenceKourovka14Problem71Wanted

-- The proved refutation applies directly to Plotkin's proposition.
example : ¬ sameQuasiIdentitiesImpliesGeometricallyEquivalent :=
  sameQuasiIdentitiesImpliesGeometricallyEquivalent_refuted

example (h : sameQuasiIdentitiesImpliesGeometricallyEquivalent) : False :=
  sameQuasiIdentitiesImpliesGeometricallyEquivalent_refuted h

-- Every group is geometrically equivalent to itself.
example (G : Type) [Group G] : GeometricallyEquivalent G G := fun _ _ => rfl

-- The quasi-identity with no premises and conclusion `1` holds in every group.
example (G : Type) [Group G] : (⟨0, [], 1⟩ : QuasiIdentity).HoldsIn G := by
  intro x _
  simp

-- A quasi-identity whose conclusion is one of its premises holds in every group.
example (G : Type) [Group G] :
    (⟨1, [FreeGroup.of 0], FreeGroup.of 0⟩ : QuasiIdentity).HoldsIn G := by
  intro x hx
  exact hx _ (by simp)
