/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine Conway point permutations act on the independent original-line binary module. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryUniversalModule

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Literal Conway point transport, extended linearly to the free source point module. -/
def monsterCo1GeometryFreeAction (g : Co1) :
    MonsterCo1GeometryFreeModule →ₗ[ZMod 2] MonsterCo1GeometryFreeModule :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (fun p => g • p)

/-- Transport takes every original line relation into the same original relation submodule. -/
theorem monsterCo1GeometryFreeAction_preserves (g : Co1) :
    monsterCo1GeometryLineSubmodule ≤ monsterCo1GeometryLineSubmodule.comap
      (monsterCo1GeometryFreeAction g) := by
  rw [monsterCo1GeometryLineSubmodule, Submodule.span_le]
  rintro v ⟨p, q, r, h, rfl⟩
  change monsterCo1GeometryFreeAction g
    (Finsupp.single p 1 + Finsupp.single q 1 + Finsupp.single r 1) ∈
      Submodule.span (ZMod 2) monsterCo1GeometryLineVectors
  simp only [map_add, monsterCo1GeometryFreeAction, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  exact Submodule.subset_span ⟨g • p, g • q, g • r,
    monsterCo1GeometryLine_smul g p q r h, rfl⟩

/-- The actual Conway point transport descends to the independent source universal module. -/
def monsterCo1GeometryUniversalAction (g : Co1) :
    MonsterCo1GeometryUniversalModule →ₗ[ZMod 2] MonsterCo1GeometryUniversalModule :=
  monsterCo1GeometryLineSubmodule.mapQ monsterCo1GeometryLineSubmodule
    (monsterCo1GeometryFreeAction g) (monsterCo1GeometryFreeAction_preserves g)

/-- The descended operator retains literal transport of every actual source point generator. -/
theorem monsterCo1GeometryUniversalAction_point (g : Co1) (p : MonsterCo1GeometryPoint) :
    monsterCo1GeometryUniversalAction g (monsterCo1GeometryUniversalPoint p) =
      monsterCo1GeometryUniversalPoint (g • p) := by
  change monsterCo1GeometryLineSubmodule.mapQ monsterCo1GeometryLineSubmodule
    (monsterCo1GeometryFreeAction g) _ (Submodule.Quotient.mk (Finsupp.single p 1)) = _
  rw [Submodule.mapQ_apply]
  simp only [monsterCo1GeometryFreeAction, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
