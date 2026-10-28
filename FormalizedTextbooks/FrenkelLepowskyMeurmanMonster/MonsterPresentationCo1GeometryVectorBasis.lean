/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The twenty-four actual basis-point source generators used by the finite replay. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryUniversalStability

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The first twenty-four literal actual source points are the proposed spanning family. -/
def monsterCo1GeometryVectorBasisPoint (j : Fin 24) : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoints ⟨j.val, by omega⟩

/-- The corresponding literal generators in the independent source universal module. -/
def monsterCo1GeometryVectorBasisValue (j : Fin 24) : MonsterCo1GeometryUniversalModule :=
  monsterCo1GeometryUniversalPoint (monsterCo1GeometryVectorBasisPoint j)

/-- The candidate source-module span is defined without any dimension or injectivity assumption. -/
def monsterCo1GeometryVectorBasisSpan : Submodule (ZMod 2) MonsterCo1GeometryUniversalModule :=
  Submodule.span (ZMod 2) (Set.range monsterCo1GeometryVectorBasisValue)

/-- Each of the first twenty-four literal source points belongs to the candidate source span. -/
theorem monsterCo1GeometryVectorBasis_mem (j : Fin 867) (hj : j.val < 24) :
    monsterCo1GeometryVectorValue j ∈ monsterCo1GeometryVectorBasisSpan := by
  exact Submodule.subset_span ⟨⟨j.val, hj⟩, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
