/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The independent original-line universal module maps naturally onto the actual Leech binary
module. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryLineBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryUniversalAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCo1GeometryPointSpan
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The free source point module maps each point generator to its actual binary coordinates. -/
def monsterCo1GeometryFreeBinary :
    MonsterCo1GeometryFreeModule →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) (fun p : MonsterCo1GeometryPoint => p.val)

/-- Every original genuine line relation vanishes in the actual binary module. -/
theorem monsterCo1GeometryFreeBinary_relations :
    monsterCo1GeometryLineSubmodule ≤ monsterCo1GeometryFreeBinary.ker := by
  rw [monsterCo1GeometryLineSubmodule, Submodule.span_le]
  rintro v ⟨p, q, r, h, rfl⟩
  change monsterCo1GeometryFreeBinary
    (Finsupp.single p 1 + Finsupp.single q 1 + Finsupp.single r 1) = 0
  simpa only [map_add, monsterCo1GeometryFreeBinary, Finsupp.linearCombination_single,
    one_smul] using monsterCo1GeometryLine_binary p q r h

/-- The natural map from the independent universal source module to the actual binary Leech
module. -/
def monsterCo1GeometryUniversalBinary :
    MonsterCo1GeometryUniversalModule →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  monsterCo1GeometryLineSubmodule.liftQ monsterCo1GeometryFreeBinary
    monsterCo1GeometryFreeBinary_relations

/-- The natural map retains the literal binary value of every original actual point generator. -/
theorem monsterCo1GeometryUniversalBinary_point (p : MonsterCo1GeometryPoint) :
    monsterCo1GeometryUniversalBinary (monsterCo1GeometryUniversalPoint p) = p.val := by
  change monsterCo1GeometryFreeBinary (Finsupp.single p 1) = p.val
  simp only [monsterCo1GeometryFreeBinary, Finsupp.linearCombination_single, one_smul]

/-- The independent universal source module surjects onto the actual twenty-four-dimensional
module. -/
theorem monsterCo1GeometryUniversalBinary_surjective :
    Function.Surjective monsterCo1GeometryUniversalBinary := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← generatedCo1GeometryPointSpan_eq_top]
  apply Submodule.span_le.mpr
  intro v hv
  exact ⟨monsterCo1GeometryUniversalPoint ⟨v, hv⟩,
    monsterCo1GeometryUniversalBinary_point ⟨v, hv⟩⟩

/-- The natural binary map intertwines actual Conway transport on original point generators. -/
theorem monsterCo1GeometryUniversalBinary_action_point (g : Co1) (p : MonsterCo1GeometryPoint) :
    monsterCo1GeometryUniversalBinary
      (monsterCo1GeometryUniversalAction g (monsterCo1GeometryUniversalPoint p)) =
    co1BinaryAction g (monsterCo1GeometryUniversalBinary (monsterCo1GeometryUniversalPoint p)) := by
  rw [monsterCo1GeometryUniversalAction_point, monsterCo1GeometryUniversalBinary_point,
    monsterCo1GeometryUniversalBinary_point]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
