/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual norm-eight Conway point action and its full point stabilizers. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCo1GeometryPointSeparation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTwoCoreTransport

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Source II §5.1 points are actual norm-eight binary frame classes. -/
abbrev MonsterCo1GeometryPoint := generatedCo1GeometryPoints

/-- The actual faithful Conway representation restricts to the actual frame-class point set. -/
def monsterCo1GeometryPointAction (g : Co1) (p : MonsterCo1GeometryPoint) :
    MonsterCo1GeometryPoint :=
  ⟨co1BinaryAction g p.val, generatedCo1GeometryPoints_action g p.val p.property⟩

/-- The restricted genuine binary action is a group action on actual Conway points. -/
instance monsterCo1GeometryPointMulAction : MulAction Co1 MonsterCo1GeometryPoint where
  smul := monsterCo1GeometryPointAction
  one_smul p := by
    apply Subtype.ext
    exact congrArg (fun f => f p.val) (co1BinaryAction.map_one)
  mul_smul g h p := by
    apply Subtype.ext
    exact congrArg (fun f => f p.val) (co1BinaryAction.map_mul g h)

/-- There are finitely many actual Conway points. -/
instance monsterCo1GeometryPoint_finite : Finite MonsterCo1GeometryPoint := by
  infer_instance

/-- The actual point set has the independently counted source cardinality. -/
theorem monsterCo1GeometryPoint_card : Nat.card MonsterCo1GeometryPoint = 8292375 :=
  generatedCo1GeometryPoints_card

/-- Every actual Conway point is a nonzero vector in the genuine binary Leech module. -/
theorem monsterCo1GeometryPoint_ne_zero (p : MonsterCo1GeometryPoint) : p.val ≠ 0 :=
  generatedCo1GeometryPoints_ne_zero p.val p.property

/-- The full point stabilizer is taken inside the actual Conway group. -/
def monsterCo1GeometryPointStabilizer (p : MonsterCo1GeometryPoint) : Subgroup Co1 :=
  MulAction.stabilizer Co1 p

/-- Source Q(p) is the intrinsic normal two-core of the full actual point stabilizer. -/
def monsterCo1GeometryPointTwoCore (p : MonsterCo1GeometryPoint) : Subgroup Co1 :=
  (monsterGeometryTwoCore (monsterCo1GeometryPointStabilizer p)).map
    (monsterCo1GeometryPointStabilizer p).subtype

/-- Every member of the actual point two-core fixes its defining point. -/
theorem monsterCo1GeometryPointTwoCore_fixes (p : MonsterCo1GeometryPoint)
    (g : monsterCo1GeometryPointTwoCore p) : g.val • p = p := by
  obtain ⟨h, hh, he⟩ := g.property
  rw [← he]
  exact h.property

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
