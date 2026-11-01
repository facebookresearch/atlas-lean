/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine Conway lines retain the actual quadratic and polar geometry. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryInvariantQuadratics
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryLineBinary

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every actual norm-eight frame-class point is singular in the genuine Leech binary module. -/
theorem monsterCo1GeometryPoint_squareQuad (p : MonsterCo1GeometryPoint) :
    squareQuad p.val = 0 := by
  obtain ⟨g, hg⟩ := monsterCo1GeometryPoint_reached p
  rw [← hg]
  change squareQuad (co1BinaryAction g monsterCo1GeometryBasePoint.val) = 0
  rw [co1BinaryAction_squareQuad_invariant, monsterCo1GeometryBasePoint_binary]
  decide +kernel

/-- The third point on every genuine original line is the sum of its first two actual vectors. -/
theorem monsterCo1GeometryLine_third_binary (p q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryLine p q r) : r.val = p.val + q.val := by
  exact (CharTwo.add_eq_zero.mp (monsterCo1GeometryLine_binary p q r h)).symm

/-- Any two points lying on a genuine original line have zero actual polar pairing. -/
theorem monsterCo1GeometryLine_polar (p q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryLine p q r) : co1BinaryPolar p.val q.val = 0 := by
  rw [co1BinaryPolar_quadratic, ← monsterCo1GeometryLine_third_binary p q r h,
    monsterCo1GeometryPoint_squareQuad, monsterCo1GeometryPoint_squareQuad,
    monsterCo1GeometryPoint_squareQuad]
  rfl

/-- Equal polar pairings with a fixed point force zero pairing with the third point of a genuine
line. This retains the source local-line condition without any graph-connectivity claim. -/
theorem monsterCo1GeometryLine_polar_third (s p q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryLine p q r)
    (he : co1BinaryPolar s.val p.val = co1BinaryPolar s.val q.val) :
    co1BinaryPolar s.val r.val = 0 := by
  rw [monsterCo1GeometryLine_third_binary p q r h, map_add, he]
  exact ZModModule.add_self _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
