/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1UniversalPresentation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryCommutatorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryConnected

/-! Exact genuine-line commutation in the independent nonabelian Conway presentation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original source point images square to identity as products. -/
theorem co1UniversalPoint_mul_self (p : MonsterCo1GeometryPoint) :
    (PresentedGroup.of p : Co1UniversalPresentation) * PresentedGroup.of p = 1 := by
  simpa only [pow_two] using co1UniversalPoint_square p

/-- Images of any two points on an original genuine line commute in the source group. -/
theorem co1UniversalPoint_commute_of_line (p q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryLine p q r) :
    Commute (PresentedGroup.of p : Co1UniversalPresentation) (PresentedGroup.of q) := by
  have hrpq : monsterCo1GeometryLine r p q := monsterCo1GeometryLine_swap_first _ _ _
    (monsterCo1GeometryLine_swap_last _ _ _ h)
  exact co1GeometryCommutator_line_commute (PresentedGroup.of r) (PresentedGroup.of p)
    (PresentedGroup.of q) (co1UniversalPoint_mul_self r) (co1UniversalPoint_mul_self p)
    (co1UniversalPoint_mul_self q) (co1UniversalPoint_line r p q hrpq)

/-- Original collinearity entails genuine commutation without a global abelianity assumption. -/
theorem co1UniversalPoint_commute_of_adjacent (p q : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryAdjacent p q) :
    Commute (PresentedGroup.of p : Co1UniversalPresentation) (PresentedGroup.of q) := by
  obtain ⟨r, hr⟩ := h
  exact co1UniversalPoint_commute_of_line p q r hr

/-- The exact original point images generate the entire independently presented group. -/
theorem co1UniversalPoint_generates :
    Subgroup.closure (Set.range (fun p : MonsterCo1GeometryPoint =>
      (PresentedGroup.of p : Co1UniversalPresentation))) = ⊤ :=
  PresentedGroup.closure_range_of co1UniversalRelations

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
