/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The independent universal nonabelian representation of the actual source geometry. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryPoints
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original universal-representation relations: point involutions and line products.
See Ivanov–Shpectorov II §2.1, §7.1 and Ivanov I Lemma 8.6.2. -/
def monsterGeometryRelations : Set (FreeGroup MonsterGeometryPoint) :=
  {w | (∃ p, w = FreeGroup.of p ^ 2) ∨
    ∃ p q r, monsterGeometryLine p q r ∧
      w = FreeGroup.of p * FreeGroup.of q * FreeGroup.of r}

/-- The independently presented universal representation of the actual Q-incidence geometry. -/
abbrev MonsterGeometryPresentation := PresentedGroup monsterGeometryRelations

/-- All original geometry relations hold in the actual generated group. -/
theorem monsterGeometryRelations_valid (w : FreeGroup MonsterGeometryPoint)
    (hw : w ∈ monsterGeometryRelations) :
    FreeGroup.lift (fun p : MonsterGeometryPoint => p.val) w = 1 := by
  rcases hw with ⟨p, rfl⟩ | ⟨p, q, r, hline, rfl⟩
  · simpa only [map_pow, FreeGroup.lift_apply_of] using monsterGeometryPoint_square p
  · simpa only [map_mul, FreeGroup.lift_apply_of] using hline.2.2.2.1

/-- The canonical map sends each independent geometry generator to its actual involution. -/
noncomputable def monsterGeometryIntoGenerated : MonsterGeometryPresentation →* G :=
  PresentedGroup.toGroup monsterGeometryRelations_valid

/-- Literal generator values for the source geometry representation. -/
@[simp] theorem monsterGeometryIntoGenerated_generator (p : MonsterGeometryPoint) :
    monsterGeometryIntoGenerated (PresentedGroup.of p) = p.val :=
  PresentedGroup.toGroup.of monsterGeometryRelations_valid

/-- Distinct actual geometry points remain distinct in the independent presentation. -/
theorem monsterGeometryPresentation_generator_injective :
    Function.Injective (fun p : MonsterGeometryPoint =>
      (PresentedGroup.of p : MonsterGeometryPresentation)) := by
  intro p q h
  apply Subtype.ext
  have he := congrArg monsterGeometryIntoGenerated h
  simpa only [monsterGeometryIntoGenerated_generator] using he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
