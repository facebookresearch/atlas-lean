/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryUniversalBinary
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.Abelianization.Defs

/-! The genuine Conway geometry's universal nonabelian representation,
with original line relations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Source II sections2.1 and5.4: actual point involutions and all genuine line products. -/
def co1UniversalRelations : Set (FreeGroup MonsterCo1GeometryPoint) :=
  {w | (∃ p, w = FreeGroup.of p ^ 2) ∨
    ∃ p q r, monsterCo1GeometryLine p q r ∧
      w = FreeGroup.of p * FreeGroup.of q * FreeGroup.of r}

/-- The source universal group uses exactly the genuine Conway geometry.
Commutativity is not assumed. -/
abbrev Co1UniversalPresentation := PresentedGroup co1UniversalRelations

/-- Original point generators are involutions in the independently presented source group. -/
theorem co1UniversalPoint_square (p : MonsterCo1GeometryPoint) :
    (PresentedGroup.of p : Co1UniversalPresentation) ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := co1UniversalRelations) (x := FreeGroup.of p ^ 2)
    (Or.inl ⟨p, rfl⟩)
  simpa only [map_pow, PresentedGroup.of] using h

/-- Every genuine original line has its defining product equal to one. -/
theorem co1UniversalPoint_line (p q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryLine p q r) :
    (PresentedGroup.of p : Co1UniversalPresentation) * PresentedGroup.of q *
      PresentedGroup.of r = 1 := by
  have he := PresentedGroup.one_of_mem (rels := co1UniversalRelations)
    (x := FreeGroup.of p * FreeGroup.of q * FreeGroup.of r) (Or.inr ⟨p, q, r, h, rfl⟩)
  simpa only [map_mul, PresentedGroup.of] using he

/-- All original nonabelian source relations hold in the independently presented binary module. -/
theorem co1UniversalRelations_module_valid (w : FreeGroup MonsterCo1GeometryPoint)
    (hw : w ∈ co1UniversalRelations) :
    FreeGroup.lift (fun p => Multiplicative.ofAdd (monsterCo1GeometryUniversalPoint p)) w = 1 := by
  rcases hw with ⟨p, rfl⟩ | ⟨p, q, r, h, rfl⟩
  · simp only [pow_two, map_mul, FreeGroup.lift_apply_of]
    change monsterCo1GeometryUniversalPoint p + monsterCo1GeometryUniversalPoint p = 0
    exact ZModModule.add_self _
  · simp only [map_mul, FreeGroup.lift_apply_of]
    change monsterCo1GeometryUniversalPoint p + monsterCo1GeometryUniversalPoint q +
      monsterCo1GeometryUniversalPoint r = 0
    exact monsterCo1GeometryUniversalPoint_line p q r h

/-- The natural map retains the exact source point generator in the independent binary module. -/
def co1UniversalIntoModule :
    Co1UniversalPresentation →* Multiplicative MonsterCo1GeometryUniversalModule :=
  PresentedGroup.toGroup co1UniversalRelations_module_valid

/-- Literal point values under the natural source group-to-module map. -/
theorem co1UniversalIntoModule_point (p : MonsterCo1GeometryPoint) :
    co1UniversalIntoModule (PresentedGroup.of p) =
      Multiplicative.ofAdd (monsterCo1GeometryUniversalPoint p) :=
  PresentedGroup.toGroup.of co1UniversalRelations_module_valid

/-- Distinct genuine geometry points remain distinct in the independent nonabelian presentation. -/
theorem co1UniversalPoint_injective :
    Function.Injective (fun p : MonsterCo1GeometryPoint =>
      (PresentedGroup.of p : Co1UniversalPresentation)) := by
  intro p q h
  apply Subtype.ext
  have he := congrArg (fun x : Co1UniversalPresentation =>
    monsterCo1GeometryUniversalBinary (co1UniversalIntoModule x).toAdd) h
  rw [co1UniversalIntoModule_point, co1UniversalIntoModule_point] at he
  change monsterCo1GeometryUniversalBinary (monsterCo1GeometryUniversalPoint p) =
    monsterCo1GeometryUniversalBinary (monsterCo1GeometryUniversalPoint q) at he
  simpa only [monsterCo1GeometryUniversalBinary_point] using he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
