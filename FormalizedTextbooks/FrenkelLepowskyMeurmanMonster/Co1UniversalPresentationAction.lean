/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1UniversalPresentation

/-! The actual Conway group transports the original nonabelian universal presentation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual Conway transport preserves every original point-square and genuine line relation. -/
theorem co1UniversalRelations_action_valid (g : Co1)
    (w : FreeGroup MonsterCo1GeometryPoint) (hw : w ∈ co1UniversalRelations) :
    FreeGroup.lift (fun p => (PresentedGroup.of (g • p) : Co1UniversalPresentation)) w = 1 := by
  rcases hw with ⟨p, rfl⟩ | ⟨p, q, r, h, rfl⟩
  · simpa only [map_pow, FreeGroup.lift_apply_of] using co1UniversalPoint_square (g • p)
  · simpa only [map_mul, FreeGroup.lift_apply_of] using
      co1UniversalPoint_line (g • p) (g • q) (g • r) (monsterCo1GeometryLine_smul g p q r h)

/-- Each actual Conway element induces a literal source-presentation endomorphism. -/
def co1UniversalActionEnd (g : Co1) : Co1UniversalPresentation →* Co1UniversalPresentation :=
  PresentedGroup.toGroup (co1UniversalRelations_action_valid g)

/-- The actual endomorphism has the original point action on every source generator. -/
theorem co1UniversalActionEnd_point (g : Co1) (p : MonsterCo1GeometryPoint) :
    co1UniversalActionEnd g (PresentedGroup.of p) = PresentedGroup.of (g • p) :=
  PresentedGroup.toGroup.of (co1UniversalRelations_action_valid g)

/-- The identity Conway element acts identically on the whole source group. -/
theorem co1UniversalActionEnd_one : co1UniversalActionEnd (1 : Co1) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro p
  simp only [co1UniversalActionEnd_point, one_smul, MonoidHom.id_apply]

/-- Composition on the whole source group respects the actual Conway multiplication. -/
theorem co1UniversalActionEnd_mul (g h : Co1) :
    co1UniversalActionEnd (g * h) = (co1UniversalActionEnd g).comp (co1UniversalActionEnd h) := by
  apply PresentedGroup.ext
  intro p
  simp only [MonoidHom.comp_apply, co1UniversalActionEnd_point, mul_smul]

/-- The actual inverse Conway element supplies the inverse of each full source endomorphism. -/
theorem co1UniversalActionEnd_inverse (g : Co1) :
    Function.LeftInverse (co1UniversalActionEnd g⁻¹) (co1UniversalActionEnd g) := by
  have h : (co1UniversalActionEnd g⁻¹).comp (co1UniversalActionEnd g) = MonoidHom.id _ := by
    rw [← co1UniversalActionEnd_mul, inv_mul_cancel, co1UniversalActionEnd_one]
  exact fun x => DFunLike.congr_fun h x

/-- The actual Conway element acts by an automorphism of the independent source group. -/
def co1UniversalActionAut (g : Co1) : MulAut Co1UniversalPresentation where
  toFun := co1UniversalActionEnd g
  invFun := co1UniversalActionEnd g⁻¹
  left_inv := co1UniversalActionEnd_inverse g
  right_inv := by
    intro x
    have h := co1UniversalActionEnd_inverse g⁻¹ x
    rw [inv_inv] at h
    exact h
  map_mul' := (co1UniversalActionEnd g).map_mul

/-- Source universality is admissible for the entire actual Conway group. -/
def co1UniversalRepresentation : Co1 →* MulAut Co1UniversalPresentation where
  toFun := co1UniversalActionAut
  map_one' := by
    apply MulEquiv.ext
    intro x
    change co1UniversalActionEnd 1 x = x
    exact DFunLike.congr_fun co1UniversalActionEnd_one x
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    change co1UniversalActionEnd (g * h) x = co1UniversalActionEnd g (co1UniversalActionEnd h x)
    exact DFunLike.congr_fun (co1UniversalActionEnd_mul g h) x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
