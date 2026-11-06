/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1UniversalPresentationAction

/-! The actual Conway action on the independent source universal group is faithful. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Fixing every genuine source point forces equality in the actual Conway group. -/
theorem co1GeometryPointAction_eq_of_forall (g h : Co1)
    (hp : ∀ p : MonsterCo1GeometryPoint, g • p = h • p) : g = h := by
  apply co1BinaryAction_injective
  apply LinearEquiv.toLinearMap_injective
  have hs : Submodule.span (ZMod 2)
      (Set.range (fun p : MonsterCo1GeometryPoint => p.val)) = ⊤ := by
    have hr : Set.range (fun p : MonsterCo1GeometryPoint => p.val) =
        generatedCo1GeometryPoints := by
      ext v
      constructor
      · rintro ⟨p, rfl⟩
        exact p.property
      · intro hv
        exact ⟨⟨v, hv⟩, rfl⟩
    rw [hr]
    exact generatedCo1GeometryPointSpan_eq_top
  apply LinearMap.ext_on_range hs
  intro p
  exact congrArg Subtype.val (hp p)

/-- Original point-generator faithfulness gives an injective actual Conway automorphism action. -/
theorem co1UniversalRepresentation_injective : Function.Injective co1UniversalRepresentation := by
  intro g h he
  apply co1GeometryPointAction_eq_of_forall g h
  intro p
  apply co1UniversalPoint_injective
  have hp := congrArg (fun a : MulAut Co1UniversalPresentation => a (PresentedGroup.of p)) he
  change co1UniversalActionEnd g (PresentedGroup.of p) =
    co1UniversalActionEnd h (PresentedGroup.of p) at hp
  simpa only [co1UniversalActionEnd_point] using hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
