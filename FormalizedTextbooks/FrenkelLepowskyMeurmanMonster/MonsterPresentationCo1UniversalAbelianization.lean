/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalAbelianizationModule

/-! The actual universal group abelianization equals the genuine source line module. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The natural source map factors through the actual commutator quotient. -/
def co1UniversalAbelianizationIntoModule : Abelianization Co1UniversalPresentation →*
    Multiplicative MonsterCo1GeometryUniversalModule :=
  Abelianization.lift co1UniversalIntoModule

/-- The module map in the reverse direction, retaining literal point generators. -/
def co1UniversalModuleIntoAbelianizationGroup : Multiplicative MonsterCo1GeometryUniversalModule →*
    Abelianization Co1UniversalPresentation :=
  co1UniversalModuleIntoAbelianization.toAddMonoidHom.toMultiplicativeLeft

/-- The forward natural group map also respects the induced binary scalar structure. -/
def co1UniversalAbelianizationIntoModuleLinear :
    Additive (Abelianization Co1UniversalPresentation) →ₗ[ZMod 2]
      MonsterCo1GeometryUniversalModule :=
  co1UniversalAbelianizationIntoModule.toAdditiveLeft.toZModLinearMap 2

/-- The forward map preserves each original source point. -/
theorem co1UniversalAbelianizationIntoModuleLinear_point (p : MonsterCo1GeometryPoint) :
    co1UniversalAbelianizationIntoModuleLinear (co1UniversalAbelianPoint p) =
      monsterCo1GeometryUniversalPoint p := by
  change (co1UniversalAbelianizationIntoModule
    (Abelianization.of (PresentedGroup.of p))).toAdd = _
  rw [co1UniversalAbelianizationIntoModule, Abelianization.lift_apply_of,
    co1UniversalIntoModule_point]
  rfl

/-- The two source maps compose to the identity on the genuine universal line module. -/
theorem co1UniversalAbelianization_module_right_inverse :
    Function.RightInverse co1UniversalModuleIntoAbelianization
      co1UniversalAbelianizationIntoModuleLinear := by
  have h : co1UniversalAbelianizationIntoModuleLinear.comp
      co1UniversalModuleIntoAbelianization = LinearMap.id := by
    apply LinearMap.ext_on_range monsterCo1GeometryUniversalPoint_span
    intro p
    simp only [LinearMap.comp_apply, co1UniversalModuleIntoAbelianization_point,
      co1UniversalAbelianizationIntoModuleLinear_point, LinearMap.id_apply]
  exact fun x => LinearMap.congr_fun h x

/-- The same two source maps compose to the identity on the actual commutator quotient. -/
theorem co1UniversalAbelianization_group_left_inverse :
    Function.LeftInverse co1UniversalModuleIntoAbelianizationGroup
      co1UniversalAbelianizationIntoModule := by
  have h : (co1UniversalModuleIntoAbelianizationGroup.comp
      co1UniversalAbelianizationIntoModule).comp Abelianization.of = Abelianization.of := by
    apply PresentedGroup.ext
    intro p
    change co1UniversalModuleIntoAbelianizationGroup
      (co1UniversalAbelianizationIntoModule (Abelianization.of (PresentedGroup.of p))) = _
    rw [co1UniversalAbelianizationIntoModule, Abelianization.lift_apply_of,
      co1UniversalIntoModule_point]
    have hp := co1UniversalModuleIntoAbelianization_point p
    exact congrArg Additive.toMul hp
  have he : co1UniversalModuleIntoAbelianizationGroup.comp
      co1UniversalAbelianizationIntoModule = MonoidHom.id _ :=
    Abelianization.hom_ext _ _ h
  exact fun x => DFunLike.congr_fun he x

/-- The independently presented source group's abelianization is exactly the genuine line module. -/
def co1UniversalAbelianizationEquiv : Abelianization Co1UniversalPresentation ≃*
    Multiplicative MonsterCo1GeometryUniversalModule :=
  MulEquiv.ofBijective co1UniversalAbelianizationIntoModule
    ⟨co1UniversalAbelianization_group_left_inverse.injective, fun x =>
      ⟨co1UniversalModuleIntoAbelianizationGroup x,
        congrArg Multiplicative.ofAdd (co1UniversalAbelianization_module_right_inverse x.toAdd)⟩⟩

/-- The source group-to-line-module map kills exactly its actual commutator subgroup. -/
theorem co1UniversalIntoModule_ker :
    co1UniversalIntoModule.ker = commutator Co1UniversalPresentation := by
  rw [← Abelianization.ker_of]
  ext x
  constructor
  · intro hx
    apply co1UniversalAbelianization_group_left_inverse.injective
    change co1UniversalIntoModule x = co1UniversalAbelianizationIntoModule 1
    rw [map_one]
    exact hx
  · intro hx
    change co1UniversalIntoModule x = 1
    have h := congrArg co1UniversalAbelianizationIntoModule hx
    simpa only [co1UniversalAbelianizationIntoModule, Abelianization.lift_apply_of,
      map_one] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
