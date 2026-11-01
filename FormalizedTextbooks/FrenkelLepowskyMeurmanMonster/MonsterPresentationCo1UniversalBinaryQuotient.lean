/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact source abelianization has the actual binary module as its natural quotient. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalAbelianization
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorRecognition
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.TypeTags.Finite

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The proved genuine-line module identification viewed as a multiplicative group equivalence. -/
def co1UniversalModuleBinaryEquiv :
    Multiplicative MonsterCo1GeometryUniversalModule ≃*
      Multiplicative (Fin 24 → ZMod 2) where
  toFun x := Multiplicative.ofAdd (monsterCo1GeometryUniversalBinaryEquiv x.toAdd)
  invFun x := Multiplicative.ofAdd (monsterCo1GeometryUniversalBinaryEquiv.symm x.toAdd)
  left_inv x := congrArg Multiplicative.ofAdd
    (monsterCo1GeometryUniversalBinaryEquiv.symm_apply_apply x.toAdd)
  right_inv x := congrArg Multiplicative.ofAdd
    (monsterCo1GeometryUniversalBinaryEquiv.apply_symm_apply x.toAdd)
  map_mul' x y := congrArg Multiplicative.ofAdd
    (monsterCo1GeometryUniversalBinaryEquiv.map_add x.toAdd y.toAdd)

/-- The original nonabelian source group's abelianization is naturally the actual binary group. -/
def co1UniversalAbelianizationBinaryEquiv :
    Abelianization Co1UniversalPresentation ≃* Multiplicative (Fin 24 → ZMod 2) :=
  co1UniversalAbelianizationEquiv.trans co1UniversalModuleBinaryEquiv

/-- The natural binary quotient of the independent genuine-line nonabelian presentation. -/
def co1UniversalIntoBinary :
    Co1UniversalPresentation →* Multiplicative (Fin 24 → ZMod 2) :=
  co1UniversalModuleBinaryEquiv.toMonoidHom.comp co1UniversalIntoModule

/-- The exact abelianization equivalence retains the original source quotient map. -/
theorem co1UniversalAbelianizationBinaryEquiv_of (x : Co1UniversalPresentation) :
    co1UniversalAbelianizationBinaryEquiv (Abelianization.of x) = co1UniversalIntoBinary x := rfl

/-- Every genuine source point maps to its actual full binary coordinate vector. -/
theorem co1UniversalIntoBinary_point (p : MonsterCo1GeometryPoint) :
    co1UniversalIntoBinary (PresentedGroup.of p) = Multiplicative.ofAdd p.val := by
  change Multiplicative.ofAdd
    (monsterCo1GeometryUniversalBinaryEquiv
      (co1UniversalIntoModule (PresentedGroup.of p)).toAdd) = _
  rw [co1UniversalIntoModule_point]
  exact congrArg Multiplicative.ofAdd (monsterCo1GeometryUniversalBinaryEquiv_point p)

/-- The natural binary source quotient is surjective onto the actual twenty-four coordinates. -/
theorem co1UniversalIntoBinary_surjective : Function.Surjective co1UniversalIntoBinary := by
  intro v
  obtain ⟨a, ha⟩ := co1UniversalAbelianizationBinaryEquiv.surjective v
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective a
  have hx' : Abelianization.of x = a := hx
  rw [← hx', co1UniversalAbelianizationBinaryEquiv_of] at ha
  exact ⟨x, ha⟩

/-- The natural actual-coordinate quotient kills exactly the original source commutator. -/
theorem co1UniversalIntoBinary_ker :
    co1UniversalIntoBinary.ker = commutator Co1UniversalPresentation := by
  exact (MonoidHom.ker_comp_of_injective co1UniversalIntoModule
    co1UniversalModuleBinaryEquiv.toMonoidHom co1UniversalModuleBinaryEquiv.injective).trans
      co1UniversalIntoModule_ker

/-- Finiteness of the actual source commutator implies finiteness of the whole source group. -/
theorem co1UniversalPresentation_finite_of_commutator_finite
    (hcomm : Finite (commutator Co1UniversalPresentation)) : Finite Co1UniversalPresentation := by
  have : Finite co1UniversalIntoBinary.ker := co1UniversalIntoBinary_ker.symm ▸ hcomm
  exact (MonoidHom.finite_iff_finite_ker_range co1UniversalIntoBinary).mpr
    ⟨inferInstance, inferInstance⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
