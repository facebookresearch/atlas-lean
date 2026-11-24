/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# The forgetful functor on additive commutative groups

Corepresentability of the forgetful functor and categorical properties of the
lifted integer generator.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

/-- The `AddCommGrpCat`-valued coyoneda functor at `ULift ℤ` is naturally
isomorphic to the identity functor. -/
noncomputable def AddCommGrpCat.coyonedaObjIsoId :
    AddCommGrpCat.coyoneda.obj (Opposite.op (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      CategoryTheory.Functor.id AddCommGrpCat.{u} :=
  NatIso.ofComponents
    (fun G =>
      (AddCommGrpCat.homAddEquiv.symm.trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv G)).toAddCommGrpIso)
    (fun {X Y} f => by ext x; rfl)

/-- The preadditive coyoneda functor at `ULift ℤ` is naturally isomorphic
to the identity functor. -/
noncomputable def AddCommGrpCat.preadditiveCoyonedaObjIsoId :
    CategoryTheory.preadditiveCoyoneda.obj
        (Opposite.op (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      CategoryTheory.Functor.id AddCommGrpCat.{u} :=
  AddCommGrpCat.preadditiveCoyonedaIso.app
      (Opposite.op (AddCommGrpCat.of (ULift.{u} ℤ))) ≪≫
    AddCommGrpCat.coyonedaObjIsoId

namespace AddCommGrpCat

/-- The lifted integers are projective in `AddCommGrpCat`. -/
instance projective_uliftInt : Projective (of (ULift.{u} ℤ)) := by
  have hP : Projective (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
    exact ModuleCat.projective_of_categoryTheory_projective _
  exact ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.map_projective_iff
    (ModuleCat.of ℤ (ULift.{u} ℤ))).mpr hP

/-- The lifted integers form a separator in `AddCommGrpCat`. -/
theorem isSeparator_uliftInt : IsSeparator (of (ULift.{u} ℤ)) := by
  intro A B f g h
  simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq', ULift.forall]
  intro x
  specialize h (ofHom
    (AddMonoidHom.mk' (fun y => y • x) fun y z => by simp only [add_smul])) 1
  aesop

universe w

/-- The lifted integers are finitely presentable with respect to filtered
diagrams whose universe is no larger than the ambient coefficient universe. -/
noncomputable instance isFinitelyPresentable_uliftInt [UnivLE.{w, u}] :
    IsFinitelyPresentable.{w} (of (ULift.{u} ℤ)) := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  let _ : PreservesFilteredColimitsOfSize.{w, w} (forget AddCommGrpCat.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE (forget AddCommGrpCat.{u})
  constructor
  intro J
  exact preservesColimitsOfShape_of_natIso (J := J)
    coyonedaObjIsoForget.symm
end AddCommGrpCat

end
