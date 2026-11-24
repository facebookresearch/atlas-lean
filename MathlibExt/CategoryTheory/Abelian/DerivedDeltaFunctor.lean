/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Additive
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.DeltaFunctor
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ParameterMap
public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaFunctor
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ParameterMap
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ConnectingNaturality
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Derived δ-functors of additive functors

A natural transformation between additive functors induces a morphism of their left- or
right-derived δ-functors. Its degree maps are derived natural transformations, and naturality
of the horseshoe boundaries gives compatibility with connecting maps. The two constructions
have separate projective- and injective-resolution hypotheses.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

section Left

variable [HasProjectiveResolutions C]

namespace NatTrans

/-- Left-derived degree maps form a morphism of the derived δ-functors. -/
def leftDerivedDeltaFunctorMap {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    F.leftDerivedDeltaFunctor ⟶ G.leftDerivedDeltaFunctor := by
  let α' : AdditiveFunctor.of F ⟶ AdditiveFunctor.of G := ObjectProperty.homMk α
  refine HomologicalDeltaFunctor.homMk C D
    (fun n => (leftDerivedDegreeFunctor C D n).map α') ?_
  intro n S
  change (F.leftDerivedDeltaFunctor.connecting n).app S ≫
      (NatTrans.leftDerived α n).app S.obj.X₁ =
    (NatTrans.leftDerived α (n + 1)).app S.obj.X₃ ≫
      (G.leftDerivedDeltaFunctor.connecting n).app S
  rw [F.leftDerivedDeltaFunctor_connecting_app,
    G.leftDerivedDeltaFunctor_connecting_app]
  exact (LeftDerivedDelta.LDdelta_natural_functor α n S.obj S.property).symm

/-- Every degree of the δ-functor map is the literal left-derived transformation. -/
@[simp]
theorem leftDerivedDeltaFunctorMap_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (n : ℕ) :
    HomologicalDeltaFunctor.Hom.app (NatTrans.leftDerivedDeltaFunctorMap α) n =
      NatTrans.leftDerived α n := rfl

end NatTrans

variable (C D) in
/-- Additive functors form their left-derived homological δ-functor family. -/
def leftDerivedDeltaFunctorFamily : (C ⥤+ D) ⥤ HomologicalDeltaFunctor C D where
  obj F := F.obj.leftDerivedDeltaFunctor
  map α := NatTrans.leftDerivedDeltaFunctorMap α.hom
  map_id F := by
    apply HomologicalDeltaFunctor.hom_ext C D
    intro n
    change (leftDerivedDegreeFunctor C D n).map (𝟙 F) =
      𝟙 ((leftDerivedDegreeFunctor C D n).obj F)
    exact (leftDerivedDegreeFunctor C D n).map_id F
  map_comp α β := by
    apply HomologicalDeltaFunctor.hom_ext C D
    intro n
    change (leftDerivedDegreeFunctor C D n).map (α ≫ β) =
      (leftDerivedDegreeFunctor C D n).map α ≫ (leftDerivedDegreeFunctor C D n).map β
    exact (leftDerivedDegreeFunctor C D n).map_comp α β

/-- The family object is the left-derived factory of the underlying functor. -/
theorem leftDerivedDeltaFunctorFamily_obj (F : C ⥤+ D) :
    (leftDerivedDeltaFunctorFamily C D).obj F = F.obj.leftDerivedDeltaFunctor := rfl

/-- Degree evaluation of a family map recovers the parameter transformation. -/
theorem leftDerivedDeltaFunctorFamily_map_app {F G : C ⥤+ D} (α : F ⟶ G) (n : ℕ) :
    HomologicalDeltaFunctor.Hom.app ((leftDerivedDeltaFunctorFamily C D).map α) n =
      NatTrans.leftDerived α.hom n := rfl

end Left

section Right

variable [HasInjectiveResolutions C]

namespace NatTrans


end NatTrans

variable (C D) in
/-- Additive functors form their right-derived cohomological δ-functor family. -/
def rightDerivedDeltaFunctorFamily : (C ⥤+ D) ⥤ CohomologicalDeltaFunctor C D where
  obj F := F.obj.rightDerivedDeltaFunctor
  map α := NatTrans.rightDerivedDeltaFunctorMap α.hom
  map_id F := by
    apply CohomologicalDeltaFunctor.hom_ext C D
    intro n
    change NatTrans.rightDerived (𝟙 F.obj) n = 𝟙 (F.obj.rightDerived n)
    exact NatTrans.rightDerived_id F.obj n
  map_comp α β := by
    apply CohomologicalDeltaFunctor.hom_ext C D
    intro n
    change NatTrans.rightDerived (α.hom ≫ β.hom) n =
      NatTrans.rightDerived α.hom n ≫ NatTrans.rightDerived β.hom n
    exact NatTrans.rightDerived_comp α.hom β.hom n

/-- The family object is the right-derived factory of the underlying functor. -/
theorem rightDerivedDeltaFunctorFamily_obj (F : C ⥤+ D) :
    (rightDerivedDeltaFunctorFamily C D).obj F = F.obj.rightDerivedDeltaFunctor := rfl

/-- Degree evaluation of a family map recovers the parameter transformation. -/
theorem rightDerivedDeltaFunctorFamily_map_app {F G : C ⥤+ D} (α : F ⟶ G) (n : ℕ) :
    CohomologicalDeltaFunctor.Hom.app ((rightDerivedDeltaFunctorFamily C D).map α) n =
      NatTrans.rightDerived α.hom n := rfl

end Right
end CategoryTheory

end
