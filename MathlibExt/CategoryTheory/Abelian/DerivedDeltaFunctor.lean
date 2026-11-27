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
# Derived delta-functors of additive functors

For abelian `C,D`, a natural transformation between additive functors
`C → D` induces a morphism of their derived delta-functors. Projective
resolutions in `C` give the homological left-derived construction;
injective resolutions give the cohomological right-derived construction.
In degree `n`, the maps are the derived natural transformations and
commute with all horseshoe connecting maps. These assignments are
functors on the category of additive functors.
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

/-- Let `C,D` be abelian, with projective resolutions in `C`. For additive `F,G : C → D` and `α : F → G`, the maps `L_nα`
form a morphism of their left-derived homological delta-functors. -/
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

/-- Let `C,D` be abelian, with projective resolutions in `C`. For additive `F,G : C → D` and `α : F → G`, the degree-`n`
component of the induced homological delta-functor morphism is `L_nα`. -/
@[simp]
theorem leftDerivedDeltaFunctorMap_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (n : ℕ) :
    HomologicalDeltaFunctor.Hom.app (NatTrans.leftDerivedDeltaFunctorMap α) n =
      NatTrans.leftDerived α n := rfl

end NatTrans

variable (C D) in
/-- Let `C,D` be abelian, with projective resolutions in `C`. Left derivation defines a functor from additive functors
`C → D` to homological delta-functors, taking `F` to its family
`L_nF` and a transformation to its derived degree maps. -/
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

/-- Let `C,D` be abelian, with projective resolutions in `C`. The image of an additive functor `F : C → D` under this
assignment is its left-derived homological delta-functor. -/
theorem leftDerivedDeltaFunctorFamily_obj (F : C ⥤+ D) :
    (leftDerivedDeltaFunctorFamily C D).obj F = F.obj.leftDerivedDeltaFunctor := rfl

/-- Let `C,D` be abelian, with projective resolutions in `C`. For additive functors `F,G : C → D` and a transformation `α`,
the degree-`n` component of the family map is `L_nα`. -/
theorem leftDerivedDeltaFunctorFamily_map_app {F G : C ⥤+ D} (α : F ⟶ G) (n : ℕ) :
    HomologicalDeltaFunctor.Hom.app ((leftDerivedDeltaFunctorFamily C D).map α) n =
      NatTrans.leftDerived α.hom n := rfl

end Left

section Right

variable [HasInjectiveResolutions C]

namespace NatTrans


end NatTrans

variable (C D) in
/-- Let `C,D` be abelian, with injective resolutions in `C`. Right derivation defines a functor from additive functors
`C → D` to cohomological delta-functors, taking `F` to its family
`R^nF` and a transformation to its derived degree maps. -/
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

/-- Let `C,D` be abelian, with injective resolutions in `C`. The image of an additive functor `F : C → D` under this
assignment is its right-derived cohomological delta-functor. -/
theorem rightDerivedDeltaFunctorFamily_obj (F : C ⥤+ D) :
    (rightDerivedDeltaFunctorFamily C D).obj F = F.obj.rightDerivedDeltaFunctor := rfl

/-- Let `C,D` be abelian, with injective resolutions in `C`. For additive functors `F,G : C → D` and a transformation `α`,
the degree-`n` component of the family map is `R^nα`. -/
theorem rightDerivedDeltaFunctorFamily_map_app {F G : C ⥤+ D} (α : F ⟶ G) (n : ℕ) :
    CohomologicalDeltaFunctor.Hom.app ((rightDerivedDeltaFunctorFamily C D).map α) n =
      NatTrans.rightDerived α.hom n := rfl

end Right
end CategoryTheory

end
