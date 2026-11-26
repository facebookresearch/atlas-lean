/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Action.DiscreteAbelian
public import MathlibExt.CategoryTheory.Action.Invariants

-- Authors: @toskua, Avocado

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory

namespace CategoryTheory.DiscreteAbelianAction

variable (G : Type u) [Monoid G] [TopologicalSpace G]

/-- The actual trivial discrete continuous action on every original abelian group. -/
def trivialObject (A : AddCommGrpCat.{w}) : DiscreteAbelianAction.{u, w} G := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  letI : DistribMulAction G A :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  letI : ContinuousSMul G A := ⟨continuous_snd⟩
  exact DiscreteAbelianAction.of G A

/-- The construction retains the exact original carrier and integer-module action. -/
theorem trivialObject_carrier (A : AddCommGrpCat.{w}) :
    (underlying (trivialObject G A) : Type w) = A := rfl

/-- Every original coefficient is fixed by the actual left action. -/
theorem trivialObject_smul (A : AddCommGrpCat.{w}) (g : G)
    (x : underlying (trivialObject G A)) : g • x = x := rfl

/-- Every original additive coefficient arrow has the same underlying function. -/
def trivialMap {A B : AddCommGrpCat.{w}} (f : A ⟶ B) :
    trivialObject G A ⟶ trivialObject G B :=
  ofAddHom ⟨f.hom, fun _ _ => rfl⟩

theorem trivialMap_apply {A B : AddCommGrpCat.{w}} (f : A ⟶ B) (x : A) :
    homToAdd (trivialMap G f) x = f.hom x := rfl

/-- The one full trivial-module functor includes arbitrary infinite groups and all maps. -/
def trivialFunctor : AddCommGrpCat.{w} ⥤ DiscreteAbelianAction.{u, w} G where
  obj := trivialObject G
  map := trivialMap G
  map_id A := by
    apply (forget G).map_injective
    ext x
    rfl
  map_comp f g := by
    apply (forget G).map_injective
    ext x
    rfl

theorem trivialFunctor_forget :
    trivialFunctor G ⋙ forget G = 𝟭 AddCommGrpCat.{w} := rfl

end CategoryTheory.DiscreteAbelianAction

end

noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory

namespace CategoryTheory.DiscreteAbelianAction
variable (G : Type u) [Group G] [TopologicalSpace G]

/-- Fixed vectors of the actual trivial module are the SAME original coefficient group. -/
def trivialInvariantsEquiv (A : AddCommGrpCat.{w}) :
    invariantsFunctor.obj (trivialObject G A) ≃+ A where
  toFun x := x.val
  invFun a := ⟨a, fun _ => rfl⟩
  left_inv _x := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem trivialInvariantsEquiv_apply (A : AddCommGrpCat.{w})
    (x : invariantsFunctor.obj (trivialObject G A)) :
    trivialInvariantsEquiv G A x = x.val := rfl

/-- Every additive coefficient map has its literal original fixed-vector value. -/
theorem trivialInvariantsEquiv_naturality {A B : AddCommGrpCat.{w}} (f : A ⟶ B)
    (x : invariantsFunctor.obj (trivialObject G A)) :
    trivialInvariantsEquiv G B ((invariantsFunctor.map (trivialMap G f)) x) =
      f.hom (trivialInvariantsEquiv G A x) := rfl

end CategoryTheory.DiscreteAbelianAction

end

noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory

namespace CategoryTheory.DiscreteAbelianAction
variable (G : Type u) (H : Type v) [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]

/-- Genuine group restriction keeps the same trivial coefficient, including independent group ranks. -/
def trivialRestrictionIso (φ : H →ₜ* G) (A : AddCommGrpCat.{w}) :
    (GaloisUnits.restrictModules φ).obj (trivialObject G A) ≅ trivialObject H A where
  hom := ofAddHom ⟨AddMonoidHom.id A, fun _ _ => rfl⟩
  inv := ofAddHom ⟨AddMonoidHom.id A, fun _ _ => rfl⟩
  hom_inv_id := by
    apply (forget H).map_injective
    ext a
    rfl
  inv_hom_id := by
    apply (forget H).map_injective
    ext a
    rfl

theorem trivialRestrictionIso_hom_apply (φ : H →ₜ* G) (A : AddCommGrpCat.{w}) (a : A) :
    homToAdd (trivialRestrictionIso G H φ A).hom a = a := rfl

theorem trivialRestrictionIso_inv_apply (φ : H →ₜ* G) (A : AddCommGrpCat.{w}) (a : A) :
    homToAdd (trivialRestrictionIso G H φ A).inv a = a := rfl

/-- Every original coefficient function commutes with the literal identity restriction comparison. -/
theorem trivialRestrictionIso_naturality (φ : H →ₜ* G) {A B : AddCommGrpCat.{w}}
    (f : A ⟶ B) :
    (GaloisUnits.restrictModules φ).map (trivialMap G f) ≫
      (trivialRestrictionIso G H φ B).hom =
    (trivialRestrictionIso G H φ A).hom ≫ trivialMap H f := by
  apply (forget H).map_injective
  ext a
  rfl

end CategoryTheory.DiscreteAbelianAction

end
