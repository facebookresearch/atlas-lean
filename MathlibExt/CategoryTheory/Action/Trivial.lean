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

/-!
# Trivial discrete abelian actions and their fixed points

For a monoid G with a topology in universe u, every abelian group A in universe w has a trivial
discrete continuous action g•a=a. Additive coefficient maps define a functor from abelian groups
to these actions, and forgetting the action recovers the coefficient group and its morphisms.

When G is a group, all coefficients of a trivial action are fixed, giving a natural additive
equivalence (triv_G A)^G≃A. For a continuous homomorphism φ:H→G between groups in independent
universes, restriction of triv_G A is isomorphic to triv_H A by identity coefficient maps. These
isomorphisms are natural in A.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory

namespace CategoryTheory.DiscreteAbelianAction

variable (G : Type u) [Monoid G] [TopologicalSpace G]

/-- Let G be a monoid with a topology in universe u and let abelian coefficient groups lie in
universe w, independently. For A, the trivial coefficient action triv_G A has the same abelian
group with the discrete topology and action g•a=a. The action map G×A→A is the second
projection, hence continuous. -/
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

/-- Let G be a monoid with a topology in universe u and let abelian coefficient groups lie in
universe w, independently. For an abelian group A, the underlying coefficient carrier of triv_G
A equals A as a type in universe w. Its abelian-group operations and integer module structure
are the coefficient ones, with the discrete topology. -/
theorem trivialObject_carrier (A : AddCommGrpCat.{w}) :
    (underlying (trivialObject G A) : Type w) = A := rfl

/-- Let G be a monoid with a topology in universe u and let abelian coefficient groups lie in
universe w, independently. For A, g∈G, and a in the underlying group of triv_G A, the action
satisfies g•a=a. This holds for every coefficient, without any finiteness requirement on G or A. -/
theorem trivialObject_smul (A : AddCommGrpCat.{w}) (g : G)
    (x : underlying (trivialObject G A)) : g • x = x := rfl

/-- Let G be a monoid with a topology in universe u and let abelian coefficient groups lie in
universe w, independently. For an additive morphism f:A→B, the induced action morphism triv_G
A→triv_G B has underlying function a↦f(a). It is equivariant because both actions are trivial,
and continuous because the coefficient groups are discrete. -/
def trivialMap {A B : AddCommGrpCat.{w}} (f : A ⟶ B) :
    trivialObject G A ⟶ trivialObject G B :=
  ofAddHom ⟨f.hom, fun _ _ => rfl⟩

theorem trivialMap_apply {A B : AddCommGrpCat.{w}} (f : A ⟶ B) (x : A) :
    homToAdd (trivialMap G f) x = f.hom x := rfl

/-- Let G be a monoid with a topology in universe u and let abelian coefficient groups lie in
universe w, independently. The functor triv_G sends A to its trivial discrete continuous action
and f:A→B to the action morphism with the same additive function. If U forgets the action, then
U∘triv_G is the identity functor on abelian groups in universe w. -/
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

/-- Let G be a group with a topology in universe u and let abelian coefficient groups lie in
universe w, independently. For A, the additive equivalence (triv_G A)^G≃A sends a fixed
coefficient to its underlying element. Its inverse sends a∈A to the fixed vector represented by
a, since every g∈G acts as the identity. -/
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

/-- Let G be a group with a topology in universe u and let abelian coefficient groups lie in
universe w, independently. Let e_A:(triv_G A)^G≃A be the fixed-point equivalence. For an
additive coefficient map f:A→B and fixed x∈triv_G A, e_B(F(triv_G f)(x))=f(e_A(x)), where F
takes fixed points. Both sides are the same coefficient value in B. -/
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

/-- Let G and H be groups with topologies in universes u and v, φ:H→G a continuous homomorphism, and
A an abelian group in universe w. The restriction of triv_G A along φ is isomorphic to triv_H A.
Both the forward and inverse action morphisms are the identity on A. -/
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

/-- Let G,H be groups with topologies in universes u,v and φ:H→G a continuous homomorphism, with
abelian coefficient groups in universe w. Write e_A:Res_φ(triv_G A)≅triv_H A for the identity
coefficient comparison. For f:A→B, Res_φ(triv_G f)≫e_B.hom=e_A.hom≫triv_H f. -/
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
