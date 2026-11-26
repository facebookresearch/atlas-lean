/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-!
# Discrete continuous actions on abelian groups

Let G be a monoid with a topology in universe u. Objects are abelian groups in an independent
universe v with discrete topology and a jointly continuous additive G-action. The morphisms are
precisely G-equivariant additive maps: such maps are integer-linear for the given integer
actions and continuous from the discrete source. Hom addition is pointwise, and forgetting the
action retains the group and its additive maps.

Additive equivariant bijections are isomorphisms. For a group G, every element of an object has
an open stabilizer. When G is a topological group, open stabilizers are equivalent to joint
continuity for an additive action on a discrete group. Restriction along a continuous monoid
homomorphism pulls back the action and preserves the coefficient groups and maps, with identity,
composition and equal-map comparison isomorphisms.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u v

namespace CategoryTheory

/-- Let G be a monoid with a topology in universe u. This category consists of topological integer
modules in v with discrete underlying groups and jointly continuous additive G-actions. Its
objects have no finiteness restriction, and u,v are independent. -/
abbrev DiscreteAbelianAction (G : Type u) [Monoid G] [TopologicalSpace G] :=
  DiscreteContAction (TopModuleCat.{v} ℤ) G

namespace DiscreteAbelianAction

variable {G : Type u} [Monoid G] [TopologicalSpace G]

/-- For a monoid G with a topology and discrete continuous abelian G-actions, equivariant additive
morphisms form abelian groups under pointwise addition. Composition is additive in each
variable, giving the category its preadditive structure. -/
instance instPreadditive : Preadditive (DiscreteAbelianAction.{u, v} G) := by
  letI : Preadditive (TopModuleCat.{v} ℤ) := inferInstance
  letI : Preadditive (Action (TopModuleCat.{v} ℤ) G) := inferInstance
  letI : Preadditive (ContAction (TopModuleCat.{v} ℤ) G) := inferInstance
  exact Preadditive.fullSubcategory _

/-- For a monoid G with a topology and an object X of its discrete abelian action category, this is
the underlying topological ℤ-module. Its carrier and additive group are the given coefficient
group, with its discrete topology. -/
abbrev underlying (X : DiscreteAbelianAction.{u, v} G) : TopModuleCat.{v} ℤ :=
  X.obj.obj.V

instance instDistribMulAction (X : DiscreteAbelianAction.{u, v} G) :
    DistribMulAction G (underlying X) where
  toMulAction := inferInstanceAs (MulAction G
    ((forget₂ (Action (TopModuleCat.{v} ℤ) G) TopCat).obj X.obj.obj))
  smul_zero g := map_zero (X.obj.obj.ρ g).asHom.hom
  smul_add g x y := map_add (X.obj.obj.ρ g).asHom.hom x y

instance instDiscreteTopology (X : DiscreteAbelianAction.{u, v} G) :
    DiscreteTopology (underlying X) := X.property

instance instContinuousSMul (X : DiscreteAbelianAction.{u, v} G) :
    ContinuousSMul G (underlying X) := X.obj.property

/-- Let G be a monoid in universe u with a topology, and let X,Y be discrete continuous G-actions on
abelian groups in coefficient universe v, independent of u. For g∈G and x in the underlying
group of X, g•x equals the value at x of the action endomorphism ρ_X(g). This is the specified
additive action. -/
@[simp] lemma smul_def (X : DiscreteAbelianAction.{u, v} G)
    (g : G) (x : underlying X) :
    g • x = (X.obj.obj.ρ g).asHom.hom x := rfl

/-- Let G be a monoid in universe u with a topology, and let X,Y be discrete continuous G-actions on
abelian groups in coefficient universe v, independent of u. For an object X, the map G×X→X
sending (g,x) to g•x is continuous. Joint continuity is part of its continuous-action structure. -/
lemma continuous_action (X : DiscreteAbelianAction.{u, v} G) :
    Continuous (fun p : G × underlying X => p.1 • p.2) := continuous_smul

/-- For a monoid G with a topology in u, this functor sends discrete continuous abelian actions in v
to their underlying abelian groups. An action morphism is sent to its same additive function,
and the functor is faithful. -/
def forget (G : Type u) [Monoid G] [TopologicalSpace G] :
    DiscreteAbelianAction.{u, v} G ⥤ AddCommGrpCat.{v} :=
  ObjectProperty.ι (ContAction.IsDiscrete (V := TopModuleCat.{v} ℤ) (G := G)) ⋙
    ObjectProperty.ι (Action.isContinuous (TopModuleCat.{v} ℤ) G) ⋙
    Action.forget (TopModuleCat.{v} ℤ) G ⋙
    forget₂ (TopModuleCat.{v} ℤ) (ModuleCat.{v} ℤ) ⋙
    forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}

instance : (forget (G := G)).Faithful where
  map_injective {X Y} f g h := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ConcreteCategory.ext
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun k => k.hom x) h

/-- Let G be a monoid in universe u with a topology, and let X,Y be discrete continuous G-actions on
abelian groups in coefficient universe v, independent of u. The value of the forgetful functor
at X is the abelian group of its underlying topological integer module. The carrier and addition
are retained. -/
@[simp] lemma forget_obj (X : DiscreteAbelianAction.{u, v} G) :
    (forget G).obj X = AddCommGrpCat.of (underlying X) := rfl

/-- Let G be a monoid in universe u with a topology, and let X,Y be discrete continuous G-actions on
abelian groups in coefficient universe v, independent of u. For f:X→Y, this additive map between
the underlying groups is the carrier function of f. It forgets the equivariance and continuity
conditions without changing values. -/
abbrev homToAdd {X Y : DiscreteAbelianAction.{u, v} G} (f : X ⟶ Y) :
    underlying X →+ underlying Y := f.hom.hom.hom.hom.toAddMonoidHom

@[simp] lemma forget_map {X Y : DiscreteAbelianAction.{u, v} G} (f : X ⟶ Y) :
    ((forget G).map f).hom = homToAdd f := rfl

@[simp] lemma homToAdd_id (X : DiscreteAbelianAction.{u, v} G) :
    homToAdd (𝟙 X) = AddMonoidHom.id (underlying X) := rfl

@[simp] lemma homToAdd_comp {X Y Z : DiscreteAbelianAction.{u, v} G}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homToAdd (f ≫ g) = (homToAdd g).comp (homToAdd f) := rfl

/-- Let X,Y be topological integer modules in v and assume only X is discrete. Any additive map
f:X→Y gives a continuous ℤ-linear map. Additivity preserves integer multiplication for the given
module structures, and discreteness of the source gives continuity. -/
def addHomContinuousLinearMap (X Y : TopModuleCat.{v} ℤ) [DiscreteTopology X]
    (f : X →+ Y) : X →L[ℤ] Y where
  toLinearMap :=
    @LinearMap.mk _ _ _ _ _ _ _ _ _ X.toModuleCat.isModule Y.toModuleCat.isModule
      { toFun := f, map_add' := f.map_add }
      (fun n x => by
        convert! AddMonoidHom.map_zsmul f n x <;>
          ext <;> apply int_smul_eq_zsmul)
  cont := continuous_of_discreteTopology

@[simp] lemma addHomContinuousLinearMap_apply
    (X Y : TopModuleCat.{v} ℤ) [DiscreteTopology X] (f : X →+ Y) (x : X) :
    addHomContinuousLinearMap X Y f x = f x := rfl

/-- Let G be a monoid in universe u with a topology, and let X,Y be discrete continuous G-actions on
abelian groups in coefficient universe v, independent of u. This set consists of additive maps f
between the underlying groups satisfying f(g•x)=g•f(x) for every g∈G and x∈X. -/
abbrev EquivariantAddHom (X Y : DiscreteAbelianAction.{u, v} G) :=
  {f : underlying X →+ underlying Y // ∀ (g : G) (x : underlying X), f (g • x) = g • f x}

/-- Let G be a monoid in universe u with a topology, and let X,Y be discrete continuous G-actions on
abelian groups in coefficient universe v, independent of u. Given an additive f:X→Y satisfying
f(g•x)=g•f(x), this construction makes it a categorical morphism. Its integer linearity follows
from additivity and continuity from the discrete source. -/
def ofAddHom {X Y : DiscreteAbelianAction.{u, v} G}
    (f : EquivariantAddHom X Y) : X ⟶ Y :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := TopModuleCat.ofHom (addHomContinuousLinearMap (underlying X) (underlying Y) f.1)
      comm := fun g => by
        ext x
        exact f.2 g x })

@[simp] lemma homToAdd_ofAddHom {X Y : DiscreteAbelianAction.{u, v} G}
    (f : EquivariantAddHom X Y) : homToAdd (ofAddHom f) = f.1 := rfl

/-- Let G be a monoid in universe u with a topology, and let X,Y be discrete continuous G-actions on
abelian groups in coefficient universe v, independent of u. For f:X→Y, g∈G and x∈X, the
underlying additive map satisfies f(g•x)=g•f(x). This is the categorical action-commuting square
evaluated on x. -/
lemma homToAdd_equivariant {X Y : DiscreteAbelianAction.{u, v} G}
    (f : X ⟶ Y) (g : G) (x : underlying X) :
    homToAdd f (g • x) = g • homToAdd f x :=
  congrArg (fun h => h.hom x) (f.hom.hom.comm g)

/-- Let G be a monoid in universe u with a topology, and let X,Y be discrete continuous G-actions on
abelian groups in coefficient universe v, independent of u. There is a bijection between
morphisms X→Y and additive maps of the underlying groups with f(g•x)=g•f(x). The two directions
retain the same carrier functions. -/
def homEquiv (X Y : DiscreteAbelianAction.{u, v} G) :
    (X ⟶ Y) ≃ EquivariantAddHom X Y where
  toFun f := ⟨homToAdd f, homToAdd_equivariant f⟩
  invFun := ofAddHom
  left_inv f := by
    apply (forget G).map_injective
    ext x
    rfl
  right_inv f := by
    apply Subtype.ext
    rfl

section Objects

variable (G) (M : Type v) [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

/-- Let G be a monoid and M a discrete abelian group with a distributive G-action. Its maps x↦g•x
are continuous integer-linear endomorphisms and define an action object on its topological
ℤ-module. The monoid and coefficient universes are independent. -/
def underlyingAction : Action (TopModuleCat.{v} ℤ) G where
  V := TopModuleCat.of ℤ M
  ρ :=
    { toFun g := .of (TopModuleCat.ofHom
        (addHomContinuousLinearMap (TopModuleCat.of ℤ M) (TopModuleCat.of ℤ M)
          { toFun := fun x => g • x
            map_zero' := smul_zero g
            map_add' := smul_add g }))
      map_one' := by
        ext x
        exact one_smul G x
      map_mul' g h := by
        ext x
        exact mul_smul g h x }

/-- Let G be a monoid with a topology in u and M a discrete abelian group in v with an additive
G-action. If the action is jointly continuous, M with those maps is an object of the discrete
continuous abelian action category. -/
def of : DiscreteAbelianAction.{u, v} G :=
  ⟨⟨underlyingAction G M, ‹ContinuousSMul G M›⟩, ‹DiscreteTopology M›⟩

/-- For a monoid G with a topology and a discrete abelian group M with jointly continuous additive
G-action, the underlying carrier of the bundled action object is M. -/
@[simp] lemma of_carrier : (underlying (of G M) : Type v) = M := rfl

-- simpNF only sees `of_carrier` in the coercion's type
/-- For a discrete abelian group M with a jointly continuous additive action of a monoid G, the
bundled object's value g•x is the given action value on M. -/
@[simp, nolint simpNF]
lemma of_smul (g : G) (x : M) :
    ((of G M).obj.obj.ρ g).asHom.hom x = (g • x : M) := rfl

end Objects

/-- Let G be a monoid in universe u with a topology, and let X,Y be discrete continuous G-actions on
abelian groups in coefficient universe v, independent of u. For a morphism f:X→Y whose
underlying additive function is bijective, this is an isomorphism X≅Y with forward map f. Its
inverse additive equivalence is equivariant, and its discrete source makes it continuous. -/
def isoOfBijective {X Y : DiscreteAbelianAction.{u, v} G}
    (f : X ⟶ Y) (h : Function.Bijective (homToAdd f)) : X ≅ Y := by
  let e : underlying X ≃+ underlying Y :=
    { __ := homToAdd f, __ := Equiv.ofBijective (homToAdd f) h }
  let inverse : EquivariantAddHom Y X := ⟨e.symm.toAddMonoidHom, by
    intro g y
    apply e.injective
    change e (e.symm (g • y)) = e (g • e.symm y)
    rw [e.apply_symm_apply]
    change g • y = homToAdd f (g • e.symm y)
    rw [homToAdd_equivariant]
    exact congrArg (fun z => g • z) (e.apply_symm_apply y).symm⟩
  exact
    { hom := f
      inv := ofAddHom inverse
      hom_inv_id := by
        apply (forget G).map_injective
        ext x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply (forget G).map_injective
        ext y
        exact e.apply_symm_apply y }

@[simp] lemma isoOfBijective_hom {X Y : DiscreteAbelianAction.{u, v} G}
    (f : X ⟶ Y) (h : Function.Bijective (homToAdd f)) :
    (isoOfBijective f h).hom = f := rfl

/-- Let G be a monoid in universe u with a topology, and let X,Y be discrete continuous G-actions on
abelian groups in coefficient universe v, independent of u. If f:X→Y is a morphism and its
underlying additive map is bijective, then f is an isomorphism in the discrete action category. -/
lemma isIso_of_bijective {X Y : DiscreteAbelianAction.{u, v} G}
    (f : X ⟶ Y) (h : Function.Bijective (homToAdd f)) : IsIso f :=
  (isoOfBijective f h).isIso_hom

/-- For a discrete continuous abelian G-action X, bundling its underlying discrete coefficient group
and action again gives an object canonically isomorphic to X. The forward and inverse additive
maps are identities. -/
def ofUnderlyingIso (X : DiscreteAbelianAction.{u, v} G) :
    of G (underlying X) ≅ X where
  hom := ofAddHom ⟨AddMonoidHom.id _, fun _ _ => rfl⟩
  inv := ofAddHom ⟨AddMonoidHom.id _, fun _ _ => rfl⟩
  hom_inv_id := by
    apply (forget G).map_injective
    ext x
    rfl
  inv_hom_id := by
    apply (forget G).map_injective
    ext x
    rfl

end DiscreteAbelianAction

namespace DiscreteAbelianAction

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Let G be a group with a topology, X a jointly continuous additive action on a discrete abelian
group and x∈X. The stabilizer subgroup {g:g•x=x} is open in G, as the inverse image of the open
singleton {x} under its orbit map. -/
lemma stabilizer_isOpen (X : DiscreteAbelianAction.{u, v} G) (x : underlying X) :
    IsOpen (MulAction.stabilizer G x : Set G) := _root_.stabilizer_isOpen G x

variable [IsTopologicalGroup G]

/-- Let G be a topological group and M a discrete abelian group with a distributive G-action. Joint
continuity of G×M→M is equivalent to openness of the stabilizer subgroup of each x∈M. The monoid
and coefficient sizes need no equality or finiteness condition. -/
lemma continuousSMul_iff_open_stabilizers (M : Type v) [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M] :
    ContinuousSMul G M ↔ ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G) :=
  continuousSMul_iff_stabilizer_isOpen

end DiscreteAbelianAction
end CategoryTheory

universe w a

namespace GaloisUnits

section ModuleRestriction
variable {G : Type u} {H : Type v} [Monoid G] [Monoid H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- For monoids G,H with topologies in independent universes and a continuous monoid homomorphism
φ:H→G, restriction sends a discrete abelian G-action M to the H-action h•x=φ(h)•x. Its
coefficient group may have a third independent universe, and all additive morphisms are
retained. -/
def restrictModules (φ : H →ₜ* G) :
    DiscreteAbelianAction.{u, w} G ⥤ DiscreteAbelianAction.{v, w} H :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ ContAction.res (TopModuleCat.{w} ℤ) φ)
    (fun X => X.property)

@[simp] theorem restrictModules_underlying (φ : H →ₜ* G)
    (M : DiscreteAbelianAction.{u, w} G) :
    DiscreteAbelianAction.underlying ((restrictModules φ).obj M) =
      DiscreteAbelianAction.underlying M := rfl

@[simp, nolint simpNF] -- simpNF only sees `restrictModules_underlying` in the coercion's type
theorem restrictModules_action (φ : H →ₜ* G)
    (M : DiscreteAbelianAction.{u, w} G) (h : H)
    (x : DiscreteAbelianAction.underlying M) :
    (((restrictModules φ).obj M).obj.obj.ρ h).asHom.hom x =
      (M.obj.obj.ρ (φ h)).asHom.hom x := rfl

@[simp] theorem restrictModules_map (φ : H →ₜ* G)
    {M N : DiscreteAbelianAction.{u, w} G} (f : M ⟶ N) :
    DiscreteAbelianAction.homToAdd ((restrictModules φ).map f) =
      DiscreteAbelianAction.homToAdd f := rfl
end ModuleRestriction

section RestrictionComparisons
variable {G : Type u} {H : Type v} {J : Type a}
  [Monoid G] [Monoid H] [Monoid J]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace J]

/-- For a monoid G with a topology, pullback along id_G is naturally isomorphic to the identity
functor on discrete continuous abelian G-actions. Each comparison component has the identity
additive map on the coefficient group. -/
def restrictModulesId : restrictModules (ContinuousMonoidHom.id G) ≅
    𝟭 (DiscreteAbelianAction.{u, w} G) :=
  NatIso.ofComponents fun M => ObjectProperty.isoMk _
    (ObjectProperty.isoMk _ ((Action.resId (TopModuleCat.{w} ℤ)).app M.obj.obj))

/-- For continuous monoid homomorphisms φ:H→G and ψ:J→H, restriction along φ∘ψ is naturally
isomorphic to restriction along φ followed by ψ. The comparison acts as identity on each
coefficient group, with independent group and coefficient universes. -/
def restrictModulesComp (φ : H →ₜ* G) (ψ : J →ₜ* H) :
    restrictModules (φ.comp ψ) ≅ restrictModules φ ⋙ restrictModules ψ :=
  NatIso.ofComponents fun M => ObjectProperty.isoMk _
    ((ContAction.resComp (TopModuleCat.{w} ℤ) ψ φ).app M.obj)

/-- For continuous monoid homomorphisms φ,φ′:H→G with φ=φ′, their restriction functors on discrete
continuous abelian actions are naturally isomorphic. The coefficient groups and the additive
component maps are identified by identity. -/
def restrictModulesCongr (φ φ' : H →ₜ* G) (h : φ = φ') :
    restrictModules.{u, v, w} φ ≅ restrictModules φ' :=
  NatIso.ofComponents fun M => ObjectProperty.isoMk _
    ((ContAction.resCongr (TopModuleCat.{w} ℤ) φ φ' h).app M.obj)

@[simp] theorem restrictModulesId_hom (M : DiscreteAbelianAction.{u, w} G) :
    DiscreteAbelianAction.homToAdd (restrictModulesId.hom.app M) =
      AddMonoidHom.id (DiscreteAbelianAction.underlying M) := rfl

@[simp] theorem restrictModulesComp_hom (φ : H →ₜ* G) (ψ : J →ₜ* H)
    (M : DiscreteAbelianAction.{u, w} G) :
    DiscreteAbelianAction.homToAdd ((restrictModulesComp φ ψ).hom.app M) =
      AddMonoidHom.id (DiscreteAbelianAction.underlying M) := rfl

@[simp] theorem restrictModulesCongr_hom (φ φ' : H →ₜ* G) (h : φ = φ')
    (M : DiscreteAbelianAction.{u, w} G) :
    DiscreteAbelianAction.homToAdd ((restrictModulesCongr φ φ' h).hom.app M) =
      AddMonoidHom.id (DiscreteAbelianAction.underlying M) := rfl
end RestrictionComparisons

end GaloisUnits
