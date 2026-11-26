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

/-! # All discrete continuous abelian actions

The objects are the stock discrete continuous actions on topological integer
modules. Every equivariant additive map is an arrow, including between objects
with arbitrary stored integer-module structures. The constructions below retain
the original groups, action functions, identities and compositions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u v

namespace CategoryTheory

/-- All discrete continuous abelian actions, without a finiteness restriction. -/
abbrev DiscreteAbelianAction (G : Type u) [Monoid G] [TopologicalSpace G] :=
  DiscreteContAction (TopModuleCat.{v} ℤ) G

namespace DiscreteAbelianAction

variable {G : Type u} [Monoid G] [TopologicalSpace G]

/-- The stock Hom addition on every discrete continuous abelian action category. -/
instance instPreadditive : Preadditive (DiscreteAbelianAction.{u, v} G) := by
  letI : Preadditive (TopModuleCat.{v} ℤ) := inferInstance
  letI : Preadditive (Action (TopModuleCat.{v} ℤ) G) := inferInstance
  letI : Preadditive (ContAction (TopModuleCat.{v} ℤ) G) := inferInstance
  exact Preadditive.fullSubcategory _

/-- The same underlying topological integer module. -/
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

/-- The stock action is the original endomorphism evaluated on the same element. -/
@[simp] lemma smul_def (X : DiscreteAbelianAction.{u, v} G)
    (g : G) (x : underlying X) :
    g • x = (X.obj.obj.ρ g).asHom.hom x := rfl

/-- Joint continuity, on the actual underlying group and action. -/
lemma continuous_action (X : DiscreteAbelianAction.{u, v} G) :
    Continuous (fun p : G × underlying X => p.1 • p.2) := continuous_smul

/-- Forget only the extra structures, retaining the original abelian group. -/
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

/-- The underlying group has the same carrier and addition. -/
@[simp] lemma forget_obj (X : DiscreteAbelianAction.{u, v} G) :
    (forget G).obj X = AddCommGrpCat.of (underlying X) := rfl

/-- The original additive function underlying an arrow. -/
abbrev homToAdd {X Y : DiscreteAbelianAction.{u, v} G} (f : X ⟶ Y) :
    underlying X →+ underlying Y := f.hom.hom.hom.hom.toAddMonoidHom

@[simp] lemma forget_map {X Y : DiscreteAbelianAction.{u, v} G} (f : X ⟶ Y) :
    ((forget G).map f).hom = homToAdd f := rfl

@[simp] lemma homToAdd_id (X : DiscreteAbelianAction.{u, v} G) :
    homToAdd (𝟙 X) = AddMonoidHom.id (underlying X) := rfl

@[simp] lemma homToAdd_comp {X Y Z : DiscreteAbelianAction.{u, v} G}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homToAdd (f ≫ g) = (homToAdd g).comp (homToAdd f) := rfl

/-- Every additive map is integer-linear for the exact stored module structures.
Continuity follows from the discrete source. -/
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

/-- All original equivariant additive maps between two objects. -/
abbrev EquivariantAddHom (X Y : DiscreteAbelianAction.{u, v} G) :=
  {f : underlying X →+ underlying Y // ∀ (g : G) (x : underlying X), f (g • x) = g • f x}

/-- Package any original equivariant additive map as an arrow. -/
def ofAddHom {X Y : DiscreteAbelianAction.{u, v} G}
    (f : EquivariantAddHom X Y) : X ⟶ Y :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := TopModuleCat.ofHom (addHomContinuousLinearMap (underlying X) (underlying Y) f.1)
      comm := fun g => by
        ext x
        exact f.2 g x })

@[simp] lemma homToAdd_ofAddHom {X Y : DiscreteAbelianAction.{u, v} G}
    (f : EquivariantAddHom X Y) : homToAdd (ofAddHom f) = f.1 := rfl

/-- The arrow condition is exactly the original elementwise equivariance law. -/
lemma homToAdd_equivariant {X Y : DiscreteAbelianAction.{u, v} G}
    (f : X ⟶ Y) (g : G) (x : underlying X) :
    homToAdd f (g • x) = g • homToAdd f x :=
  congrArg (fun h => h.hom x) (f.hom.hom.comm g)

/-- Arrows are exactly all equivariant additive maps, with the same functions. -/
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

/-- The original unbundled action as a stock action on its discrete group. -/
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

/-- Every discrete continuous abelian action is an object; no size or finiteness
condition is imposed on its group or its stabilizers collectively. -/
def of : DiscreteAbelianAction.{u, v} G :=
  ⟨⟨underlyingAction G M, ‹ContinuousSMul G M›⟩, ‹DiscreteTopology M›⟩

/-- The construction retains the original carrier. -/
@[simp] lemma of_carrier : (underlying (of G M) : Type v) = M := rfl

/-- The construction retains the original additive action function. -/
@[simp, nolint simpNF] -- simpNF only sees `of_carrier` in the coercion's type
lemma of_smul (g : G) (x : M) :
    ((of G M).obj.obj.ρ g).asHom.hom x = (g • x : M) := rfl

end Objects

/-- A bijective arrow has its genuine additive, integer-linear, equivariant
continuous inverse on the same discrete carriers. Its forward map is the
original arrow. -/
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

/-- Actual bijectivity yields an isomorphism in the full discrete action category. -/
lemma isIso_of_bijective {X Y : DiscreteAbelianAction.{u, v} G}
    (f : X ⟶ Y) (h : Function.Bijective (homToAdd f)) : IsIso f :=
  (isoOfBijective f h).isIso_hom

/-- Repackaging an existing object retains it up to the actual identity maps. -/
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

/-- Every element of every object has its own open stabilizer. -/
lemma stabilizer_isOpen (X : DiscreteAbelianAction.{u, v} G) (x : underlying X) :
    IsOpen (MulAction.stabilizer G x : Set G) := _root_.stabilizer_isOpen G x

variable [IsTopologicalGroup G]

/-- The same joint-continuity condition is the elementwise open-stabilizer
criterion, without a uniform quotient condition. -/
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

/-- For a continuous monoid homomorphism `φ : H →ₜ* G`, pull back a discrete
continuous abelian action of `G` to an action of `H` by `h • x = φ h • x`.
The underlying coefficient group and additive maps are unchanged, and its
universe is independent of the two monoid universes. -/
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

/-- Pullback along the identity continuous monoid homomorphism is naturally
isomorphic to the identity functor on discrete continuous abelian actions.
Its components induce the identity additive maps on the coefficient groups. -/
def restrictModulesId : restrictModules (ContinuousMonoidHom.id G) ≅
    𝟭 (DiscreteAbelianAction.{u, w} G) :=
  NatIso.ofComponents fun M => ObjectProperty.isoMk _
    (ObjectProperty.isoMk _ ((Action.resId (TopModuleCat.{w} ℤ)).app M.obj.obj))

/-- For continuous monoid homomorphisms `φ : H →ₜ* G` and `ψ : J →ₜ* H`,
pullback along `φ.comp ψ` is naturally isomorphic to pullback along `φ` followed
by pullback along `ψ`. The coefficient groups may have an independent universe. -/
def restrictModulesComp (φ : H →ₜ* G) (ψ : J →ₜ* H) :
    restrictModules (φ.comp ψ) ≅ restrictModules φ ⋙ restrictModules ψ :=
  NatIso.ofComponents fun M => ObjectProperty.isoMk _
    ((ContAction.resComp (TopModuleCat.{w} ℤ) ψ φ).app M.obj)

/-- Equal continuous monoid homomorphisms `φ, φ' : H →ₜ* G` induce naturally
isomorphic pullback functors on discrete continuous abelian actions.
The comparison acts as the identity on each underlying coefficient group. -/
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
