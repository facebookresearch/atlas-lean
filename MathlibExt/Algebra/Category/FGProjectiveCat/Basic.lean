/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import MathlibExt.CategoryTheory.ExactCategory.Split

/-!
# The additive category of finite projective modules

For a ring `R`, `FGProjectiveCat.{v} R` is the full subcategory of `ModuleCat.{v} R` whose
objects are finitely generated projective `R`-modules. Morphisms are `R`-linear maps, and
categorical isomorphisms correspond to linear equivalences.

The property of being finite projective is closed under retracts and binary products. The
category has a zero object and binary biproducts, and carries the split exact structure. It is
essentially small in the ring universe through its inclusion in the category of finite
modules. The ring and module-carrier universes are independent.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

variable (R : Type u) [Ring R]

/-- Finite projectivity as a property of module-category objects.

A module-category object has this property exactly when its underlying `R`-module is both
finitely generated and projective. -/
def ModuleCat.isFGProjective : ObjectProperty (ModuleCat.{v} R) :=
  fun V => Module.Finite R V ∧ Module.Projective R V

/-- Full subcategory of finitely generated projective modules.

For a ring `R`, `FGProjectiveCat.{v} R` consists of the objects of `ModuleCat.{v} R`
satisfying `Module.Finite R V ∧ Module.Projective R V`, with all module-category morphisms
between them. -/
abbrev FGProjectiveCat := (ModuleCat.isFGProjective.{v} R).FullSubcategory

namespace FGProjectiveCat

variable {R}

/-- Underlying carrier of a finite projective module object.

The carrier of `M : FGProjectiveCat.{v} R` is the carrier of its underlying module-category
object and lies in universe `v`. -/
@[reducible]
def carrier (M : FGProjectiveCat.{v} R) : Type v :=
  M.obj.carrier

/- Finite projective objects use the carrier of their underlying module. -/
instance : CoeSort (FGProjectiveCat.{v} R) (Type v) :=
  ⟨carrier⟩

attribute [coe] carrier

/-- Finite projective carrier agrees with the underlying module carrier.

For `M : FGProjectiveCat.{v} R`, `M.obj.carrier = M.carrier`. -/
@[simp]
lemma obj_carrier (M : FGProjectiveCat.{v} R) : M.obj.carrier = M.carrier :=
  rfl

/- For any ring R, every object of FGProjectiveCat R is a finitely generated R-module. -/
instance (M : FGProjectiveCat.{v} R) : Module.Finite R M :=
  M.property.1

/- For any ring R, every object of FGProjectiveCat R is a projective R-module. -/
instance (M : FGProjectiveCat.{v} R) : Module.Projective R M :=
  M.property.2

/- The zero module provides an object of the finite projective category. -/
instance : Inhabited (FGProjectiveCat.{v} R) :=
  ⟨⟨ModuleCat.of R PUnit, by
      constructor
      · infer_instance
      · infer_instance⟩⟩

/-- Composition of finite projective morphisms as linear composition.

For morphisms `f : A ⟶ B` and `g : B ⟶ C`, the underlying linear map of `f ≫ g` is
`g.hom.hom.comp f.hom.hom`. -/
@[simp]
lemma hom_hom_comp {A B C : FGProjectiveCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom.hom = g.hom.hom.comp f.hom.hom :=
  rfl

/-- Identity of a finite projective object as a linear identity.

The underlying linear map of the identity morphism on a finite projective module object is
`LinearMap.id`. -/
@[simp]
lemma hom_hom_id (A : FGProjectiveCat.{v} R) :
    (𝟙 A : A ⟶ A).hom.hom = LinearMap.id :=
  rfl

/-- Bundling a finite projective module.

An additive commutative group `V` with an `R`-module structure, finite generation, and module
projectivity defines an object `FGProjectiveCat.of V`. -/
abbrev of (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Projective R V] : FGProjectiveCat.{v} R :=
  ⟨ModuleCat.of R V, ⟨inferInstanceAs (Module.Finite R V), inferInstanceAs (Module.Projective R V)⟩⟩

/-- Carrier of a bundled finite projective module.

The carrier of the finite projective object constructed from `V` is `V`. -/
@[simp]
lemma of_carrier (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Projective R V] :
    (of (R := R) V : Type v) = V :=
  rfl

/-- Bundling a linear map between finite projective modules.

An `R`-linear map between finite projective modules gives a morphism between their bundled
objects in `FGProjectiveCat`. -/
abbrev ofHom {V W : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Projective R V] [AddCommGroup W] [Module R W] [Module.Finite R W]
    [Module.Projective R W] (f : V →ₗ[R] W) : of (R := R) V ⟶ of (R := R) W :=
  ConcreteCategory.ofHom f

/-- Linear maps determine finite projective morphisms.

Two morphisms between finite projective module objects are equal if their underlying
`R`-linear maps are equal. -/
@[ext]
lemma hom_ext {V W : FGProjectiveCat.{v} R} {f g : V ⟶ W}
    (h : f.hom.hom = g.hom.hom) : f = g :=
  ObjectProperty.hom_ext _ (ModuleCat.hom_ext h)

/-- Finite projective categorical isomorphism as a linear equivalence.

An isomorphism between objects of `FGProjectiveCat` gives an `R`-linear equivalence between
their carriers by forgetting to `ModuleCat`. -/
def isoToLinearEquiv {V W : FGProjectiveCat.{v} R} (i : V ≅ W) : V ≃ₗ[R] W :=
  ((forget₂ (FGProjectiveCat.{v} R) (ModuleCat.{v} R)).mapIso i).toLinearEquiv

/-- Linear equivalence as an isomorphism of finite projective objects.

An `R`-linear equivalence between finite projective modules gives an isomorphism between their
corresponding `FGProjectiveCat` objects. -/
@[simps]
def LinearEquiv.toFGProjectiveCatIso
    {V W : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Projective R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Projective R W]
    (e : V ≃ₗ[R] W) : FGProjectiveCat.of (R := R) V ≅ FGProjectiveCat.of (R := R) W where
  hom := ConcreteCategory.ofHom e.toLinearMap
  inv := ConcreteCategory.ofHom e.symm.toLinearMap
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

/-- Inclusion of finite projective objects in the module category.

The full-subcategory inclusion `FGProjectiveCat.{v} R ⥤ ModuleCat.{v} R` sends each object and
morphism to its underlying module object and linear map. -/
def toModuleCat : FGProjectiveCat.{v} R ⥤ ModuleCat.{v} R :=
  (ModuleCat.isFGProjective.{v} R).ι

instance : (toModuleCat : FGProjectiveCat.{v} R ⥤ ModuleCat.{v} R).Full :=
  (ModuleCat.isFGProjective.{v} R).full_ι

instance : (toModuleCat : FGProjectiveCat.{v} R ⥤ ModuleCat.{v} R).Faithful :=
  (ModuleCat.isFGProjective.{v} R).faithful_ι

instance : (toModuleCat : FGProjectiveCat.{v} R ⥤ ModuleCat.{v} R).Additive :=
  CategoryTheory.Functor.fullSubcategoryInclusion_additive (ModuleCat.isFGProjective R)

end FGProjectiveCat

namespace ModuleCat

section Instances

variable {R}

/-- Finite projective module property is nonempty.

The one-element zero module is finite and projective, giving an object with the finite
projective property. -/
instance isFGProjective_nonempty : (isFGProjective.{v} R).Nonempty :=
  ⟨of R PUnit, ⟨by infer_instance, by infer_instance⟩⟩

/-- Finite projective modules are closed under retracts.

A retract in `ModuleCat` of a finitely generated projective module is again finitely generated
and projective. -/
instance isFGProjective_isStableUnderRetracts :
    (isFGProjective.{v} R).IsStableUnderRetracts where
  of_retract {X Y} r hY := by
    obtain ⟨hFinY, hProjY⟩ := hY
    have hRetract : r.i ≫ r.r = 𝟙 X := r.retract
    have hComp : r.r.hom.comp r.i.hom = LinearMap.id :=
      congrArg Hom.hom hRetract
    constructor
    · have hSurj : Function.Surjective r.r.hom := by
        intro x
        use r.i.hom x
        have : r.r.hom (r.i.hom x) = x := by
          have := LinearMap.congr_fun hComp x
          simpa using this
        exact this
      exact Module.Finite.of_surjective r.r.hom hSurj
    · exact Module.Projective.of_split r.i.hom r.r.hom hComp

/-- Binary products of finite projective modules remain finite projective.

The object property `ModuleCat.isFGProjective` is closed under limits of a discrete two-object
diagram. In particular, the product of two finite projective modules is finite projective. -/
instance isFGProjective_isClosedUnderBinaryProducts :
    (isFGProjective.{v} R).IsClosedUnderLimitsOfShape
      (Discrete WalkingPair) := by
  constructor
  intro Y hY
  obtain ⟨p⟩ := hY
  let M := p.diag.obj ⟨WalkingPair.left⟩
  let N := p.diag.obj ⟨WalkingPair.right⟩
  have hM : isFGProjective.{v} R M := p.prop_diag_obj ⟨WalkingPair.left⟩
  have hN : isFGProjective.{v} R N := p.prop_diag_obj ⟨WalkingPair.right⟩
  have hProd : isFGProjective.{v} R (of R (M × N)) := by
    constructor
    · let : Module.Finite R M := hM.1
      let : Module.Finite R N := hN.1
      infer_instance
    · let : Module.Projective R M := hM.2
      let : Module.Projective R N := hN.2
      infer_instance
  let hc := binaryProductLimitCone M N
  let e : p.diag ≅ pair M N := diagramIsoPair p.diag
  have hLimit : IsLimit ((Cone.postcompose e.inv).obj hc.cone) :=
    (IsLimit.postcomposeInvEquiv e hc.cone).2 hc.isLimit
  have iso : Y ≅ of R (M × N) :=
    p.isLimit.conePointUniqueUpToIso hLimit
  exact (isFGProjective.{v} R).prop_of_iso iso.symm hProd

end Instances

end ModuleCat

section CategoryInstances

variable (R : Type u) [Ring R]

/-- Binary biproducts induced by binary products. -/
instance : HasBinaryBiproducts (FGProjectiveCat.{v} R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The split exact structure on `FGProjectiveCat`. -/
instance : ExactCategory (FGProjectiveCat.{v} R) :=
  ExactCategory.splitExactCategory (C := FGProjectiveCat.{v} R)

end CategoryInstances

section EssentiallySmall

variable (R : Type u) [Ring R]

/-- Essentially small via `FGModuleCat R`. -/
instance : EssentiallySmall.{u} (FGProjectiveCat.{v} R) :=
  let h : ModuleCat.isFGProjective.{v} R ≤ ModuleCat.isFG.{v} R := fun _ h => h.1
  essentiallySmall_of_fully_faithful ((ModuleCat.isFGProjective.{v} R).ιOfLE h)

end EssentiallySmall
