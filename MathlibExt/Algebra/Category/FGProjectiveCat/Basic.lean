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
# The category of finitely generated projective modules

For a ring `R`, `FGProjectiveCat R` is the full subcategory of `ModuleCat R`
spanned by finite projective modules. It is additive: in Mathlib encoded by
`Preadditive` plus `HasZeroObject` plus `HasBinaryBiproducts`; binary products
are `of R (M × N)`. Hence it carries the split exact structure and is
essentially small via `FGModuleCat R`.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

variable (R : Type u) [Ring R]

/-- Finite and projective as a property of `ModuleCat R`-objects. -/
def ModuleCat.isFGProjective : ObjectProperty (ModuleCat.{v} R) :=
  fun V => Module.Finite R V ∧ Module.Projective R V

/-- FG projective modules as a full subcategory. -/
abbrev FGProjectiveCat := (ModuleCat.isFGProjective.{v} R).FullSubcategory

namespace FGProjectiveCat

variable {R}

/-- Carrier synonym, marked `@[coe]`. -/
@[reducible]
def carrier (M : FGProjectiveCat.{v} R) : Type v :=
  M.obj.carrier

/-- Coercion to `Type`. -/
instance : CoeSort (FGProjectiveCat.{v} R) (Type v) :=
  ⟨carrier⟩

attribute [coe] carrier

@[simp]
lemma obj_carrier (M : FGProjectiveCat.{v} R) : M.obj.carrier = M.carrier :=
  rfl

/-- Finite instance from property. -/
instance (M : FGProjectiveCat.{v} R) : Module.Finite R M :=
  M.property.1

/-- Projective instance from property. -/
instance (M : FGProjectiveCat.{v} R) : Module.Projective R M :=
  M.property.2

/-- Inhabited by `PUnit`. -/
instance : Inhabited (FGProjectiveCat.{v} R) :=
  ⟨⟨ModuleCat.of R PUnit, by
      constructor
      · infer_instance
      · infer_instance⟩⟩

@[simp]
lemma hom_hom_comp {A B C : FGProjectiveCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom.hom = g.hom.hom.comp f.hom.hom :=
  rfl

@[simp]
lemma hom_hom_id (A : FGProjectiveCat.{v} R) :
    (𝟙 A : A ⟶ A).hom.hom = LinearMap.id :=
  rfl

/-- Lift a f.g. projective module. -/
abbrev of (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Projective R V] : FGProjectiveCat.{v} R :=
  ⟨ModuleCat.of R V, ⟨inferInstanceAs (Module.Finite R V), inferInstanceAs (Module.Projective R V)⟩⟩

@[simp]
lemma of_carrier (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Projective R V] :
    (of (R := R) V : Type v) = V :=
  rfl

/-- Lift a linear map. -/
abbrev ofHom {V W : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Projective R V] [AddCommGroup W] [Module R W] [Module.Finite R W]
    [Module.Projective R W] (f : V →ₗ[R] W) : of (R := R) V ⟶ of (R := R) W :=
  ConcreteCategory.ofHom f

/-- Extensionality via underlying linear maps. -/
@[ext]
lemma hom_ext {V W : FGProjectiveCat.{v} R} {f g : V ⟶ W}
    (h : f.hom.hom = g.hom.hom) : f = g :=
  ObjectProperty.hom_ext _ (ModuleCat.hom_ext h)

/-- Iso to linear equivalence. -/
def isoToLinearEquiv {V W : FGProjectiveCat.{v} R} (i : V ≅ W) : V ≃ₗ[R] W :=
  ((forget₂ (FGProjectiveCat.{v} R) (ModuleCat.{v} R)).mapIso i).toLinearEquiv

/-- Linear equivalence to iso. -/
@[simps]
def LinearEquiv.toFGProjectiveCatIso
    {V W : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Projective R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Projective R W]
    (e : V ≃ₗ[R] W) : FGProjectiveCat.of (R := R) V ≅ FGProjectiveCat.of (R := R) W where
  hom := ConcreteCategory.ofHom e.toLinearMap
  inv := ConcreteCategory.ofHom e.symm.toLinearMap
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

/-- Inclusion into `ModuleCat R`. -/
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

/-- Nonempty by `PUnit`. -/
instance isFGProjective_nonempty : (isFGProjective.{v} R).Nonempty :=
  ⟨of R PUnit, ⟨by infer_instance, by infer_instance⟩⟩

/-- Stable under retracts. -/
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

/-- Closed under binary products. -/
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
