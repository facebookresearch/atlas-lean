/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Basic
public import MathlibExt.CategoryTheory.Monoidal.GroupCompletion
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationFiberHomology

/-!
# The skeleton action on core homology

Left biproduct translation on `Core C` depends only on the skeleton class,
is unital up to natural isomorphism, and converts biproduct addition into
composition.  Applying category homology gives a representation of the
multiplicative form of `Skeleton C` on the homology of `Core C`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe w v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Isomorphic left summands define naturally isomorphic core translation
functors. -/
noncomputable def coreLeftTranslationIsoOfIso
    {s t : C} (e : s ≅ t) :
    coreLeftTranslationFunctor s ≅ coreLeftTranslationFunctor t :=
  NatIso.ofComponents
    (fun X => Core.isoMk (biprod.mapIso e (Iso.refl X.of))) (by
      intro X Y g
      apply Core.hom_ext
      change
        biprod.map (𝟙 s) g.iso.hom ≫
            biprod.map e.hom (𝟙 Y.of) =
          biprod.map e.hom (𝟙 X.of) ≫
            biprod.map (𝟙 t) g.iso.hom
      apply biprod.hom_ext <;> simp)

/-- Translation by the zero object is naturally isomorphic to the identity
on the core. -/
noncomputable def coreLeftTranslationZeroIso :
    coreLeftTranslationFunctor (0 : C) ≅ 𝟭 (Core C) :=
  NatIso.ofComponents
    (fun X => Core.isoMk (isoZeroBiprod (isZero_zero C)).symm) (by
      intro X Y g
      apply Core.hom_ext
      change
        biprod.map (𝟙 (0 : C)) g.iso.hom ≫
            (isoZeroBiprod (isZero_zero C)).symm.hom =
          (isoZeroBiprod (isZero_zero C)).symm.hom ≫ g.iso.hom
      simp)

/-- Translation by a biproduct is translation by the second summand followed
by translation by the first summand. -/
noncomputable def coreLeftTranslationBiprodIso (s t : C) :
    coreLeftTranslationFunctor (s ⊞ t) ≅
      coreLeftTranslationFunctor t ⋙ coreLeftTranslationFunctor s :=
  NatIso.ofComponents
    (fun X => Core.isoMk (biprod.associator s t X.of)) (by
      intro X Y g
      apply Core.hom_ext
      change
        biprod.map (𝟙 (s ⊞ t)) g.iso.hom ≫
            (biprod.associator s t Y.of).hom =
          (biprod.associator s t X.of).hom ≫
            biprod.map (𝟙 s) (biprod.map (𝟙 t) g.iso.hom)
      apply biprod.hom_ext
      · simp [Category.assoc]
      · apply biprod.hom_ext <;> simp [Category.assoc])

/-- Translation by the chosen representative of the zero skeleton class is
naturally the identity. -/
noncomputable def coreLeftTranslationSkeletonZeroIso :
    coreLeftTranslationFunctor ((0 : Skeleton C).out) ≅ 𝟭 (Core C) :=
  coreLeftTranslationIsoOfIso
      (fromSkeletonToSkeletonIso (0 : C)) ≪≫
    coreLeftTranslationZeroIso

/-- Translation by the chosen representative of a sum of skeleton classes
is the composite of their chosen translations. -/
noncomputable def coreLeftTranslationSkeletonAddIso
    (x y : Skeleton C) :
    coreLeftTranslationFunctor (x + y).out ≅
      coreLeftTranslationFunctor y.out ⋙
        coreLeftTranslationFunctor x.out :=
  coreLeftTranslationIsoOfIso
      (fromSkeletonToSkeletonIso (x.out ⊞ y.out)) ≪≫
    coreLeftTranslationBiprodIso x.out y.out

section Homology

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [UnivLE.{max u v, w}]

/-- Action of a skeleton class on core homology by left translation. -/
noncomputable def coreTranslationHomologyMap
    (R : AddCommGrpCat.{w}) (n : ℕ) (x : Skeleton C) :
    (nerve (Core C)).homology R n ⟶
      (nerve (Core C)).homology R n :=
  SSet.homologyMap
    (nerveMap (coreLeftTranslationFunctor x.out)) R n

omit [HasZeroObject C] in
/-- On a represented skeleton class, the action agrees with translation by
the representing object itself. -/
theorem coreTranslationHomologyMap_toSkeleton
    (R : AddCommGrpCat.{w}) (n : ℕ) (s : C) :
    coreTranslationHomologyMap C R n (toSkeleton s) =
      SSet.homologyMap (nerveMap (coreLeftTranslationFunctor s)) R n :=
  (NatTrans.nerveHomotopy
    (coreLeftTranslationIsoOfIso
      (fromSkeletonToSkeletonIso s)).hom).congr_homologyMap R n

/-- The zero skeleton class acts as the identity on core homology. -/
theorem coreTranslationHomologyMap_zero
    (R : AddCommGrpCat.{w}) (n : ℕ) :
    coreTranslationHomologyMap C R n 0 = 𝟙 _ := by
  let H : Cat.{v, u} ⥤ AddCommGrpCat.{w} :=
    categoryHomologyFunctor AddCommGrpCat.{w} R n
  have h := categoryHomologyMap_eq_of_natIso AddCommGrpCat.{w}
    (coreLeftTranslationSkeletonZeroIso (C := C)) R n
  change H.map
      (coreLeftTranslationFunctor ((0 : Skeleton C).out)).toCatHom = 𝟙 _
  calc
    _ = H.map (𝟭 (Core C)).toCatHom := h
    _ = 𝟙 _ := H.map_id (Cat.of (Core C))

/-- Addition of skeleton classes acts by composition of the corresponding
core-homology endomorphisms. -/
theorem coreTranslationHomologyMap_add
    (R : AddCommGrpCat.{w}) (n : ℕ) (x y : Skeleton C) :
    coreTranslationHomologyMap C R n (x + y) =
      coreTranslationHomologyMap C R n y ≫
        coreTranslationHomologyMap C R n x := by
  let H : SSet.{max u v} ⥤ AddCommGrpCat.{w} :=
    SSet.homologyFunctor R n
  have h := (NatTrans.nerveHomotopy
    (coreLeftTranslationSkeletonAddIso x y).hom).congr_homologyMap R n
  have hIso :
      H.map (nerveMap (coreLeftTranslationFunctor (x + y).out)) =
        H.map (nerveMap (coreLeftTranslationFunctor y.out ⋙
          coreLeftTranslationFunctor x.out)) := h
  have hNerve :
      nerveMap (coreLeftTranslationFunctor y.out ⋙
          coreLeftTranslationFunctor x.out) =
        nerveMap (coreLeftTranslationFunctor y.out) ≫
          nerveMap (coreLeftTranslationFunctor x.out) :=
    (nerveMap_comp _ _).symm
  change H.map (nerveMap (coreLeftTranslationFunctor (x + y).out)) =
    H.map (nerveMap (coreLeftTranslationFunctor y.out)) ≫
      H.map (nerveMap (coreLeftTranslationFunctor x.out))
  calc
    _ = H.map (nerveMap (coreLeftTranslationFunctor y.out ⋙
          coreLeftTranslationFunctor x.out)) := hIso
    _ = H.map (nerveMap (coreLeftTranslationFunctor y.out) ≫
          nerveMap (coreLeftTranslationFunctor x.out)) := by
      rw [hNerve]
    _ = _ := H.map_comp _ _

/-- Representation of the multiplicative skeleton monoid on core homology. -/
noncomputable def coreTranslationHomologyRepresentation
    (R : AddCommGrpCat.{w}) (n : ℕ) :
    Representation ℤ (Multiplicative (Skeleton C))
      ((nerve (Core C)).homology (C := AddCommGrpCat.{w}) R n) where
  toFun x :=
    (coreTranslationHomologyMap C R n x.toAdd).hom.toIntLinearMap
  map_one' := by
    apply LinearMap.ext
    intro z
    have h := ConcreteCategory.congr_hom
      (coreTranslationHomologyMap_zero C R n) z
    simpa using h
  map_mul' x y := by
    apply LinearMap.ext
    intro z
    have h := ConcreteCategory.congr_hom
      (coreTranslationHomologyMap_add C R n x.toAdd y.toAdd) z
    simpa [Module.End.mul_apply] using h

/-- Core homology equipped with its module structure over the additive
monoid algebra of `Skeleton C`. -/
noncomputable abbrev coreTranslationHomologyModule
    (R : AddCommGrpCat.{w}) (n : ℕ) :=
  (coreTranslationHomologyRepresentation C R n).asModule

/-- The underlying integer module of the skeleton-action module is the
original core homology group. -/
noncomputable def coreTranslationHomologyModuleEquiv
    (R : AddCommGrpCat.{w}) (n : ℕ) :
    coreTranslationHomologyModule C R n ≃ₗ[ℤ]
      ((nerve (Core C)).homology (C := AddCommGrpCat.{w}) R n) :=
  (coreTranslationHomologyRepresentation C R n).asModuleEquiv

/-- A skeleton monomial acts by the corresponding core left-translation
homology map. -/
@[simp↓]
theorem coreTranslationHomologyModuleEquiv_monomial_smul
    (R : AddCommGrpCat.{w}) (n : ℕ) (x : Skeleton C)
    (z : coreTranslationHomologyModule C R n) :
    coreTranslationHomologyModuleEquiv C R n
        (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
          (Multiplicative.ofAdd x) • z) =
      (coreTranslationHomologyMap C R n x).hom
        (coreTranslationHomologyModuleEquiv C R n z) := by
  change (coreTranslationHomologyRepresentation C R n).asModuleEquiv
      ((MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
        (Multiplicative.ofAdd x)) • z) =
    (coreTranslationHomologyMap C R n x).hom
      ((coreTranslationHomologyRepresentation C R n).asModuleEquiv z)
  rw [Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_of]
  rfl

end Homology

end SInverseS
end CategoryTheory

end
