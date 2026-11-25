/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/DayConvolution/Monoid.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Monoidal.Mon
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.DayConvolution.Braided

/-!
# Lax monoidal functors as Day convolution monoids

For monoidal categories `C` and `V`, a monoid for the Day convolution product on `C ⊛⥤ V` is the
same thing as a lax monoidal functor `C ⥤ V`: by the universal property of the Day convolution
`F ⊗ F` as a left Kan extension of `F ⊠ F` along the tensor product of `C`, a multiplication
`F ⊗ F ⟶ F` is a natural family `F x ⊗ F y ⟶ F (x ⊗ y)`, and a unit `𝟙_ ⟶ F` is a morphism
`𝟙_ V ⟶ F (𝟙_ C)`. This file constructs the direction used to build monoids: the tensorator and
unit of a lax monoidal functor `F` make `F` a monoid object of `C ⊛⥤ V`, which is commutative when
`F` is lax braided and the braiding of `C` is symmetric. Monoidal natural transformations become
monoid morphisms.

The symmetry assumption on `C` comes from the convention of Mathlib's Day convolution braiding,
which restricts along the units to `F x ⊗ G y ⟶ G y ⊗ F x ⟶ (G ⊗ F) (y ⊗ x) ⟶ (G ⊗ F) (x ⊗ y)`,
the last map being the braiding `β_ y x` of `C`.

The main application is the sphere symmetric sequence `n ↦ (S¹)^∧n`, a lax braided functor out
of the finite-bijection groupoid, whose Day convolution monoid structure is the ring structure of
the sphere symmetric spectrum.

The monoid laws are verified using the restatements, along the Day convolution units, of the
whiskerings, the associator and the unitors of `C ⊛⥤ V` and the corresponding extensionality
lemmas from `MathlibExt.SpectraSource.CategoryTheory.Monoidal.DayConvolution.Basic`. The unit
  and multiplication
are built with `DayFunctor.unitDesc` and `DayFunctor.tensorDesc` from Robin Carlier's Day
convolution formalization in Mathlib (`Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor`).

## Main definitions

* `DayFunctor.monObj`: the Day convolution monoid structure on a lax monoidal functor.
* `DayFunctor.isCommMonObj`: it is commutative for a lax braided functor out of a symmetric
  monoidal category.
* `DayFunctor.isMonHom`: monoidal natural transformations are monoid morphisms.

## Main statements

* `DayFunctor.ν_comp_one_natTrans_app`, `DayFunctor.η_app_comp_mul_natTrans_app`: the unit and
  multiplication restrict along the Day convolution units to the unit and the tensorator of `F`.

## References

* B. Day, *On closed categories of functors*, Reports of the Midwest Category Seminar IV,
  Lecture Notes in Math. 137 (1970), 1-38.
* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.MonoidalCategory.DayFunctor

open scoped ExternalProduct
open LawfulDayConvolutionMonoidalCategoryStruct

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), Limits.PreservesColimitsOfShape
      (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), Limits.PreservesColimitsOfShape
      (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

section LaxMonoidal

variable (F : C ⊛⥤ V) [F.functor.LaxMonoidal]

/-- The Day convolution monoid structure on a lax monoidal functor `F`: its unit and
multiplication are induced by the unit `ε` and the tensorator `μ` of `F`. -/
instance monObj : MonObj F where
  one := unitDesc (Functor.LaxMonoidal.ε F.functor)
  mul := tensorDesc
    { app p := Functor.LaxMonoidal.μ F.functor p.1 p.2
      naturality p q f := by simp [tensorHom_def] }
  one_mul := unit_tensor_hom_ext fun y ↦ by
    simp [← comp_whiskerRight_assoc]
  mul_one := tensor_unit_hom_ext fun x ↦ by
    simp [← whiskerLeft_comp_assoc]
  mul_assoc := tensor_tensor_hom_ext fun x y z ↦ by
    simp [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc]

/-- The unit of the Day convolution monoid `F` restricts along `ν` to the unit `ε` of `F`. -/
@[reassoc (attr := simp)]
lemma ν_comp_one_natTrans_app :
    ν C V ≫ (MonObj.one : 𝟙_ (C ⊛⥤ V) ⟶ F).natTrans.app (𝟙_ C) =
      Functor.LaxMonoidal.ε F.functor :=
  ν_comp_unitDesc _

/-- The multiplication of the Day convolution monoid `F` restricts along `η F F` to the
tensorator `μ` of `F`. -/
@[reassoc (attr := simp)]
lemma η_app_comp_mul_natTrans_app (x y : C) :
    (η F F).app (x, y) ≫ (MonObj.mul : F ⊗ F ⟶ F).natTrans.app (x ⊗ y) =
      Functor.LaxMonoidal.μ F.functor x y :=
  η_comp_tensorDesc_app _ _ _

end LaxMonoidal

/-- A monoidal natural transformation of lax monoidal functors is a morphism of the associated
Day convolution monoids. -/
instance isMonHom {F G : C ⊛⥤ V} [F.functor.LaxMonoidal] [G.functor.LaxMonoidal] (f : F ⟶ G)
    [NatTrans.IsMonoidal f.natTrans] : IsMonHom f where
  one_hom := unit_hom_ext (by simp)
  mul_hom := tensor_hom_ext fun x y ↦ by simp

section LaxBraided

variable [SymmetricCategory C] [BraidedCategory V] (F : C ⊛⥤ V) [F.functor.LaxBraided]

/-- The Day convolution monoid of a lax braided functor out of a symmetric monoidal category is
commutative. -/
instance isCommMonObj : IsCommMonObj F where
  mul_comm := tensor_hom_ext fun x y ↦ by
    simp [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp]

end LaxBraided

end

end CategoryTheory.MonoidalCategory.DayFunctor
