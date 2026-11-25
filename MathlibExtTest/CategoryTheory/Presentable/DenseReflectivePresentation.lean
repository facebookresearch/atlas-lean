/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.DenseReflectivePresentation
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Category.Basic

/-!
# Dense reflective presentation on the original coefficient category

These contracts require no limit hypothesis. They check the actual small
presentable index, both original Hom functions, the original unit/counit,
and the entire native comma cocone with its actual legs. Concrete empty and
infinite presheaves and a nonidentity coefficient arrow retain those formulas.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uM vM

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.DenseReflectivePresentationTest

open DenseReflectivePresentation

variable (M : Type uM) [Category.{vM} M] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalLocallyPresentable M κ]

example : SmallCategory (index M κ) := inferInstance

example : (dense M κ).IsDense := inferInstance

example (d : index M κ) : IsCardinalPresentable ((dense M κ).obj d) κ :=
  dense_obj_presentable M κ d

example : Reflective (restrictedYoneda M κ) := inferInstance

example : left M κ ⊣ restrictedYoneda M κ := adjunction M κ

example (d : index M κ) (X : M) (f : (dense M κ).obj d ⟶ X) :
    (homEquiv M κ d X).symm (homEquiv M κ d X f) = f :=
  (homEquiv M κ d X).symm_apply_apply f

example (d : index M κ) (X : M)
    (z : ((restrictedYoneda M κ).obj X).obj (op d)) :
    homEquiv M κ d X ((homEquiv M κ d X).symm z) = z :=
  (homEquiv M κ d X).apply_symm_apply z

example (d : index M κ) {X Y : M} (f : (dense M κ).obj d ⟶ X) (g : X ⟶ Y) :
    ((restrictedYoneda M κ).map g).app (op d) (homEquiv M κ d X f) =
      homEquiv M κ d Y (f ≫ g) :=
  (homEquiv_naturality_right M κ d f g).symm

example {d e : index M κ} (a : d ⟶ e) (X : M) (f : (dense M κ).obj e ⟶ X) :
    ((restrictedYoneda M κ).obj X).map a.op (homEquiv M κ e X f) =
      homEquiv M κ d X ((dense M κ).map a ≫ f) :=
  (homEquiv_naturality_left M κ a X f).symm

example (P : (index M κ)ᵒᵖ ⥤ Type w) : Small.{w} (presentationShape M κ P) :=
  presentationShape_small M κ P

example (P : (index M κ)ᵒᵖ ⥤ Type w) : IsColimit (presentationCocone M κ P) :=
  presentationIsColimit M κ P

example (P : (index M κ)ᵒᵖ ⥤ Type w) (j : presentationShape M κ P) :
    (presentationCocone M κ P).ι.app j =
      (ShrinkHoms.equivalence.{w} M).inverse.map
        ((uliftYoneda.{w}.leftKanExtensionUnit (normalizedDense M κ)).app j.left ≫
          (uliftYoneda.{w}.leftKanExtension (normalizedDense M κ)).map j.hom) :=
  presentationCocone_ι M κ P j

example (P : (index M κ)ᵒᵖ ⥤ Type w) (X : M) (f : (left M κ).obj P ⟶ X)
    (d : index M κ) (x : P.obj (op d)) :
    ((adjunction M κ).homEquiv P X f).app (op d) x =
      homEquiv M κ d X (generatorLeg M κ P d x ≫ f) :=
  adjunction_homEquiv_app M κ P X f d x

example (P : (index M κ)ᵒᵖ ⥤ Type w) (d : index M κ) (x : P.obj (op d)) :
    ((adjunction M κ).unit.app P).app (op d) x =
      homEquiv M κ d ((left M κ).obj P) (generatorLeg M κ P d x) :=
  unit_app_app M κ P d x

example (P : (index M κ)ᵒᵖ ⥤ Type w) (X : M)
    (α : P ⟶ (restrictedYoneda M κ).obj X) (d : index M κ) (x : P.obj (op d)) :
    generatorLeg M κ P d x ≫ ((adjunction M κ).homEquiv P X).symm α =
      (homEquiv M κ d X).symm (α.app (op d) x) :=
  generatorLeg_homEquiv_symm M κ P X α d x

example (X : M) (d : index M κ) (f : (dense M κ).obj d ⟶ X) :
    generatorLeg M κ ((restrictedYoneda M κ).obj X) d (homEquiv M κ d X f) ≫
      (adjunction M κ).counit.app X = f :=
  counit_generatorLeg M κ X d f

section Concrete

attribute [local instance] Cardinal.fact_isRegular_aleph0

example : IsColimit (presentationCocone (Type) Cardinal.aleph0.{0}
    ((Functor.const _).obj PEmpty)) :=
  presentationIsColimit _ _ _

example : IsColimit (presentationCocone (Type) Cardinal.aleph0.{0}
    ((Functor.const _).obj ℕ)) :=
  presentationIsColimit _ _ _

/-- The actual nonidentity collapse arrow is retained by the full
restricted-Yoneda component function and its original Hom inverse. -/
def collapse : ULift Bool ⟶ ULift Bool := ↾fun _ ↦ ⟨true⟩

example (d : index (Type) Cardinal.aleph0.{0})
    (f : (dense (Type) Cardinal.aleph0.{0}).obj d ⟶ ULift Bool) :
    (homEquiv (Type) Cardinal.aleph0.{0} d (ULift Bool)).symm
      (((restrictedYoneda (Type) Cardinal.aleph0.{0}).map collapse).app (op d)
        (homEquiv (Type) Cardinal.aleph0.{0} d (ULift Bool) f)) = f ≫ collapse := by
  rw [← homEquiv_naturality_right]
  exact (homEquiv _ _ _ _).symm_apply_apply _

end Concrete

end CategoryTheory.DenseReflectivePresentationTest
