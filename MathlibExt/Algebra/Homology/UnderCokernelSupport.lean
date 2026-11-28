/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Limits.Shapes.UnderCokernel
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Nonnegative support of under-category cokernels

For a fixed integer-indexed complex I, an object η : I → X of the under category has
nonnegative cokernel support when (coker η)_i is zero for every i<0. This property is closed
under colimits of the stated shape, including the empty diagram.

For a zero under-map the condition is exactly nonnegative support of X. In integer cochain
complexes, it is the predicate that the cokernel is strictly supported in degrees at least
zero.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

noncomputable section

universe v u w w'

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {c : ComplexShape ℤ} (I : HomologicalComplex C c)

/-- The negative-degree vanishing property of an under-category cokernel.

For η : I → X, require each negative-degree object of coker η to be zero. -/
def underCokernelNonnegativeProperty : ObjectProperty (Under I) :=
  fun η => ∀ i : ℤ, i < 0 →
    IsZero ((eval C c i).obj ((underCokernel I).obj η))

/-- The cokernel support property as degreewise vanishing.

The property is equivalent to zero objects (coker η)_i for all i<0. -/
theorem underCokernelNonnegativeProperty_iff (η : Under I) :
    underCokernelNonnegativeProperty I η ↔ ∀ i : ℤ, i < 0 → IsZero ((cokernel η.hom).X i) :=
  Iff.rfl

/-- The cokernel support condition for a zero under-map.

For the zero map I → X, the condition is exactly that X has zero negative-degree terms. -/
theorem underCokernelNonnegativeProperty_zeroUnder_iff (X : HomologicalComplex C c) :
    underCokernelNonnegativeProperty I ((zeroUnder I).obj X) ↔
      ∀ i : ℤ, i < 0 → IsZero (X.X i) := by
  have e : cokernel (0 : I ⟶ X) ≅ X := cokernelZeroIsoTarget
  constructor
  · intro h i hi
    exact ((eval C c i).mapIso e).isZero_iff.mp (h i hi)
  · intro h i hi
    exact ((eval C c i).mapIso e).isZero_iff.mpr (h i hi)

section Colimits

variable {J : Type w} [Category.{w'} J] [HasColimitsOfShape J C]

/-- Colimit cocones preserve nonnegative cokernel support.

If every object in an under-category diagram has this cokernel support, so does the point of
an actual colimit cocone. -/
theorem underCokernelNonnegativeProperty_of_isColimit
    {D : J ⥤ Under I} {s : Cocone D} (hs : IsColimit s)
    (hD : ∀ j : J, underCokernelNonnegativeProperty I (D.obj j)) :
    underCokernelNonnegativeProperty I s.pt := by
  intro i hi
  let F := underCokernel I ⋙ eval C c i
  have hF : IsColimit (F.mapCocone s) := isColimitOfPreserves F hs
  change IsZero (F.mapCocone s).pt
  rw [IsZero.iff_id_eq_zero]
  apply hF.hom_ext
  intro j
  exact (hD j i hi).eq_of_src _ _

/-- Closure under the stated colimit shape.

The nonnegative under-cokernel property is closed under colimits of shape J. -/
instance underCokernelNonnegativeProperty_closedUnderColimits :
    (underCokernelNonnegativeProperty I).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le X hX := by
    rcases hX with ⟨hX⟩
    exact underCokernelNonnegativeProperty_of_isColimit I hX.isColimit hX.prop_diag_obj

/-- The chosen colimit has nonnegative cokernel support.

A diagram whose objects satisfy the support condition has a chosen colimit satisfying it. -/
theorem underCokernelNonnegativeProperty_colimit (D : J ⥤ Under I) [HasColimit D]
    (hD : ∀ j : J, underCokernelNonnegativeProperty I (D.obj j)) :
    underCokernelNonnegativeProperty I (colimit D) :=
  (underCokernelNonnegativeProperty I).prop_colimit D hD

end Colimits

/-- The empty under-category colimit has zero negative cokernel terms.

The initial under-object's cokernel satisfies the nonnegative support property. -/
theorem underCokernelNonnegativeProperty_empty_colimit :
    underCokernelNonnegativeProperty I (colimit (Functor.empty.{0} (Under I))) := by
  apply underCokernelNonnegativeProperty_colimit
  intro j
  exact isEmptyElim j

end HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The under-cokernel support condition is strict lower support at zero.

For integer cochain complexes, the property is equivalent to IsStrictlyGE 0 of the cokernel
complex. -/
theorem underCokernelNonnegativeProperty_iff_isStrictlyGE
    (I : CochainComplex C ℤ) (η : Under I) :
    HomologicalComplex.underCokernelNonnegativeProperty I η ↔
      ((underCokernel I).obj η).IsStrictlyGE 0 :=
  (((underCokernel I).obj η).isStrictlyGE_iff 0).symm

end CochainComplex
