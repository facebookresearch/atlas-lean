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
# Negative-degree support of actual under-category cokernels

The support predicate evaluates the actual fixed-source cokernel in every
negative integer degree. Its colimit closure follows from the earned
cokernel left adjoint, native degreewise evaluation preservation, and the
universal property of a colimit of zero objects. The argument includes
empty diagrams and leaves degree zero unrestricted.
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

/-- The original full cokernel has zero evaluations in every negative integer degree. -/
def underCokernelNonnegativeProperty : ObjectProperty (Under I) :=
  fun η => ∀ i : ℤ, i < 0 →
    IsZero ((eval C c i).obj ((underCokernel I).obj η))

/-- The property concerns the literal existing cokernel of the original under arrow. -/
theorem underCokernelNonnegativeProperty_iff (η : Under I) :
    underCokernelNonnegativeProperty I η ↔ ∀ i : ℤ, i < 0 → IsZero ((cokernel η.hom).X i) :=
  Iff.rfl

/-- For a zero under arrow, the support condition is the original target's negative support. -/
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

/-- Every actual colimiting under cocone retains the negative support of its actual cokernels. -/
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

/-- Native object-property colimit closure for the actual under-cokernel support predicate. -/
instance underCokernelNonnegativeProperty_closedUnderColimits :
    (underCokernelNonnegativeProperty I).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le X hX := by
    rcases hX with ⟨hX⟩
    exact underCokernelNonnegativeProperty_of_isColimit I hX.isColimit hX.prop_diag_obj

/-- The actual chosen under colimit has an actual full cokernel with zero negative evaluations. -/
theorem underCokernelNonnegativeProperty_colimit (D : J ⥤ Under I) [HasColimit D]
    (hD : ∀ j : J, underCokernelNonnegativeProperty I (D.obj j)) :
    underCokernelNonnegativeProperty I (colimit D) :=
  (underCokernelNonnegativeProperty I).prop_colimit D hD

end Colimits

/-- The actual empty under colimit has supported cokernel, without any support hypothesis on `I`. -/
theorem underCokernelNonnegativeProperty_empty_colimit :
    underCokernelNonnegativeProperty I (colimit (Functor.empty.{0} (Under I))) := by
  apply underCokernelNonnegativeProperty_colimit
  intro j
  exact isEmptyElim j

end HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- For original integer cochain complexes this is exactly native strict support at zero. -/
theorem underCokernelNonnegativeProperty_iff_isStrictlyGE
    (I : CochainComplex C ℤ) (η : Under I) :
    HomologicalComplex.underCokernelNonnegativeProperty I η ↔
      ((underCokernel I).obj η).IsStrictlyGE 0 :=
  (((underCokernel I).obj η).isStrictlyGE_iff 0).symm

end CochainComplex
