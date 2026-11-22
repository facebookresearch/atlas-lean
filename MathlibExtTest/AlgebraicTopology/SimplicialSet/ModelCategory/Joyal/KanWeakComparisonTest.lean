/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.KanWeakComparison

/-!
# Kan Weak Comparison Test
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory MonoidalClosed

universe u

namespace MathlibExtTest.KanWeakComparison

variable {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y] (f : X ⟶ Y)

example : SSet.categoricalEquivalences f ↔ SSet.realizationWeakEquivalences f :=
  SSet.categoricalEquivalences_iff_realizationWeakEquivalences_of_kanComplex f

example (hf : SSet.categoricalEquivalences f) : SSet.realizationWeakEquivalences f :=
  (SSet.categoricalEquivalences_iff_realizationWeakEquivalences_of_kanComplex f).mp hf

example (hf : SSet.realizationWeakEquivalences f) : SSet.categoricalEquivalences f :=
  (SSet.categoricalEquivalences_iff_realizationWeakEquivalences_of_kanComplex f).mpr hf

example (hf : SSet.realizationWeakEquivalences f) :
    ∃ g : Y ⟶ X,
      Nonempty (SSet.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (SSet.Homotopy (g ≫ f) (𝟙 Y)) :=
  SSet.KanComplex.W.exists_homotopy_inverse
    ((SSet.KanComplex.W_iff_realizationWeakEquivalence f).mpr hf)

example {g : Y ⟶ X} (hX : SSet.Homotopy (f ≫ g) (𝟙 X))
    (hY : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    hX.edgeIhom.IsEquivalence ∧ hY.edgeIhom.IsEquivalence :=
  ⟨SSet.Edge.isEquivalence_of_kanComplex hX.edgeIhom,
    SSet.Edge.isEquivalence_of_kanComplex hY.edgeIhom⟩

example {g : Y ⟶ X} (hX : SSet.Homotopy (f ≫ g) (𝟙 X)) :
    SSet.Homotopy.ofIhomEdge hX.edgeIhom = hX :=
  SSet.Homotopy.ofIhomEdge_edgeIhom hX

example (hf : SSet.categoricalEquivalences f) :
    ∃ g : Y ⟶ X,
      (∃ e : SSet.Edge (SSet.ihomVertexEquiv X X (f ≫ g))
        (SSet.ihomVertexEquiv X X (𝟙 X)), e.IsEquivalence) ∧
      (∃ e : SSet.Edge (SSet.ihomVertexEquiv Y Y (g ≫ f))
        (SSet.ihomVertexEquiv Y Y (𝟙 Y)), e.IsEquivalence) :=
  hf.hasHoInverse.exists_isEquivalence_edges

example {A B : SSet.{u + 1}} [SSet.KanComplex A] [SSet.KanComplex B]
    (g : A ⟶ B) :
    SSet.categoricalEquivalences g ↔ SSet.realizationWeakEquivalences g :=
  SSet.categoricalEquivalences_iff_realizationWeakEquivalences_of_kanComplex g

end MathlibExtTest.KanWeakComparison
