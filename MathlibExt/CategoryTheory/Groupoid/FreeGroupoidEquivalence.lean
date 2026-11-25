/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory

/-!
# Full native groupoid completion of an actual category equivalence

The native completion maps both original inverse functors. Their actual
unit and counit natural isomorphisms extend uniquely through the original
completion units. The resulting equivalence retains the exact native
functor maps and the original category unit square, at independent
category object and Hom universes.
-/

noncomputable section
universe u v uD vD
open CategoryTheory

namespace CategoryTheory.FreeGroupoid

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D] (e : C ≌ D)

/-- Complete both actual original inverse functors and retain their full natural isomorphisms. -/
def mapEquivalence : FreeGroupoid C ≌ FreeGroupoid D := by
  let F := map e.functor
  let G := map e.inverse
  have hF : of C ⋙ F ⋙ G ≅ of C := by
    change of C ⋙ map e.functor ⋙ map e.inverse ≅ of C
    rw [← map_comp, of_comp_map]
    exact (Functor.isoWhiskerRight e.unitIso.symm (of C)) ≪≫ Functor.leftUnitor (of C)
  have hG : of D ⋙ G ⋙ F ≅ of D := by
    change of D ⋙ map e.inverse ⋙ map e.functor ≅ of D
    rw [← map_comp, of_comp_map]
    exact (Functor.isoWhiskerRight e.counitIso (of D)) ≪≫ Functor.leftUnitor (of D)
  exact Equivalence.mk F G (liftNatIso (F ⋙ G) (𝟭 _) hF).symm
    (liftNatIso (G ⋙ F) (𝟭 _) hG)

/-- The completed forward map is the SAME actual native full original functor map. -/
theorem mapEquivalence_functor : (mapEquivalence e).functor = map e.functor := rfl

/-- The completed inverse map is the SAME actual native full original inverse functor map. -/
theorem mapEquivalence_inverse : (mapEquivalence e).inverse = map e.inverse := rfl

end CategoryTheory.FreeGroupoid
