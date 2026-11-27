/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomSuspensionGenerators

/-!
# Whole original forward Hom of the simplicial suspension

The sole original generating simplicial set identifies with the entire
forward Hom of its actual free enriched suspension. Both inverse maps
retain every original scalar cell and the same two original object
labels. No locally Kan or Bergner-model assumption is used.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.CoherentRealization.HomSuspensionForward
open SimplicialQuiver HomSuspensionGenerators
variable (K : SSet.{u})

/-- The whole original generating map into the actual forward Hom of the free suspension. -/
def generator : K ⟶ freeHom (quiver K) left right :=
  eqToHom (quiver_forward K).symm ≫ SimplicialQuiver.generator (quiver K) left right

/-- The supplied original generating simplicial set is exactly the entire actual forward
free Hom. -/
theorem generator_isIso : IsIso (SimplicialQuiver.generator (quiver K) left right) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  constructor
  · intro a b h
    let _ : Quiver Objects.{u} := quiverAt (quiver K) n
    have hA : a ≍ b := Quiver.Path.hom_heq_of_cons_eq_cons h
    exact eq_of_heq hA
  · intro p
    obtain ⟨a, ha⟩ := path_forward K p
    exact ⟨a, ha.symm⟩

/-- The actual whole forward Hom isomorphism from the supplied original simplicial set. -/
def homIso : K ≅ freeHom (quiver K) left right := by
  let _ := generator_isIso K
  exact (eqToIso (quiver_forward K).symm) ≪≫ asIso (SimplicialQuiver.generator (quiver
    K) left right)

/-- The entire forward map is precisely the original generating inclusion with its actual
generating-Hom equality. -/
theorem homIso_hom : (homIso K).hom = generator K := rfl

/-- The actual whole inverse reads each supplied original generating cell back without
changing its scalar degree. -/
theorem generator_readback (n : SimplexCategoryᵒᵖ) (a : K.obj n) :
    (homIso K).inv.app n ((generator K).app n a) = a :=
  congr($((homIso K).hom_inv_id).app n a)

/-- The same entire original free forward Hom cell is recovered after its actual original
generating-cell readback. -/
theorem inverse_readback (n : SimplexCategoryᵒᵖ) (p : (freeHom (quiver K) left right).obj n) :
    (generator K).app n ((homIso K).inv.app n p) = p :=
  congr($((homIso K).inv_hom_id).app n p)

end CategoryTheory.CoherentRealization.HomSuspensionForward
