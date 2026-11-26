/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomSuspensionGenerators

/-!
# Forward Hom of the simplicial suspension

The sole generating simplicial set identifies with the 
forward Hom of its free enriched suspension. Both inverse maps
retain every scalar cell and the same two object
labels. 
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.CoherentRealization.HomSuspensionForward
open SimplicialQuiver HomSuspensionGenerators
variable (K : SSet.{u})

/-- The generating map into the forward Hom of the free suspension. -/
def generator : K ⟶ freeHom (quiver K) left right :=
  eqToHom (quiver_forward K).symm ≫ SimplicialQuiver.generator (quiver K) left right

/-- The supplied generating simplicial set is exactly the forward
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

/-- The forward Hom isomorphism from the supplied simplicial set. -/
def homIso : K ≅ freeHom (quiver K) left right := by
  let _ := generator_isIso K
  exact (eqToIso (quiver_forward K).symm) ≪≫ asIso (SimplicialQuiver.generator (quiver
    K) left right)

/-- The forward map is precisely the generating inclusion with its 
generatingHom equality. -/
theorem homIso_hom : (homIso K).hom = generator K := rfl

/-- The inverse reads each supplied generating cell back without
changing its scalar degree. -/
theorem generator_readback (n : SimplexCategoryᵒᵖ) (a : K.obj n) :
    (homIso K).inv.app n ((generator K).app n a) = a :=
  congr($((homIso K).hom_inv_id).app n a)

/-- The same free forward Hom cell is recovered after its 
generating-cell readback. -/
theorem inverse_readback (n : SimplexCategoryᵒᵖ) (p : (freeHom (quiver K) left right).obj n) :
    (generator K).app n ((homIso K).inv.app n p) = p :=
  congr($((homIso K).inv_hom_id).app n p)

end CategoryTheory.CoherentRealization.HomSuspensionForward
