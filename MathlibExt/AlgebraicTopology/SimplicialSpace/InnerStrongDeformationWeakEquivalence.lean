/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexProductProjection
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerOneSimplexCylinder

/-!
# Reedy weakness of inner strong deformation retracts

The literal inner one-simplex projection is a weak equivalence in the named
Reedy model.  Degreewise it is the first projection `T × Δ[1] ⟶ T`; symmetry
reduces it to the realized standard-simplex second projection.  The generic
localization theorem then makes every map carrying strong deformation data for
this cylinder a Reedy weak equivalence.
-/

set_option autoImplicit false
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open scoped MonoidalCategory Simplicial SimplicialSpace.Inner

namespace SimplicialSpace.ReedyModel

/-- The projection of the literal inner one-simplex cylinder is a weak
equivalence in the named Reedy model, for every simplicial space. -/
theorem innerOneSimplex_projection_weakEquivalence
    (X : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    weakEquivalences SimplicialSpace.{u}
      (innerOneSimplexPrecylinder.app X).π := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  rw [← HomotopicalAlgebra.weakEquivalence_iff]
  rw [weakEquivalence_iff]
  intro n
  let T := X.diagram.obj (Opposite.op ⦋n⦌)
  have hsnd : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map
        (snd (Δ[1] : SSet.{u}) T : (Δ[1] : SSet.{u}) ⊗ T ⟶ T)) :=
    TopCat.mem_of_eq_toFun
      (SSet.realizedStdSimplexProdSndHomotopyEquiv 1 T) rfl
  have hfst := MorphismProperty.RespectsIso.precomp
    TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (β_ T (Δ[1] : SSet.{u})).hom)
    (SSet.toTop.map
      (snd (Δ[1] : SSet.{u}) T : (Δ[1] : SSet.{u}) ⊗ T ⟶ T)) hsnd
  change SSet.realizationWeakEquivalences
    ((T ◁ toUnit (Δ[1] : SSet.{u})) ≫ (ρ_ T).hom)
  rw [whiskerLeft_toUnit_comp_rightUnitor_hom]
  have hfst' : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (fst T (Δ[1] : SSet.{u}))) := by
    simpa only [← Functor.map_comp, braiding_hom_snd] using hfst
  exact (TopCat.mem_weakHomotopyEquivalences_iff _).1 hfst'

/-- Inner one-simplex strong deformation data imply genuine weakness in the
same named Reedy model. -/
theorem weakEquivalence_of_innerStrongDeformationData
    {A B : SimplicialSpace.{u}} {j : A ⟶ B}
    (D : innerOneSimplexPrecylinder.StrongDeformationData j) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    weakEquivalences SimplicialSpace.{u} j := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  exact D.weakEquivalence_of_projection
    (innerOneSimplex_projection_weakEquivalence B)

end SimplicialSpace.ReedyModel
