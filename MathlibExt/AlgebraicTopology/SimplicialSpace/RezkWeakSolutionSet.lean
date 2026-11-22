/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.BoundaryWeakInterpolation
import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalGenerationCardinal

/-!
# Generatorwise solution sets for Rezk weak equivalences

Choose one common eligible cardinal for the literal Reedy and auxiliary
families, then its canonical local-replacement envelope. The strict bounded
interpolation theorem supplies a Type-u weakly initial family in the comma
category from every literal Reedy boundary to all original Rezk weak arrows.

This is exactly the solution-set field consumed by Smith recognition. Both
components of every original Arrow morphism remain strict equalities.
-/

set_option autoImplicit false
noncomputable section

universe u

open CategoryTheory CategoryTheory.MorphismProperty

namespace SimplicialSpace

/-- Every literal Reedy boundary generator has a working-universe solution set
against the full original Rezk weak class. -/
theorem rezkWeakEquivalences_boundary_solution_set
    {A B : SimplicialSpace.{u}} (i : A ⟶ B)
    (hi : ReedyGeneratingFamilies.I.{u} i) :
    ∃ (S : Type u)
      (q : S → rezkWeakEquivalences.{u}.arrowObjectProperty.FullSubcategory)
      (h : ∀ s, Arrow.mk i ⟶
        rezkWeakEquivalences.{u}.arrowObjectProperty.ι.obj (q s)),
      ∀ (T : rezkWeakEquivalences.{u}.arrowObjectProperty.FullSubcategory)
        (sq : Arrow.mk i ⟶
          rezkWeakEquivalences.{u}.arrowObjectProperty.ι.obj T),
        ∃ (s : S) (ψ : q s ⟶ T),
          h s ≫ rezkWeakEquivalences.{u}.arrowObjectProperty.ι.map ψ = sq := by
  obtain ⟨κ, hκ, hbot, _hC, _hI, _hJ, hLocal⟩ :=
    LocalGenerators.exists_common_smallness_cardinal.{u}
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hbot
  let _ : LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ := hLocal
  obtain ⟨e⟩ := exists_localReplacementCardinalEnvelope κ
  obtain ⟨S, q, h, _hbounded, hfactor⟩ :=
    e.boundedBoundaryWeakSolutionFamily i hi
  exact ⟨S, q, h, hfactor⟩

end SimplicialSpace
