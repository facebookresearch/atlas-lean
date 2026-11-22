/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKan
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWhitehead
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceIhomComponents
import MathlibExt.AlgebraicTopology.Quasicategory.Core
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# The categorical and realization weak classes on Kan complexes

Joyal Corollary 9.8 identifies the two weak predicates on the same original
map between Kan complexes. The proof uses the public inverse-map theorems
and their original internal-Hom edges and simplicial homotopies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory MonoidalClosed

universe u

namespace SSet

/-- For the same original map between Kan complexes, categorical weakness
is equivalent to realization weakness in every value universe. -/
theorem categoricalEquivalences_iff_realizationWeakEquivalences_of_kanComplex
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y) :
    categoricalEquivalences f ↔ realizationWeakEquivalences f := by
  constructor
  · intro hf
    obtain ⟨g, ⟨eX, _⟩, ⟨eY, _⟩⟩ := hf.hasHoInverse.exists_isEquivalence_edges
    have hfg : realizationWeakEquivalences (f ≫ g) :=
      (realizationWeakEquivalences_iff_of_ihom_component_eq (π₀.sound eX)).mpr
        (MorphismProperty.id_mem realizationWeakEquivalences X)
    have hgf : realizationWeakEquivalences (g ≫ f) :=
      (realizationWeakEquivalences_iff_of_ihom_component_eq (π₀.sound eY)).mpr
        (MorphismProperty.id_mem realizationWeakEquivalences Y)
    exact realizationWeakEquivalences.left_of_comp_comp (a := f) (b := g) (c := f)
      hfg hgf
  · intro hf
    obtain ⟨g, ⟨hX⟩, ⟨hY⟩⟩ := KanComplex.W.exists_homotopy_inverse
      ((KanComplex.W_iff_realizationWeakEquivalence f).mpr hf)
    exact categoricalEquivalences.of_isEquivalence_edges g
      (Edge.isEquivalence_of_kanComplex hX.edgeIhom)
      (Edge.isEquivalence_of_kanComplex hY.edgeIhom)

end SSet
