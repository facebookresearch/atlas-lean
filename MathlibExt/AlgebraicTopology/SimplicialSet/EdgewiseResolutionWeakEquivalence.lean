/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialRows
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.EdgewiseResolution
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialObjectHomotopyRealization

import
  MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence

/-!
# Weak equivalence of the edgewise comparison

Every fixed-inner row of the edgewise resolution has an ordinary extra
degeneracy.  Rewriting its augmentation as the corresponding component of the
transposed bisimplicial augmentation proves that component is a realization
weak equivalence.  The inner-row diagonal theorem then proves the same for the
diagonal augmentation, and the exact diagonal comparison square identifies
the literal map `SSet.esdComparison.app X` as a realization weak equivalence.

This file does not construct a global extra degeneracy, a levelwise-discrete
realization comparison, an iterated-realization or Fubini equivalence, an
arbitrary topological total-decalage theorem, or any outer-bisimplicial,
Quillen, Stage, or Q/S consequence.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Opposite

open scoped Simplicial

universe u

namespace SSet

/-- Every fixed-inner row of the edgewise-resolution augmentation is a
realization weak equivalence. -/
theorem edgewiseResolutionRow_mem_realizationWeakEquivalences
    (X : SSet.{u}) (q : SimplexCategoryᵒᵖ) :
    realizationWeakEquivalences
      ((simplicialTransposeFunctor.map
        (edgewiseResolution X).hom).app q) := by
  change realizationWeakEquivalences
    (((CategoryTheory.SimplicialObject.transposeFunctor (Type u)).map
      (edgewiseResolution X).hom).app q)
  rw [← edgewiseResolutionRow_hom X q]
  exact (edgewiseResolutionRowExtraDegeneracy X q).hom_mem_realizationWeakEquivalences

/-- The diagonal of the edgewise-resolution augmentation is a realization
weak equivalence. -/
theorem edgewiseResolutionDiagonalAugmentation_mem_realizationWeakEquivalences
    (X : SSet.{u}) :
    realizationWeakEquivalences
      (simplicialDiagonalFunctor.map (edgewiseResolution X).hom) := by
  apply simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows
  intro m
  exact edgewiseResolutionRow_mem_realizationWeakEquivalences X
    (Opposite.op (SimplexCategory.mk m))

/-- The literal comparison from edgewise subdivision to the original
simplicial set is a realization weak equivalence. -/
theorem esdComparison_mem_realizationWeakEquivalences
    (X : SSet.{u}) :
    realizationWeakEquivalences (SSet.esdComparison.app X) := by
  have hPost := MorphismProperty.RespectsIso.postcomp realizationWeakEquivalences
    (diagonalConstIso X).hom
    (simplicialDiagonalFunctor.map (edgewiseResolution X).hom)
    (edgewiseResolutionDiagonalAugmentation_mem_realizationWeakEquivalences X)
  have hPre : realizationWeakEquivalences
      ((edgewiseResolutionDiagonalIso X).hom ≫ SSet.esdComparison.app X) := by
    exact (edgewiseResolution_diagonal_augmentation X).symm ▸ hPost
  exact (realizationWeakEquivalences.cancel_left_of_respectsIso
    (edgewiseResolutionDiagonalIso X).hom (SSet.esdComparison.app X)).mp hPre

end SSet

end
