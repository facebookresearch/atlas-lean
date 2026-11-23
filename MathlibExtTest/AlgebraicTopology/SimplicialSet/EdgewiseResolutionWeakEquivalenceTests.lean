/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.EdgewiseResolutionWeakEquivalence

/-!
# Tests for weak equivalence of the edgewise comparison

These tests pin the exact transposed row map, fixed inner degrees zero through
two and an arbitrary inner degree, the diagonal augmentation, and the literal
map `SSet.esdComparison.app X`.  They also recheck the target-vertex `δ 0`
orientation, constant simplicial sets, universe polymorphism, standard axioms,
and the absence of stronger topological or global-instance claims.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Opposite

open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace EdgewiseResolutionWeakEquivalenceTests

section Rows

variable (X : SSet.{u})

/-- The row augmentation used by the weak-equivalence proof is literally the
corresponding transposed component. -/
example (q : SimplexCategoryᵒᵖ) :
    (SSet.edgewiseResolutionRow X q).hom =
      (SSet.simplicialTransposeFunctor.map
        (SSet.edgewiseResolution X).hom).app q :=
  SSet.edgewiseResolutionRow_hom X q

example (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences
      ((SSet.simplicialTransposeFunctor.map
        (SSet.edgewiseResolution X).hom).app q) :=
  SSet.edgewiseResolutionRow_mem_realizationWeakEquivalences X q

example :
    SSet.realizationWeakEquivalences
      ((SSet.simplicialTransposeFunctor.map
        (SSet.edgewiseResolution X).hom).app
          (Opposite.op (SimplexCategory.mk 0))) :=
  SSet.edgewiseResolutionRow_mem_realizationWeakEquivalences X
    (Opposite.op (SimplexCategory.mk 0))

example :
    SSet.realizationWeakEquivalences
      ((SSet.simplicialTransposeFunctor.map
        (SSet.edgewiseResolution X).hom).app
          (Opposite.op (SimplexCategory.mk 1))) :=
  SSet.edgewiseResolutionRow_mem_realizationWeakEquivalences X
    (Opposite.op (SimplexCategory.mk 1))

example :
    SSet.realizationWeakEquivalences
      ((SSet.simplicialTransposeFunctor.map
        (SSet.edgewiseResolution X).hom).app
          (Opposite.op (SimplexCategory.mk 2))) :=
  SSet.edgewiseResolutionRow_mem_realizationWeakEquivalences X
    (Opposite.op (SimplexCategory.mk 2))

end Rows

section DiagonalAndRawMap

variable (X : SSet.{u})

example :
    SSet.realizationWeakEquivalences
      (SSet.simplicialDiagonalFunctor.map
        (SSet.edgewiseResolution X).hom) :=
  SSet.edgewiseResolutionDiagonalAugmentation_mem_realizationWeakEquivalences X

example :
    SSet.realizationWeakEquivalences (SSet.esdComparison.app X) :=
  SSet.esdComparison_mem_realizationWeakEquivalences X

/-- The resolution augmentation still selects the target vertex `δ 0`, not
the source vertex `δ 1`. -/
example (x : X.obj (Opposite.op (SimplexCategory.mk 1))) :
    ((SSet.edgewiseResolution X).hom.app
      (Opposite.op (SimplexCategory.mk 0))).app
        (Opposite.op (SimplexCategory.mk 0)) x =
      X.δ 0 x := by
  rw [SSet.edgewiseResolution_hom_app_app]
  change X.map (SimplexCategory.edgewiseRightInclusion.app
    (SimplexCategory.mk 0)).op x = _
  rw [SimplexCategory.edgewiseRightInclusion_app_zero]
  rfl

end DiagonalAndRawMap

section Constant

example (A : Type u) :
    SSet.realizationWeakEquivalences
      (SSet.esdComparison.app
        ((SimplicialObject.const (Type u)).obj A)) :=
  SSet.esdComparison_mem_realizationWeakEquivalences _

end Constant

section Universes

variable (X₀ : SSet.{0}) (X₁ : SSet.{1})

example :
    SSet.realizationWeakEquivalences (SSet.esdComparison.app X₀) :=
  SSet.esdComparison_mem_realizationWeakEquivalences X₀

example :
    SSet.realizationWeakEquivalences (SSet.esdComparison.app X₁) :=
  SSet.esdComparison_mem_realizationWeakEquivalences X₁

example :
    SSet.realizationWeakEquivalences
      ((SSet.simplicialTransposeFunctor.map
        (SSet.edgewiseResolution X₁).hom).app
          (Opposite.op (SimplexCategory.mk 2))) :=
  SSet.edgewiseResolutionRow_mem_realizationWeakEquivalences X₁
    (Opposite.op (SimplexCategory.mk 2))

end Universes

section Nonclaims

/- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.edgewiseResolutionExtraDegeneracy

/- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.levelwiseDiscreteRealizationIso

/- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.edgewiseResolutionIteratedRealizationEquiv

/- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.edgewiseResolutionOuterRows_mem_realizationWeakEquivalences

/- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.esdComparison_stageEquivalence

example : True := by
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory SSet.{u} := inferInstance
  trivial

end Nonclaims

#print axioms SSet.edgewiseResolutionRow_mem_realizationWeakEquivalences
#print axioms
  SSet.edgewiseResolutionDiagonalAugmentation_mem_realizationWeakEquivalences
#print axioms SSet.esdComparison_mem_realizationWeakEquivalences

end EdgewiseResolutionWeakEquivalenceTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
