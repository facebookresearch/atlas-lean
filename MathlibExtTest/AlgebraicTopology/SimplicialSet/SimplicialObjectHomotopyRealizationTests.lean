/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialObjectHomotopyRealization

/-!
# Tests for realization of combinatorial simplicial homotopies

These tests exercise the generic realized homotopy equivalence, its literal
forward map, realization weak-equivalence membership, a nontrivial standard
simplex extra degeneracy, and universe polymorphism.  Negative guards exclude
levelwise-discrete, iterated-realization, edgewise, and global-instance claims.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace SimplicialObjectHomotopyRealizationTests

private def idCompHomotopy (X : SSet.{u}) :
    SimplicialObject.Homotopy ((𝟙 X) ≫ 𝟙 X) (𝟙 X) := by
  simpa using SimplicialObject.Homotopy.refl (𝟙 X)

section Generic

variable (X : SSet.{u})

example : ContinuousMap.HomotopyEquiv
    (SSet.toTop.obj X) (SSet.toTop.obj X) :=
  SSet.realizedHomotopyEquivOfSimplicialObjectHomotopyEquiv
    X X (𝟙 X) (𝟙 X) (idCompHomotopy X) (idCompHomotopy X)

example :
    (SSet.realizedHomotopyEquivOfSimplicialObjectHomotopyEquiv
      X X (𝟙 X) (𝟙 X) (idCompHomotopy X) (idCompHomotopy X)).toFun =
        (SSet.toTop.map (𝟙 X)).hom := by
  simp

example : SSet.realizationWeakEquivalences (𝟙 X) :=
  SSet.realizationWeakEquivalences_of_simplicialObjectHomotopyEquiv
    (𝟙 X) (𝟙 X) (idCompHomotopy X) (idCompHomotopy X)

end Generic

section ExtraDegeneracy

variable {A : SimplicialObject.Augmented (Type u)}
  (ed : A.ExtraDegeneracy)

example : SSet.realizationWeakEquivalences A.hom :=
  ed.hom_mem_realizationWeakEquivalences

/-- The standard simplex extra degeneracy is a nonconstant reusable consumer
of the Type-valued theorem. -/
example (Δ : SimplexCategory) :
    SSet.realizationWeakEquivalences
      (SSet.Augmented.stdSimplex.obj Δ).hom :=
  SimplicialObject.Augmented.ExtraDegeneracy.hom_mem_realizationWeakEquivalences
    (SSet.Augmented.StandardSimplex.extraDegeneracy Δ)

end ExtraDegeneracy

section Universes

variable (X₀ : SSet.{0}) (X₁ : SSet.{1})

example : SSet.realizationWeakEquivalences (𝟙 X₀) :=
  SSet.realizationWeakEquivalences_of_simplicialObjectHomotopyEquiv
    (𝟙 X₀) (𝟙 X₀) (idCompHomotopy X₀) (idCompHomotopy X₀)

example : SSet.realizationWeakEquivalences (𝟙 X₁) :=
  SSet.realizationWeakEquivalences_of_simplicialObjectHomotopyEquiv
    (𝟙 X₁) (𝟙 X₁) (idCompHomotopy X₁) (idCompHomotopy X₁)

end Universes

section Nonclaims

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check SSet.levelwiseDiscreteRealizationIso

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check SSet.edgewiseResolutionRow_mem_realizationWeakEquivalences

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check SSet.iteratedRealizationHomotopyEquivOfSimplicialObjectHomotopy

end Nonclaims

#print axioms SSet.realizedHomotopyEquivOfSimplicialObjectHomotopyEquiv
#print axioms SSet.realizationWeakEquivalences_of_simplicialObjectHomotopyEquiv
#print axioms
  CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.hom_mem_realizationWeakEquivalences

end SimplicialObjectHomotopyRealizationTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
