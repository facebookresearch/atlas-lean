/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedFibreClosingPaths

/-!
The same isotropic path with identity comparison must give the zero
normalized loop. This detects the degeneracy subtraction in the
source concatenation h · id · h⁻¹.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.DerivedIsotropicResidues

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedIsotropicResidues
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k}
    {D : AffineDRSystem Q} {NC : NegativeCyclicDiagram D.functor (2 : ℤ)} {X : Prestack k}
    {G : GlobalNCModel D 2 NC X} {n : ℤ} {ω : ClosedForm G n}

/-- The actual identity-comparison residue data, retaining the same nonconstant isotropic path. -/
def identityComparison (h : IsotropicPath G n ω) : ResiduePaths G n where
  left := ω
  right := ω
  first := h
  comparison := SSet.Edge.id ω
  second := h

/-- Its complete normalized edge vanishes, including the degeneracy term. -/
example (h : IsotropicPath G n ω) : residueTerm (identityComparison h) = 0 := by
  change (show (closedModules G n) _⦋1⦌ from h.edge) +
    (closedModules G n).σ 0 (show (closedModules G n) _⦋0⦌ from ω) -
      (show (closedModules G n) _⦋1⦌ from h.edge) -
        (closedModules G n).σ 0 (show (closedModules G n) _⦋0⦌ from ω) = 0
  abel

end MathlibExtTest.AlgebraicGeometry.DerivedIsotropicResidues
