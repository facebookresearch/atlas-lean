/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RelativeWittGeneralLinearOrbits

/-!
# Native Witt source boundary and axiom probes

The zero perfect algebra is an actual residue-algebra test. The public
functor and geometric-map definitions are probed independently of every
Wanted constructor; these probes do not claim the constructors are proved.
-/

set_option autoImplicit false

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.RelativeWittLoopTests

private def zeroTest (p : ℕ) [Fact p.Prime] : PerfectAlgebra p (ZMod p) :=
  letI : Algebra (ZMod p) (ZMod 1) :=
    (show ZMod p →+* ZMod 1 from
      { toFun := fun _ ↦ 0
        map_zero' := rfl
        map_one' := Subsingleton.elim _ _
        map_add' := fun _ _ ↦ Subsingleton.elim _ _
        map_mul' := fun _ _ ↦ Subsingleton.elim _ _ }).toAlgebra
  ⟨CommAlgCat.of (ZMod p) (ZMod 1), by
    constructor
    · exact Subsingleton.elim _ _
    · constructor
      · intro x y _h
        exact Subsingleton.elim _ _
      · intro y
        exact ⟨0, Subsingleton.elim _ _⟩⟩

private theorem includes_zero_algebra (p : ℕ) [Fact p.Prime] :
    ∃ R : PerfectAlgebra p (ZMod p), Subsingleton R.obj :=
  ⟨zeroTest p, inferInstanceAs (Subsingleton (ZMod 1))⟩

section GeneralLinearCoordinates

open MathlibExt.AlgebraicGeometry.NativeGeneralLinearSchemeCoordinates
open MathlibExt.AlgebraicGeometry.AlgebraicGroupPointRepresentations

/-- The coordinate condition pins the point dictionary: any two realizations give the same matrix
for every point, so composing a dictionary with inversion is not another realization. -/
example (B : Type) [CommRing B] (n : ℕ) (P P' : PointRealization B n) (A : CommAlgCat.{0} B)
    (g : (testSchemes B).obj (Opposite.op A) ⟶ scheme B n) (i j : Fin n) :
    (letI := P.group;
      ((show GL (Fin n) A from (P.points.hom.app A).hom g) : Matrix (Fin n) (Fin n) A) i j) =
      (letI := P'.group;
        ((show GL (Fin n) A from (P'.points.hom.app A).hom g) : Matrix (Fin n) (Fin n) A) i j) :=
  (P.coordinates A g i j).trans (P'.coordinates A g i j).symm

end GeneralLinearCoordinates

#print axioms includes_zero_algebra
#print axioms MathlibExt.AlgebraicGeometry.RelativeWittLatticeModels.coordinateSpan
#print axioms MathlibExt.AlgebraicGeometry.RelativeWittLatticeModels.ScalarExtension.functor
#print axioms MathlibExt.AlgebraicGeometry.RelativeWittLatticeModels.ScalarExtension.transition
#print axioms MathlibExt.AlgebraicGeometry.RelativeWittLatticeModels.matrixTransform
#print axioms MathlibExt.AlgebraicGeometry.RelativeWittSpaceStages.relativeMap
#print axioms MathlibExt.AlgebraicGeometry.RelativeWittIndRealizations.boundedDiagram
#print axioms MathlibExt.AlgebraicGeometry.RelativeWittIndRealizations.pointDictionary
#print axioms MathlibExt.AlgebraicGeometry.NativeGeneralLinearSchemeCoordinates.scheme
#print axioms MathlibExt.AlgebraicGeometry.RelativeWittGeneralLinearOrbits.loopMatrix
