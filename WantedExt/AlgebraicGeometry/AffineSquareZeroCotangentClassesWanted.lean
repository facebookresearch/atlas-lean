/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AffineSquareZeroCotangentClasses

/-!
# Native extension-class comparison requests

The actual polynomial cotangent, extension kernel and two lifted-face
formula are fixed in MathlibExt. These requests integrate the completed
cotangent/extension classification and independence into those native
carriers. No arbitrary arrow L to I[1] is accepted as an extension class.
Source: Stacks Project 0GPU,08RB,08SP; AxiomMath/Stacks,
c496df0d9beea9deaeabcea8492605f9a0a2313b, Apache2.0,
Deformation/RingThickening/{CotangentLift,CotangentExtComparison,
CotangentObstructionCocycle,CotangentObstructionClasses}.lean.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.AffineSquareZeroCotangentClassesWanted

open _root_.MathlibExt.AlgebraicGeometry
open GeometricCotangentComplex AffineSquareZeroCotangentClasses

def_wanted nativeSquareZeroCotangentClass (k A : Type) [CommRing k] [CommRing A] [Algebra k A]
    (R : PolynomialResolution k A) (E : Extension k A) :
    Σ L : PolynomialLift R E, NormalizedCochain R E L

theorem_wanted nativeSquareZeroCotangentClassIndependent (k A : Type)
    [CommRing k] [CommRing A] [Algebra k A] (R : PolynomialResolution k A) (E : Extension k A) :
    Independent R E

theorem_wanted nativeSquareZeroCotangentClassNaturality (k A : Type)
    [CommRing k] [CommRing A] [Algebra k A] (R : PolynomialResolution k A)
    (E F : Extension k A) (u : ExtensionMap E F) : Natural R E u

end WantedExt.AlgebraicGeometry.AffineSquareZeroCotangentClassesWanted
