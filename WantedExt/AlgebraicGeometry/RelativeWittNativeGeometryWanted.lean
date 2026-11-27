/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RelativeWittGeneralLinearOrbits

/-!
# Native relative Witt-lattice and ind-space construction requests

Source: Zhu, arXiv:1407.8519v3, formula (0.1.2), pp. 2--3,
Sections 0.5 and 1.2.1, pp. 6--9, Theorems 0.1 and 1.4,
and Proposition 1.20, p. 16. The residue field remains an arbitrary
perfect characteristic-p field. The coefficient ring is the original
complete finite totally ramified Witt DVR; every map is the original
Witt tensor map or its uniformizer localization.

The generic general-linear point realization is the normalized native
integration dictionary for its determinant-localized coordinate scheme.
The lattice and ind-space requests retain the exact functors, native
matrix images, every perfect-algebra test including zero, actual proper
algebraic-space deperfections, and closed transition maps. The algebraic
space carrier and etale quotient descent are completed source inputs.

These requests do not assert the construction or its proof. Geometric
Satake, equivariant perverse categories, coefficient/dual-group and
general reductive Schubert dictionaries are separate interfaces.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeWittNativeGeometry

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.RelativeWittLatticeModels
open MathlibExt.AlgebraicGeometry.RelativeWittCoefficientDVRModels
open MathlibExt.AlgebraicGeometry.RelativeWittSpaceStages
open MathlibExt.AlgebraicGeometry.RelativeWittIndRealizations
open MathlibExt.AlgebraicGeometry.RelativeWittGeneralLinearOrbits
open MathlibExt.AlgebraicGeometry.NativeGeneralLinearSchemeCoordinates

/-- Realize the fixed determinant-localized coordinate scheme on every algebra. -/
public def_wanted generalLinearPointRealization (B : Type) [CommRing B] (n : ℕ) :
    PointRealization B n

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
  (B : Type) [CommRing B] [IsDomain B] [Algebra (WittVector p k) B] (pi : B)
  (n : ℕ)

/-- Construct the original finite-projective lattice scalar-extension functor. -/
public def_wanted latticeScalarExtension (C : CoefficientData p k B pi) :
    ScalarExtension p k B pi n

variable (D : ScalarExtension p k B pi n)

/-- Construct actual matrix images, positive-loop stability and all map squares. -/
public def_wanted latticeMatrixAction (C : CoefficientData p k B pi) :
    MatrixAction p k B pi n D

/-- Represent all actual bounded lattices by increasing proper ind-perfections. -/
public def_wanted latticeIndSpaceStages (C : CoefficientData p k B pi) :
    IndLatticeStages p k B pi n D

/-- The original bounded inclusions exhaust the actual full lattice presheaf. -/
public def_wanted boundedLatticeUnion : IsColimit (boundedPresheafCocone D)

/-- The actual space-stage colimit equals the original fpqc lattice sheaf. -/
public def_wanted latticeIndRealization (S : IndLatticeStages p k B pi n D) :
    IndRealization S

variable (P : PointRealization B n) (A : MatrixAction p k B pi n D)

/-- The natural map on loops is their original matrix-translated standard lattice. -/
public def_wanted loopLatticeCoordinates (C : CoefficientData p k B pi) :
    OrbitCoordinates p k B pi n P D A

/-- Normalize the fpqc loop quotient to the original finite-projective lattices. -/
public def_wanted generalLinearLatticeQuotient
    (C : CoefficientData p k B pi)
    (O : OrbitCoordinates p k B pi n P D A) : QuotientComparison p k B pi n P D A O

end WantedExt.AlgebraicGeometry.RelativeWittNativeGeometry
