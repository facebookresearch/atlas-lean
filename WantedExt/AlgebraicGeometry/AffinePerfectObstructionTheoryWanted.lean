/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheory
public import MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheoryPolynomialLiftIndependence
public import MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheoryPresentationObstructionEqZeroIff

/-!
# An actual affine POT-to-deformation comparison

The morphism is into the computed full cotangent complex of a genuine
polynomial resolution. Its source has actual finite-free terms in degrees
−1 and 0. The cocycle is fixed on pure differentials by the lifted simplicial
face difference; the coefficient is the actual conormal kernel module of
the square-zero extension. Its composition with the POT map is the displayed
obstruction class, and lifting means an actual algebra section of the quotient.

This is an affine, finite-free package. It does not replace the full cotangent
complex by an arbitrarily named object or assume a lifting criterion as a
definition. Existing generic square-zero and cotangent constructions are
credited in the completed core. Reference: Behrend--Fantechi, *The intrinsic
normal cone*, §4, https://arxiv.org/abs/alg-geom/9601010.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AffinePerfectObstructionTheoryWanted

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
open MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheory

variable {k B : Type} [Field k] [CommRing B] [Algebra k B]

/-- The obstruction cocycle of a lift across a square-zero extension: for a field $k$, a
$k$-algebra $B$ with a polynomial resolution $\varepsilon : P_\bullet \to B$, a surjection of
$k$-algebras $Q \to B$ whose kernel $I$ satisfies $I^2 = 0$, and a $k$-algebra map
$L : P_0 \to Q$ lifting $\varepsilon_0$, a morphism of complexes of $B$-modules from
`affineComplex R`, the complex $\Omega_{P_\bullet/k} \otimes_{P_\bullet} B$, to the conormal
module $I/I^2$ placed in degree $-1$, whose degree $-1$ component sends $1 \otimes dp$ to the
class of $L(d_0 p) - L(d_1 p)$ for every $p \in P_1$ (`CotangentExtensionCocycle`). -/
public def_wanted extensionCocycle (R : PolynomialResolution k B)
    (Q : Algebra.Extension.{0} k B) (_squareZero : Q.ker ^ 2 = ⊥)
    (L : PolynomialLift R Q) : CotangentExtensionCocycle R Q L

/-- The normalized class under a genuine perfect obstruction theory detects
actual algebra lifts of the identity affine point across the extension. -/
public theorem_wanted vanishing_iff_lift [Algebra.FiniteType k B]
    (R : PolynomialResolution k B) (T : PerfectObstructionTheory R)
    (Q : Algebra.Extension.{0} k B) (_squareZero : Q.ker ^ 2 = ⊥)
    (L : PolynomialLift R Q) (C : CotangentExtensionCocycle R Q L) :
    obstructionClass T C = 0 ↔ Nonempty (Liftings Q)

end WantedExt.AlgebraicGeometry.AffinePerfectObstructionTheoryWanted
