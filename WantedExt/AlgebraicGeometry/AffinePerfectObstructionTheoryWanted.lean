/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheory

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

/-- Construct the actual normalized cochain cocycle across a square-zero
extension, rather than choosing an unconstrained class in an obstruction group. -/
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

/-- The class in the actual derived obstruction group is independent of the
chosen polynomial lift, with the explicit cocycle normalization retained. -/
public theorem_wanted polynomial_lift_independence
    (R : PolynomialResolution k B) (T : PerfectObstructionTheory R)
    (Q : Algebra.Extension.{0} k B) (_squareZero : Q.ker ^ 2 = ⊥)
    (L L' : PolynomialLift R Q)
    (C : CotangentExtensionCocycle R Q L) (C' : CotangentExtensionCocycle R Q L') :
    obstructionClass T C = obstructionClass T C'

open MathlibExt.AlgebraicGeometry.AffineObstructionComplexes in
/-- For a perfect obstruction theory relative to the naive cotangent complex of a presentation
`G` of `B` and a square-zero extension `Q` of a `B`-algebra `A`, the obstruction attached to a
morphism of extensions from `G` to `Q` vanishes exactly when `B → A` lifts to `Q`
(Behrend--Fantechi, Theorem 4.5, affine presentation form). -/
public theorem_wanted presentation_obstruction_eq_zero_iff {n : ℕ}
    {G : Algebra.Generators k B (Fin n)} (T : PresentationTheory G)
    {A : Type} [CommRing A] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
    (Q : Algebra.Extension.{0} k A) (_squareZero : Q.ker ^ 2 = ⊥)
    (h : Algebra.Extension.Hom G.toExtension Q) :
    obstruction T.model Q h T.comparison = 0 ↔ HasLift (B := B) Q

end WantedExt.AlgebraicGeometry.AffinePerfectObstructionTheoryWanted
