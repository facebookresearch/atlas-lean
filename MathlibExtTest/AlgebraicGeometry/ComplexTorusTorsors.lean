/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ComplexTorusTorsors

@[expose] public section

/-! # Tests for `MathlibExt.AlgebraicGeometry.ComplexTorusTorsors` -/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.ComplexTorusTorsors

namespace MathlibExtTest.AlgebraicGeometry.ComplexTorusTorsors

/-- `Gm` carries Mathlib's group-object structure, and acts on itself. -/
example : GrpObj Gm := inferInstance

example : Gm ⊗ Gm ⟶ Gm := MonObj.mul

example : ModObj Gm Gm := ModObj.regular Gm

/-- A torsor's quotient map is invariant on complex points, for the analytic
action of that torsor. -/
example {X Y : ComplexScheme} (A : ModObj Gm X) (q : X ⟶ Y) [T : TorusTorsor A q] (g : ℂˣ)
    (x : space X) :
    letI := T.mulAction
    spaceMap q (g • x) = spaceMap q x :=
  quotientInvariant A q g x

/-- Its Borel augmentation induces a map on Betti cohomology. -/
example {X Y : ComplexScheme} (A : ModObj Gm X) (q : X ⟶ Y) [TorusTorsor A q] (n : ℤ) :
    MathlibExt.AlgebraicGeometry.BettiRealization.Cohomology (space Y) n →ₗ[ℚ]
      MathlibExt.AlgebraicGeometry.BettiRealization.Cohomology (torsorBorel A q) n :=
  MathlibExt.AlgebraicGeometry.BettiFunctoriality.cohomologyPullback (borelQuotientMap A q) n

/-- Two torsor structures on the same scheme have their own Borel models and
augmentations: the analytic action is selected by the torsor, not by the
underlying space. -/
example {X Y Y' : ComplexScheme} (A B : ModObj Gm X) (q : X ⟶ Y) (r : X ⟶ Y')
    [TorusTorsor A q] [TorusTorsor B r] :
    (torsorBorel A q ⟶ space Y) × (torsorBorel B r ⟶ space Y') :=
  (borelQuotientMap A q, borelQuotientMap B r)

/-- Equivariant restriction along an equivariant map of spaces with continuous
actions. -/
example {Z : TopCat.{0}} [MulAction ℂˣ Z] [ContinuousSMul ℂˣ Z] (n : ℤ) :=
  equivariantRestriction (𝟙 Z) (fun _ _ => rfl) n

end MathlibExtTest.AlgebraicGeometry.ComplexTorusTorsors

end
