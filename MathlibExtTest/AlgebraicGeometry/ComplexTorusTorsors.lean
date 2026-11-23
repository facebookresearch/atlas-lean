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

/-- `Gm` carries Mathlib's group-object structure. -/
example : GrpObj Gm := inferInstance

example : Gm ⊗ Gm ⟶ Gm := MonObj.mul

/-- A torsor's quotient map is invariant on complex points, and its Borel
augmentation and equivariant restriction maps are available. -/
example {X Y : ComplexScheme} (A : GmAction X) (q : X ⟶ Y) [TorusTorsor A q] (g : ℂˣ)
    (x : space X) : spaceMap q (g • x) = spaceMap q x :=
  quotientInvariant A q g x

example {X Y : ComplexScheme} (A : GmAction X) (q : X ⟶ Y) [TorusTorsor A q] (n : ℤ) :
    MathlibExt.AlgebraicGeometry.BettiRealization.Cohomology (space Y) n →ₗ[ℚ]
      MathlibExt.AlgebraicGeometry.BettiRealization.Cohomology
        (MathlibExt.Topology.ContinuousBorel.borel ℂˣ (space X)) n :=
  MathlibExt.AlgebraicGeometry.BettiFunctoriality.cohomologyPullback (borelQuotientMap A q) n

example {X : ComplexScheme} (A : GmAction X) (q : X ⟶ X) [TorusTorsor A q] (n : ℤ) :=
  equivariantRestriction (𝟙 (space X)) (fun _ _ => rfl) n

end MathlibExtTest.AlgebraicGeometry.ComplexTorusTorsors

end
