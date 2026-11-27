/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.CStarAlgebra.NonUnitalRepresentation
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Public nonunital representation smoke tests

Use the representation factory on functions vanishing at infinity and on the
zero algebra. A separate zero-Hilbert witness checks that the public norm law
requires no nontrivial Hilbert-space instance. The factory's chosen space is
not required to coincide with that witness.
-/

noncomputable section
open scoped ZeroAtInfty
open MathlibExt.Analysis.CStarAlgebra.NonUnitalRepresentation
namespace NonUnitalRepresentationSmoke

-- This coefficient algebra is genuinely nonunital; the test uses its actual
-- C-star structure and the factory's actual Hilbert data.
example (f : C₀(ℝ, ℂ)) :
    ‖(faithfulHilbertRepresentationData C₀(ℝ, ℂ)).representation f‖ = ‖f‖ :=
  (faithfulHilbertRepresentationData C₀(ℝ, ℂ)).norm_representation f

-- The public factory also exposes an actual star homomorphism, so its zero
-- coefficient acts as the zero endomorphism without a unitality assumption.
example : (faithfulHilbertRepresentationData C₀(ℝ, ℂ)).representation 0 = 0 :=
  map_zero _

local instance : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
local instance : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ

private abbrev ZeroCoefficients := CStarMatrix (Fin 0) (Fin 0) ℂ
private abbrev ZeroHilbert := EuclideanSpace ℂ (Fin 0)

/-- Empty rows force equality of all matrices in the actual zero coefficient algebra. -/
private instance zeroCoefficientsSubsingleton : Subsingleton ZeroCoefficients where
  allEq a b := by
    apply CStarMatrix.ext
    intro i j
    exact Fin.elim0 i

-- Zero square matrices give an actual zero coefficient algebra. The canonical
-- factory remains usable and faithful on that algebra.
example : Function.Injective
    (faithfulHilbertRepresentationData ZeroCoefficients).representation :=
  (faithfulHilbertRepresentationData ZeroCoefficients).injective_representation

/-- An explicit zero-algebra representation on the zero Hilbert space. -/
private def zeroData : FaithfulHilbertRepresentationData ZeroCoefficients where
  space := ZeroHilbert
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  representation := 0
  injective_representation := fun _ _ _ => Subsingleton.elim _ _

-- This forces the public norm proof through the zero-Hilbert operator algebra,
-- covering the missing C-star endomorphism instance from the native failure.
example (a : ZeroCoefficients) : ‖zeroData.representation a‖ = ‖a‖ :=
  zeroData.norm_representation a

-- The norm equality agrees with the actual zero coefficient norm rather than
-- introducing an independent norm or a nonzero-space premise.
example (a : ZeroCoefficients) : ‖zeroData.representation a‖ = 0 := by
  rw [zeroData.norm_representation]
  have ha : a = 0 := Subsingleton.elim _ _
  rw [ha, norm_zero]

end NonUnitalRepresentationSmoke
