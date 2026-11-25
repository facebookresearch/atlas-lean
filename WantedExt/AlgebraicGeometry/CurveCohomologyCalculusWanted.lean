/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CurveCohomologyCalculus

@[expose] public section

/-!
# Degree additivity on proper curves

For invertible modules `L`, `M` on a proper curve over a field,
`deg (L ⊗ M) = deg L + deg M`, where the degree is `χ(L) - χ(𝒪)`.

Reference: Stacks Project, Tag 0AYX.
-/

namespace WantedExt.AlgebraicGeometry.CurveCohomologyCalculusWanted

open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.CurveCohomologyCalculus

universe u

/-- The degree of line bundles on a proper curve is additive under tensor products. -/
public theorem_wanted isDegreeAdditive {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProperCurve f] (T : CurveTensorEulerInputs f) :
    IsDegreeAdditive f T

end WantedExt.AlgebraicGeometry.CurveCohomologyCalculusWanted
