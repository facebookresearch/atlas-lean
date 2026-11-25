/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NonarchimedeanModelComparison

/-!
# Actual nonarchimedean intersection and J functionals

The trivial metric uses the actual projection to the polarized variety.
The mixed intersection and J are computed from the same compactified
model polarization, exponent and base volume as the existing energy.
Common-model invariance is a separate comparison request.

Reference: Boucksom--Hisamoto--Jonsson, arXiv:1504.06568v3, Section 7.2
and Proposition 7.24. J is V^-1 (phi . phi_triv^n) minus E.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NonarchimedeanIntersectionFunctionals

open CategoryTheory _root_.AlgebraicGeometry
open LogPairs NonarchimedeanCartierModels NonarchimedeanModelComparison

variable {k : Type} [Field k] {n : ℕ} {P : LogPair k n}
  {L : P.variety.X.left.Modules}

/-- The actual trivial polarization pulled to the common model. -/
def trivialModelLine (M : VerticalModel P L) : M.model.X.left.Modules :=
  (Scheme.Modules.pullback (baseProjection M).left).obj L

/-- The trivial polarization on the model is a line bundle. -/
theorem trivialModelLine_isLineBundle (M : VerticalModel P L) :
    CoherentCurveLinearSeries.IsLineBundle (trivialModelLine M) :=
  M.polarization.pullback _

/-- The native mixed intersection with the n trivial factors. -/
def mixedTrivial (M : VerticalModel P L) : ℝ :=
  haveI := M.properOverField
  haveI := M.baseProper
  DivisorDynamics.mixedIntersection M.model.X (n + 1) M.model.dimension.le
    (fun i => if i.val = 0 then modelPolarizationLine M
      else ⟨trivialModelLine M, trivialModelLine_isLineBundle M⟩) /
      ((M.exponent : ℝ) * baseVolume P (baseLine M))

/-- The source's actual J functional, with no assigned numerical operator. -/
def jFunctional (M : VerticalModel P L) : ℝ := mixedTrivial M - energy M

end MathlibExt.AlgebraicGeometry.NonarchimedeanIntersectionFunctionals
