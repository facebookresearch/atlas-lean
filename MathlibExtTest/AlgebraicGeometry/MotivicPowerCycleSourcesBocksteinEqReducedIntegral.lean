/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MotivicPowerCycleSourcesBocksteinEqReducedIntegral

/-!
# Vanishing of the mod-ℓ Bockstein

The Bockstein comparison implies that a class with vanishing integral Bockstein
also has vanishing mod-ℓ Bockstein.

Source: Vladimir Voevodsky, *Reduced power operations in motivic cohomology*,
arXiv:math/0107109v1, Construction 5.3 and Sections 6/9.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicGeometry.MotivicPowerCycleSourcesBocksteinEqReducedIntegral

open CategoryTheory CategoryTheory.Limits MathlibExt.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels MotivicStandardSchemes
open NisnevichTransferModels EffectiveMotivicComplexModels PointedMotivicModels
open ReducedMotivicCohomologyModels MotivicBocksteinModels

noncomputable section

example {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D G} {S : TransferSheafificationModel D G}
  {T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R)} {N : NisTensorSystem k}
  (B : CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)
    (ell : ℕ) [Fact ell.Prime]
    (F : ReducedFreeNisSystem k) (X : PointedSpaces (k := k)) (p q : ℤ)
    (I : CoefficientConeSource B (integralSequence ell) q)
    (M : CoefficientConeSource B (modSequence ell) q)
    (u : ReducedCohomology B F X p q (ModCoefficients ell))
    (h : integralBockstein B ell F X p q I u = 0) :
    bockstein B ell F X p q M u = 0 := by
  rw [WantedExt.AlgebraicGeometry.MotivicPowerCycleSourcesWanted.bockstein_eq_reduced_integral
    B ell F X p q I M u, h]
  simp [ReducedMotivicCohomologyModels.coefficientMap]

end

end MathlibExtTest.AlgebraicGeometry.MotivicPowerCycleSourcesBocksteinEqReducedIntegral
