/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.HodgeModuleCurveExtensionMinimalExtensionNoBoundaryQuotient
import Mathlib.Tactic.Push

/-!
# Strict stable submodules of the minimal extension

For unipotent rational monodromy `(T - 1)^b = 0` with `b > 0` and the logarithm
truncated below degree `b`, a strict connection-stable submodule misses every
parameter multiple of some section of the minimal extension.

Sources: M. Saito, *Modules de Hodge polarisables*, Publ. RIMS 24 (1988), §3.2;
C. Schnell, *An overview of Morihiko Saito's theory of mixed Hodge modules*,
§18, Parts 1 and 2.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry
namespace HodgeModuleCurveExtensionMinimalExtensionNoBoundaryQuotient

open CategoryTheory
open MathlibExt.Geometry.RationalHodgeStructures
open MathlibExt.Geometry.LimitingHodgeStructures
open MathlibExt.AlgebraicGeometry.HodgeModuleCurveExtension
open WantedExt.AlgebraicGeometry.HodgeModuleCurveExtensionWanted

example
    (V : ModuleCat.{0} ℚ) [FiniteDimensional ℚ V]
    (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) (w : ℤ)
    (H : PolarizedPeriodVariation C e w) (b : ℕ) (hb : 0 < b)
    (hT : (H.rationalDeck.toLinearMap - 1) ^ b = 0)
    (P : Submodule LocalPowerSeries (Fin r → LocalMeromorphicSeries))
    (hP : P < minimalModule C e H b)
    (hstable : ∀ v, v ∈ P → formalConnection C e H b v ∈ P) :
    ∃ v, v ∈ minimalModule C e H b ∧ ∀ n : ℕ,
      (algebraMap LocalPowerSeries LocalMeromorphicSeries PowerSeries.X) ^ n • v ∉ P := by
  classical
  by_contra h
  push Not at h
  exact hP.ne
    (minimal_extension_no_boundary_quotient
      V C r e w H b hb hT P hP.le hstable h)

end HodgeModuleCurveExtensionMinimalExtensionNoBoundaryQuotient
end MathlibExtTest.AlgebraicGeometry
