/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.Certificate
import Code.Exact3D.CriticalExponentCriteria










namespace StatMech
namespace Exact3D

namespace RGCertificate



theorem rgToExponentBridge_of_hasCriticalNu {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (hν : HasCriticalNu M correlationLength C.predictedExponent) :
    C.RGToExponentBridge correlationLength :=
  C.bridge_of_hasCriticalNu correlationLength hν




theorem rgToExponentBridge_of_eventually_exact_power {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    C.RGToExponentBridge correlationLength := by
  exact hasCriticalNu_of_eventually_exact_power M correlationLength C.predictedExponent hξ



theorem rgToExponentBridge_of_exact_power_on_Ioo {ι : Type*}
    {M : CriticalModel ι} (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hξ :
      ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC →
        correlationLength β =
          Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    C.RGToExponentBridge correlationLength := by
  refine rgToExponentBridge_of_eventually_exact_power C correlationLength ?_
  filter_upwards [Ioo_mem_nhdsLT (by linarith : M.betaC - δ < M.betaC)] with β hβ
  exact hξ β hβ

end RGCertificate

end Exact3D
end StatMech
