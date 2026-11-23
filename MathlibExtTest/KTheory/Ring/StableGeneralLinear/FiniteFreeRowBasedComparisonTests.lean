/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowBasedComparison

noncomputable section

open CategoryTheory
open AlgebraicKTheory.StableGL

universe u

variable (R : Type u) [Ring R]

example : finiteFreeRowBasedZeroComparison R (ordinaryBGLBasepoint R) =
    SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R) :=
  finiteFreeRowBasedZeroComparison_basepoint R

example (t : unitInterval) :
    finiteFreeRowBasedZeroComparisonHomotopy R (t, ordinaryBGLBasepoint R) =
      finiteFreeRowStableZeroComparisonUnitPath R t :=
  finiteFreeRowBasedZeroComparison_homotopy_basepoint R t

example (q : ℕ) : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor q).map
    (finiteFreeRowBasedZeroComparison R)) :=
  finiteFreeRowBasedZeroComparison_integral_isIso R q

end
