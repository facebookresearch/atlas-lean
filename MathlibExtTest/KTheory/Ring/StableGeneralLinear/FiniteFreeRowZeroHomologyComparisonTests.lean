/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowZeroHomologyComparison

noncomputable section

open CategoryTheory
open AlgebraicKTheory.StableGL

universe u

variable (R : Type u) [Ring R] (A : AddCommGrpCat.{u}) (q : ℕ)

example : Function.Surjective (finiteFreeRowIntrinsicHomologyComparison R A q) :=
  finiteFreeRowIntrinsicHomologyComparison_surjective R A q

example : IsIso (finiteFreeRowIntrinsicHomologyComparison R A q) :=
  finiteFreeRowIntrinsicHomologyComparison_isIso R A q

example : IsIso (finiteFreeRowStableHomologyComparison R A q) :=
  finiteFreeRowStableHomologyComparison_isIso R A q

example : IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A).map
    (finiteFreeRowStableZeroComparison R)) :=
  finiteFreeRowStableZeroComparison_homology_isIso R A q

example : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor q).map
    (finiteFreeRowStableZeroComparison R)) :=
  finiteFreeRowStableZeroComparison_integral_isIso R q

example (k : ℕ) : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor k).map
    (finiteFreeRowStableZeroComparison (Matrix (Fin 2) (Fin 2) ℤ))) :=
  finiteFreeRowStableZeroComparison_integral_isIso (Matrix (Fin 2) (Fin 2) ℤ) k

end
