/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyFiltration

/-! # Tests for the induced filtration on total homology -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantHomologyFiltrationTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (n : ℕ) (i : EInt) :
    (horizontalTotalHomologyFiltration K n).obj i =
      image (horizontalCompleteHomologyToTotal K n i) :=
  horizontalTotalHomologyFiltration_obj K n i

example (n : ℕ) :
    IsIso ((horizontalTotalHomologyFiltration K n).ι.app
      ((n : ℤ) : EInt)) :=
  horizontalTotalHomologyFiltration_exhaustive K n

example (n : ℕ) :
    IsIso (horizontalCompleteHomologyToTotal K n
      (((n : ℤ) + 1) : EInt)) :=
  horizontalCompleteHomologyToTotal_isIso_succ K n

example (a : ℤ) (ha : a < 0) (n : ℕ) :
    IsZero ((horizontalTotalHomologyFiltration K n).obj (a : EInt)) :=
  horizontalTotalHomologyFiltration_obj_isZero_of_neg K a ha n

example (p q : ℕ) :
    Mono (horizontalTotalHomologyFiltrationStepMap K p q) := inferInstance

example (p q : ℕ) :
    (ShortComplex.cokernelSequence
      (horizontalTotalHomologyFiltrationStepMap K p q)).ShortExact :=
  horizontalTotalHomologyFiltrationStepShortExact K p q

end HomologicalComplex₂.FirstQuadrantHomologyFiltrationTests

end
