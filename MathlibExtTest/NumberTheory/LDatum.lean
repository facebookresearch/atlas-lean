/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LDatum

@[expose] public section

noncomputable section

open Complex Polynomial

namespace LanglandsTunnell

variable {ι : Type*} (D : LDatum ι)

-- `exactSource` consumers with the original binders.
example (s : ℂ) : ℂ := D.LFun s

example (s : ℂ) : ℂ := D.archFactor s

example : Prop := D.WellFormed

example : Prop := D.IsNice

example (Λ : ℂ → ℂ) : Prop := Complex.BoundedOnStrips Λ

-- Boundary: the empty bad factor is one, and empty bad data is bad data.
example (s : ℂ) : LDatum.badFactor 0 s = 1 :=
  LDatum.badFactor_zero s

example : LDatum.IsBadData 0 := LDatum.isBadData_zero

example (hC : D.gammaC = 0) (s : ℂ) :
    D.archFactor s = (D.gammaR.map fun μ => Gammaℝ (s + μ)).prod :=
  D.archFactor_of_gammaC_eq_zero hC s

end LanglandsTunnell
