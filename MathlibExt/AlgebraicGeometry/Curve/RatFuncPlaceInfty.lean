/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_RatFuncPlaceInfty.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.RatFunc.Valuation
public import MathlibExt.AlgebraicGeometry.Curve.Place
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The infinite place of a rational function field

This file defines the place at infinity of the rational function field `RatFunc K`.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain WithZero

namespace AlgebraicCurve

namespace RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

theorem nontrivial_valueGroup_inftyValuation :
    Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass (RatFunc.inftyValuation K))) := by
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  refine ⟨Units.mk0 (RatFunc.inftyValuation K RatFunc.X)
    (by rw [RatFunc.inftyValuation.X]; exact exp_ne_zero), ?_, ?_⟩
  · exact MonoidWithZeroHom.mem_valueGroup _ ⟨RatFunc.X, rfl⟩
  · rw [ne_eq, Units.ext_iff, Units.val_mk0, Units.val_one, RatFunc.inftyValuation.X]
    simp

def placeInfty : Place K (RatFunc K) :=
  haveI := nontrivial_valueGroup_inftyValuation K
  { toValuationSubring := (RatFunc.inftyValuation K).valuationSubring
    algebraMap_mem' := fun a => by
      rw [Valuation.mem_valuationSubring_iff]
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one (v := RatFunc.inftyValuation K) a
    ne_top' := by
      simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
      infer_instance
    isPrincipalIdealRing' :=
      (Valuation.valuationSubring_isDiscreteValuationRing
        (RatFunc.inftyValuation K)).toIsPrincipalIdealRing }

@[simp]
theorem placeInfty_toValuationSubring :
    (placeInfty K).toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := rfl

end RationalFunctionField

end AlgebraicCurve
