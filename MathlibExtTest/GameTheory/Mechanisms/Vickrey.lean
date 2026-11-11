/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.Mechanisms.Vickrey

/-- Boundary check: with two bidders, bidder `0` with valuation `5`
gains nothing by deviating from truthful bidding, whatever the other
bid profile was. -/
example (b : Fin 2 → ℝ) :
    vickreyUtility 5 b 0 ≤ vickreyUtility 5 (Function.update b 0 5) 0 :=
  vickrey_truthful_dominant (by norm_num) 0 5 b

/-- Boundary check: truthful bidding never loses money for a
nonnegative valuation. -/
example (b : Fin 2 → ℝ) : 0 ≤ vickreyUtility 5 (Function.update b 0 5) 0 :=
  vickrey_ir (by norm_num) 0 (by norm_num) b
