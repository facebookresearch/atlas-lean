/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Majority is not in AC0

Source:
M. Ajtai, "Σ₁¹-formulae on finite structures", Annals of Pure and Applied Logic 24 (1983),
1-48; J. Håstad, "Almost optimal lower bounds for small depth circuits" (STOC 1986).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.MajorityNotInAC0

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Majority is not in AC0

The majority language is not in `AC0`: no polynomial-size, constant-depth, unbounded fan-in
AND/OR/NOT circuit family computes majority.
-/

/-- **Majority is not in AC0.** The majority language is not in the class $\mathsf{AC}^0$.

Source: M. Ajtai, "Σ₁¹-formulae on finite structures", Annals
of Pure and Applied Logic 24 (1983), 1-48; J. Håstad, "Almost optimal lower bounds for
small depth circuits" (STOC 1986). -/
public theorem_wanted majority_not_in_ac0 :
    majorityDec ∉ AC0

end MetaMathlibExt.Complexity.KeyTheorems.MajorityNotInAC0
