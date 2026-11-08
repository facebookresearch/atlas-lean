/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Parity is not in AC0

Source:
M. Furst, J. Saxe, and M. Sipser, "Parity, circuits, and the polynomial-time hierarchy",
Mathematical Systems Theory 17 (1984), 13-27; M. Ajtai, "Σ₁¹-formulae on finite structures",
Annals of Pure and Applied Logic 24 (1983), 1-48; J. Håstad, "Almost optimal lower bounds for
small depth circuits", Proceedings of the Eighteenth Annual ACM Symposium on Theory of
Computing (STOC 1986), 6-20.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.ParityNotInAC0

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Parity is not in AC0

The parity language is not in `AC0`: no polynomial-size, constant-depth, unbounded fan-in
AND/OR/NOT circuit family computes parity. `AC0` and `parityDec` are the shared definitions.
-/

/-- **Parity is not in AC0.** Source: M. Furst, J. Saxe, and M. Sipser, "Parity, circuits, and
the polynomial-time hierarchy", Mathematical Systems Theory 17 (1984), 13-27; M. Ajtai,
"Σ₁¹-formulae on finite structures", Annals of Pure and Applied Logic 24 (1983), 1-48; J.
Håstad, "Almost optimal lower bounds for small depth circuits", Proceedings of the
Eighteenth Annual ACM Symposium on Theory of Computing (STOC 1986), 6-20. -/
public theorem_wanted parity_not_in_ac0 :
    parityDec ∉ AC0

end MetaMathlibExt.Complexity.KeyTheorems.ParityNotInAC0
