/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Smolensky: parity is not in AC0[mod 3]

Source:
R. Smolensky, "Algebraic methods in the theory of lower bounds for Boolean circuit complexity",
Proceedings of the Nineteenth Annual ACM Symposium on Theory of Computing (STOC 1987), 77-82.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Smolensky

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Smolensky: parity is not in AC0[mod 3]

The parity language is not in `AC0[mod 3]`: no polynomial-size, constant-depth circuit family
with AND/OR/NOT gates and `MOD₃` gates computes parity. `AC0Mod 3` is the shared class with
only modulus-`3` `mod` gates.
-/

/-- **Smolensky: parity is not in AC0[mod 3].** Source: R. Smolensky, "Algebraic methods in
the theory of lower bounds for Boolean circuit complexity", Proceedings of the Nineteenth
Annual ACM Symposium on Theory of Computing (STOC 1987), 77-82. -/
public theorem_wanted smolensky :
    parityDec ∉ AC0Mod 3

end MetaMathlibExt.Complexity.KeyTheorems.Smolensky
