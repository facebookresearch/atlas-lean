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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Classes
public import CSLibExt.Computability.Complexity.Smolensky


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

/-- **Razborov: majority is not in AC0[mod 2].** The majority language (more `true` than
`false` bits) is not in `AC0[mod 2]`: no polynomial-size, constant-depth circuit family with
AND/OR/NOT gates and `MOD₂` gates computes majority (A. A. Razborov, "Lower bounds on the size
of bounded depth networks over a complete basis with logical addition", Mat. Zametki 41
(1987), 598-607; English translation Math. Notes 41 (1987), 333-338). Razborov approximates
each gate by a low-degree polynomial over `𝔽₂` and shows that majority has no such
approximation. Smolensky extended the method to `MOD_p` gates for a prime `p`, which cannot
compute `MOD_q` when `q` is not a power of `p`; `smolensky` is the case `p = 3`, `q = 2`. -/
public theorem_wanted razborov_majority_not_in_ac0_mod_two :
    majorityDec ∉ AC0Mod 2

end MetaMathlibExt.Complexity.KeyTheorems.Smolensky
