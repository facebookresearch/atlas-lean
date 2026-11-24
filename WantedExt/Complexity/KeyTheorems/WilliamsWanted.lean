/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Williams: NEXP is not contained in ACC0

Source:
R. Williams, "Non-uniform ACC circuit lower bounds", Journal of the ACM 61 (2014), 1-32 (CCC
2011).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Williams

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Williams: NEXP is not contained in ACC0

There is a language in `NEXP` that is not in `ACC0`: nondeterministic exponential time is not
captured by polynomial-size, constant-depth circuits with `MOD` gates. `ACC0` is the shared
class, defined as the union over fixed moduli `m` of `AC0[mod m]` - one fixed modulus per
circuit family.
-/

/-- **Williams: NEXP is not contained in ACC0.** Some decision problem lies in NEXP but not in
$\mathsf{ACC}^0$.

Source: R. Williams, "Non-uniform ACC circuit
lower bounds", Journal of the ACM 61 (2014), 1-32 (CCC 2011). -/
public theorem_wanted williams_nexp_not_in_acc0 :
    ∃ L : MetaMathlibExt.ComplexityTheory.DecisionProblem, L ∈ NEXP ∧ L ∉ ACC0

end MetaMathlibExt.Complexity.KeyTheorems.Williams
