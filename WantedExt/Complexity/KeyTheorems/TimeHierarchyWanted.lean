/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Deterministic time hierarchy

Source:
J. Hartmanis and R. E. Stearns, "On the computational complexity of algorithms", Transactions
of the American Mathematical Society 117 (1965), 285-306.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.TimeHierarchy

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Deterministic time hierarchy

There is a language decidable in deterministic quadratic time that is not decidable in
deterministic linear time, on the CSLib multi-tape model (`DTIME`). The multi-tape `DTIME` here
is the deterministic class of the repo's `CSLibExt` time/space development.
-/

/-- **Deterministic time hierarchy.** Source: J. Hartmanis and R. E. Stearns, "On the
computational complexity of algorithms", Transactions of the American Mathematical Society
117 (1965), 285-306. -/
public theorem_wanted time_hierarchy :
    ∃ L : Set (List Bool), L ∈ Cslib.Turing.MultiTapeTM.DTIME (fun n => n ^ 2) ∧
      L ∉ Cslib.Turing.MultiTapeTM.DTIME (fun n => n)

end MetaMathlibExt.Complexity.KeyTheorems.TimeHierarchy
