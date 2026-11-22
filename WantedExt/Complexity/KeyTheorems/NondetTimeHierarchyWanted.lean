/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nondeterministic time hierarchy

Source:
S. A. Cook, "A hierarchy for nondeterministic time complexity", Journal of Computer and System
Sciences 7 (1973), 343-353; S. Zak, "A Turing machine time hierarchy", Theoretical Computer
Science 26 (1983), 327-333.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.NondetTimeHierarchy

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Nondeterministic time hierarchy

There is a language decidable by a nondeterministic machine in quadratic time that is not
decidable by any nondeterministic machine in linear time. `NTIME` is the nondeterministic
multi-tape class defined in the shared classes file (acceptance by an accepting computation
path).
-/

/-- **Nondeterministic time hierarchy.** Source: S. A. Cook, "A hierarchy for nondeterministic
time complexity", Journal of Computer and System Sciences 7 (1973), 343-353; S. Zak, "A
Turing machine time hierarchy", Theoretical Computer Science 26 (1983), 327-333. -/
public theorem_wanted nondet_time_hierarchy :
    ∃ L : Set (List Bool), L ∈ NTIME (fun n => n ^ 2) ∧ L ∉ NTIME (fun n => n)

end MetaMathlibExt.Complexity.KeyTheorems.NondetTimeHierarchy
