/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NP is contained in PP

Source:
J. Gill, "Computational complexity of probabilistic Turing machines" (1977).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.NPSubsetPP

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# NP is contained in PP

Every `NP` language is in `PP`: guess a witness at random, accept if it verifies, otherwise
accept with probability `1/2`; the acceptance probability is `> 1/2` exactly on yes-instances.
-/

/-- **NP is contained in PP.** Every decision problem in NP also belongs to PP, the class of
decision problems decided in probabilistic polynomial time with unbounded error.

Source: J. Gill, "Computational complexity of probabilistic
Turing machines" (1977). -/
public theorem_wanted np_subset_pp :
    MetaMathlibExt.ComplexityTheory.NP ⊆ PP

end MetaMathlibExt.Complexity.KeyTheorems.NPSubsetPP
