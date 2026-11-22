/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NEXP is contained in EXPSPACE

Source:
S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009 (NEXP ⊆ EXPSPACE by
exhaustive simulation).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.NEXPSubsetEXPSPACE

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# NEXP is contained in EXPSPACE

Every nondeterministic exponential-time language is in deterministic exponential space. A
binary-branching computation of time `T = 2^{poly(n)}` has `2^T` (doubly exponentially many)
computation paths; the simulation works by depth-first traversal of the computation tree,
reusing `O(T)` space, so the space used is exponential.
-/

/-- **NEXP is contained in EXPSPACE.** Source: S. Arora and B. Barak, Computational
Complexity: A Modern Approach, 2009 (NEXP ⊆ EXPSPACE by exhaustive simulation). -/
public theorem_wanted nexp_subset_expspace :
    NEXP ⊆ EXPSPACE

end MetaMathlibExt.Complexity.KeyTheorems.NEXPSubsetEXPSPACE
