/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PSPACE is contained in EXP

Source:
S. Arora and B. Barak, Computational Complexity: A Modern Approach, Cambridge University Press,
2009, Theorem 4.14 (PSPACE ⊆ EXP).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.PSPACESubsetEXP

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# PSPACE is contained in EXP

Every polynomial-space language is in deterministic exponential time: a polynomial-space
machine has only exponentially many configurations, so exhaustive configuration-graph search
decides the language in exponential time.
-/

/-- **PSPACE is contained in EXP.** Every decision problem in PSPACE belongs to EXP, the class of
decision problems decidable in deterministic exponential time.

Source: S. Arora and B. Barak, Computational Complexity: A
Modern Approach, Cambridge University Press, 2009, Theorem 4.14 (PSPACE ⊆ EXP). -/
public theorem_wanted pspace_subset_exp :
    PSPACE ⊆ EXP

end MetaMathlibExt.Complexity.KeyTheorems.PSPACESubsetEXP
