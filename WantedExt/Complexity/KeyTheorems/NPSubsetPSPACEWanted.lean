/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NP is contained in PSPACE

Source:
S. Arora and B. Barak, Computational Complexity: A Modern Approach, Cambridge University Press,
2009, Theorem 4.14 (NP ⊆ PSPACE); C. H. Papadimitriou, Computational Complexity, Addison-
Wesley, 1994, Theorem 7.2.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.NPSubsetPSPACE

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# NP is contained in PSPACE

Every language in the canonical `NP` class (polynomial-time verifiable) is in `PSPACE`
(polynomial-space decidable on the multi-tape model). The proof enumerates verifier witnesses
in polynomial space.
-/

/-- **NP is contained in PSPACE.** Source: S. Arora and B. Barak, Computational Complexity: A
Modern Approach, Cambridge University Press, 2009, Theorem 4.14 (NP ⊆ PSPACE); C. H.
Papadimitriou, Computational Complexity, Addison-Wesley, 1994, Theorem 7.2. -/
public theorem_wanted np_subset_pspace :
    MetaMathlibExt.ComplexityTheory.NP ⊆ PSPACE

end MetaMathlibExt.Complexity.KeyTheorems.NPSubsetPSPACE
