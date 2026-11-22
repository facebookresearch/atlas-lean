/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BPP is contained in PSPACE

Source:
S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009 (BPP ⊆ PSPACE).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.BPPSubsetPSPACE

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# BPP is contained in PSPACE

Every bounded-error probabilistic polynomial-time language is in polynomial space, by
enumerating random strings in polynomial space.
-/

/-- **BPP is contained in PSPACE.** Source: S. Arora and B. Barak, Computational Complexity: A
Modern Approach, 2009 (BPP ⊆ PSPACE). -/
public theorem_wanted bpp_subset_pspace :
    BPP ⊆ PSPACE

end MetaMathlibExt.Complexity.KeyTheorems.BPPSubsetPSPACE
