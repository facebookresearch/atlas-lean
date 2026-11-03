/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PP is contained in PSPACE

Source:
J. Gill, "Computational complexity of probabilistic Turing machines" (1977); S. Arora and B.
Barak, Computational Complexity: A Modern Approach, 2009 (PP ⊆ PSPACE).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.PPSubsetPSPACE

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# PP is contained in PSPACE

Every probabilistic polynomial-time language with unbounded error is in polynomial space, by
enumerating random strings in polynomial space.
-/

/-- **PP is contained in PSPACE.** Every decision problem in PP, the class of decision problems
decided with unbounded error in probabilistic polynomial time, belongs to PSPACE.

Source: J. Gill, "Computational complexity of probabilistic
Turing machines" (1977); S. Arora and B. Barak, Computational Complexity: A Modern
Approach, 2009 (PP ⊆ PSPACE). -/
public theorem_wanted pp_subset_pspace :
    PP ⊆ PSPACE

end MetaMathlibExt.Complexity.KeyTheorems.PPSubsetPSPACE
