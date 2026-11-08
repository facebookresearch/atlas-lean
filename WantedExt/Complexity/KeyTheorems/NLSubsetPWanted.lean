/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NL is contained in P

Source:
S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Theorem 4.14 (NL ⊆
P); C. H. Papadimitriou, Computational Complexity, 1994.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.NLSubsetP

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# NL is contained in P

Every nondeterministic logarithmic-space language is in deterministic polynomial time, by
exhaustive search of the polynomially many configurations of a log-space machine.
-/

/-- **NL is contained in P.** Source: S. Arora and B. Barak, Computational Complexity: A
Modern Approach, 2009, Theorem 4.14 (NL ⊆ P); C. H. Papadimitriou, Computational
Complexity, 1994. -/
public theorem_wanted nl_subset_p :
    NL ⊆ MetaMathlibExt.ComplexityTheory.P

end MetaMathlibExt.Complexity.KeyTheorems.NLSubsetP
