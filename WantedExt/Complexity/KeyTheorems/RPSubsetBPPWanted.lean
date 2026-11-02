/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RP is contained in BPP

Source:
S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Chapter 7
(error reduction for RP); M. Sipser, Introduction to the Theory of Computation,
3rd ed., 2013, Theorem 10.13 (RP ⊆ BPP via amplification).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.RPSubsetBPP

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# RP is contained in BPP

Every one-sided-error randomized polynomial-time language is in `BPP`:
repeating the `RP` verifier and taking the majority (or the OR) of the outcomes
amplifies the yes-instance acceptance probability from `≥ 1/2` past `2/3`
while keeping the no-instance probability at `0`. Not proved here: amplification
builds a new verifier over concatenated random strings, and showing it is
polynomial-time is a Turing-machine construction (`IsPolyTime` of the repeated
verifier composed with majority), not a logical consequence of the definitions.
`ZPP ⊆ BPP` follows from this together with the proved `ZPP ⊆ RP`.
-/

/-- **RP is contained in BPP.** Every decision problem in the class $\mathsf{RP}$ of
one-sided-error randomized polynomial-time decision problems also belongs to the class
$\mathsf{BPP}$ of bounded-error probabilistic polynomial-time decision problems.

Source: S. Arora and B. Barak, Computational Complexity:
A Modern Approach, 2009, Chapter 7 (error reduction for RP); M. Sipser,
Introduction to the Theory of Computation, 3rd ed., 2013, Theorem 10.13
(RP ⊆ BPP via amplification). -/
public theorem_wanted rp_subset_bpp :
    RP ⊆ BPP

end MetaMathlibExt.Complexity.KeyTheorems.RPSubsetBPP
