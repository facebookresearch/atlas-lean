/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Adleman's theorem: BPP is contained in P/poly

Source:
L. Adleman, "Two theorems on random polynomial time", Proceedings of the Nineteenth Annual
Symposium on Foundations of Computer Science (FOCS 1978), 75-83.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Adleman

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Adleman's theorem: BPP is contained in P/poly

Every bounded-error probabilistic polynomial-time language is in `P/poly`: a probabilistic
algorithm's random coins can be fixed to a single polynomial-length advice string that works
for all inputs of each length, by the probabilistic method.
-/

/-- **Adleman's theorem: BPP is contained in P/poly.** Every decision problem in BPP lies in
P/poly.

Source: L. Adleman, "Two theorems on
random polynomial time", Proceedings of the Nineteenth Annual Symposium on Foundations of
Computer Science (FOCS 1978), 75-83. -/
public theorem_wanted adleman :
    BPP ⊆ PPoly

end MetaMathlibExt.Complexity.KeyTheorems.Adleman
