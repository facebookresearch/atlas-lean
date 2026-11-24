/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MA is contained in AM

Source:
L. Babai, "Trading group theory for randomness", Proceedings of the Seventeenth
Annual ACM Symposium on Theory of Computing (STOC 1985), 421-429; S. Arora and
B. Barak, Computational Complexity: A Modern Approach, 2009, Theorem 8.2
(MA ⊆ AM).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.MASubsetAM

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# MA is contained in AM

Every Merlin-Arthur language is in `AM`: Merlin's message may as well be sent
after Arthur's coins. Not proved here: the same verifier does not work, since
in `AM` Merlin chooses the witness after seeing the coins, so the soundness
argument needs error amplification first (drive the per-witness soundness error
far below `2 ^ -(witness length)`) and then a union bound over all of Merlin's
possible messages. Both the amplification (a new verifier over concatenated
random strings, needing an `IsPolyTime` witness) and the counting union bound
are beyond a definitional unfolding.
-/

/-- **MA is contained in AM.** Every decision problem in the class $\mathsf{MA}$ is in the class
$\mathsf{AM}$.

Source: L. Babai, "Trading group theory for randomness",
Proceedings of the Seventeenth Annual ACM Symposium on Theory of Computing
(STOC 1985), 421-429; S. Arora and B. Barak, Computational Complexity: A Modern
Approach, 2009, Theorem 8.2 (MA ⊆ AM). -/
public theorem_wanted ma_subset_am :
    MA ⊆ AM

end MetaMathlibExt.Complexity.KeyTheorems.MASubsetAM
