/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AM is contained in Pi_2 (Babai)

Source:
L. Babai, "Trading group theory for randomness", Proceedings of the Seventeenth Annual ACM
Symposium on Theory of Computing (STOC 1985), 421-429; see also O. Goldreich and D. Zuckerman
and the set lower-bound protocol of Goldwasser-Sipser.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.AMSubsetPi2

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# AM is contained in Pi_2 (Babai)

Every Arthur-Merlin language is in `Π₂^p`: the set lower-bound protocol turns the probabilistic
`∃`-after-randomness definition of `AM` into two alternating quantifier blocks.
-/

/-- **AM is contained in Pi_2 (Babai).** Source: L. Babai, "Trading group theory for
randomness", Proceedings of the Seventeenth Annual ACM Symposium on Theory of Computing
(STOC 1985), 421-429; see also O. Goldreich and D. Zuckerman and the set lower-bound
protocol of Goldwasser-Sipser. -/
public theorem_wanted am_subset_pi2 :
    AM ⊆ PiK 2

end MetaMathlibExt.Complexity.KeyTheorems.AMSubsetPi2
