/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Toda's theorem: PH is contained in P^#P

Source:
S. Toda, "PP is as hard as the polynomial-time hierarchy", SIAM Journal on Computing 20 (1991),
865-877 (FOCS 1989).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Toda

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Toda's theorem: PH is contained in P^#P

The polynomial hierarchy is contained in `P` with a `#P` oracle: every `PH` language can be
decided in polynomial time given access to a counting oracle. `PWithSharpP` is the oracle class
of the shared file (polynomial-time next-query / final-decision functions with polynomially
many adaptive queries and polynomially bounded query lengths).
-/

/-- **Toda's theorem: PH is contained in P^#P.** Source: S. Toda, "PP is as hard as the
polynomial-time hierarchy", SIAM Journal on Computing 20 (1991), 865-877 (FOCS 1989). -/
public theorem_wanted toda :
    PH ⊆ PWithSharpP

end MetaMathlibExt.Complexity.KeyTheorems.Toda
