/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Karp-Lipton theorem: NP in P/poly collapses PH

Source:
R. M. Karp and R. J. Lipton, "Some connections between nonuniform and uniform complexity
classes", Proceedings of the Twelfth Annual ACM Symposium on Theory of Computing (STOC 1980),
302-309.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.KarpLipton

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Karp-Lipton theorem: NP in P/poly collapses PH

If `NP` is contained in `P/poly` (polynomial time with polynomial advice), then the polynomial
hierarchy collapses to its second level: `PH = Σ₂^p`. `PH` and `Σ₂^p` are the alternating-
quantifier classes of the shared file; `P/poly` is the advice class.
-/

/-- **Karp-Lipton theorem: NP in P/poly collapses PH.** If every decision problem in NP belongs to
P/poly (polynomial time with polynomial advice), then the polynomial hierarchy PH equals its
second level $\Sigma_2^p$.

Source: R. M. Karp and R. J. Lipton,
"Some connections between nonuniform and uniform complexity classes", Proceedings of the
Twelfth Annual ACM Symposium on Theory of Computing (STOC 1980), 302-309. -/
public theorem_wanted karp_lipton :
    MetaMathlibExt.ComplexityTheory.NP ⊆ PPoly → PH = SigmaK 2

end MetaMathlibExt.Complexity.KeyTheorems.KarpLipton
