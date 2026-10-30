/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BQP is contained in PP

Source:
E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on
Computing 26 (1997), 1411-1473 (BQP ⊆ PP); L. Adleman, J. DeMarrais, and
M.-D. Huang, "Quantum computability", SIAM Journal on Computing 26 (1997),
1524-1540; S. Arora and B. Barak, Computational Complexity: A Modern Approach,
2009, Theorem 10.2.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.BQPSubsetPP

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# BQP is contained in PP

Every bounded-error quantum polynomial-time language is in `PP`: the gap
between the accepting and rejecting squared amplitudes is a difference of two
`#P`-like counts (accepting paths minus rejecting paths), rescaled so that its
sign decides membership. Not proved here: the argument needs the path-integral
expansion of the quantum circuit, a proof that the gap has the sign of
`2 * (#accepting paths) - (#all paths)` after clearing denominators, and a
polynomial-time verifier whose accepting-coin count implements that gap;
none of that follows from the `BQP` definition alone.
-/

/-- **BQP is contained in PP.** Source: E. Bernstein and U. Vazirani, "Quantum
complexity theory", SIAM Journal on Computing 26 (1997), 1411-1473 (BQP ⊆ PP);
L. Adleman, J. DeMarrais, and M.-D. Huang, "Quantum computability", SIAM
Journal on Computing 26 (1997), 1524-1540; S. Arora and B. Barak, Computational
Complexity: A Modern Approach, 2009, Theorem 10.2. -/
public theorem_wanted bqp_subset_pp :
    BQP ⊆ PP

end MetaMathlibExt.Complexity.KeyTheorems.BQPSubsetPP
