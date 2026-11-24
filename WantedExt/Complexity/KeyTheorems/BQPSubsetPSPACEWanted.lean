/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BQP is contained in PSPACE

Source:
E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on
Computing 26 (1997), 1411-1473 (BQP ⊆ PSPACE); S. Arora and B. Barak,
Computational Complexity: A Modern Approach, 2009, Theorem 10.2.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.BQPSubsetPSPACE

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# BQP is contained in PSPACE

Every bounded-error quantum polynomial-time language is in polynomial space:
the acceptance probability is a sum over exponentially many paths (the Feynman
path integral), and the sum can be accumulated one path at a time in polynomial
space, since each path's amplitude is a product of polynomially many gate
entries with rational real and imaginary parts. Not proved here: the argument
needs exact rational arithmetic for the path amplitudes, a summation over all
`4 ^ (number of gates)` paths, and a multi-tape space simulation turning the
sum into a `PSPACE` membership witness; none of that follows from the `BQP`
definition alone.
-/

/-- **BQP is contained in PSPACE.** Every decision problem in BQP, the class of bounded-error
quantum polynomial-time decision problems, lies in PSPACE, the class of decision problems
decidable in polynomial space.

Source: E. Bernstein and U. Vazirani, "Quantum
complexity theory", SIAM Journal on Computing 26 (1997), 1411-1473
(BQP ⊆ PSPACE); S. Arora and B. Barak, Computational Complexity: A Modern
Approach, 2009, Theorem 10.2. -/
public theorem_wanted bqp_subset_pspace :
    BQP ⊆ PSPACE

end MetaMathlibExt.Complexity.KeyTheorems.BQPSubsetPSPACE
