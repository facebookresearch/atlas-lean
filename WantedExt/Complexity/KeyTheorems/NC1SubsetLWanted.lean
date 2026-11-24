/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NC^1 is contained in L

Source:
S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Theorem 6.22 (NC¹ ⊆ L); M. Sipser, Introduction to the Theory of Computation,
3rd ed., 2013, Theorem 9.21 (NC¹ ⊆ L).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.NC1SubsetL

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# NC^1 is contained in L

Every language decidable by log-space uniform polynomial-size bounded-fan-in
(`≤ 2`) `O(log n)`-depth circuits is in deterministic logarithmic space: a
depth-first evaluation of the circuit keeps one `O(log n)`-bit path on the
work tape. Bounded fan-in is part of the shared `NCK` definition; without it
the class would be `AC¹`, not `NC¹`. Not proved here:
evaluating a circuit in logarithmic space needs a multi-tape Turing machine
that generates gates on demand from the uniformity function and recurses down
the circuit with a bounded stack; building that machine and its space bound is
a Turing-machine construction, not a logical consequence of the definitions.
The intended `L` is the `LogSpace` class of the shared file.
-/

/-- **NC^1 is contained in L.** Every decision problem in $\mathsf{NC}^1$ belongs to the class
$\mathsf{L}$ of decision problems decidable in deterministic logarithmic space.

Source: S. Arora and B. Barak, Computational Complexity:
A Modern Approach, 2009, Theorem 6.22 (NC¹ ⊆ L); M. Sipser, Introduction to the
Theory of Computation, 3rd ed., 2013, Theorem 9.21 (NC¹ ⊆ L). -/
public theorem_wanted nc1_subset_logspace :
    NCK 1 ⊆ LogSpace

end MetaMathlibExt.Complexity.KeyTheorems.NC1SubsetL
