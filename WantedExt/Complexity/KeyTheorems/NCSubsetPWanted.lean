/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NC is contained in P

Source:
S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Theorem 6.22 (NC ⊆ P); M. Sipser, Introduction to the Theory of Computation,
3rd ed., 2013, Theorem 9.21.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.NCSubsetP

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# NC is contained in P

Every language decidable by log-space uniform polynomial-size bounded-fan-in
polylog-depth circuits is in `P`: generate the circuit (log space, hence polynomial time)
and evaluate it gate by gate (polynomial time). Not proved here: turning the
log-space uniformity function (a multi-tape Turing machine) into a
polynomial-time circuit generator, and then into an `IsPolyTime` membership
witness for the `P` class, is a Turing-machine simulation, not a logical
consequence of the definitions.
-/

/-- **NC is contained in P.** Every decision problem in $\mathsf{NC}$ belongs to $\mathsf{P}$.

Source: S. Arora and B. Barak, Computational Complexity:
A Modern Approach, 2009, Theorem 6.22 (NC ⊆ P); M. Sipser, Introduction to the
Theory of Computation, 3rd ed., 2013, Theorem 9.21. -/
public theorem_wanted nc_subset_p :
    NC ⊆ P

end MetaMathlibExt.Complexity.KeyTheorems.NCSubsetP
