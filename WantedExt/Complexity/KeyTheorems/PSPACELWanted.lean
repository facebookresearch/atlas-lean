/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# There is a PSPACE language outside L (space-hierarchy separation)

Source:
R. W. Stearns, J. Hartmanis, and P. M. Lewis II, "Hierarchies of memory limited computations"
(1965); S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.PSPACEL

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# There is a PSPACE language outside L (space-hierarchy separation)

There is a language in polynomial space that is not in deterministic logarithmic space, by the
space hierarchy theorem applied at logarithmic vs polynomial scales. This is the separation
direction only: it does not include the `LogSpace ⊆ PSPACE` containment.
-/

/-- **There is a PSPACE language outside L (space-hierarchy separation).** There is a decision
problem that belongs to PSPACE but not to the class $\mathsf{L}$ of decision problems decidable
in deterministic logarithmic space.

Source: R. W.
Stearns, J. Hartmanis, and P. M. Lewis II, "Hierarchies of memory limited computations"
(1965); S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009. -/
public theorem_wanted l_ne_pspace :
    ∃ L : MetaMathlibExt.ComplexityTheory.DecisionProblem, L ∈ PSPACE ∧ L ∉ LogSpace

end MetaMathlibExt.Complexity.KeyTheorems.PSPACEL
