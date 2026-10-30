/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# There is an EXP language outside P (time-hierarchy separation)

Source:
J. Hartmanis and R. E. Stearns, "On the computational complexity of algorithms", Transactions
of the American Mathematical Society 117 (1965), 285-306; S. Arora and B. Barak, Computational
Complexity: A Modern Approach, 2009, Corollary 3.5.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.PneqEXP

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# There is an EXP language outside P (time-hierarchy separation)

There is a language in deterministic exponential time that is not in polynomial time, by the
time hierarchy theorem applied at polynomial vs exponential scales. This is the separation
direction only: it does not include the `P ⊆ EXP` containment, which would bridge the canonical
`P` machine model to the multi-tape `DTIME` model.
-/

/-- **There is an EXP language outside P (time-hierarchy separation).** Source: J. Hartmanis
and R. E. Stearns, "On the computational complexity of algorithms", Transactions of the
American Mathematical Society 117 (1965), 285-306; S. Arora and B. Barak, Computational
Complexity: A Modern Approach, 2009, Corollary 3.5. -/
public theorem_wanted p_ne_exp :
    ∃ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ EXP ∧ L ∉ MetaMathlibExt.ComplexityTheory.P

end MetaMathlibExt.Complexity.KeyTheorems.PneqEXP
