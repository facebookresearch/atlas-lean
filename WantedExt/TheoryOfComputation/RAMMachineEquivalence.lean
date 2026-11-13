/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Decidability.RAMMachines

@[expose] public section

set_option autoImplicit false

namespace Cslib.RAMMachineEquivalenceWanted

/-- **RAM machines compute exactly the computable predicates**: a predicate
is RAM decidable iff it is computable. Source: Aho–Hopcroft–Ullman,
*The Design and Analysis of Computer Algorithms*, 1974, §1.2; Soare,
*Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 2.3. -/
theorem_wanted ram_decidable_iff_computablePred :
  ∀ {P : ℕ → Prop}, Cslib.Decidability.RAMDecidable P ↔ ComputablePred P

end Cslib.RAMMachineEquivalenceWanted
