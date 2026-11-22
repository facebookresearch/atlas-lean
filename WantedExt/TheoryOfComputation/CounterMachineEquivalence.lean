/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Decidability.CounterMachines

@[expose] public section

set_option autoImplicit false

namespace Cslib.CounterMachineEquivalenceWanted

/-- **Counter machines compute exactly the computable predicates**: a
predicate is counter-machine decidable iff it is computable. Source:
Minsky, *Computation: Finite and Infinite Machines*, 1967, §11; Soare,
*Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 2.3. -/
theorem_wanted counter_decidable_iff_computablePred :
  ∀ {P : ℕ → Prop}, Cslib.Decidability.CounterDecidable P ↔ ComputablePred P

end Cslib.CounterMachineEquivalenceWanted
