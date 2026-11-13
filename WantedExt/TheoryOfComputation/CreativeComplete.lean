/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Decidability.SpecialSets
public import Mathlib.Computability.Reduce

@[expose] public section

set_option autoImplicit false

namespace Cslib.CreativeCompleteWanted

/-- **Creative sets are many-one complete for the RE sets**: every RE set
many-one reduces to a creative set, by the recursion theorem and
parametrized s-m-n. Source: Soare, *Recursively Enumerable Sets and
Degrees*, Ch. I, Theorem 5.8; Rogers, *Theory of Recursive Functions and
Effective Computability*, §8.4. -/
theorem_wanted creative_complete :
  ∀ {P : ℕ → Prop}, Cslib.Decidability.Creative P →
    ∀ {Q : ℕ → Prop}, REPred Q → ManyOneReducible Q P

end Cslib.CreativeCompleteWanted
