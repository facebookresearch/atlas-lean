/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Decidability.SpecialSets

@[expose] public section

set_option autoImplicit false

namespace Cslib.SimpleSetExistenceWanted

/-- **A simple set exists**: there is an RE set whose complement is immune,
by a finite-injury priority construction. Source: Soare, *Recursively
Enumerable Sets and Degrees*, Ch. III, Theorem 3.1 (Post's construction);
Rogers, *Theory of Recursive Functions and Effective Computability*,
§8.5. -/
theorem_wanted simple_exists : ∃ P : ℕ → Prop, Cslib.Decidability.Simple P

end Cslib.SimpleSetExistenceWanted
