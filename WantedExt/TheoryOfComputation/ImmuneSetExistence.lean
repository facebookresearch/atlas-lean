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

namespace Cslib.ImmuneSetExistenceWanted

/-- **An immune set exists**: there is an infinite set with no infinite RE
subset, by a finite-injury priority construction (in fact every simple
set's complement is immune). Source: Soare, *Recursively Enumerable Sets
and Degrees*, Ch. I, §5; Rogers, *Theory of Recursive Functions and
Effective Computability*, §8.5. -/
theorem_wanted immune_exists : ∃ P : ℕ → Prop, Cslib.Decidability.Immune P

end Cslib.ImmuneSetExistenceWanted
