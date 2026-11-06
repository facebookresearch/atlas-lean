/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1NormalTwoSubgroup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryIrreducibleSubspaces

/-! The actual Conway quotient has no nontrivial normal 2-subgroup. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every normal 2-subgroup of actual Co1 is trivial, using the proved genuine binary action. -/
theorem co1_normal_two_subgroup_eq_bot (P : Subgroup Co1) [P.Normal]
    (hP : IsPGroup 2 P) : P = ⊥ :=
  co1_normal_two_subgroup_eq_bot_of_irreducible
    co1BinaryAction_invariant_subspace_dichotomy P hP

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
