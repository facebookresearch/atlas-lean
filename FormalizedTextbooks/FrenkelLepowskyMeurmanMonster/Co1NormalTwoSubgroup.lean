/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1NormalTwoSubgroupGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! Normal 2-subgroups of the actual Conway quotient, with binary irreducibility explicit. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Actual Co1 has no nontrivial normal 2-subgroup once its genuine binary action is irreducible. -/
theorem co1_normal_two_subgroup_eq_bot_of_irreducible
    (hirreducible : ∀ W : Submodule (ZMod 2) (Fin 24 → ZMod 2),
      (∀ g v, v ∈ W → co1BinaryAction g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : Subgroup Co1) [P.Normal] (hP : IsPGroup 2 P) : P = ⊥ :=
  faithful_irreducible_binary_normal_two_subgroup_eq_bot co1BinaryAction
    co1BinaryAction_injective hirreducible P hP

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
