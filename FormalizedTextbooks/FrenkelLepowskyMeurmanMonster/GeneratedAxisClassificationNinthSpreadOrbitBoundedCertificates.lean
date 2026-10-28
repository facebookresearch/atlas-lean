/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket26
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket27
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket28
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedPacket29

/-! The thirty complete packets imply every original 960-index spread condition. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Euclidean division gives complete disjoint coverage of all 960 indices. -/
private theorem generatedNinth_spread_bounded_all (P : Fin 960 → Prop)
    (h : ∀ k : Fin 30, ∀ m : Fin 32,
      P ⟨32 * k.val + m.val, by omega⟩) : ∀ i : Fin 960, P i := by
  intro i
  let k : Fin 30 := ⟨i.val / 32, by omega⟩
  let m : Fin 32 := ⟨i.val % 32, Nat.mod_lt _ (by omega)⟩
  have hi : (⟨32 * k.val + m.val, by omega⟩ : Fin 960) = i := by
    apply Fin.ext
    dsimp only [k, m]
    omega
  simpa only [hi] using h k m

/-- The exact original spread predicate holds at every index. -/
theorem generatedNinth_spread_bounded_indices_injective : ∀ i : Fin 960,
    Function.Injective (generatedNinthSpreadIndices i) := by
  apply generatedNinth_spread_bounded_all
  intro k
  fin_cases k
  · exact generatedNinth_spread_bounded_indices_injective_packet_00
  · exact generatedNinth_spread_bounded_indices_injective_packet_01
  · exact generatedNinth_spread_bounded_indices_injective_packet_02
  · exact generatedNinth_spread_bounded_indices_injective_packet_03
  · exact generatedNinth_spread_bounded_indices_injective_packet_04
  · exact generatedNinth_spread_bounded_indices_injective_packet_05
  · exact generatedNinth_spread_bounded_indices_injective_packet_06
  · exact generatedNinth_spread_bounded_indices_injective_packet_07
  · exact generatedNinth_spread_bounded_indices_injective_packet_08
  · exact generatedNinth_spread_bounded_indices_injective_packet_09
  · exact generatedNinth_spread_bounded_indices_injective_packet_10
  · exact generatedNinth_spread_bounded_indices_injective_packet_11
  · exact generatedNinth_spread_bounded_indices_injective_packet_12
  · exact generatedNinth_spread_bounded_indices_injective_packet_13
  · exact generatedNinth_spread_bounded_indices_injective_packet_14
  · exact generatedNinth_spread_bounded_indices_injective_packet_15
  · exact generatedNinth_spread_bounded_indices_injective_packet_16
  · exact generatedNinth_spread_bounded_indices_injective_packet_17
  · exact generatedNinth_spread_bounded_indices_injective_packet_18
  · exact generatedNinth_spread_bounded_indices_injective_packet_19
  · exact generatedNinth_spread_bounded_indices_injective_packet_20
  · exact generatedNinth_spread_bounded_indices_injective_packet_21
  · exact generatedNinth_spread_bounded_indices_injective_packet_22
  · exact generatedNinth_spread_bounded_indices_injective_packet_23
  · exact generatedNinth_spread_bounded_indices_injective_packet_24
  · exact generatedNinth_spread_bounded_indices_injective_packet_25
  · exact generatedNinth_spread_bounded_indices_injective_packet_26
  · exact generatedNinth_spread_bounded_indices_injective_packet_27
  · exact generatedNinth_spread_bounded_indices_injective_packet_28
  · exact generatedNinth_spread_bounded_indices_injective_packet_29

/-- The exact original spread predicate holds at every index. -/
theorem generatedNinth_spread_bounded_hash_sum : ∀ i : Fin 960,
    (∑ j : Fin 9, 2 ^ (generatedNinthSpreadIndices i j).val) % 18446744073709551557 =
      generatedNinthSpreadHashes i := by
  apply generatedNinth_spread_bounded_all
  intro k
  fin_cases k
  · exact generatedNinth_spread_bounded_hash_sum_packet_00
  · exact generatedNinth_spread_bounded_hash_sum_packet_01
  · exact generatedNinth_spread_bounded_hash_sum_packet_02
  · exact generatedNinth_spread_bounded_hash_sum_packet_03
  · exact generatedNinth_spread_bounded_hash_sum_packet_04
  · exact generatedNinth_spread_bounded_hash_sum_packet_05
  · exact generatedNinth_spread_bounded_hash_sum_packet_06
  · exact generatedNinth_spread_bounded_hash_sum_packet_07
  · exact generatedNinth_spread_bounded_hash_sum_packet_08
  · exact generatedNinth_spread_bounded_hash_sum_packet_09
  · exact generatedNinth_spread_bounded_hash_sum_packet_10
  · exact generatedNinth_spread_bounded_hash_sum_packet_11
  · exact generatedNinth_spread_bounded_hash_sum_packet_12
  · exact generatedNinth_spread_bounded_hash_sum_packet_13
  · exact generatedNinth_spread_bounded_hash_sum_packet_14
  · exact generatedNinth_spread_bounded_hash_sum_packet_15
  · exact generatedNinth_spread_bounded_hash_sum_packet_16
  · exact generatedNinth_spread_bounded_hash_sum_packet_17
  · exact generatedNinth_spread_bounded_hash_sum_packet_18
  · exact generatedNinth_spread_bounded_hash_sum_packet_19
  · exact generatedNinth_spread_bounded_hash_sum_packet_20
  · exact generatedNinth_spread_bounded_hash_sum_packet_21
  · exact generatedNinth_spread_bounded_hash_sum_packet_22
  · exact generatedNinth_spread_bounded_hash_sum_packet_23
  · exact generatedNinth_spread_bounded_hash_sum_packet_24
  · exact generatedNinth_spread_bounded_hash_sum_packet_25
  · exact generatedNinth_spread_bounded_hash_sum_packet_26
  · exact generatedNinth_spread_bounded_hash_sum_packet_27
  · exact generatedNinth_spread_bounded_hash_sum_packet_28
  · exact generatedNinth_spread_bounded_hash_sum_packet_29

/-- The exact original spread predicate holds at every index. -/
theorem generatedNinth_spread_bounded_lookup : ∀ i : Fin 960,
    generatedNinthSpreadLookup (generatedNinthSpreadHashes i) = i.val := by
  apply generatedNinth_spread_bounded_all
  intro k
  fin_cases k
  · exact generatedNinth_spread_bounded_lookup_packet_00
  · exact generatedNinth_spread_bounded_lookup_packet_01
  · exact generatedNinth_spread_bounded_lookup_packet_02
  · exact generatedNinth_spread_bounded_lookup_packet_03
  · exact generatedNinth_spread_bounded_lookup_packet_04
  · exact generatedNinth_spread_bounded_lookup_packet_05
  · exact generatedNinth_spread_bounded_lookup_packet_06
  · exact generatedNinth_spread_bounded_lookup_packet_07
  · exact generatedNinth_spread_bounded_lookup_packet_08
  · exact generatedNinth_spread_bounded_lookup_packet_09
  · exact generatedNinth_spread_bounded_lookup_packet_10
  · exact generatedNinth_spread_bounded_lookup_packet_11
  · exact generatedNinth_spread_bounded_lookup_packet_12
  · exact generatedNinth_spread_bounded_lookup_packet_13
  · exact generatedNinth_spread_bounded_lookup_packet_14
  · exact generatedNinth_spread_bounded_lookup_packet_15
  · exact generatedNinth_spread_bounded_lookup_packet_16
  · exact generatedNinth_spread_bounded_lookup_packet_17
  · exact generatedNinth_spread_bounded_lookup_packet_18
  · exact generatedNinth_spread_bounded_lookup_packet_19
  · exact generatedNinth_spread_bounded_lookup_packet_20
  · exact generatedNinth_spread_bounded_lookup_packet_21
  · exact generatedNinth_spread_bounded_lookup_packet_22
  · exact generatedNinth_spread_bounded_lookup_packet_23
  · exact generatedNinth_spread_bounded_lookup_packet_24
  · exact generatedNinth_spread_bounded_lookup_packet_25
  · exact generatedNinth_spread_bounded_lookup_packet_26
  · exact generatedNinth_spread_bounded_lookup_packet_27
  · exact generatedNinth_spread_bounded_lookup_packet_28
  · exact generatedNinth_spread_bounded_lookup_packet_29

/-- The exact original spread predicate holds at every index. -/
theorem generatedNinth_spread_bounded_parent_lt : ∀ i : Fin 960, i ≠ 0 →
    (generatedNinthSpreadParent i).val < i.val := by
  apply generatedNinth_spread_bounded_all
  intro k
  fin_cases k
  · exact generatedNinth_spread_bounded_parent_lt_packet_00
  · exact generatedNinth_spread_bounded_parent_lt_packet_01
  · exact generatedNinth_spread_bounded_parent_lt_packet_02
  · exact generatedNinth_spread_bounded_parent_lt_packet_03
  · exact generatedNinth_spread_bounded_parent_lt_packet_04
  · exact generatedNinth_spread_bounded_parent_lt_packet_05
  · exact generatedNinth_spread_bounded_parent_lt_packet_06
  · exact generatedNinth_spread_bounded_parent_lt_packet_07
  · exact generatedNinth_spread_bounded_parent_lt_packet_08
  · exact generatedNinth_spread_bounded_parent_lt_packet_09
  · exact generatedNinth_spread_bounded_parent_lt_packet_10
  · exact generatedNinth_spread_bounded_parent_lt_packet_11
  · exact generatedNinth_spread_bounded_parent_lt_packet_12
  · exact generatedNinth_spread_bounded_parent_lt_packet_13
  · exact generatedNinth_spread_bounded_parent_lt_packet_14
  · exact generatedNinth_spread_bounded_parent_lt_packet_15
  · exact generatedNinth_spread_bounded_parent_lt_packet_16
  · exact generatedNinth_spread_bounded_parent_lt_packet_17
  · exact generatedNinth_spread_bounded_parent_lt_packet_18
  · exact generatedNinth_spread_bounded_parent_lt_packet_19
  · exact generatedNinth_spread_bounded_parent_lt_packet_20
  · exact generatedNinth_spread_bounded_parent_lt_packet_21
  · exact generatedNinth_spread_bounded_parent_lt_packet_22
  · exact generatedNinth_spread_bounded_parent_lt_packet_23
  · exact generatedNinth_spread_bounded_parent_lt_packet_24
  · exact generatedNinth_spread_bounded_parent_lt_packet_25
  · exact generatedNinth_spread_bounded_parent_lt_packet_26
  · exact generatedNinth_spread_bounded_parent_lt_packet_27
  · exact generatedNinth_spread_bounded_parent_lt_packet_28
  · exact generatedNinth_spread_bounded_parent_lt_packet_29

/-- The exact original spread predicate holds at every index. -/
theorem generatedNinth_spread_bounded_edge_indices : ∀ i : Fin 960, i ≠ 0 → ∀ j : Fin 9,
    generatedNinthSpreadSystemTarget (generatedNinthSpreadGenerator i)
      (generatedNinthSpreadIndices (generatedNinthSpreadParent i) j) =
        generatedNinthSpreadIndices i (generatedNinthSpreadEdgePermutation i j) := by
  apply generatedNinth_spread_bounded_all
  intro k
  fin_cases k
  · exact generatedNinth_spread_bounded_edge_indices_packet_00
  · exact generatedNinth_spread_bounded_edge_indices_packet_01
  · exact generatedNinth_spread_bounded_edge_indices_packet_02
  · exact generatedNinth_spread_bounded_edge_indices_packet_03
  · exact generatedNinth_spread_bounded_edge_indices_packet_04
  · exact generatedNinth_spread_bounded_edge_indices_packet_05
  · exact generatedNinth_spread_bounded_edge_indices_packet_06
  · exact generatedNinth_spread_bounded_edge_indices_packet_07
  · exact generatedNinth_spread_bounded_edge_indices_packet_08
  · exact generatedNinth_spread_bounded_edge_indices_packet_09
  · exact generatedNinth_spread_bounded_edge_indices_packet_10
  · exact generatedNinth_spread_bounded_edge_indices_packet_11
  · exact generatedNinth_spread_bounded_edge_indices_packet_12
  · exact generatedNinth_spread_bounded_edge_indices_packet_13
  · exact generatedNinth_spread_bounded_edge_indices_packet_14
  · exact generatedNinth_spread_bounded_edge_indices_packet_15
  · exact generatedNinth_spread_bounded_edge_indices_packet_16
  · exact generatedNinth_spread_bounded_edge_indices_packet_17
  · exact generatedNinth_spread_bounded_edge_indices_packet_18
  · exact generatedNinth_spread_bounded_edge_indices_packet_19
  · exact generatedNinth_spread_bounded_edge_indices_packet_20
  · exact generatedNinth_spread_bounded_edge_indices_packet_21
  · exact generatedNinth_spread_bounded_edge_indices_packet_22
  · exact generatedNinth_spread_bounded_edge_indices_packet_23
  · exact generatedNinth_spread_bounded_edge_indices_packet_24
  · exact generatedNinth_spread_bounded_edge_indices_packet_25
  · exact generatedNinth_spread_bounded_edge_indices_packet_26
  · exact generatedNinth_spread_bounded_edge_indices_packet_27
  · exact generatedNinth_spread_bounded_edge_indices_packet_28
  · exact generatedNinth_spread_bounded_edge_indices_packet_29

/-- The exact original spread predicate holds at every index. -/
theorem generatedNinth_spread_bounded_edge_permutation_surjective : ∀ i : Fin 960,
    Function.Surjective (generatedNinthSpreadEdgePermutation i) := by
  apply generatedNinth_spread_bounded_all
  intro k
  fin_cases k
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_00
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_01
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_02
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_03
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_04
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_05
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_06
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_07
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_08
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_09
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_10
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_11
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_12
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_13
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_14
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_15
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_16
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_17
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_18
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_19
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_20
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_21
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_22
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_23
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_24
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_25
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_26
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_27
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_28
  · exact generatedNinth_spread_bounded_edge_permutation_surjective_packet_29

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
