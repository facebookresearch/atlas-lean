/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.QCoordinateGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedQCentralizerIdentity

/-! A finite coordinate test for actual generated-group equality. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Commutation with the twenty-four coordinate lifts and z implies commutation with all Q. -/
theorem generated_commuting_all_q_of_coordinates (g : G)
    (hi : ∀ i : Fin 24, Commute g (qIntoGenerated (qCoordinateGenerator i)))
    (hz : Commute g (qIntoGenerated qCentralInvolution)) :
    ∀ q : Q, Commute g (qIntoGenerated q) := by
  let K : Subgroup Q := (Subgroup.centralizer {g}).comap qIntoGenerated
  have hK : K = ⊤ := by
    apply qCoordinate_subgroup_eq_top
    · intro i
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hi i).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hz.symm
  intro q
  have hq : q ∈ K := by rw [hK]; exact Subgroup.mem_top q
  exact (Subgroup.mem_centralizer_singleton_iff.mp hq).symm

/-- Twenty-five commutation checks and one nonzero tensor vector suffice for identity. -/
theorem generated_coordinate_identity_of_tensor_fixed (g : G)
    (hi : ∀ i : Fin 24, Commute g (qIntoGenerated (qCoordinateGenerator i)))
    (hz : Commute g (qIntoGenerated qCentralInvolution)) (x : GriessSpace)
    (hx : g.val x = x) (ht : (griessConwayEncode x).2.2 ≠ 0) : g = 1 :=
  generated_commuting_all_q_identity_of_tensor_fixed g
    (generated_commuting_all_q_of_coordinates g hi hz) x hx ht

/-- For an actual local element z commutation is automatic, leaving twenty-four checks. -/
theorem generated_local_coordinate_identity_of_tensor_fixed (h : H)
    (hi : ∀ i : Fin 24,
      Commute (localIntoGenerated h) (qIntoGenerated (qCoordinateGenerator i)))
    (x : GriessSpace) (hx : (localIntoGenerated h).val x = x)
    (ht : (griessConwayEncode x).2.2 ≠ 0) : localIntoGenerated h = 1 :=
  generated_coordinate_identity_of_tensor_fixed (localIntoGenerated h) hi
    (localIntoGenerated_commute_central h) x hx ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
