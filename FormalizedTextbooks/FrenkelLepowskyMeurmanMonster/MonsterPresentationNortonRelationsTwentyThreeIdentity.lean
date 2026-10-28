/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Twenty-three actual Q checks and the delta-zero tensor determine a local group element. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTwentyThreeQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TensorMatrixCommutant

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine pure Griess tensor with spin delta zero in physical coordinate zero. -/
noncomputable def monsterNortonTwentyThreeTensorVector : GriessSpace :=
  griessConwayDecode (0, (0, tensorColumnInsert 0 (Pi.single 0 1 : SpinSpace)))

/-- The delta-zero test vector has exactly its actual pure tensor coordinates. -/
theorem monsterNortonTwentyThreeTensorVector_encode :
    griessConwayEncode monsterNortonTwentyThreeTensorVector =
      (0, (0, tensorColumnInsert 0 (Pi.single 0 1 : SpinSpace))) :=
  griessConwayEncode_decode _ (by intro i j; rfl)

/-- Twenty-three full coordinate commutation checks put an actual local element in Q. -/
theorem monsterNortonLocal_twentyThree_mem_Q (h : H)
    (hi : ∀ i : Fin 24, i ≠ 23 → Commute h (inclQ (qCoordinateGenerator i))) :
    h ∈ inclQ.range := by
  induction h using QuotientGroup.induction_on with
  | H f =>
    have hconj (q : Q) : inclQ (spinConjugation f.val.1 q) =
        localFiberIntoH f * inclQ q * (localFiberIntoH f)⁻¹ := by
      change QuotientGroup.mk' localDiagonalSubgroup
        (localFiberIncl (spinConjugation f.val.1 q)) = _
      rw [localFiberIncl_conjugate, map_mul, map_mul, map_inv]
      rfl
    have hs : ∀ i : Fin 24, i ≠ 23 → spinConjugation f.val.1 (qCoordinateGenerator i) =
        qCoordinateGenerator i := by
      intro i hi23
      apply inclQ_injective
      have hc := (hi i hi23).eq
      change localFiberIntoH f * inclQ (qCoordinateGenerator i) =
        inclQ (qCoordinateGenerator i) * localFiberIntoH f at hc
      rw [hconj, hc, mul_assoc, mul_inv_cancel, mul_one]
    have hb := monsterNortonSpinBinary_eq_one_of_twentyThree f.val.1 hs
    have he : f.val.2 ∈ signsSubgroup :=
      (leechBinaryAction_mem_kernel_iff_sign _).mp (f.property.symm.trans hb)
    rw [inclQ_range_eq_projH_ker]
    change QuotientGroup.mk f.val.2 = (1 : leechIsomSubgroup ⧸ signsSubgroup)
    exact (QuotientGroup.eq_one_iff _).mpr he

private theorem q_spin_zero_of_tensor_fixed (q : Q)
    (hx : (qIntoGenerated q).val monsterNortonTwentyThreeTensorVector =
      monsterNortonTwentyThreeTensorVector) :
    spinRepresentation q (Pi.single 0 1) 0 = 1 := by
  have h := congrArg (fun x : GriessSpace => (griessConwayEncode x).2.2 0 0) hx
  change (griessConwayEncode (localGriessRepresentation (localFiberIncl q)
    monsterNortonTwentyThreeTensorVector)).2.2 0 0 = _ at h
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_tensor,
    monsterNortonTwentyThreeTensorVector_encode] at h
  change localTensorRepresentation (localFiberIncl q)
    (tensorColumnInsert 0 (Pi.single 0 1 : SpinSpace)) 0 0 =
      (tensorColumnInsert 0 (Pi.single 0 1 : SpinSpace)) 0 0 at h
  rw [localTensorRepresentation_q] at h
  change spinRepresentation q (Pi.single 0 1) 0 = 1 at h
  exact h

/-- Twenty-three coordinate checks and the fixed actual delta-zero tensor force local identity. -/
theorem monsterNortonGenerated_twentyThree_identity (g : G)
    (hg : g ∈ localIntoGenerated.range)
    (hi : ∀ i : Fin 24, i ≠ 23 → Commute g (qIntoGenerated (qCoordinateGenerator i)))
    (hx : g.val monsterNortonTwentyThreeTensorVector = monsterNortonTwentyThreeTensorVector) :
    g = 1 := by
  obtain ⟨h, hh⟩ := hg
  have hiH : ∀ i : Fin 24, i ≠ 23 → Commute h (inclQ (qCoordinateGenerator i)) := by
    intro i hi23
    change h * inclQ (qCoordinateGenerator i) = inclQ (qCoordinateGenerator i) * h
    apply localIntoGenerated_injective
    rw [map_mul, map_mul]
    change localIntoGenerated h * qIntoGenerated (qCoordinateGenerator i) =
      qIntoGenerated (qCoordinateGenerator i) * localIntoGenerated h
    rw [hh]
    exact (hi i hi23).eq
  obtain ⟨q, hq⟩ := monsterNortonLocal_twentyThree_mem_Q h hiH
  have hqg : qIntoGenerated q = g := by
    change localIntoGenerated (inclQ q) = g
    rw [hq, hh]
  have hiQ : ∀ i : Fin 24, i ≠ 23 → Commute q (qCoordinateGenerator i) := by
    intro i hi23
    change q * qCoordinateGenerator i = qCoordinateGenerator i * q
    apply qIntoGenerated_injective
    rw [map_mul, map_mul, hqg]
    exact (hi i hi23).eq
  have hfix : (qIntoGenerated q).val monsterNortonTwentyThreeTensorVector =
      monsterNortonTwentyThreeTensorVector := by rw [hqg]; exact hx
  have hqone := monsterNortonQ_twentyThree_eq_one_of_spin_zero q hiQ
    (q_spin_zero_of_tensor_fixed q hfix)
  rw [hqone, map_one] at hqg
  exact hqg.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
