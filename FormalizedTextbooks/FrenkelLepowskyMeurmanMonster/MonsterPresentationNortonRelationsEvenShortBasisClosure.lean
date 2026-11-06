/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact phase-complete lifting of the actual twenty-three even-short binary basis. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortBasisBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.QCoordinateGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem q_mem_of_binary_mem (K : Subgroup Q) (hz : qCentralInvolution ∈ K)
    (q : Q) (hq : toAdd (qQuotHom q) ∈ qSubgroupBinaryImage K) : q ∈ K := by
  obtain ⟨k, hk, he⟩ := hq
  have he : qQuotHom k = qQuotHom q := he
  have hdiff : k⁻¹ * q ∈ centerQ := by
    rw [← qQuotHom_ker]
    change qQuotHom (k⁻¹ * q) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hm := K.mul_mem hk ((centerQ_le_of_central_mem K hz) hdiff)
  simpa only [mul_inv_cancel_left] using hm

/-- Containment of the actual even-short lifts and z implies every first-twenty-three lift. -/
theorem monsterNortonEvenShortBasis_coordinates_mem (K : Subgroup Q)
    (hz : qCentralInvolution ∈ K)
    (hb : ∀ k : Fin 23, monsterNortonShortQ (monsterNortonEvenShortBasis k) ∈ K)
    (i : Fin 23) : qCoordinateGenerator (Fin.castAdd 1 i) ∈ K := by
  have hbin (k : Fin 23) : monsterNortonEvenShortBasisBinary k ∈ qSubgroupBinaryImage K := by
    have hq := Subgroup.mem_map_of_mem qQuotHom (hb k)
    change toAdd (monsterNortonShortQ (monsterNortonEvenShortBasis k)).base ∈
      qSubgroupBinaryImage K at hq
    rwa [monsterNortonEvenShortBasisBinary_actual k] at hq
  have hi : (∑ k : Fin 23,
      monsterNortonEvenShortBasisInverse i k • monsterNortonEvenShortBasisBinary k) ∈
        qSubgroupBinaryImage K := by
    apply Submodule.sum_mem
    intro k _
    exact (qSubgroupBinaryImage K).smul_mem _ (hbin k)
  rw [monsterNortonEvenShortBasisInverse_certificate] at hi
  exact q_mem_of_binary_mem K hz (qCoordinateGenerator (Fin.castAdd 1 i)) hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
