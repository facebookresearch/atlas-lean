/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightTransport

/-! Internal short-vector transitivity in every actual coordinate E8 section. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Two genuine short vectors in any actual octad section are conjugate
by concrete generators preserving that same section. -/
theorem generatedOctad_short_transitive (c : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hw : ∑ i, (c i).val = 8)
    (u v : leechIntegral) (hu : generatedOctadSupported c u.val)
    (hv : generatedOctadSupported c v.val)
    (hnu : leechSquareSum u.val = 32) (hnv : leechSquareSum v.val = 32) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      generatedOctadPreserves c e ∧ leechIntegralAction e u = v := by
  obtain ⟨p, hp⟩ := golayOctad_to_standard c hc hw
  let P := golayPermutationIsometry p
  have hP (x : leechIntegral) :
      generatedStandardOctadSupported (leechIntegralAction P x).val ↔
        generatedOctadSupported c x.val :=
    (generatedOctadSupported_standard _).symm.trans
      (generatedOctadSupported_permutation c golayStandardOctad p hp x)
  obtain ⟨a, ha, hap, hau⟩ := generatedE8Short_reduction
    (leechIntegralAction P u) (by rw [leechIntegralAction_squareSum, hnu]) ((hP u).mpr hu)
  obtain ⟨b, hb, hbp, hbv⟩ := generatedE8Short_reduction
    (leechIntegralAction P v) (by rw [leechIntegralAction_squareSum, hnv]) ((hP v).mpr hv)
  have hmid := generatedStandardOctadPreserves_mul b⁻¹ a
    (generatedStandardOctadPreserves_inv b hbp) hap
  refine ⟨P⁻¹ * (b⁻¹ * a) * P,
    leechConcreteGeneratorSubgroup.mul_mem
      (leechConcreteGeneratorSubgroup.mul_mem
        (leechConcreteGeneratorSubgroup.inv_mem (golayPermutationIsometry_mem_concrete p))
        (leechConcreteGeneratorSubgroup.mul_mem
          (leechConcreteGeneratorSubgroup.inv_mem hb) ha))
      (golayPermutationIsometry_mem_concrete p), ?_, ?_⟩
  · intro x
    have he : leechIntegralAction P (leechIntegralAction (P⁻¹ * (b⁻¹ * a) * P) x) =
        leechIntegralAction (b⁻¹ * a) (leechIntegralAction P x) := by
      rw [← LinearEquiv.mul_apply, ← map_mul]
      have hm : P * (P⁻¹ * (b⁻¹ * a) * P) = (b⁻¹ * a) * P := by group
      rw [hm, map_mul, LinearEquiv.mul_apply]
    exact (hP _).symm.trans (by
      rw [he]
      exact (hmid _).trans (hP x))
  · apply (leechIntegralAction P).injective
    apply (leechIntegralAction b).injective
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul]
    have hm : b * P * (P⁻¹ * (b⁻¹ * a) * P) = a * P := by group
    rw [hm, map_mul, LinearEquiv.mul_apply]
    apply Subtype.ext
    exact hau.trans hbv.symm


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
