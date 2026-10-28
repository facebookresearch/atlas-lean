/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightTransitivity

/-! Internal norm-eight transitivity for every actual coordinate Golay octad. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Support in the specified actual binary octad. -/
def generatedOctadSupported (c : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) : Prop :=
  ∀ i, c i = 0 → u i = 0

/-- Preservation of the specified integral coordinate section in both directions. -/
def generatedOctadPreserves (c : Fin 24 → ZMod 2) (e : leechIsomSubgroup) : Prop :=
  ∀ u : leechIntegral, generatedOctadSupported c (leechIntegralAction e u).val ↔
    generatedOctadSupported c u.val

/-- For the standard octad the support predicates agree. -/
theorem generatedOctadSupported_standard (u : Fin 24 → ℤ) :
    generatedOctadSupported golayStandardOctad u ↔ generatedStandardOctadSupported u := by
  constructor
  · intro h i hi
    exact h i (by simp [golayStandardOctad, show ¬ i.val < 8 by omega])
  · intro h i hi
    have hb : 8 ≤ i.val := by
      by_contra hn
      simp [golayStandardOctad, show i.val < 8 by omega] at hi
    exact h i hb

/-- A genuine Golay permutation transports exactly the whole integral coordinate section. -/
theorem generatedOctadSupported_permutation (c d : Fin 24 → ZMod 2)
    (p : golayAutomorphismSubgroup) (hp : golayPermute p.val c = d) (u : leechIntegral) :
    generatedOctadSupported d (leechIntegralAction (golayPermutationIsometry p) u).val ↔
      generatedOctadSupported c u.val := by
  rw [leechIntegralAction_golayPermutation]
  constructor
  · intro h i hi
    have hd : d (p.val i) = 0 := by
      have he := congrFun hp (p.val i)
      change c (p.val.symm (p.val i)) = d (p.val i) at he
      simpa only [p.val.symm_apply_apply, hi] using he.symm
    simpa only [golayIntegerPermute, p.val.symm_apply_apply] using h (p.val i) hd
  · intro h i hi
    have hc : c (p.val.symm i) = 0 := (congrFun hp i).trans hi
    exact h (p.val.symm i) hc

/-- Two genuine norm-eight vectors in any actual octad section are conjugate
by concrete generators preserving that same section. -/
theorem generatedOctad_normEight_transitive (c : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hw : ∑ i, (c i).val = 8)
    (u v : leechIntegral) (hu : generatedOctadSupported c u.val)
    (hv : generatedOctadSupported c v.val)
    (hnu : leechSquareSum u.val = 64) (hnv : leechSquareSum v.val = 64) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      generatedOctadPreserves c e ∧ leechIntegralAction e u = v := by
  obtain ⟨p, hp⟩ := golayOctad_to_standard c hc hw
  let P := golayPermutationIsometry p
  have hP (x : leechIntegral) :
      generatedStandardOctadSupported (leechIntegralAction P x).val ↔
        generatedOctadSupported c x.val :=
    (generatedOctadSupported_standard _).symm.trans
      (generatedOctadSupported_permutation c golayStandardOctad p hp x)
  obtain ⟨a, ha, hap, hau⟩ := generatedStandardOctad_normEight_transitive
    (leechIntegralAction P u) (by rw [leechIntegralAction_squareSum, hnu]) ((hP u).mpr hu)
  obtain ⟨b, hb, hbp, hbv⟩ := generatedStandardOctad_normEight_transitive
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
