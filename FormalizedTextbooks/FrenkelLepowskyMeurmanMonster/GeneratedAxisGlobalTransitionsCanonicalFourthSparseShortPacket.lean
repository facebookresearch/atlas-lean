/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCanonicalFourthShortRationalPacket

/-! A complete finite preferred-basis packet for the genuine original Fourth short vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- All pair rows and all 63 original octad Fourier rows. -/
abbrev GeneratedAxisGlobalCanonicalFourthShortPacketIndex :=
  (Fin 2 × Fin 276) ⊕ (Fin 63 × Fin 64)

/-- The original preferred coordinate of each true source packet term. -/
def generatedAxisGlobalCanonicalFourthShortPacketLabel :
    GeneratedAxisGlobalCanonicalFourthShortPacketIndex → GriessShortIndex
  | Sum.inl p => Sum.inl p
  | Sum.inr (j, e) => Sum.inr (Sum.inl (generatedFourthEvenRootOctad j, e))

/-- Exact original pair coefficients and source-signed Fourier coefficients. -/
def generatedAxisGlobalCanonicalFourthShortPacketCoefficient :
    GeneratedAxisGlobalCanonicalFourthShortPacketIndex → ℚ
  | Sum.inl (s, p) => generatedAxisGlobalCanonicalFourthPairShortQ s p
  | Sum.inr (j, e) =>
      (trialityIntegerMatrix e (generatedFourthEvenRootSign j) : ℚ) / 8 *
        (generatedAxisGlobalIntSign (generatedFourthEvenCoefficientCache j) : ℚ)

/-- Repeated octad labels retain all their actual original Fourier contributions. -/
def generatedAxisGlobalCanonicalFourthSparseShortQ (r : GriessShortIndex) : ℚ :=
  ∑ p : GeneratedAxisGlobalCanonicalFourthShortPacketIndex,
    generatedAxisGlobalCanonicalFourthShortPacketCoefficient p *
      (if generatedAxisGlobalCanonicalFourthShortPacketLabel p = r then 1 else 0)

private theorem fourth_sparse_code (j : Fin 63) (o : Fin 759) :
    generatedFourthEvenRootOctad j = o ↔ generatedFourthEvenRootCode j = golayOctadLabel o := by
  constructor
  · intro h
    simpa only [generatedFourthEvenRootOctad_label] using congrArg golayOctadLabel h
  · intro h
    apply golayOctadLabel_injective
    simpa only [generatedFourthEvenRootOctad_label] using h

/-- The entire finite basis packet equals the full original rational short formula. -/
theorem generatedAxisGlobalCanonicalFourthSparseShortQ_eq (r : GriessShortIndex) :
    generatedAxisGlobalCanonicalFourthSparseShortQ r = generatedAxisGlobalCanonicalFourthFastShortQ r := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · simp [generatedAxisGlobalCanonicalFourthSparseShortQ,
      generatedAxisGlobalCanonicalFourthShortPacketCoefficient,
      generatedAxisGlobalCanonicalFourthShortPacketLabel,
      generatedAxisGlobalCanonicalFourthFastShortQ, Fintype.sum_sum_type]
  · simp only [generatedAxisGlobalCanonicalFourthSparseShortQ, Fintype.sum_sum_type,
      Fintype.sum_prod_type, generatedAxisGlobalCanonicalFourthShortPacketCoefficient,
      generatedAxisGlobalCanonicalFourthShortPacketLabel,
      generatedAxisGlobalCanonicalFourthFastShortQ]
    simp only [Sum.inl_ne_inr, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq]
    simp_rw [mul_ite, mul_one, mul_zero, ite_and]
    simp only [Finset.sum_const_zero, Finset.sum_ite_irrel,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [generatedFourthQShortBasisOctadNumerator]
    push_cast
    rw [Finset.sum_div]
    simp only [zero_add]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : generatedFourthEvenRootOctad j = o
    · have hc := (fourth_sparse_code j o).mp h
      by_cases hp : generatedFourthEvenCoefficientCache j = 0
      · simp [h, hc, hp, generatedAxisGlobalIntSign]
      · simp [h, hc, hp, generatedAxisGlobalIntSign]
        exact (neg_div _ _).symm
    · have hc : generatedFourthEvenRootCode j ≠ golayOctadLabel o :=
        fun hc => h ((fourth_sparse_code j o).mpr hc)
      simp [h, hc]
  · simp [generatedAxisGlobalCanonicalFourthSparseShortQ,
      generatedAxisGlobalCanonicalFourthShortPacketCoefficient,
      generatedAxisGlobalCanonicalFourthShortPacketLabel,
      generatedAxisGlobalCanonicalFourthFastShortQ, Fintype.sum_sum_type]

/-- The finite original preferred-basis sum is the entire genuine Fourth short constituent. -/
theorem generatedAxisGlobalCanonicalFourthSparseShortPacket_actual :
    (griessConwayEncode generatedFourthAxis).2.1 =
      ∑ p : GeneratedAxisGlobalCanonicalFourthShortPacketIndex,
        (generatedAxisGlobalCanonicalFourthShortPacketCoefficient p : ℝ) •
          Pi.single (generatedAxisGlobalCanonicalFourthShortPacketLabel p) (1 : ℝ) := by
  funext r
  rw [← generatedAxisGlobalCanonicalFourthFastShortQ_actual,
    ← generatedAxisGlobalCanonicalFourthSparseShortQ_eq]
  simp only [generatedAxisGlobalCanonicalFourthSparseShortQ, Rat.cast_sum, Rat.cast_mul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : generatedAxisGlobalCanonicalFourthShortPacketLabel p = r <;> simp [h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
