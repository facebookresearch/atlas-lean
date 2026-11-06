/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketPairSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketOddCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketOctadCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketLabels
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketReindex

/-! The complete labelled packet is the original canonical short vector in every coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The complete canonical pair numerator in the genuine input coordinate enumeration. -/
def generatedSeventhXiShortPairCoefficient (s : Fin 2) (p : Fin 276) : ℤ :=
  (if p.val = 248 ∨ p.val = 250 ∨ p.val = 256 then 4 else 0) +
    (if s = 0 then 1 else -1) *
      generatedSeventhXiTensorFrame (generatedSeventhXiShortInputCoordinates p).1 *
      generatedSeventhXiTensorFrame (generatedSeventhXiShortInputCoordinates p).2

private def pairVector : GriessShortIndex → ℝ :=
  ∑ s : Fin 2, ∑ p : Fin 276, ((generatedSeventhXiShortPairCoefficient s p : ℝ) / 32) •
    Pi.single (generatedSeventhXiShortInputLabel s p) 1

private def octadVector : GriessShortIndex → ℝ :=
  ∑ g : Fin 231, ∑ e : Fin 64, ((generatedSeventhXiShortPackedOctadCoefficient g e : ℝ) / 32) •
    Pi.single (Sum.inr (Sum.inl (generatedSeventhXiOctadFamily g, e))) 1

private def oddVector : GriessShortIndex → ℝ :=
  ∑ g : Fin 512, ∑ j : Fin 24, ((generatedSeventhXiShortPackedOddCoefficient g j : ℝ) / 32) •
    Pi.single (Sum.inr (Sum.inr (generatedSeventhXiShortPackedOddCode g, j))) 1

private theorem input_label_eq (a s : Fin 2) (b p : Fin 276) :
    generatedSeventhXiShortInputLabel a b = generatedSeventhXiShortInputLabel s p ↔
      a = s ∧ b = p := by
  have hi : Function.Injective generatedSeventhXiShortInputIndex :=
    generatedSeventhXiShortInputEquiv.injective
  simp only [generatedSeventhXiShortInputLabel, Sum.inl.injEq, Prod.mk.injEq, hi.eq_iff]

private theorem pairVector_apply (s : Fin 2) (p : Fin 276) :
    pairVector (generatedSeventhXiShortInputLabel s p) =
      (generatedSeventhXiShortPairCoefficient s p : ℝ) / 32 := by
  simp only [pairVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    input_label_eq, mul_ite, mul_one, mul_zero]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem octadVector_apply (o : Fin 759) (e : Fin 64) :
    octadVector (Sum.inr (Sum.inl (o, e))) =
      ∑ g : Fin 231, if generatedSeventhXiOctadFamily g = o then
        (generatedSeventhXiShortPackedOctadCoefficient g e : ℝ) / 32 else 0 := by
  simp only [octadVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, eq_comm]

private theorem oddVector_apply (d : Fin 2048) (j : Fin 24) :
    oddVector (Sum.inr (Sum.inr (d, j))) =
      ∑ g : Fin 512, if generatedSeventhXiShortPackedOddCode g = d then
        (generatedSeventhXiShortPackedOddCoefficient g j : ℝ) / 32 else 0 := by
  simp only [oddVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    Sum.inr.injEq, Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, eq_comm]

/-- All three complete signed basis blocks equal the original canonical short vector. -/
private theorem generatedSeventhXiShort_source_vector_parts :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1 =
      pairVector + octadVector + oddVector := by
  funext r
  cases r with
  | inl r =>
    obtain ⟨s, p⟩ := r
    obtain ⟨q, hq⟩ := generatedSeventhXiShortInputEquiv.surjective p
    change generatedSeventhXiShortInputIndex q = p at hq
    subst p
    change _ = pairVector (generatedSeventhXiShortInputLabel s q) + _ + _
    apply Eq.trans (b := (generatedSeventhXiShortPairCoefficient s q : ℝ) / 32)
    · exact generatedSeventhXiShort_pair_coefficient s q
    · rw [pairVector_apply]
      simp [octadVector, oddVector]
  | inr r =>
    cases r with
    | inl r =>
      obtain ⟨o, e⟩ := r
      rw [Pi.add_apply, Pi.add_apply, octadVector_apply,
        generatedSeventhXiShortOctadCoefficient_sum]
      simp [pairVector, oddVector, generatedSeventhXiShortInputLabel]
    | inr r =>
      obtain ⟨d, j⟩ := r
      rw [Pi.add_apply, Pi.add_apply, oddVector_apply, generatedSeventhXiShortOddCoefficient_sum]
      simp [pairVector, octadVector, generatedSeventhXiShortInputLabel]

private theorem packet_pair_term (s : Fin 2) (p : Fin 276) :
    let k : Fin 27624 := ⟨276 * s.val + p.val, by omega⟩
    ((generatedSeventhXiShortPacketCoefficient k : ℝ) / 32) •
      Pi.single (generatedSeventhXiShortPacketLabel k) 1 =
        ((generatedSeventhXiShortPairCoefficient s p : ℝ) / 32) •
          Pi.single (generatedSeventhXiShortInputLabel s p) 1 := by
  have h : 276 * s.val + p.val < 552 := by omega
  have hs : (276 * s.val + p.val) / 276 = s.val := by omega
  have hp : (276 * s.val + p.val) % 276 = p.val := by omega
  simp only [generatedSeventhXiShortPacketCoefficient, generatedSeventhXiShortPacketLabel,
    h, dite_true, hs, hp]
  rfl

private theorem packet_octad_term (g : Fin 231) (e : Fin 64) :
    let k : Fin 27624 := ⟨552 + 64 * g.val + e.val, by omega⟩
    ((generatedSeventhXiShortPacketCoefficient k : ℝ) / 32) •
      Pi.single (generatedSeventhXiShortPacketLabel k) 1 =
        ((generatedSeventhXiShortPackedOctadCoefficient g e : ℝ) / 32) •
          Pi.single (Sum.inr (Sum.inl (generatedSeventhXiOctadFamily g, e))) 1 := by
  have h1 : ¬552 + 64 * g.val + e.val < 552 := by omega
  have h2 : 552 + 64 * g.val + e.val < 15336 := by omega
  have hg : (552 + 64 * g.val + e.val - 552) / 64 = g.val := by omega
  have he : (552 + 64 * g.val + e.val - 552) % 64 = e.val := by omega
  simp only [generatedSeventhXiShortPacketCoefficient, generatedSeventhXiShortPacketLabel,
    h1, h2, dite_false, dite_true, hg, he]

private theorem packet_odd_term (g : Fin 512) (j : Fin 24) :
    let k : Fin 27624 := ⟨15336 + 24 * g.val + j.val, by omega⟩
    ((generatedSeventhXiShortPacketCoefficient k : ℝ) / 32) •
      Pi.single (generatedSeventhXiShortPacketLabel k) 1 =
        ((generatedSeventhXiShortPackedOddCoefficient g j : ℝ) / 32) •
          Pi.single (Sum.inr (Sum.inr (generatedSeventhXiShortPackedOddCode g, j))) 1 := by
  have h1 : ¬15336 + 24 * g.val + j.val < 552 := by omega
  have h2 : ¬15336 + 24 * g.val + j.val < 15336 := by omega
  have hg : (15336 + 24 * g.val + j.val - 15336) / 24 = g.val := by omega
  have hj : (15336 + 24 * g.val + j.val - 15336) % 24 = j.val := by omega
  simp only [generatedSeventhXiShortPacketCoefficient, generatedSeventhXiShortPacketLabel,
    h1, h2, dite_false, hg, hj]

/-- The complete labelled packet equals the entire original canonical short vector. -/
theorem generatedSeventhXiShortPacketVector_actual :
    generatedSeventhXiShortPacketVector =
      (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1 := by
  unfold generatedSeventhXiShortPacketVector
  rw [generatedSeventhXiShortPacket_sum_split]
  simp_rw [packet_pair_term, packet_octad_term, packet_odd_term]
  exact generatedSeventhXiShort_source_vector_parts.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
