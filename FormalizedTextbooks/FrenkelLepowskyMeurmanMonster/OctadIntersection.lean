/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual Golay octad intersection bounds and the four-point-overlap sum octad. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPairQProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.DisjointOctadTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

def golayOctadWord (o : Fin 759) : Fin 24 → ZMod 2 :=
  golayEncoder (golayLabelCoefficients (golayOctadLabel o))
def golayOctadSupport (o : Fin 759) : Finset (Fin 24) :=
  golayMaskSupport (golayEncodedMask (golayOctadLabel o).val)
theorem golayOctadIntersection_support (o p : Fin 759) :
    golayOctadIntersection o p = golayOctadSupport o ∩ golayOctadSupport p := rfl

@[simp] theorem golayOctadSupport_card (o : Fin 759) : (golayOctadSupport o).card = 8 :=
  golayOctad_support_card o

@[simp] theorem golayOctadWord_mem_code (o : Fin 759) : golayOctadWord o ∈ golayCode :=
  ⟨_, rfl⟩

@[simp] theorem golayOctadWord_ne_zero_iff (o : Fin 759) (i : Fin 24) :
    golayOctadWord o i ≠ 0 ↔ i ∈ golayOctadSupport o := by
  simp only [golayOctadWord, golayLabelEncoder_boolean, golayOctadSupport,
    golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  cases hb : (golayEncodedMask (golayOctadLabel o).val).testBit i.val <;>
    norm_num [golayBooleanCast]

theorem golayOctadWord_weight (o : Fin 759) : (∑ i, (golayOctadWord o i).val) = 8 := by
  calc
    _ = golayMaskWeight (golayEncodedMask (golayOctadLabel o).val) := by
      apply Finset.sum_congr rfl
      intro i _
      exact golayLabelEncoder_match _ i
    _ = 8 := by rw [← golayMaskSupport_card]; exact golayOctad_support_card o

theorem golayOctadWord_injective : Function.Injective golayOctadWord := by
  intro o p h
  apply golayOctadLabel_injective
  apply golayLabelCoefficients_bijective.1
  exact golayEncoder_injective h

private theorem binary_add_weight (a b : ZMod 2) :
    (a+b).val + 2 * (if a ≠ 0 ∧ b ≠ 0 then 1 else 0) = a.val + b.val := by
  fin_cases a <;> fin_cases b <;> decide +kernel

private theorem binary_support_sum_weight (a b : Fin 24 → ZMod 2)
    (A B : Finset (Fin 24)) (ha : ∀ i, a i ≠ 0 ↔ i ∈ A)
    (hb : ∀ i, b i ≠ 0 ↔ i ∈ B) :
    (∑ i, ((a+b) i).val) + 2 * (A ∩ B).card =
      (∑ i, (a i).val) + (∑ i, (b i).val) := by
  have hpoint (i : Fin 24) :
      ((a+b) i).val + 2 * (if i ∈ A ∩ B then 1 else 0) = (a i).val + (b i).val := by
    simpa only [Pi.add_apply, Finset.mem_inter, ← ha i, ← hb i] using
      binary_add_weight (a i) (b i)
  have hs := congrArg (fun f : Fin 24 → ℕ => ∑ i, f i) (funext hpoint)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id] using hs

/-- The symmetric difference of two eight-point supports has weight16 minus
 twice the intersection size. This proof sums the four binary-coordinate cases. -/
theorem golayOctad_sum_weight (o p : Fin 759) :
    (∑ i, ((golayOctadWord o + golayOctadWord p) i).val) +
      2 * (golayOctadIntersection o p).card = 16 := by
  have hs := binary_support_sum_weight (golayOctadWord o) (golayOctadWord p)
    (golayOctadSupport o) (golayOctadSupport p)
    (golayOctadWord_ne_zero_iff o) (golayOctadWord_ne_zero_iff p)
  rw [golayOctadWord_weight, golayOctadWord_weight] at hs
  simpa only [golayOctadIntersection_support, show (8 + 8 : ℕ) = 16 by decide] using hs

theorem golayOctad_sum_ne_zero (o p : Fin 759) (hop : o ≠ p) :
    golayOctadWord o + golayOctadWord p ≠ 0 := by
  intro h
  have he : golayOctadWord o = golayOctadWord p := by
    have ht := congrArg (fun v : Fin 24 → ZMod 2 => v + golayOctadWord p) h
    simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using ht
  exact hop (golayOctadWord_injective he)

/-- Distinct Golay octads intersect in exactly zero, two, or four points. -/
theorem golayOctad_intersection_cases (o p : Fin 759) (hop : o ≠ p) :
    (golayOctadIntersection o p).card = 0 ∨ (golayOctadIntersection o p).card = 2 ∨
      (golayOctadIntersection o p).card = 4 := by
  have hsum := golayOctad_sum_weight o p
  have hc : golayOctadWord o + golayOctadWord p ∈ golayCode :=
    golayCode.add_mem (golayOctadWord_mem_code o) (golayOctadWord_mem_code p)
  have hmin := golayCode_weight_ge_eight _ hc (golayOctad_sum_ne_zero o p hop)
  have hw := golayCode_weights _ hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  omega

theorem golayOctad_intersection_le_four (o p : Fin 759) (hop : o ≠ p) :
    (golayOctadIntersection o p).card ≤ 4 := by
  rcases golayOctad_intersection_cases o p hop with h | h | h <;> omega

theorem golayOctad_intersection_even (o p : Fin 759) : 2 ∣ (golayOctadIntersection o p).card := by
  by_cases hop : o = p
  · subst p
    rw [golayOctadIntersection_support, Finset.inter_self, golayOctadSupport_card]
    norm_num
  · rcases golayOctad_intersection_cases o p hop with h | h | h <;> rw [h] <;> norm_num

/-- Every weight-eight vector of the actual Golay code has a unique catalogued octad label. -/
theorem golayOctadWord_of_weight_eight (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode)
    (hw : (∑ i, (c i).val) = 8) : ∃! o : Fin 759, golayOctadWord o = c := by
  obtain ⟨a, ha⟩ := hc
  obtain ⟨d, hd⟩ := golayLabelCoefficients_bijective.2 a
  have hm : golayMaskWeight (golayEncodedMask d.val) = 8 := by
    rw [← hw, ← ha, ← hd]
    apply Finset.sum_congr rfl
    intro i _
    exact (golayLabelEncoder_match d i).symm
  have hmem : d ∈ golayOctads := Finset.mem_filter.mpr ⟨Finset.mem_univ d, hm⟩
  let o : Fin 759 := (golayOctads.orderIsoOfFin golayOctads_card).symm ⟨d,hmem⟩
  have ho : golayOctadLabel o = d :=
    congrArg Subtype.val
      ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply ⟨d,hmem⟩)
  have hwitness : golayOctadWord o = c := by rw [golayOctadWord, ho, hd, ha]
  exact ⟨o, hwitness, fun p hp => golayOctadWord_injective (hp.trans hwitness.symm)⟩

/-- Two octads with a four-point intersection add to a unique third actual octad. -/
theorem golayOctad_sum_octad (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) :
    ∃! u : Fin 759, golayOctadWord u = golayOctadWord o + golayOctadWord p := by
  apply golayOctadWord_of_weight_eight
  · exact golayCode.add_mem (golayOctadWord_mem_code o) (golayOctadWord_mem_code p)
  · have hs := golayOctad_sum_weight o p
    rw [hfour] at hs
    omega

/-- The third octad also has precisely the sum of the two published twelve-bit labels. -/
theorem golayOctad_sum_label_coefficients (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) :
    ∃! u : Fin 759, golayLabelCoefficients (golayOctadLabel u) =
      golayLabelCoefficients (golayOctadLabel o) + golayLabelCoefficients (golayOctadLabel p) := by
  obtain ⟨u, hu, huniq⟩ := golayOctad_sum_octad o p hfour
  have hcoeff : golayLabelCoefficients (golayOctadLabel u) =
      golayLabelCoefficients (golayOctadLabel o) + golayLabelCoefficients (golayOctadLabel p) := by
    apply golayEncoder_injective
    rw [map_add]
    exact hu
  refine ⟨u, hcoeff, ?_⟩
  intro v hv
  apply huniq
  have he := congrArg golayEncoder hv
  simpa only [map_add, golayOctadWord] using he


theorem golayOctad_intersection_le_two_or_four (o p : Fin 759) (hop : o ≠ p) :
    (golayOctadIntersection o p).card ≤ 2 ∨ (golayOctadIntersection o p).card = 4 := by
  rcases golayOctad_intersection_cases o p hop with h | h | h <;> omega

/-- A four-point overlap gives a twelve-point physical union. -/
theorem golayOctad_union_card (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) :
    (golayOctadSupport o ∪ golayOctadSupport p).card = 12 := by
  have h := Finset.card_union_add_card_inter (golayOctadSupport o) (golayOctadSupport p)
  rw [golayOctadSupport_card, golayOctadSupport_card,
    ← golayOctadIntersection_support, hfour] at h
  omega

private theorem binary_add_ne_zero : ∀ a b : ZMod 2,
    a+b ≠ 0 ↔ (a ≠ 0 ∧ b = 0) ∨ (b ≠ 0 ∧ a = 0) := by
  decide +kernel

/-- The third octad support is the physical symmetric difference of its two parents. -/
theorem golayOctad_sum_support (o p u : Fin 759)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p) :
    golayOctadSupport u = symmDiff (golayOctadSupport o) (golayOctadSupport p) := by
  ext i
  simp only [← golayOctadWord_ne_zero_iff, Finset.mem_symmDiff, hu, Pi.add_apply,
    not_not]
  exact binary_add_ne_zero _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
