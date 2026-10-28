/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Support of products of two coordinate-pair classes in the actual Leech quotient.
Short sums/differences have every coordinate divisible by four, so the
classified norm-four representatives are coordinate pairs again.
Source: Seysen, arXiv:2002.10921v3, §6.2.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortBasisProduct

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative

theorem griessPairIntegral_dvd_four (s : Fin 2) (p : Fin 276) (i : Fin 24) :
    4 ∣ griessShortIntegral (Sum.inl (s, p)) i := by
  simp only [griessShortIntegral]
  split_ifs <;> norm_num

theorem leechFour_short_class_is_pair (v : leechIntegral)
    (hv : leechSquareSum v.val = 32) (hf : ∀ i, 4 ∣ v.val i) :
    ∃ s : Fin 2, ∃ p : Fin 276, leechReduction v = griessShortClass (Sum.inl (s, p)) := by
  obtain ⟨s, p, h | h⟩ := four_short_pair v.val hv hf
  · refine ⟨s, p, ?_⟩
    have he : v = griessShortLatticeVector (Sum.inl (s, p)) := Subtype.ext h
    rw [he]
    rfl
  · refine ⟨s, p, ?_⟩
    have he : v = -griessShortLatticeVector (Sum.inl (s, p)) := Subtype.ext h
    rw [he, leechReduction_neg]
    rfl

/-- A short output of two pair classes is another pair class; octad and odd
labels cannot occur. This follows from the actual lattice geometry. -/
theorem griessPairQ_product_short_is_pair (s t : Fin 2) (p q : Fin 276)
    (u : GriessShortIndex)
    (hprod : (griessShortQ (Sum.inl (s, p)) * griessShortQ (Sum.inl (t, q))).base =
      (griessShortQ u).base) :
    ∃ w : Fin 2, ∃ r : Fin 276, u = Sum.inl (w, r) := by
  have hc := (griessShortQ_product_base_class _ _ u).mp hprod
  have hs : IsLeechShortClass (griessShortClass (Sum.inl (s, p)) +
      griessShortClass (Sum.inl (t, q))) := by
    rw [hc]
    exact (griessShortClassMap u).property
  have hpair := (griessShort_sum_class_iff_pairing _ _).mp hs
  have hstep (v : leechIntegral) (hv : leechSquareSum v.val = 32)
      (hf : ∀ i, 4 ∣ v.val i)
      (hred : leechReduction v = griessShortClass (Sum.inl (s, p)) +
        griessShortClass (Sum.inl (t, q))) :
      ∃ w : Fin 2, ∃ r : Fin 276, u = Sum.inl (w, r) := by
    obtain ⟨w, r, he⟩ := leechFour_short_class_is_pair v hv hf
    refine ⟨w, r, ?_⟩
    apply griessShortClass_injective
    exact hc.symm.trans (hred.symm.trans he)
  rcases hpair with hp | hm
  · refine hstep (griessShortLatticeVector (Sum.inl (s, p)) -
      griessShortLatticeVector (Sum.inl (t, q))) ?_ ?_ ?_
    · change leechSquareSum (griessShortIntegral (Sum.inl (s, p)) -
        griessShortIntegral (Sum.inl (t, q))) = 32
      rw [leechSquareSum_sub, griessShortIntegral_squareSum, griessShortIntegral_squareSum, hp]
      norm_num
    · intro i
      exact dvd_sub (griessPairIntegral_dvd_four s p i) (griessPairIntegral_dvd_four t q i)
    · rw [map_sub]
      change griessShortClass _ - griessShortClass _ = _
      have hn : -griessShortClass (Sum.inl (t, q)) = griessShortClass (Sum.inl (t, q)) := by
        rw [griessShortClass, ← map_neg, leechReduction_neg]
      rw [sub_eq_add_neg, hn]
  · refine hstep (griessShortLatticeVector (Sum.inl (s, p)) +
      griessShortLatticeVector (Sum.inl (t, q))) ?_ ?_ ?_
    · change leechSquareSum (griessShortIntegral (Sum.inl (s, p)) +
        griessShortIntegral (Sum.inl (t, q))) = 32
      rw [leechSquareSum_add, griessShortIntegral_squareSum, griessShortIntegral_squareSum, hm]
      norm_num
    · intro i
      exact dvd_add (griessPairIntegral_dvd_four s p i) (griessPairIntegral_dvd_four t q i)
    · exact map_add leechReduction _ _
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
