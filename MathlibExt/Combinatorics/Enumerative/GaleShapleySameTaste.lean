/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.StableMatchingSequences
import Mathlib.Data.Finset.Max

/-!
# Gale–Shapley rounds with identical men's preferences

In each round the unengaged men all propose to the same woman, the next in their common ranking.
She keeps her favorite among them. Earlier engagements persist because no new proposal goes to
any of the earlier women. Thus the number of unengaged men decreases by one in each round until
it reaches zero.

## References

* Matvey Borodin, Aidan Duncan, Boyan Litchev, Jiahe Liu, Veronika Moroz, Matthew Qian,
  Rohith Raghavan, Garima Rastogi, Michael Voigt, and Tanya Khovanova,
  [*Sequences of the Stable Matching Problem*](https://cs.uwaterloo.ca/journals/JIS/VOL27/Khovanova/khova32.pdf),
  Journal of Integer Sequences 27 (2024), Article 24.2.2, pp. 1–24, Section 3.4, Proposition 1.
-/

set_option autoImplicit false

namespace MetaMathlibExt.StableMatchingSequences

variable {n : ℕ}

/-- With a common ranking, proposals to the same woman are made at the same position. -/
private theorem gsEngaged_iff_of_same_taste (P : PreferenceProfile n)
    (h : ∀ i i' : Fin n, P.1 i = P.1 i') (p : Fin n → ℕ) (i : Fin n) :
    GSEngaged P p i ↔ ∃ r : Fin n, r.val + 1 = p i ∧
      ∀ j : Fin n, r.val < p j → womanRank P (P.1 i r) i ≤ womanRank P (P.1 i r) j := by
  constructor
  · rintro ⟨r, hr, hbest⟩
    exact ⟨r, hr, fun j hj => hbest j r hj (by rw [h j i])⟩
  · rintro ⟨r, hr, hbest⟩
    refine ⟨r, hr, fun j s hs heq => hbest j ?_⟩
    rw [h j i] at heq
    rwa [(P.1 i).injective heq] at hs

private theorem gsProposals_le_round (P : PreferenceProfile n) (t : ℕ) (i : Fin n) :
    gsProposals P t i ≤ t := by
  classical
  induction t with
  | zero => simp [gsProposals_zero]
  | succ t ih =>
    rw [gsProposals_succ]
    split
    · exact ih.trans (Nat.le_succ t)
    · exact Nat.succ_le_succ ih

/-- The men without a provisional engagement after round `t`. -/
private noncomputable def gsUnengaged (P : PreferenceProfile n) (t : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ¬ GSEngaged P (gsProposals P t) i

private theorem mem_gsUnengaged {P : PreferenceProfile n} {t : ℕ} {i : Fin n} :
    i ∈ gsUnengaged P t ↔ ¬ GSEngaged P (gsProposals P t) i := by
  classical
  simp [gsUnengaged]

/-- If the unengaged men have each made `t` proposals, exactly one of them leaves that set in
round `t + 1`: the next woman's favorite among those men. -/
private theorem gsUnengaged_succ (P : PreferenceProfile n)
    (h : ∀ i i' : Fin n, P.1 i = P.1 i') {t : ℕ} (ht : t < n)
    (hcount : ∀ i ∈ gsUnengaged P t, gsProposals P t i = t) (hne : (gsUnengaged P t).Nonempty) :
    ∃ m ∈ gsUnengaged P t, gsUnengaged P (t + 1) = (gsUnengaged P t).erase m := by
  classical
  have hhold (i : Fin n) (hi : GSEngaged P (gsProposals P t) i) :
      gsProposals P (t + 1) i = gsProposals P t i := by
    rw [gsProposals_succ, ite_eq_left hi]
  have hfree (i : Fin n) (hi : i ∈ gsUnengaged P t) : gsProposals P (t + 1) i = t + 1 := by
    rw [gsProposals_succ, ite_eq_right (mem_gsUnengaged.mp hi), hcount i hi]
  -- At any earlier position, the set of men who have proposed there is unchanged.
  have hstay (i : Fin n) (hi : GSEngaged P (gsProposals P t) i) :
      GSEngaged P (gsProposals P (t + 1)) i := by
    obtain ⟨s, hs, hbest⟩ := (gsEngaged_iff_of_same_taste P h _ i).mp hi
    refine (gsEngaged_iff_of_same_taste P h _ i).mpr ⟨s, ?_, fun j hj => hbest j ?_⟩
    · rwa [hhold i hi]
    · by_cases hje : GSEngaged P (gsProposals P t) j
      · rwa [hhold j hje] at hj
      · rw [hcount j (mem_gsUnengaged.mpr hje)]
        exact Nat.lt_of_succ_le (by simpa only [← hs] using gsProposals_le_round P t i)
  obtain ⟨a, ha⟩ := hne
  let r : Fin n := ⟨t, ht⟩
  let w : Fin n := P.1 a r
  -- The only proposals at the new position are those of the previously unengaged men.
  have hnext (i : Fin n) (hi : i ∈ gsUnengaged P t) :
      GSEngaged P (gsProposals P (t + 1)) i ↔
        ∀ j ∈ gsUnengaged P t, womanRank P w i ≤ womanRank P w j := by
    rw [gsEngaged_iff_of_same_taste P h]
    have hw : P.1 i r = w := by
      rw [h i a]
    constructor
    · rintro ⟨s, hs, hbest⟩ j hj
      rw [hfree i hi] at hs
      have hsr : s = r := Fin.ext (Nat.succ.inj hs)
      subst s
      rw [← hw]
      exact hbest j (by rw [hfree j hj]; exact Nat.lt_succ_self t)
    · intro hbest
      refine ⟨r, (hfree i hi).symm, fun j hj => ?_⟩
      rw [hw]
      by_cases hje : GSEngaged P (gsProposals P t) j
      · rw [hhold j hje] at hj
        exact (Nat.not_lt_of_ge (gsProposals_le_round P t j) hj).elim
      · exact hbest j (mem_gsUnengaged.mpr hje)
  let ranks := (gsUnengaged P t).image (womanRank P w)
  have hranks : ranks.Nonempty := ⟨womanRank P w a, Finset.mem_image_of_mem _ ha⟩
  obtain ⟨m, hm, hmr⟩ := Finset.mem_image.mp (ranks.min'_mem hranks)
  have hmin (j : Fin n) (hj : j ∈ gsUnengaged P t) : womanRank P w m ≤ womanRank P w j :=
    hmr.trans_le (ranks.min'_le _ (Finset.mem_image_of_mem _ hj))
  refine ⟨m, hm, Finset.ext fun i => ?_⟩
  by_cases hi : i ∈ gsUnengaged P t
  · have hwin : GSEngaged P (gsProposals P (t + 1)) i ↔ i = m := by
      constructor
      · intro hei
        have hle := (hnext i hi).mp hei m hm
        exact (P.2 w).symm.injective (Fin.ext (le_antisymm hle (hmin i hi)))
      · intro him
        rw [him]
        exact (hnext m hm).mpr hmin
    rw [mem_gsUnengaged, hwin, Finset.mem_erase]
    simp [hi]
  · have hei : GSEngaged P (gsProposals P t) i := by
      by_contra hni
      exact hi (mem_gsUnengaged.mpr hni)
    rw [mem_gsUnengaged, Finset.mem_erase]
    simp [hstay i hei, hi]

/-- After `t ≤ n` rounds, exactly `n - t` men are unengaged, and each has made `t` proposals. -/
private theorem gsUnengaged_card (P : PreferenceProfile n)
    (h : ∀ i i' : Fin n, P.1 i = P.1 i') (t : ℕ) (ht : t ≤ n) :
    (gsUnengaged P t).card = n - t ∧ ∀ i ∈ gsUnengaged P t, gsProposals P t i = t := by
  classical
  induction t with
  | zero =>
    have hz (i : Fin n) : ¬ GSEngaged P (gsProposals P 0) i := by
      rintro ⟨r, hr, -⟩
      rw [gsProposals_zero] at hr
      exact Nat.succ_ne_zero _ hr
    exact ⟨by simp [gsUnengaged, hz], by simp [gsProposals_zero]⟩
  | succ t ih =>
    have htn : t < n := ht
    obtain ⟨hc, hp⟩ := ih (Nat.le_of_lt htn)
    have hne : (gsUnengaged P t).Nonempty := Finset.card_pos.mp (by rw [hc]; omega)
    obtain ⟨m, hm, herase⟩ := gsUnengaged_succ P h htn hp hne
    refine ⟨?_, fun i hi => ?_⟩
    · rw [herase, Finset.card_erase_of_mem hm, hc]
      omega
    · rw [herase] at hi
      have hi' := (Finset.mem_erase.mp hi).2
      rw [gsProposals_succ, ite_eq_right (mem_gsUnengaged.mp hi'), hp i hi']

/-- **Gale–Shapley rounds when all men have the same preferences.** Let $P$ be a preference
profile for $n$ men and $n$ women in which all men rank the women in the same order. Then the
men-proposing Gale–Shapley algorithm on $P$ ends in exactly $n$ rounds.

Source: Borodin, Duncan, Litchev, Liu, Moroz, Qian, Raghavan, Rastogi, Voigt,
and Khovanova, *Sequences of the Stable Matching Problem*, Journal of Integer
Sequences 27 (2024), Article 24.2.2, Proposition 1
(`jis-2024-24.2.2-prop-1`). -/
public theorem galeShapleyRounds_of_same_taste (P : PreferenceProfile n)
    (h : ∀ i i' : Fin n, P.1 i = P.1 i') :
    galeShapleyRounds P = n := by
  classical
  let finished : Set ℕ := {t | ∀ i : Fin n, GSEngaged P (gsProposals P t) i}
  have hleast : IsLeast finished n := by
    constructor
    · have hempty : gsUnengaged P n = ∅ :=
        Finset.card_eq_zero.mp (by simpa using (gsUnengaged_card P h n le_rfl).1)
      intro i
      by_contra hi
      have hmem := mem_gsUnengaged.mpr hi
      simp [hempty] at hmem
    · intro t ht
      by_contra! htn
      have hempty : gsUnengaged P t = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact mem_gsUnengaged.mp hi (ht i)
      have hc := (gsUnengaged_card P h t htn.le).1
      rw [hempty, Finset.card_empty] at hc
      omega
  exact (isLeast_csInf ⟨n, hleast.1⟩).unique hleast

end MetaMathlibExt.StableMatchingSequences
