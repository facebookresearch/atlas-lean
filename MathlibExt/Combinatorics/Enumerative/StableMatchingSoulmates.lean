/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.StableMatchingSequences
import Mathlib.Data.Set.Card

/-!
# Stable matching with all but one soulmate pair

A profile with `n - 1` soulmate pairs has a unique stable matching. The Gale–Shapley round count
is the number of proposals made by the man without a soulmate.
-/

set_option autoImplicit false

namespace MetaMathlibExt.StableMatchingSequences

variable {n : ℕ}

section

variable {P : PreferenceProfile n} {i j : Fin n}

private theorem stable_matches_soulmates {μ : Equiv.Perm (Fin n)} (hμ : IsStableMatching P μ)
    (hs : IsSoulmatePair P i j) : μ i = j := by
  by_contra hne
  have hhusband : μ.symm j ≠ i := fun heq => hne (μ.eq_symm_apply.mp heq.symm)
  refine (isStableMatching_iff P μ).mp hμ i j ⟨?_, ?_⟩
  · rw [hs.1]
    exact Nat.pos_of_ne_zero fun h =>
      hne ((P.1 i).symm.injective (Fin.ext (h.trans hs.1.symm)))
  · rw [hs.2]
    exact Nat.pos_of_ne_zero fun h =>
      hhusband ((P.2 j).symm.injective (Fin.ext (h.trans hs.2.symm)))

private theorem no_soulmate_subsingleton (h : soulmatePairCount P = n - 1) :
    {i : Fin n | ∀ j : Fin n, ¬ IsSoulmatePair P i j}.Subsingleton := by
  let f : {ij : Fin n × Fin n // IsSoulmatePair P ij.1 ij.2} → Fin n := fun x => x.1.1
  have hf : Function.Injective f := by
    rintro ⟨⟨i, j⟩, hj⟩ ⟨⟨i', j'⟩, hj'⟩ (rfl : i = i')
    have hEq : j = j' := (P.1 i).symm.injective (Fin.ext (hj.1.trans hj'.1.symm))
    subst j'
    rfl
  have hset : {i : Fin n | ∀ j : Fin n, ¬ IsSoulmatePair P i j} = (Set.range f)ᶜ := by
    ext i
    change (∀ j, ¬ IsSoulmatePair P i j) ↔ ¬ ∃ x, f x = i
    constructor
    · rintro hi ⟨⟨⟨i', j⟩, hj⟩, (rfl : i' = i)⟩
      exact hi j hj
    · exact fun hi j hj => hi ⟨⟨(i, j), hj⟩, rfl⟩
  rw [hset, ← Set.ncard_le_one_iff_subsingleton, Set.ncard_compl,
    Set.ncard_range_of_injective hf, Nat.card_fin]
  change n - soulmatePairCount P ≤ 1
  omega

private theorem not_engaged_zero (P : PreferenceProfile n) (i : Fin n) :
    ¬ GSEngaged P (gsProposals P 0) i := by
  rintro ⟨r, hr, _⟩
  exact Nat.succ_ne_zero _ hr

private theorem soulmate_engaged_of_one (hs : IsSoulmatePair P i j) {p : Fin n → ℕ}
    (hp : p i = 1) : GSEngaged P p i := by
  refine ⟨(P.1 i).symm j, ?_, ?_⟩
  · change manRank P i j + 1 = p i
    rw [hs.1, hp]
  · intro k r _ _
    rw [Equiv.apply_symm_apply, hs.2]
    exact Nat.zero_le _

private theorem soulmate_proposals (hs : IsSoulmatePair P i j) (t : ℕ) :
    gsProposals P (t + 1) i = 1 := by
  classical
  induction t with
  | zero => rw [gsProposals_succ, ite_eq_right (not_engaged_zero P i), gsProposals_zero]
  | succ t ih => rw [gsProposals_succ, ite_eq_left (soulmate_engaged_of_one hs ih), ih]

private theorem outsider_engaged_iff (μ : Equiv.Perm (Fin n)) (i : Fin n)
    (hs : ∀ k, k ≠ i → IsSoulmatePair P k (μ k)) {p : Fin n → ℕ}
    (hp : ∀ k, k ≠ i → p k = 1) :
    GSEngaged P p i ↔ p i = manRank P i (μ i) + 1 := by
  constructor
  · rintro ⟨r, hr, hbest⟩
    have hw : P.1 i r = μ i := by
      by_contra hne
      let k := μ.symm (P.1 i r)
      have hk : k ≠ i := fun heq => hne (μ.symm_apply_eq.mp heq)
      have hpair : IsSoulmatePair P k (P.1 i r) := by
        simpa only [k, Equiv.apply_symm_apply] using hs k hk
      -- The woman's soulmate proposed to her and she ranks him first.
      have hproposal : manRank P k (P.1 i r) < p k := by
        rw [hpair.1, hp k hk]
        exact Nat.zero_lt_one
      have hle := hbest k ((P.1 k).symm (P.1 i r)) hproposal (Equiv.apply_symm_apply _ _)
      rw [hpair.2, Nat.le_zero] at hle
      exact hk ((P.2 (P.1 i r)).symm.injective (Fin.ext (hpair.2.trans hle.symm)))
    rw [← hr, ← hw, manRank, Equiv.symm_apply_apply]
  · intro hi
    refine ⟨(P.1 i).symm (μ i), hi.symm, ?_⟩
    intro k r hr hw
    simp only [Equiv.apply_symm_apply] at hw ⊢
    by_cases hk : k = i
    · subst k
      exact le_rfl
    · -- Every other man only proposed to his own wife.
      have hrank : manRank P k (μ i) = 0 := by
        rw [← hw, manRank, Equiv.symm_apply_apply]
        exact Nat.lt_one_iff.mp (hp k hk ▸ hr)
      exact (hk (μ.injective
        ((P.1 k).symm.injective (Fin.ext ((hs k hk).1.trans hrank.symm))))).elim

private theorem rounds_of_outsider (μ : Equiv.Perm (Fin n)) (i : Fin n)
    (hs : ∀ k, k ≠ i → IsSoulmatePair P k (μ k)) :
    galeShapleyRounds P = manRank P i (μ i) + 1 := by
  classical
  let rounds := manRank P i (μ i) + 1
  have hengaged (t : ℕ) : GSEngaged P (gsProposals P t) i ↔ gsProposals P t i = rounds := by
    cases t with
    | zero =>
      exact iff_of_false (not_engaged_zero P i) (Nat.succ_ne_zero _).symm
    | succ t =>
      exact outsider_engaged_iff μ i hs fun k hk => soulmate_proposals (hs k hk) t
  have hproposals (t : ℕ) (ht : t ≤ rounds) : gsProposals P t i = t := by
    induction t with
    | zero => rfl
    | succ t ih =>
      have hprev := ih (by omega)
      have hfree : ¬ GSEngaged P (gsProposals P t) i := by
        rw [hengaged, hprev]
        omega
      rw [gsProposals_succ, ite_eq_right hfree, hprev]
  have hdone : rounds ∈ {t : ℕ | ∀ k : Fin n, GSEngaged P (gsProposals P t) k} := by
    intro k
    by_cases hk : k = i
    · subst k
      exact (hengaged rounds).mpr (hproposals rounds le_rfl)
    · exact soulmate_engaged_of_one (hs k hk) (soulmate_proposals (hs k hk) _)
  refine le_antisymm (Nat.sInf_le hdone) ?_
  apply le_of_not_gt
  intro hlt
  have hfinish : GSEngaged P (gsProposals P (galeShapleyRounds P)) i :=
    Nat.sInf_mem ⟨rounds, hdone⟩ i
  have heq := (hengaged _).mp hfinish
  rw [hproposals _ hlt.le] at heq
  exact hlt.ne heq

end

/-- **Profiles with $n - 1$ soulmate pairs.** Let $P$ be a preference profile for $n$ men and $n$
women with exactly $n - 1$ soulmate pairs (read as $0$ when $n = 0$). Then $P$ has exactly one
stable matching. Moreover, for every stable matching $\mu$ of $P$ and every man $i$ who has no
soulmate, the men-proposing Gale–Shapley algorithm on $P$ ends after $r + 1$ rounds, where $r$ is
the zero-based position at which man $i$ ranks his wife $\mu(i)$.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 7
(`jis-2024-24.2.2-prop-7`). -/
public theorem unique_stable_matching_of_soulmatePairCount_eq_pred
    (P : PreferenceProfile n) (h : soulmatePairCount P = n - 1) :
    (∃! μ : Equiv.Perm (Fin n), IsStableMatching P μ) ∧
      ∀ μ : Equiv.Perm (Fin n), IsStableMatching P μ →
        ∀ i : Fin n, (∀ j : Fin n, ¬ IsSoulmatePair P i j) →
          galeShapleyRounds P = manRank P i (μ i) + 1 := by
  classical
  have houtside := no_soulmate_subsingleton h
  obtain ⟨μ, hμ⟩ :=
    MathlibExt.Combinatorics.Matching.GaleShapley.gale_shapley_exists_stable_matching_general
      rfl (manPrefs P) (womanPrefs P)
  constructor
  · refine ⟨μ, hμ, fun ν hν => Equiv.ext fun i => ?_⟩
    by_cases hi : ∃ j, IsSoulmatePair P i j
    · obtain ⟨j, hj⟩ := hi
      exact (stable_matches_soulmates hν hj).trans (stable_matches_soulmates hμ hj).symm
    · -- The two matchings agree on all men with soulmates, leaving one possible partner.
      let k := μ.symm (ν i)
      have hk : μ k = ν i := μ.apply_symm_apply (ν i)
      have hki : k = i := by
        by_cases hsk : ∃ j, IsSoulmatePair P k j
        · obtain ⟨j, hj⟩ := hsk
          apply ν.injective
          exact (stable_matches_soulmates hν hj).trans
            ((stable_matches_soulmates hμ hj).symm.trans hk)
        · exact houtside (fun j hj => hsk ⟨j, hj⟩) (fun j hj => hi ⟨j, hj⟩)
      rwa [hki, eq_comm] at hk
  · intro ν hν i hi
    apply rounds_of_outsider ν i
    intro k hk
    obtain ⟨j, hj⟩ : ∃ j, IsSoulmatePair P k j := by
      by_contra hno
      exact hk (houtside (fun j hj => hno ⟨j, hj⟩) hi)
    rwa [stable_matches_soulmates hν hj]

end MetaMathlibExt.StableMatchingSequences
