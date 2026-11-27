/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.Matching.StableMechanism
import Mathlib.Algebra.Group.End
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Order.Preorder.Finite

/-!
# Incentives of the man-optimal stable mechanism

Truthful reporting is a dominant strategy for every man under a man-optimal stable mechanism.
The proof also gives weak Pareto optimality. If some men improve under another matching, a man
who does not improve forms a blocking pair for that matching.
-/

public section

namespace MathlibExt.GameTheory.Matching.StableMechanismIncentivesWanted

open MathlibExt.Combinatorics.Matching.GaleShapley
open MathlibExt.GameTheory.Matching.StableMechanism

/-- A self-map of a nonempty finite set acts as a permutation on a nonempty set of
periodic points. Extend that permutation by the identity. -/
private theorem exists_cycle_perm {α : Type*} [Finite α] [Nonempty α] (f : α → α) :
    ∃ σ : Equiv.Perm α, (∀ x, σ x = x ∨ σ x = f x) ∧ ∃ x, σ x = f x := by
  classical
  let a : α := Classical.arbitrary α
  obtain ⟨i, j, hij, heq⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := fun n : ℕ => f^[n] a) (fun _ => Set.mem_univ _)
  let s := Function.ptsOfPeriod f (j - i)
  have hi : f^[i] a ∈ s := by
    change f^[j - i] (f^[i] a) = f^[i] a
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij.le]
    exact heq.symm
  have hbij := Function.bijOn_ptsOfPeriod f (Nat.sub_pos_of_lt hij)
  let e : Equiv.Perm s := Equiv.ofBijective _ hbij.bijective
  let σ : Equiv.Perm α := Equiv.Perm.ofSubtype e
  have hσ (x : α) (hx : x ∈ s) : σ x = f x :=
    Equiv.Perm.ofSubtype_apply_of_mem e hx
  refine ⟨σ, fun x => ?_, _, hσ _ hi⟩
  by_cases hx : x ∈ s
  · exact Or.inr (hσ x hx)
  · exact Or.inl (Equiv.Perm.ofSubtype_apply_of_not_mem e hx)

/-- In a nonempty set of men, suppose each man's partner has a favorite among all men who
prefer her to their current partners, and that favorite belongs to the set. Rotating a cycle
of these choices gives a stable improvement, contradicting man-optimality. -/
private theorem not_closed_under_favorite_suitors {M W : Type*} [Finite M]
    {mp : MPrefs M W} {wp : WPrefs M W} {μ : PerfectMatching M W}
    (hμ : IsManOptimalStable mp wp μ) (s : Set M) (hs : s.Nonempty)
    (hbest : ∀ k : s, ∃ b : s, (mp b).lt (μ k) (μ b) ∧
      ∀ j, (mp j).lt (μ k) (μ j) → ¬ (wp (μ k)).lt j b) : False := by
  classical
  have : Nonempty s := hs.to_subtype
  choose b hb hfavorite using hbest
  obtain ⟨τ, hτ, i, hi⟩ := exists_cycle_perm b
  let σ := Equiv.Perm.ofSubtype τ
  have hσ (k : M) : σ k = k ∨ ((mp (σ k)).lt (μ k) (μ (σ k)) ∧
      ∀ j, (mp j).lt (μ k) (μ j) → ¬ (wp (μ k)).lt j (σ k)) := by
    by_cases hk : k ∈ s
    · rw [show σ k = ↑(τ ⟨k, hk⟩) from Equiv.Perm.ofSubtype_apply_of_mem τ hk]
      rcases hτ ⟨k, hk⟩ with e | e
      · exact Or.inl (congrArg Subtype.val e)
      · exact Or.inr (e ▸ ⟨hb ⟨k, hk⟩, hfavorite ⟨k, hk⟩⟩)
    · exact Or.inl (Equiv.Perm.ofSubtype_apply_of_not_mem τ hk)
  -- Give the old partner of k to σ k.
  let ρ : PerfectMatching M W := σ.symm.trans μ
  have partner (m : M) : ρ (σ m) = μ m := by simp [ρ]
  have improves (m : M) : ρ m = μ m ∨ (mp m).lt (ρ m) (μ m) := by
    obtain ⟨k, rfl⟩ := σ.surjective m
    rw [partner]
    rcases hσ k with hk | hk
    · exact Or.inl (by rw [hk])
    · exact Or.inr hk.1
  -- Any man who could block after reassignment was already a suitor of that woman.
  -- A woman who changed partners chose her favorite among precisely those men.
  have stable : IsStable mp wp ρ := by
    intro m w block
    obtain ⟨hm, hw⟩ := block
    have hm' : (mp m).lt w (μ m) := by
      rcases improves m with he | hlt
      · rwa [he] at hm
      · exact (mp m).trans hm hlt
    obtain ⟨k, rfl⟩ := μ.surjective w
    have hk : ρ.symm (μ k) = σ k := ρ.symm_apply_eq.mpr (partner k).symm
    rw [hk] at hw
    rcases hσ k with he | he
    · exact hμ.1 m (μ k) ⟨hm', by simpa [he] using hw⟩
    · exact he.2 m hm' hw
  apply hμ.2 ρ stable (σ i)
  have hmove : σ i = ↑(b i) := (Equiv.Perm.ofSubtype_apply_coe τ i).trans (congrArg Subtype.val hi)
  rw [partner, hmove]
  exact hb i

/-- If some men gain relative to the man-optimal matching, a man outside that set
forms a blocking pair for the proposed matching. -/
private theorem exists_blockingPair_of_improvement {M W : Type*} [Finite M]
    {mp : MPrefs M W} {wp : WPrefs M W} {μ : PerfectMatching M W}
    (hμ : IsManOptimalStable mp wp μ) (ν : PerfectMatching M W)
    (gain : ∃ i, (mp i).lt (ν i) (μ i)) :
    ∃ j w, ¬ (mp j).lt (ν j) (μ j) ∧ IsBlockingPair mp wp ν j w := by
  classical
  let s : Set M := {j | (mp j).lt (ν j) (μ j)}
  by_contra noBlock
  -- If w prefers j to her new partner and j ranks w at least as high as his old partner,
  -- then j must have gained, or he and w would block ν.
  have mem_of_prefers {j : M} {w : W} (hj : ¬ (mp j).lt (μ j) w)
      (hw : (wp w).lt j (ν.symm w)) : j ∈ s := by
    by_contra hout
    apply noBlock ⟨j, w, hout, ?_, hw⟩
    have hne : w ≠ ν j := by
      rintro rfl
      exact (wp _).irrefl _ (by simpa using hw)
    apply ((mp j).total hne).resolve_right
    intro hlt
    rcases eq_or_ne w (μ j) with rfl | he
    · exact hout hlt
    · exact hout ((mp j).trans hlt (((mp j).total he).resolve_right hj))
  -- The women newly assigned to gainers were also assigned to gainers in μ.
  let e := ν.trans μ.symm
  have hmap : Set.MapsTo e s s := by
    intro k hk
    change (mp k).lt (ν k) (μ k) at hk
    have hne : e k ≠ k := fun he => (mp k).irrefl (μ k) (μ.symm_apply_eq.mp he ▸ hk)
    apply mem_of_prefers (w := ν k)
    · simpa [e] using (mp (e k)).irrefl (ν k)
    · rw [Equiv.symm_apply_apply]
      exact ((wp _).total hne).resolve_right fun hw => hμ.1 k (ν k) ⟨hk, hw⟩
  have hsurj := ((s.toFinite.injOn_iff_bijOn_of_mapsTo hmap).mp e.injective.injOn).surjOn
  apply not_closed_under_favorite_suitors hμ s gain
  intro k
  obtain ⟨i, his, hik⟩ := hsurj k.property
  have hwi : ν i = μ k := μ.symm_apply_eq.mp hik
  let suitors : Set M := {j | (mp j).lt (μ k) (μ j)}
  have hi : (mp i).lt (μ k) (μ i) := by rw [← hwi]; exact his
  obtain ⟨b, hb, hbest⟩ :=
    (Finite.wellFounded_of_trans_of_irrefl (wp (μ k)).lt).has_min suitors ⟨i, hi⟩
  refine ⟨⟨b, ?_⟩, hb, hbest⟩
  rcases eq_or_ne b i with rfl | hne
  · exact his
  · apply mem_of_prefers (w := μ k)
    · exact fun h => (mp b).irrefl _ ((mp b).trans hb h)
    · rw [← ν.eq_symm_apply.mpr hwi]
      exact ((wp _).total hne).resolve_right (hbest i hi)

set_option linter.unusedFintypeInType false in
/-- **Weak Pareto optimality of the man-optimal stable matching for the men** (Roth, *Math. Oper.
Res.* 7 (1982), Theorem 6). No perfect matching gives every man a partner he strictly prefers to
his partner in the man-optimal stable matching. The hypothesis `Nonempty M` excludes the empty
market, where "every man strictly prefers" holds vacuously. Roth's example after Corollary 5.1
shows that strong Pareto optimality fails. -/
theorem not_forall_lt_of_isManOptimalStable {M W : Type*} [Fintype M] [Fintype W]
    [Nonempty M] (mp : MPrefs M W) (wp : WPrefs M W) {μ : PerfectMatching M W}
    (hμ : IsManOptimalStable mp wp μ) (ν : PerfectMatching M W) :
    ¬ ∀ m, (mp m).lt (ν m) (μ m) := by
  intro hall
  obtain ⟨j, _, hj, _⟩ := exists_blockingPair_of_improvement hμ ν
    ⟨Classical.arbitrary M, hall _⟩
  exact hj (hall j)

set_option linter.unusedFintypeInType false in
/-- **Strategy-proofness of the man-optimal stable mechanism for the men** (Roth, *Math. Oper.
Res.* 7 (1982), Theorem 5; related conclusions of Dubins and Freedman are cited in its footnote
4). If a mechanism
`h` always returns the man-optimal stable matching of the stated profile, then truthful
revelation is a dominant strategy for every man. Roth states it for either side; this is the
men's side, the women's side being symmetric. Such mechanisms exist whenever the two sides have
the same size (`exists_isManOptimalStable`, and deferred acceptance on `Fin n`,
`Cslib.Algorithms.Lean.Matching.GaleShapley.exists_isManOptimalStable_mechanism`). -/
theorem isTruthfulDominantForMan_of_isManOptimalStable {M W : Type*} [Fintype M]
    [Fintype W] [DecidableEq M] (h : MatchingMechanism M W)
    (hh : ∀ mp wp, IsManOptimalStable mp wp (h mp wp)) (m : M) :
    IsTruthfulDominantForMan h m := by
  intro mp wp T gain
  let ν := h (Function.update mp m T) wp
  obtain ⟨j, w, hj, hm, hw⟩ := exists_blockingPair_of_improvement (hh mp wp) ν ⟨m, gain⟩
  have hne : j ≠ m := fun e => hj (e ▸ gain)
  apply (hh (Function.update mp m T) wp).1 j w
  exact ⟨by simpa [Function.update_of_ne hne] using hm, hw⟩

end MathlibExt.GameTheory.Matching.StableMechanismIncentivesWanted
