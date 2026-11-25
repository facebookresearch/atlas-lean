/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Social-choice integration for permutation rank distances: the
permutation Kendall tau is the Kendall tau of the induced orders.
-/

module

public import MathlibExt.Combinatorics.Enumerative.RankDistances
public import MathlibExt.GameTheory.SocialChoice.VotingRules

@[expose] public section

namespace MathlibExt.GameTheory.SocialChoice

/-- The permutation Kendall tau is the social-choice Kendall tau of the
induced orders: each discordant unordered pair contributes exactly one
ordered disagreement. -/
theorem kendallTau_eq_kendallTau_orderOfPerm {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    MetaMathlibExt.kendallTau σ τ =
      MathlibExt.GameTheory.SocialChoice.kendallTau (MetaMathlibExt.orderOfPerm σ)
        (MetaMathlibExt.orderOfPerm τ) := by
  have hlt : ∀ (π : Equiv.Perm (Fin n)) (a b : Fin n),
      (MetaMathlibExt.orderOfPerm π).lt a b ↔ π a < π b := fun π a b => Iff.rfl
  unfold MathlibExt.GameTheory.SocialChoice.kendallTau
  simp only [hlt]
  have huniv : (Finset.univ ×ˢ Finset.univ : Finset (Fin n × Fin n)) = Finset.univ := by
    ext q
    simp
  rw [huniv]
  have hswap : Finset.image Prod.swap
        (Finset.univ.filter
          (fun p : Fin n × Fin n => σ p.1 < σ p.2 ∧ τ p.2 < τ p.1)) =
        Finset.univ.filter
          (fun p : Fin n × Fin n => σ p.2 < σ p.1 ∧ τ p.1 < τ p.2) := by
    ext q
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, hdp, rfl⟩
      exact hdp
    · rintro hdp
      exact ⟨Prod.swap q, hdp, rfl⟩
  have hinj : Function.Injective (Prod.swap : Fin n × Fin n → Fin n × Fin n) := by
    apply Function.Involutive.injective
    intro p
    rfl
  have hcard : (Finset.univ.filter
        (fun p : Fin n × Fin n => σ p.1 < σ p.2 ∧ τ p.2 < τ p.1)).card =
      (Finset.univ.filter
        (fun p : Fin n × Fin n => σ p.2 < σ p.1 ∧ τ p.1 < τ p.2)).card := by
    have h := Finset.card_image_of_injective
      (Finset.univ.filter
        (fun p : Fin n × Fin n => σ p.1 < σ p.2 ∧ τ p.2 < τ p.1)) hinj
    rw [hswap] at h
    exact h.symm
  have hunion : Finset.univ.filter
      (fun p : Fin n × Fin n => MetaMathlibExt.Discordant σ τ p.1 p.2) =
      Finset.univ.filter
        (fun p : Fin n × Fin n => σ p.1 < σ p.2 ∧ τ p.2 < τ p.1) ∪
      Finset.univ.filter
        (fun p : Fin n × Fin n => σ p.2 < σ p.1 ∧ τ p.1 < τ p.2) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hd
      unfold MetaMathlibExt.Discordant at hd
      exact hd
    · rintro (hd | hd)
      · unfold MetaMathlibExt.Discordant
        exact Or.inl hd
      · unfold MetaMathlibExt.Discordant
        exact Or.inr hd
  have hdisj : Disjoint
      (Finset.univ.filter
        (fun p : Fin n × Fin n => σ p.1 < σ p.2 ∧ τ p.2 < τ p.1))
      (Finset.univ.filter
        (fun p : Fin n × Fin n => σ p.2 < σ p.1 ∧ τ p.1 < τ p.2)) := by
    rw [Finset.disjoint_left]
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rintro ⟨hlt, -⟩
    exact absurd (lt_trans hq.1 hlt) (lt_irrefl _)
  have h2 := MetaMathlibExt.card_filter_discordant_all σ τ
  rw [hunion, Finset.card_union_of_disjoint hdisj] at h2
  omega

end MathlibExt.GameTheory.SocialChoice
