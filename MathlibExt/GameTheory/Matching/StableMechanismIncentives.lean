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
# Weak Pareto optimality of the man-optimal stable matching

In a nonempty finite market, `not_forall_lt_of_isManOptimalStable` shows that no perfect matching
gives every man a partner he strictly prefers to his man-optimal stable partner.
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
  classical
  intro hall
  -- Each woman chooses her favorite among the men who prefer her to their partners in μ.
  let suitors (w : W) : Set M := {m | (mp m).lt w (μ m)}
  have best (w : W) : ∃ b ∈ suitors w, ∀ m ∈ suitors w, ¬ (wp w).lt m b := by
    apply (Finite.wellFounded_of_trans_of_irrefl (wp w).lt).has_min
    exact ⟨ν.symm w, by simpa [suitors] using hall (ν.symm w)⟩
  choose b hb hbest using best
  -- Reassign women on cycles to their chosen suitors, keeping all other couples together.
  obtain ⟨σ, hσ, i, hi⟩ := exists_cycle_perm (fun m => b (μ m))
  let ρ : PerfectMatching M W := σ.symm.trans μ
  have partner (m : M) : ρ (σ m) = μ m := by simp [ρ]
  have improves (m : M) : ρ m = μ m ∨ (mp m).lt (ρ m) (μ m) := by
    obtain ⟨k, rfl⟩ := σ.surjective m
    rw [partner]
    rcases hσ k with hk | hk
    · exact Or.inl (by rw [hk])
    · exact Or.inr (hk ▸ hb (μ k))
  -- Any man who could block after reassignment was already a suitor of that woman.
  -- A woman who changed partners chose her favorite among precisely those men.
  have stable : IsStable mp wp ρ := by
    intro m w block
    obtain ⟨hm, hw⟩ := block
    have hm' : m ∈ suitors w := by
      rcases improves m with he | hlt
      · rwa [he] at hm
      · exact (mp m).trans hm hlt
    obtain ⟨k, rfl⟩ := μ.surjective w
    have hk : ρ.symm (μ k) = σ k := ρ.symm_apply_eq.mpr (partner k).symm
    rw [hk] at hw
    rcases hσ k with he | he
    · exact hμ.1 m (μ k) ⟨hm', by simpa [he] using hw⟩
    · exact hbest (μ k) m hm' (he ▸ hw)
  apply hμ.2 ρ stable (σ i)
  rw [partner, hi]
  exact hb (μ i)

end MathlibExt.GameTheory.Matching.StableMechanismIncentivesWanted
