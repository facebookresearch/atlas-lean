/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Order.PosetMatrix

/-!
# Connectedness of posets represented by block matrices
-/

namespace MetaMathlibExt

/-- **Block properties decide connectedness of the represented poset.** Let $M$ be a poset matrix
of order $n$, a Boolean matrix with rows and columns indexed by $0, \dots, n - 1$, that
represents a partial order $P$: there is a bijection $e$ from $\{0, \dots, n - 1\}$ to $P$ such
that $e(i) \le e(j)$ if and only if $M_{ij}$ is true. Let $1 \le r < n$. If $M_{ij}$ is true for
all $i < r \le j$ (the block of $1$s property of length $r$), then $P$ is connected: every subset
$S$ of $P$ such that $x \in S \iff y \in S$ whenever $x \le y$ is empty or all of $P$. If
$M_{ij}$ is false for all $i < r \le j$ (the block of $0$s property of length $r$), then $P$ is
disconnected: some nonempty subset $S$ of $P$ with nonempty complement satisfies
$x \in S \iff y \in S$ whenever $x \le y$.

Since a relabeling of $M$ represents the same poset, this also covers matrices that satisfy a
block property after relabeling.

Source: Salah Uddin Mohammad, Md. Shah Noor, and Md. Rashed Talukder, *Recognition and
Enumeration of the Quasi-Full Rooted Trees*, Journal of Integer Sequences 28 (2025),
Article 25.6.3, Theorem 5 (`jis-2025-25.6.3-thm-5`). -/
public theorem connected_or_disconnected_of_block_property {P : Type*} [PartialOrder P]
    (n : ℕ) (M : Matrix (Fin n) (Fin n) Bool) (hM : IsPosetMatrix n M) (e : Fin n ≃ P)
    (he : ∀ i j, e i ≤ e j ↔ M i j = true) (r : ℕ) (hr₁ : 1 ≤ r) (hr₂ : r < n) :
    ((∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → M i j = true) →
      ∀ S : Set P, (∀ x y : P, x ≤ y → (x ∈ S ↔ y ∈ S)) → S = ∅ ∨ S = Set.univ) ∧
    ((∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → M i j = false) →
      ∃ S : Set P, S.Nonempty ∧ Sᶜ.Nonempty ∧ ∀ x y : P, x ≤ y → (x ∈ S ↔ y ∈ S)) := by
  let first : Fin n := ⟨0, lt_trans hr₁ hr₂⟩
  let cut : Fin n := ⟨r, hr₂⟩
  constructor
  · intro hone S hS
    have cross (i j : Fin n) (hi : i.val < r) (hj : r ≤ j.val) : e i ∈ S ↔ e j ∈ S :=
      hS _ _ ((he i j).2 (hone i j hi hj))
    have mem_iff (i : Fin n) : e first ∈ S ↔ e i ∈ S := by
      by_cases hi : i.val < r
      · exact (cross first cut hr₁ le_rfl).trans (cross i cut hi le_rfl).symm
      · exact cross first i hr₁ (le_of_not_gt hi)
    by_cases hfirst : e first ∈ S
    · exact Or.inr (Set.eq_univ_of_forall (e.surjective.forall.mpr fun i => (mem_iff i).mp hfirst))
    · exact Or.inl (Set.eq_empty_iff_forall_notMem.mpr
        (e.surjective.forall.mpr fun i hi => hfirst ((mem_iff i).mpr hi)))
  · intro hzero
    refine ⟨{x | (e.symm x).val < r}, ⟨e first, ?_⟩, ⟨e cut, ?_⟩, ?_⟩
    · change (e.symm (e first)).val < r
      rw [e.symm_apply_apply]
      exact hr₁
    · simp [cut]
    · intro x y hxy
      obtain ⟨i, rfl⟩ := e.surjective x
      obtain ⟨j, rfl⟩ := e.surjective y
      simp only [Set.mem_ofPred_eq, Equiv.symm_apply_apply]
      have hij := (he i j).mp hxy
      constructor
      · intro hi
        by_contra! hj
        simp [hzero i j hi hj] at hij
      · intro hj
        by_contra! hi
        simp [hM.upper i j (hj.trans_le hi)] at hij

end MetaMathlibExt
