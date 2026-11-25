/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Quaternion.Order

@[expose] public section

open scoped Quaternion

namespace QuaternionAlgebra

variable {a b : ℚ}

/-- Unfolding the order predicate gives its four defining properties. -/
example (Λ : Submodule ℤ ℍ[ℚ, a, b]) (h : IsOrder Λ) :
    (1 : ℍ[ℚ, a, b]) ∈ Λ ∧
      (∀ x y : ℍ[ℚ, a, b], x ∈ Λ → y ∈ Λ → x * y ∈ Λ) ∧
      Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤ ∧ Λ.FG :=
  ⟨h.one_mem, fun _ _ hx hy => h.mul_mem hx hy, h.spanTop, h.fg⟩

/-- Eichler orders are orders, and the quadratic datum unfolds. -/
example (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) (h : IsEichlerOrder Λ N)
    (t n : ℤ) (α : ℍ[ℚ, a, b]) :
    IsOrder Λ ∧ (IsQuadraticDatum t n α ↔
      α * α - (t : ℚ) • α + (n : ℚ) • (1 : ℍ[ℚ, a, b]) = 0) :=
  ⟨h.isOrder, isQuadraticDatum_iff⟩

/-- The intersection of two maximal orders is an order. -/
example (Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]) (h₁ : IsMaximalOrder Λ₁)
    (h₂ : IsMaximalOrder Λ₂) : IsOrder (Λ₁ ⊓ Λ₂) :=
  h₁.isOrder.inf h₂.isOrder

/-- The Lipschitz order in `ℍ[ℚ, -1, -1]`, spanned over `ℤ` by `1, i, j, k`. -/
private def lipschitzOrder : Submodule ℤ ℍ[ℚ, -1, -1] :=
  Submodule.span ℤ {(1 : ℍ[ℚ, -1, -1]), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩,
    ⟨0, 0, 0, 1⟩}

private theorem mem_lipschitzOrder_mk (m n p r : ℤ) :
    (⟨(m : ℚ), (n : ℚ), (p : ℚ), (r : ℚ)⟩ : ℍ[ℚ, -1, -1]) ∈ lipschitzOrder := by
  have h1 : (1 : ℍ[ℚ, -1, -1]) ∈ lipschitzOrder :=
    Submodule.subset_span (by simp)
  have hi : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -1, -1]) ∈ lipschitzOrder :=
    Submodule.subset_span (by simp)
  have hj : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, -1, -1]) ∈ lipschitzOrder :=
    Submodule.subset_span (by simp)
  have hk : (⟨0, 0, 0, 1⟩ : ℍ[ℚ, -1, -1]) ∈ lipschitzOrder :=
    Submodule.subset_span (by simp)
  have heq : (⟨(m : ℚ), (n : ℚ), (p : ℚ), (r : ℚ)⟩ : ℍ[ℚ, -1, -1]) =
      m • (1 : ℍ[ℚ, -1, -1]) + n • (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -1, -1]) +
        p • (⟨0, 0, 1, 0⟩ : ℍ[ℚ, -1, -1]) +
        r • (⟨0, 0, 0, 1⟩ : ℍ[ℚ, -1, -1]) := by
    ext <;> simp
  rw [heq]
  exact add_mem (add_mem (add_mem (Submodule.smul_mem _ _ h1)
    (Submodule.smul_mem _ _ hi)) (Submodule.smul_mem _ _ hj))
    (Submodule.smul_mem _ _ hk)

private theorem lipschitzOrder_isOrder : IsOrder lipschitzOrder := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Submodule.subset_span
    simp
  · intro x y hx hy
    induction hx using Submodule.span_induction with
    | mem u hu =>
      induction hy using Submodule.span_induction with
      | mem v hv =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
        obtain rfl | rfl | rfl | rfl := hu <;>
          obtain rfl | rfl | rfl | rfl := hv <;>
          (norm_num [QuaternionAlgebra.mk_mul_mk]; first
            | exact mem_lipschitzOrder_mk 1 0 0 0
            | exact mem_lipschitzOrder_mk 0 1 0 0
            | exact mem_lipschitzOrder_mk 0 0 1 0
            | exact mem_lipschitzOrder_mk 0 0 0 1
            | exact mem_lipschitzOrder_mk (-1) 0 0 0
            | exact mem_lipschitzOrder_mk 0 (-1) 0 0
            | exact mem_lipschitzOrder_mk 0 0 (-1) 0
            | exact mem_lipschitzOrder_mk 0 0 0 (-1))
      | zero => simp
      | add v w _ _ hv hw => rw [mul_add]; exact add_mem hv hw
      | smul c v _ hv => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hv
    | zero => simp
    | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
    | smul c u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hu
  · refine top_unique fun q _ => ?_
    have hg : ∀ g : ℍ[ℚ, -1, -1], g ∈ ({(1 : ℍ[ℚ, -1, -1]), ⟨0, 1, 0, 0⟩,
        ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩} : Set ℍ[ℚ, -1, -1]) →
        g ∈ Submodule.span ℚ (lipschitzOrder : Set ℍ[ℚ, -1, -1]) :=
      fun g hg => Submodule.subset_span (Submodule.subset_span hg)
    have hq : q = q.re • (1 : ℍ[ℚ, -1, -1]) + q.imI • ⟨0, 1, 0, 0⟩ +
        q.imJ • ⟨0, 0, 1, 0⟩ + q.imK • ⟨0, 0, 0, 1⟩ := by
      ext <;> simp
    rw [hq]
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (hg _ (by simp))
  · apply Submodule.fg_span
    exact Set.finite_insert.2 (Set.finite_insert.2
      (Set.finite_insert.2 (Set.finite_singleton _)))

example : IsOrder lipschitzOrder := lipschitzOrder_isOrder

/-- Zero is never an embedding conductor. -/
example (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) :
    ¬ HasEmbeddingConductor Λ α 0 :=
  fun h => lt_irrefl 0 h.1

/-- So no embedding class is counted with conductor zero. -/
example (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t n : ℤ) : condEmbeddingCount Λ t n 0 = 0 :=
  Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨_, _, _, h⟩ => lt_irrefl 0 h.1⟩)

private theorem exists_eq_mk_of_mem_lipschitzOrder {x : ℍ[ℚ, -1, -1]}
    (hx : x ∈ lipschitzOrder) :
    ∃ m n p r : ℤ, x = ⟨(m : ℚ), (n : ℚ), (p : ℚ), (r : ℚ)⟩ := by
  induction hx using Submodule.span_induction with
  | mem u hu =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    obtain rfl | rfl | rfl | rfl := hu
    · exact ⟨1, 0, 0, 0, by ext <;> simp⟩
    · exact ⟨0, 1, 0, 0, by ext <;> simp⟩
    · exact ⟨0, 0, 1, 0, by ext <;> simp⟩
    · exact ⟨0, 0, 0, 1, by ext <;> simp⟩
  | zero => exact ⟨0, 0, 0, 0, by ext <;> simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨m, n, p, r, rfl⟩ := hu
    obtain ⟨m', n', p', r', rfl⟩ := hv
    exact ⟨m + m', n + n', p + p', r + r', by ext <;> simp⟩
  | smul c u _ hu =>
    obtain ⟨m, n, p, r, rfl⟩ := hu
    exact ⟨c * m, c * n, c * p, c * r, by ext <;> simp⟩

/-- The embedding `i ↦ i` of `ℤ[i]` into the Lipschitz order has conductor `1`,
the least value the conductor can take. -/
example :
    EmbeddingDatum.HasConductor (Λ := lipschitzOrder) (t := 0) (n := 1)
      ⟨⟨0, 1, 0, 0⟩, Submodule.subset_span (by simp), by
        rw [isQuadraticDatum_iff]; ext <;> simp⟩ 1 := by
  refine ⟨one_pos, fun x hx ⟨c, e, hce⟩ => ?_, fun g hg hg1 => absurd hg1 (by omega)⟩
  obtain ⟨m, n, p, r, rfl⟩ := exists_eq_mk_of_mem_lipschitzOrder hx
  have hp : p = 0 := by simpa using congrArg QuaternionAlgebra.imJ hce
  have hr : r = 0 := by simpa using congrArg QuaternionAlgebra.imK hce
  subst hp hr
  exact ⟨m, n, by ext <;> simp⟩

end QuaternionAlgebra
