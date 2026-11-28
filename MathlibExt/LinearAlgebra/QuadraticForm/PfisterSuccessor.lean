/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.LinearAlgebra.QuadraticForm.Pfister
public import Mathlib.Data.Finset.Preimage
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Successor decomposition of diagonal quasi-Pfister forms

Let F be a field and a₀,…,aₙ ∈ Fˣ. Subsets of Fin(n+1) split into those omitting the last
index and those containing it. In these coordinates, the diagonal quasi-Pfister form qₐ is
isometric to q_b ⊕ (−aₙ)q_b, where b is the tuple a₀,…,aₙ₋₁. The coordinate decomposition
also gives a linear equivalence for any module over a semiring.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators

universe u v

namespace QuadraticForm

/-- **The lower Pfister subset embedding.**

For n ∈ ℕ, the embedding L : Finset(Fin n) → Finset(Fin(n+1)) sends s to its image under i ↦
i, so L(s) omits the last index n.
-/
def pfisterLowerIndex (n : ℕ) :
    Finset (Fin n) ↪ Finset (Fin (n + 1)) where
  toFun s := s.map Fin.castSuccEmb
  inj' := Finset.map_injective Fin.castSuccEmb

/-- **The upper Pfister subset embedding.**

For n ∈ ℕ, the embedding U : Finset(Fin n) → Finset(Fin(n+1)) sends s to the image of s under
i ↦ i together with the last index n.
-/
def pfisterUpperIndex (n : ℕ) :
    Finset (Fin n) ↪ Finset (Fin (n + 1)) where
  toFun s := insert (Fin.last n) (pfisterLowerIndex n s)
  inj' := by
    intro s t hst
    have herase := congrArg
      (fun q : Finset (Fin (n + 1)) => q.erase (Fin.last n)) hst
    change
      (insert (Fin.last n) (s.map Fin.castSuccEmb)).erase (Fin.last n) =
        (insert (Fin.last n) (t.map Fin.castSuccEmb)).erase (Fin.last n) at herase
    have hm : s.map Fin.castSuccEmb = t.map Fin.castSuccEmb := by
      simpa using herase
    exact Finset.map_injective Fin.castSuccEmb hm

@[simp]
private theorem last_notMem_pfisterLowerIndex
    (n : ℕ) (s : Finset (Fin n)) :
    Fin.last n ∉ pfisterLowerIndex n s := by
  simp [pfisterLowerIndex]

@[simp]
private theorem last_mem_pfisterUpperIndex
    (n : ℕ) (s : Finset (Fin n)) :
    Fin.last n ∈ pfisterUpperIndex n s := by
  change Fin.last n ∈ insert (Fin.last n) (pfisterLowerIndex n s)
  simp

/-- **Weights on the lower Pfister block.**

Let F be a field and a₀,…,aₙ ∈ Fˣ, with lower tuple bᵢ = aᵢ for i < n. For wₐ(s) = ∏ᵢ∈s (−aᵢ)
and L(s) the image of s ⊆ Fin n in Fin(n+1) omitting n, one has wₐ(L(s)) = w_b(s).
-/
@[simp]
theorem pfisterWeight_lowerIndex {F : Type u} [Field F] {n : ℕ}
    (a : Fin (n + 1) → Fˣ) (s : Finset (Fin n)) :
    pfisterWeight F a (pfisterLowerIndex n s) =
      pfisterWeight F (fun i => a i.castSucc) s := by
  change
    (∏ i ∈ s.map Fin.castSuccEmb, -(a i : F)) =
      ∏ i ∈ s, -(a i.castSucc : F)
  rw [Finset.prod_map]
  rfl

/-- **Weights on the upper Pfister block.**

Let F be a field and a₀,…,aₙ ∈ Fˣ, with bᵢ = aᵢ for i < n. Let U(s) be the image of s ⊆ Fin n
together with the last index n. For wₐ(t) = ∏ᵢ∈t (−aᵢ), one has wₐ(U(s)) = (−aₙ)w_b(s).
-/
@[simp]
theorem pfisterWeight_upperIndex {F : Type u} [Field F] {n : ℕ}
    (a : Fin (n + 1) → Fˣ) (s : Finset (Fin n)) :
    pfisterWeight F a (pfisterUpperIndex n s) =
      -(a (Fin.last n) : F) *
        pfisterWeight F (fun i => a i.castSucc) s := by
  change
    pfisterWeight F a
      (insert (Fin.last n) (pfisterLowerIndex n s)) = _
  rw [pfisterWeight_insert]
  · rw [pfisterWeight_lowerIndex]
  · exact last_notMem_pfisterLowerIndex n s

/-- **Removing the last Pfister index.**

For a subset t of Fin(n+1), pull back t along Fin.castSucc. This recovers the subset of
Fin n underlying either the lower embedding or the upper embedding.
-/
noncomputable def pfisterLowerPart
    (n : ℕ) (t : Finset (Fin (n + 1))) : Finset (Fin n) :=
  t.preimage Fin.castSucc (Fin.castSucc_injective n).injOn

@[simp]
private theorem mem_pfisterLowerPart
    (n : ℕ) (t : Finset (Fin (n + 1))) (i : Fin n) :
    i ∈ pfisterLowerPart n t ↔ i.castSucc ∈ t :=
  Finset.mem_preimage

@[simp]
private theorem pfisterLowerPart_lowerIndex
    (n : ℕ) (s : Finset (Fin n)) :
    pfisterLowerPart n (pfisterLowerIndex n s) = s := by
  ext i
  simp [pfisterLowerPart, pfisterLowerIndex]

@[simp]
private theorem pfisterLowerPart_upperIndex
    (n : ℕ) (s : Finset (Fin n)) :
    pfisterLowerPart n (pfisterUpperIndex n s) = s := by
  ext i
  simp [pfisterLowerPart, pfisterUpperIndex, pfisterLowerIndex]

private theorem pfisterLowerIndex_lowerPart
    (n : ℕ) (t : Finset (Fin (n + 1)))
    (h : Fin.last n ∉ t) :
    pfisterLowerIndex n (pfisterLowerPart n t) = t := by
  ext i
  change i ∈ (pfisterLowerPart n t).map Fin.castSuccEmb ↔ i ∈ t
  by_cases hi : i = Fin.last n
  · subst i
    simp [h]
  · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    simp

private theorem pfisterUpperIndex_lowerPart
    (n : ℕ) (t : Finset (Fin (n + 1)))
    (h : Fin.last n ∈ t) :
    pfisterUpperIndex n (pfisterLowerPart n t) = t := by
  ext i
  change i ∈ insert (Fin.last n)
      ((pfisterLowerPart n t).map Fin.castSuccEmb) ↔ i ∈ t
  by_cases hi : i = Fin.last n
  · subst i
    simp [h]
  · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    simp

/-- **The successor subset index equivalence.**

Subsets of Fin(n+1) split into two copies of subsets of Fin n, according to whether the
last index belongs to the subset. The forward maps are pfisterLowerIndex and
pfisterUpperIndex. This single equivalence supplies both the coordinate splitting and
its sum reindexing formula.
-/
noncomputable def pfisterSuccIndexEquiv (n : ℕ) :
    Sum (Finset (Fin n)) (Finset (Fin n)) ≃
      Finset (Fin (n + 1)) where
  toFun := Sum.elim (pfisterLowerIndex n) (pfisterUpperIndex n)
  invFun t := if h : Fin.last n ∈ t then
      Sum.inr (pfisterLowerPart n t)
    else
      Sum.inl (pfisterLowerPart n t)
  left_inv s := by
    cases s with
    | inl s => simp [last_notMem_pfisterLowerIndex]
    | inr s => simp [last_mem_pfisterUpperIndex]
  right_inv t := by
    by_cases h : Fin.last n ∈ t
    · dsimp only
      simp only [h, dite_true]
      exact pfisterUpperIndex_lowerPart n t h
    · dsimp only
      simp only [h, dite_false]
      exact pfisterLowerIndex_lowerPart n t h

@[simp]
private theorem pfisterSuccIndexEquiv_inl
    (n : ℕ) (s : Finset (Fin n)) :
    pfisterSuccIndexEquiv n (Sum.inl s) = pfisterLowerIndex n s :=
  rfl

@[simp]
private theorem pfisterSuccIndexEquiv_inr
    (n : ℕ) (s : Finset (Fin n)) :
    pfisterSuccIndexEquiv n (Sum.inr s) = pfisterUpperIndex n s :=
  rfl

@[simp]
private theorem pfisterSuccIndexEquiv_symm_lowerIndex
    (n : ℕ) (s : Finset (Fin n)) :
    (pfisterSuccIndexEquiv n).symm (pfisterLowerIndex n s) =
      Sum.inl s := by
  exact (pfisterSuccIndexEquiv n).symm_apply_eq.mpr rfl

@[simp]
private theorem pfisterSuccIndexEquiv_symm_upperIndex
    (n : ℕ) (s : Finset (Fin n)) :
    (pfisterSuccIndexEquiv n).symm (pfisterUpperIndex n s) =
      Sum.inr s := by
  exact (pfisterSuccIndexEquiv n).symm_apply_eq.mpr rfl

/-- **Splitting successor subset coordinates.**

Let R be a semiring and M an additive commutative monoid with an R-module structure. For n ∈
ℕ, let L(s) embed s ⊆ Fin n without the last index and U(s) add that index. The map x ↦ (s ↦
x(L(s)), s ↦ x(U(s))) is an R-linear equivalence from (Finset(Fin(n+1)) → M) to (Finset(Fin n)
→ M) × (Finset(Fin n) → M).
-/
noncomputable def pfisterSuccLinearEquiv
    (R : Type u) [Semiring R]
    {M : Type v} [AddCommMonoid M] [Module R M]
    (n : ℕ) :
    (Finset (Fin (n + 1)) → M) ≃ₗ[R]
      (Finset (Fin n) → M) × (Finset (Fin n) → M) :=
  (LinearEquiv.piCongrLeft' R
    (fun _ : Finset (Fin (n + 1)) => M) (pfisterSuccIndexEquiv n).symm).trans
    (LinearEquiv.sumArrowLequivProdArrow
      (Finset (Fin n)) (Finset (Fin n)) R M)

@[simp]
theorem pfisterSuccLinearEquiv_apply_fst
    (R : Type u) [Semiring R]
    {M : Type v} [AddCommMonoid M] [Module R M]
    (n : ℕ) (x : Finset (Fin (n + 1)) → M)
    (s : Finset (Fin n)) :
    (pfisterSuccLinearEquiv R n x).1 s =
      x (pfisterLowerIndex n s) := by
  simp [pfisterSuccLinearEquiv]

@[simp]
theorem pfisterSuccLinearEquiv_apply_snd
    (R : Type u) [Semiring R]
    {M : Type v} [AddCommMonoid M] [Module R M]
    (n : ℕ) (x : Finset (Fin (n + 1)) → M)
    (s : Finset (Fin n)) :
    (pfisterSuccLinearEquiv R n x).2 s =
      x (pfisterUpperIndex n s) := by
  simp [pfisterSuccLinearEquiv]

@[simp]
theorem pfisterSuccLinearEquiv_symm_apply_lowerIndex
    (R : Type u) [Semiring R]
    {M : Type v} [AddCommMonoid M] [Module R M]
    (n : ℕ) (x y : Finset (Fin n) → M)
    (s : Finset (Fin n)) :
    (pfisterSuccLinearEquiv R n).symm (x, y)
        (pfisterLowerIndex n s) = x s := by
  simp [pfisterSuccLinearEquiv]

@[simp]
theorem pfisterSuccLinearEquiv_symm_apply_upperIndex
    (R : Type u) [Semiring R]
    {M : Type v} [AddCommMonoid M] [Module R M]
    (n : ℕ) (x y : Finset (Fin n) → M)
    (s : Finset (Fin n)) :
    (pfisterSuccLinearEquiv R n).symm (x, y)
        (pfisterUpperIndex n s) = y s := by
  simp [pfisterSuccLinearEquiv]

/-- **The successor diagonal quasi-Pfister isometry.**

Let F be a field and a₀,…,aₙ ∈ Fˣ, with bᵢ = aᵢ for i < n. Write qₐ(x) = ∑ₛ(∏ᵢ∈s −aᵢ)xₛ² and
define q_b similarly. Splitting the coordinates by whether their subset contains n gives an
isometry qₐ ≃ q_b ⊕ (−aₙ)q_b.
-/
noncomputable def pfisterSuccEquiv
    (F : Type u) [Field F] {n : ℕ}
    (a : Fin (n + 1) → Fˣ) :
    (pfister F a).IsometryEquiv
      ((pfister F (fun i => a i.castSucc)).prod
        ((-(a (Fin.last n) : F)) •
          pfister F (fun i => a i.castSucc))) where
  toLinearEquiv := pfisterSuccLinearEquiv F n
  map_app' x := by
    rw [QuadraticMap.prod_apply, smul_apply,
      pfister_apply, pfister_apply, pfister_apply]
    change
      (∑ s : Finset (Fin n),
          pfisterWeight F (fun i => a i.castSucc) s *
            (x (pfisterLowerIndex n s) *
              x (pfisterLowerIndex n s))) +
        -(a (Fin.last n) : F) *
          (∑ s : Finset (Fin n),
            pfisterWeight F (fun i => a i.castSucc) s *
              (x (pfisterUpperIndex n s) *
                x (pfisterUpperIndex n s))) =
      ∑ t : Finset (Fin (n + 1)),
        pfisterWeight F a t * (x t * x t)
    rw [← Equiv.sum_comp (pfisterSuccIndexEquiv n)
      (fun t : Finset (Fin (n + 1)) =>
        pfisterWeight F a t * (x t * x t))]
    rw [Fintype.sum_sum_type]
    simp only [pfisterSuccIndexEquiv_inl,
      pfisterSuccIndexEquiv_inr, pfisterWeight_lowerIndex,
      pfisterWeight_upperIndex]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    ring

end QuadraticForm

end
