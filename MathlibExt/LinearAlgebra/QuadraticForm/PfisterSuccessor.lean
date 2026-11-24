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
# Successor decomposition of Pfister forms

The subset coordinates of a successor Pfister form split canonically into
two blocks: subsets avoiding the final index, and subsets containing it.
This file packages that partition as a linear equivalence and identifies the
successor Pfister form with the product of the lower Pfister form and its
scalar multiple by the negative final coefficient.

The construction is characteristic-free.  It does not assert roundness,
hyperbolicity, existence of a half-dimensional isotropic subspace, or any
norm-residue consequence.

## Main declarations

* `QuadraticForm.pfisterLowerIndex`
* `QuadraticForm.pfisterUpperIndex`
* `QuadraticForm.pfisterSuccLinearEquiv`
* `QuadraticForm.pfisterSuccEquiv`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators

universe u v

namespace QuadraticForm

/-- Embed a lower-rank Pfister coordinate as a subset avoiding the final
index. -/
def pfisterLowerIndex (n : ℕ) :
    Finset (Fin n) ↪ Finset (Fin (n + 1)) where
  toFun s := s.map Fin.castSuccEmb
  inj' := Finset.map_injective Fin.castSuccEmb

/-- Embed a lower-rank Pfister coordinate in the upper block by inserting
the final index. -/
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

/-- The full Pfister coefficient on a lower-block coordinate is the
lower-rank Pfister coefficient. -/
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

/-- The full Pfister coefficient on an upper-block coordinate is the lower
coefficient multiplied by the negative final coefficient. -/
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

private noncomputable def pfisterLowerPart
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

private noncomputable def pfisterSuccIndexEquiv (n : ℕ) :
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

/-- Split functions on successor Pfister coordinates into the block avoiding
the final index and the block containing it. -/
noncomputable def pfisterSuccLinearEquiv
    (R : Type u) [Semiring R]
    {M : Type v} [AddCommMonoid M] [Module R M]
    (n : ℕ) :
    (Finset (Fin (n + 1)) → M) ≃ₗ[R]
      (Finset (Fin n) → M) × (Finset (Fin n) → M) := by
  let e : Sum (Finset (Fin n)) (Finset (Fin n)) ≃
      Finset (Fin (n + 1)) := {
    toFun := Sum.elim (pfisterLowerIndex n) (pfisterUpperIndex n)
    invFun t := if Fin.last n ∈ t then
        Sum.inr (t.preimage Fin.castSucc (Fin.castSucc_injective n).injOn)
      else
        Sum.inl (t.preimage Fin.castSucc (Fin.castSucc_injective n).injOn)
    left_inv s := by
      cases s with
      | inl s =>
          dsimp only
          rw [Sum.elim_inl]
          rw [ite_eq_right (last_notMem_pfisterLowerIndex n s)]
          exact congrArg Sum.inl (by
            simpa [pfisterLowerPart] using pfisterLowerPart_lowerIndex n s)
      | inr s =>
          dsimp only
          rw [Sum.elim_inr]
          rw [ite_eq_left (last_mem_pfisterUpperIndex n s)]
          exact congrArg Sum.inr (by
            simpa [pfisterLowerPart] using pfisterLowerPart_upperIndex n s)
    right_inv t := by
      by_cases h : Fin.last n ∈ t
      · dsimp only
        rw [ite_eq_left h]
        simpa [pfisterLowerPart] using pfisterUpperIndex_lowerPart n t h
      · dsimp only
        rw [ite_eq_right h]
        simpa [pfisterLowerPart] using pfisterLowerIndex_lowerPart n t h }
  exact
    (LinearEquiv.piCongrLeft' R
        (fun _ : Finset (Fin (n + 1)) => M) e.symm).trans
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
  congr 1
  simpa [pfisterLowerPart] using pfisterLowerPart_lowerIndex n s

@[simp]
theorem pfisterSuccLinearEquiv_symm_apply_upperIndex
    (R : Type u) [Semiring R]
    {M : Type v} [AddCommMonoid M] [Module R M]
    (n : ℕ) (x y : Finset (Fin n) → M)
    (s : Finset (Fin n)) :
    (pfisterSuccLinearEquiv R n).symm (x, y)
        (pfisterUpperIndex n s) = y s := by
  simp [pfisterSuccLinearEquiv]
  congr 1
  simpa [pfisterLowerPart] using pfisterLowerPart_upperIndex n s

/-- A successor Pfister form is isometric to the product of the lower form
and its scalar multiple by the negative final coefficient. -/
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
