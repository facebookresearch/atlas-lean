/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Commutator relation for elementary matrices

For distinct indices `i, j, k`, `⁅E_{ik}(a), E_{kj}(b)⁆ = E_{ij}(a * b)` in
`GL n R` over an arbitrary (possibly noncommutative) ring, with commutator
`x*y*x⁻¹*y⁻¹`. As a corollary, successor stabilization is a commutator through
the newly adjoined coordinate with second coefficient `1`.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

open Matrix
open scoped commutatorElement

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [Ring R]

theorem commutatorElement_elementary (i j k : n) (hij : i ≠ j) (hik : i ≠ k)
    (hkj : k ≠ j) (a b : R) :
    ⁅elementary i k hik a, elementary k j hkj b⁆ = elementary i j hij (a * b) := by
  apply Units.ext
  -- Unfold commutator and elementary inverses to matrix products.
  have h_eq :
      (↑⁅elementary (n := n) i k hik a, elementary (n := n) k j hkj b⁆ :
          Matrix n n R) =
        (1 + Matrix.single i k a) * (1 + Matrix.single k j b) *
          (1 + Matrix.single i k (-a)) * (1 + Matrix.single k j (-b)) := by
    calc (↑⁅elementary (n := n) i k hik a, elementary (n := n) k j hkj b⁆ : Matrix n n R)
        = ↑(elementary (n := n) i k hik a * elementary (n := n) k j hkj b *
            (elementary (n := n) i k hik a)⁻¹ * (elementary (n := n) k j hkj b)⁻¹) := by
          rw [commutatorElement_def]
      _ = ↑(elementary i k hik a * elementary k j hkj b *
            elementary i k hik (-a) * elementary k j hkj (-b)) := by
          rw [elementary_inv, elementary_inv]
      _ = (↑(elementary (n := n) i k hik a) : Matrix n n R) *
            (↑(elementary (n := n) k j hkj b) : Matrix n n R) *
            (↑(elementary (n := n) i k hik (-a)) : Matrix n n R) *
            (↑(elementary (n := n) k j hkj (-b)) : Matrix n n R) := by
          simp only [Units.val_mul]
      _ = (1 + Matrix.single i k a) * (1 + Matrix.single k j b) *
            (1 + Matrix.single i k (-a)) * (1 + Matrix.single k j (-b)) := by
          simp only [coe_elementary]
  rw [h_eq, coe_elementary]
  -- Single-product simplifications.
  have h_ik_ik : Matrix.single i k a * Matrix.single i k (-a) = (0 : Matrix n n R) := by
    simp [Matrix.single_mul_single_of_ne _ _ _ _ hik.symm]
  have h_kj_kj : Matrix.single k j b * Matrix.single k j (-b) = (0 : Matrix n n R) := by
    simp [Matrix.single_mul_single_of_ne _ _ _ _ hkj.symm]
  have h_kj_ik : Matrix.single k j b * Matrix.single i k a = (0 : Matrix n n R) := by
    simp [Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
  have h_kj_ik_neg : Matrix.single k j b * Matrix.single i k (-a) = (0 : Matrix n n R) := by
    simp [Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
  have h_ij_ik : Matrix.single i j (a * b) * Matrix.single i k a = (0 : Matrix n n R) := by
    simp [Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
  have h_ij_ik_neg : Matrix.single i j (a * b) * Matrix.single i k (-a) = (0 : Matrix n n R) := by
    simp [Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
  have h_ij_kj : Matrix.single i j (a * b) * Matrix.single k j b = (0 : Matrix n n R) := by
    simp [Matrix.single_mul_single_of_ne _ _ _ _ hkj.symm]
  have h_ij_kj_neg : Matrix.single i j (a * b) * Matrix.single k j (-b) = (0 : Matrix n n R) := by
    simp [Matrix.single_mul_single_of_ne _ _ _ _ hkj.symm]
  have h_ik_kj : Matrix.single i k a * Matrix.single k j b = Matrix.single i j (a * b) := by
    simp [Matrix.single_mul_single_same]
  -- Auxiliary cancellations for same (i,k) and (k,j) families.
  have h_ik_add : Matrix.single i k a + Matrix.single i k (-a) = (0 : Matrix n n R) := by
    rw [← single_add, add_neg_cancel, single_zero]
  have h_kj_add : Matrix.single k j b + Matrix.single k j (-b) = (0 : Matrix n n R) := by
    rw [← single_add, add_neg_cancel, single_zero]
  -- Step 1: (1+ E_{ik} a)(1+ E_{kj} b) = 1+ E_{ik} a + E_{kj} b + E_{ij}(a b)
  have h12 :
      (1 + Matrix.single i k a) * (1 + Matrix.single k j b) =
        1 + Matrix.single i k a + Matrix.single k j b + Matrix.single i j (a * b) := by
    calc (1 + Matrix.single i k a) * (1 + Matrix.single k j b)
        = 1 * (1 + Matrix.single k j b) + Matrix.single i k a * (1 + Matrix.single k j b) := by
          rw [add_mul]
      _ = 1 + Matrix.single k j b + Matrix.single i k a + Matrix.single i j (a * b) := by
          simp only [mul_add, one_mul, mul_one, h_ik_kj]
          abel
      _ = 1 + Matrix.single i k a + Matrix.single k j b + Matrix.single i j (a * b) := by
          abel
  -- Step 2: multiply by (1+ E_{ik}(-a)), cancelling the E_{ik} part.
  have h12_mul_ik_neg :
      (1 + Matrix.single i k a + Matrix.single k j b + Matrix.single i j (a * b)) *
          Matrix.single i k (-a) =
        Matrix.single i k (-a) := by
    calc (1 + Matrix.single i k a + Matrix.single k j b + Matrix.single i j (a * b)) *
            Matrix.single i k (-a)
        = 1 * Matrix.single i k (-a)
            + Matrix.single i k a * Matrix.single i k (-a)
            + Matrix.single k j b * Matrix.single i k (-a)
            + Matrix.single i j (a * b) * Matrix.single i k (-a) := by
          simp only [add_mul]
      _ = Matrix.single i k (-a) := by
          simp only [one_mul, h_ik_ik, h_kj_ik_neg, h_ij_ik_neg, add_zero]
  have h123 :
      (1 + Matrix.single i k a + Matrix.single k j b + Matrix.single i j (a * b)) *
          (1 + Matrix.single i k (-a)) =
        1 + Matrix.single k j b + Matrix.single i j (a * b) := by
    calc (1 + Matrix.single i k a + Matrix.single k j b + Matrix.single i j (a * b)) *
            (1 + Matrix.single i k (-a))
        = (1 + Matrix.single i k a + Matrix.single k j b + Matrix.single i j (a * b)) * 1 +
            (1 + Matrix.single i k a + Matrix.single k j b + Matrix.single i j (a * b)) *
              Matrix.single i k (-a) := by
          rw [mul_add]
      _ = (1 + Matrix.single i k a + Matrix.single k j b + Matrix.single i j (a * b)) +
            Matrix.single i k (-a) := by
          rw [mul_one, h12_mul_ik_neg]
      _ = 1 + Matrix.single k j b + Matrix.single i j (a * b) +
            (Matrix.single i k a + Matrix.single i k (-a)) := by
          abel
      _ = 1 + Matrix.single k j b + Matrix.single i j (a * b) := by
          rw [h_ik_add, add_zero]
  -- Step 3: multiply by (1+ E_{kj}(-b)), cancelling the E_{kj} part.
  have h123_mul_kj_neg :
      (1 + Matrix.single k j b + Matrix.single i j (a * b)) *
          Matrix.single k j (-b) =
        Matrix.single k j (-b) := by
    calc (1 + Matrix.single k j b + Matrix.single i j (a * b)) *
            Matrix.single k j (-b)
        = 1 * Matrix.single k j (-b)
            + Matrix.single k j b * Matrix.single k j (-b)
            + Matrix.single i j (a * b) * Matrix.single k j (-b) := by
          simp only [add_mul]
      _ = Matrix.single k j (-b) := by
          simp only [one_mul, h_kj_kj, h_ij_kj_neg, add_zero]
  have h1234 :
      (1 + Matrix.single k j b + Matrix.single i j (a * b)) *
          (1 + Matrix.single k j (-b)) =
        1 + Matrix.single i j (a * b) := by
    calc (1 + Matrix.single k j b + Matrix.single i j (a * b)) *
            (1 + Matrix.single k j (-b))
        = (1 + Matrix.single k j b + Matrix.single i j (a * b)) * 1 +
            (1 + Matrix.single k j b + Matrix.single i j (a * b)) *
              Matrix.single k j (-b) := by
          rw [mul_add]
      _ = (1 + Matrix.single k j b + Matrix.single i j (a * b)) +
            Matrix.single k j (-b) := by
          rw [mul_one, h123_mul_kj_neg]
      _ = 1 + Matrix.single i j (a * b) +
            (Matrix.single k j b + Matrix.single k j (-b)) := by
          abel
      _ = 1 + Matrix.single i j (a * b) := by
          rw [h_kj_add, add_zero]
  calc (1 + Matrix.single i k a) * (1 + Matrix.single k j b) *
          (1 + Matrix.single i k (-a)) * (1 + Matrix.single k j (-b))
      = ((1 + Matrix.single i k a) * (1 + Matrix.single k j b) *
          (1 + Matrix.single i k (-a))) * (1 + Matrix.single k j (-b)) := by
        rw [mul_assoc]
    _ = ((1 + Matrix.single i k a + Matrix.single k j b + Matrix.single i j (a * b)) *
          (1 + Matrix.single i k (-a))) * (1 + Matrix.single k j (-b)) := by
        rw [h12, mul_assoc]
    _ = (1 + Matrix.single k j b + Matrix.single i j (a * b)) *
          (1 + Matrix.single k j (-b)) := by
        rw [h123]
    _ = 1 + Matrix.single i j (a * b) := h1234

/-- Distant-root Steinberg relation: `E_{ij}(a)` and `E_{kl}(b)` commute when `j ≠ k`
and `l ≠ i`, over an arbitrary ring. The two off-diagonal cross terms vanish by
`Matrix.single_mul_single_of_ne`. -/
theorem commute_elementary_elementary (i j k l : n) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    Commute (elementary i j hij a) (elementary k l hkl b) := by
  rw [Commute, SemiconjBy]
  apply Units.ext
  simp only [Units.val_mul, coe_elementary]
  have h_ij_kl : Matrix.single i j a * Matrix.single k l b = (0 : Matrix n n R) := by
    simp [Matrix.single_mul_single_of_ne _ _ _ _ hjk]
  have h_kl_ij : Matrix.single k l b * Matrix.single i j a = (0 : Matrix n n R) := by
    simp [Matrix.single_mul_single_of_ne _ _ _ _ hli]
  have h_left : (1 + Matrix.single i j a) * (1 + Matrix.single k l b) =
      1 + Matrix.single i j a + Matrix.single k l b := by
    calc (1 + Matrix.single i j a) * (1 + Matrix.single k l b)
        = 1 + Matrix.single i j a + Matrix.single k l b +
            Matrix.single i j a * Matrix.single k l b := by
          simp only [mul_add, add_mul, mul_one, one_mul]
          abel
      _ = 1 + Matrix.single i j a + Matrix.single k l b := by
          rw [h_ij_kl, add_zero]
  have h_right : (1 + Matrix.single k l b) * (1 + Matrix.single i j a) =
      1 + Matrix.single k l b + Matrix.single i j a := by
    calc (1 + Matrix.single k l b) * (1 + Matrix.single i j a)
        = 1 + Matrix.single k l b + Matrix.single i j a +
            Matrix.single k l b * Matrix.single i j a := by
          simp only [mul_add, add_mul, mul_one, one_mul]
          abel
      _ = 1 + Matrix.single k l b + Matrix.single i j a := by
          rw [h_kl_ij, add_zero]
  calc (1 + Matrix.single i j a) * (1 + Matrix.single k l b)
      = 1 + Matrix.single i j a + Matrix.single k l b := h_left
    _ = 1 + Matrix.single k l b + Matrix.single i j a := by abel
    _ = (1 + Matrix.single k l b) * (1 + Matrix.single i j a) := h_right.symm

@[simp]
theorem commutatorElement_elementary_eq_one (i j k l : n) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    ⁅elementary i j hij a, elementary k l hkl b⁆ = 1 :=
  (commutatorElement_eq_one_iff_commute).mpr
    (commute_elementary_elementary i j k l hij hkl hjk hli a b)

/-- Successor stabilization as a commutator through the new last coordinate.

For `i j : Fin k`, `stabilization (elementary i j a)` equals the commutator
`⁅E_{i', last}(a), E_{last, j'}(1)⁆`, where `i' = finSumFinEquiv (Sum.inl i)`,
`j' = finSumFinEquiv (Sum.inl j)`, `last = finSumFinEquiv (Sum.inr 0)`.
This exhibits every stabilized elementary generator as a single commutator,
with second coefficient `1`, directly usable for `E_∞ ≤ [GL_∞, GL_∞]`. -/
theorem stabilization_elementary_eq_commutator (R : Type*) [Ring R] {k : ℕ}
    (i j : Fin k) (hij : i ≠ j) (a : R) :
    let e : Fin k ⊕ Fin 1 ≃ Fin (k + 1) := finSumFinEquiv (m := k) (n := 1)
    let i' : Fin (k + 1) := e (Sum.inl i)
    let j' : Fin (k + 1) := e (Sum.inl j)
    let l : Fin (k + 1) := e (Sum.inr 0)
    have hi'l : i' ≠ l := by
      intro h
      have : Sum.inl (α := Fin k) (β := Fin 1) i = Sum.inr (0 : Fin 1) :=
        e.injective h
      cases this
    have hl_j' : l ≠ j' := by
      intro h
      have : Sum.inr (α := Fin k) (β := Fin 1) (0 : Fin 1) = Sum.inl j :=
        e.injective h
      cases this
    stabilization (R := R) (n := k) (elementary i j hij a) =
      ⁅elementary i' l hi'l a, elementary l j' hl_j' (1 : R)⁆ := by
  intro e i' j' l hi'l hl_j'
  -- Needed for intermediate E_{i' j'}.
  have hij' : i' ≠ j' := by
    intro h
    apply hij
    have : Sum.inl (α := Fin k) (β := Fin 1) i =
        Sum.inl (α := Fin k) (β := Fin 1) j :=
      e.injective h
    cases this
    rfl
  -- Stabilization sends E_{ij}(a) to E_{i' j'}(a).
  have h_stab : stabilization R (n := k) (elementary (n := Fin k) i j hij a) =
      elementary i' j' hij' a := by
    calc stabilization R (n := k) (elementary i j hij a)
        = reindexMulEquiv (finSumFinEquiv (m := k) (n := 1))
            (blockDiagonalOne (Fin k) (Fin 1) R (elementary i j hij a)) := rfl
      _ = reindexMulEquiv (finSumFinEquiv (m := k) (n := 1))
            (elementary (Sum.inl (α := Fin k) (β := Fin 1) i)
              (Sum.inl j) (by intro h; apply hij; cases h; rfl) a) := by
          rw [blockDiagonalOne_elementary]
      _ = elementary (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
            (by
              intro h
              apply hij
              have h' : Sum.inl (α := Fin k) (β := Fin 1) i =
                  Sum.inl (α := Fin k) (β := Fin 1) j :=
                (finSumFinEquiv (m := k) (n := 1)).injective h
              cases h'
              rfl) a := by
          rw [reindexMulEquiv_elementary]
  -- Commutator through `l` yields `a * 1`.
  have h_comm : ⁅elementary i' l hi'l a, elementary l j' hl_j' (1 : R)⁆ =
      elementary i' j' hij' (a * 1) :=
    commutatorElement_elementary i' j' l hij' hi'l hl_j' a 1
  calc stabilization R (n := k) (elementary i j hij a)
      = elementary i' j' hij' a := h_stab
    _ = elementary i' j' hij' (a * 1) := by rw [mul_one]
    _ = ⁅elementary i' l hi'l a, elementary l j' hl_j' (1 : R)⁆ := h_comm.symm

end Matrix.GeneralLinearGroup
