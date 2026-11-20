/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.CylinderPathExpansion

open Finset Matrix
open scoped BigOperators

namespace StatMech.Ising

theorem sum_snoc_reindex
    {E R : Type*} [Fintype E] [DecidableEq E] [AddCommMonoid R]
    (m : Nat) (F : (Fin (m + 1) -> E) -> R) :
    (∑ t, F t) = ∑ y : E × (Fin m -> E), F (Fin.snoc y.2 y.1) := by
  exact (Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (m + 1) => E) F).symm

theorem sum_comm_three_last
    {E₁ E₂ E₃ R : Type*} [Fintype E₁] [Fintype E₂] [Fintype E₃]
    [AddCommMonoid R] (F : E₁ -> E₂ -> E₃ -> R) :
    (∑ x, ∑ y, ∑ z, F x y z) = ∑ z, ∑ x, ∑ y, F x y z := by
  calc
    (∑ x, ∑ y, ∑ z, F x y z) = ∑ x, ∑ z, ∑ y, F x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ z, ∑ x, ∑ y, F x y z := by rw [Finset.sum_comm]

def centerMarkedPathSum
    {E R : Type*} [Fintype E] [DecidableEq E] [CommSemiring R]
    (A : Matrix E E R) (a obs : E -> R) (n : Nat) : R :=
  ∑ q : Fin (2 * n + 1) -> E,
    a (q 0) * obs (q ⟨n, by omega⟩) *
      (∏ k : Fin (2 * n), A (q k.castSucc) (q k.succ)) *
      a (q (Fin.last (2 * n)))

theorem transitionProduct_cons_snoc
    {E R : Type*} [Fintype E] [DecidableEq E] [CommMonoid R]
    (A : Matrix E E R) (x y : E) (q : Fin (m + 1) -> E) :
    (∏ k : Fin (m + 2),
        A ((Fin.cons x (Fin.snoc q y) : Fin (m + 3) -> E) k.castSucc)
          ((Fin.cons x (Fin.snoc q y) : Fin (m + 3) -> E) k.succ)) =
      A x (q 0) * (∏ k : Fin m, A (q k.castSucc) (q k.succ)) *
        A (q (Fin.last m)) y := by
  have hmid (i : Fin m) :
      (Fin.snoc q y : Fin (m + 2) -> E) i.castSucc.succ = q i.succ := by
    rw [Fin.succ_castSucc, Fin.snoc_castSucc]
  rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
  simp only [Fin.castSucc_zero, Fin.snoc_apply_zero, Fin.castSucc_succ,
    Fin.cons_zero, Fin.cons_succ, mul_assoc]
  simp_rw [hmid]
  simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

theorem center_cons_snoc
    {E : Type*} (n : Nat) (q : Fin (2 * n + 1) -> E) (x y : E) :
    (Fin.cons x (Fin.snoc q y) : Fin (2 * n + 3) -> E)
        ⟨n + 1, by omega⟩ = q ⟨n, by omega⟩ := by
  change (Fin.snoc q y : Fin (2 * n + 2) -> E) ⟨n, by omega⟩ = _
  rw [show (⟨n, by omega⟩ : Fin (2 * n + 2)) =
      (⟨n, by omega⟩ : Fin (2 * n + 1)).castSucc by
    ext
    rfl, Fin.snoc_castSucc]

theorem last_cons_snoc
    {E : Type*} (m : Nat) (q : Fin (m + 1) -> E) (x y : E) :
    (Fin.cons x (Fin.snoc q y) : Fin (m + 3) -> E)
        (Fin.last (m + 2)) = y := by
  change (Fin.snoc q y : Fin (m + 2) -> E) ⟨m + 1, by omega⟩ = _
  rw [show (⟨m + 1, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) by
    ext
    rfl, Fin.snoc_last]

set_option maxHeartbeats 800000 in

theorem centerMarkedPathSum_eq_sum_sq
    {E R : Type*} [Fintype E] [DecidableEq E] [CommSemiring R]
    (A : Matrix E E R) (hSymm : ∀ i j, A i j = A j i)
    (a obs : E -> R) (n : Nat) :
    centerMarkedPathSum A a obs n =
      ∑ i, obs i * ((A ^ n) *ᵥ a) i ^ 2 := by
  induction n generalizing a with
  | zero =>
      unfold centerMarkedPathSum
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin 1 => E)]
      simp_rw [Fintype.sum_prod_type]
      simp
      apply Finset.sum_congr rfl
      intro i hi
      ring
  | succ n ih =>
      unfold centerMarkedPathSum
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (2 * (n + 1) + 1) => E)]
      simp_rw [Fintype.sum_prod_type]
      simp_rw [show ∀ (x : E) (y : Fin (2 * (n + 1)) -> E),
          (Fin.consEquiv fun _ : Fin (2 * (n + 1) + 1) => E) (x, y) =
            Fin.cons x y by intros; rfl]
      simp only [Nat.mul_succ]
      simp_rw [sum_snoc_reindex (E := E) (R := R) (2 * n + 1)]
      simp_rw [Fintype.sum_prod_type]
      simp_rw [transitionProduct_cons_snoc]
      simp_rw [center_cons_snoc, last_cons_snoc]
      simp only [Fin.cons_zero]
      rw [sum_comm_three_last]
      rw [pow_succ]
      simp_rw [← Matrix.mulVec_mulVec]
      rw [← ih (A *ᵥ a)]
      unfold centerMarkedPathSum
      apply Finset.sum_congr rfl
      intro q hq
      simp only [Matrix.mulVec, dotProduct]
      calc
        (∑ x, ∑ y,
            a x * obs (q ⟨n, by omega⟩) *
                ((A x (q 0) * ∏ k : Fin (2 * n), A (q k.castSucc) (q k.succ)) *
                  A (q (Fin.last (2 * n))) y) * a y) =
            (∑ x, a x * A x (q 0)) *
              ((obs (q ⟨n, by omega⟩) *
                (∏ k : Fin (2 * n), A (q k.castSucc) (q k.succ))) *
              (∑ y, A (q (Fin.last (2 * n))) y * a y)) := by
          rw [Finset.sum_mul]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = (∑ x, A (q 0) x * a x) *
              ((obs (q ⟨n, by omega⟩) *
                (∏ k : Fin (2 * n), A (q k.castSucc) (q k.succ))) *
              (∑ y, A (q (Fin.last (2 * n))) y * a y)) := by
          congr 2
          funext x
          rw [hSymm]
          ring
        _ = ((∑ x, A (q 0) x * a x) * obs (q ⟨n, by omega⟩)) *
              (∏ k : Fin (2 * n), A (q k.castSucc) (q k.succ)) *
              (∑ y, A (q (Fin.last (2 * n))) y * a y) := by ring

end StatMech.Ising
