/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# AMS second-moment estimator

The Alon-Matias-Szegedy estimator for the second frequency
moment, averaged over all sign vectors: the average equals
the second frequency moment exactly. Median amplification
is not included here.
-/

@[expose] public section

/-- AMS F2 estimator, finite sign-averaging form
(ALG-27b core). Frequencies `f : Fin n → ℚ`; a sign vector
`s : Fin n → Bool` gives signs `±1`; the estimator is the
square of the signed sum. Averaged over all sign vectors,
it equals the second frequency moment `∑ i, (f i)^2`
exactly: diagonal terms contribute and cross terms cancel. -/
def signOf {n : ℕ} (s : Fin n → Bool) (i : Fin n) : ℚ :=
  if s i then 1 else -1

/-- The AMS sketch estimate for one sign vector. -/
def amsEst {n : ℕ} (f : Fin n → ℚ) (s : Fin n → Bool) : ℚ :=
  (∑ i, signOf s i * f i) ^ 2

private lemma signOf_mul_self {n : ℕ} (s : Fin n → Bool) (i : Fin n) :
    signOf s i * signOf s i = 1 := by
  unfold signOf
  cases s i <;> simp

private lemma signOf_flip_self {n : ℕ} (s : Fin n → Bool) (i : Fin n) :
    signOf (Function.update s i (!(s i))) i = -signOf s i := by
  simp only [signOf, Function.update_self]
  cases s i <;> simp

private lemma signOf_flip_other {n : ℕ} (s : Fin n → Bool) {i j : Fin n}
    (hij : j ≠ i) :
    signOf (Function.update s i (!(s i))) j = signOf s j := by
  simp only [signOf, Function.update_of_ne hij]

private lemma card_fun_bool (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

private lemma sum_diag {n : ℕ} (i : Fin n) :
    (∑ s : Fin n → Bool, (signOf s i * signOf s i)) = (2 ^ n : ℚ) := by
  calc (∑ s : Fin n → Bool, (signOf s i * signOf s i))
      = ∑ _s : Fin n → Bool, (1 : ℚ) :=
        Finset.sum_congr rfl (fun s _ => signOf_mul_self s i)
    _ = ((Fintype.card (Fin n → Bool) : ℕ) : ℚ) := by
        simp [Finset.sum_const, Finset.card_univ]
    _ = (2 ^ n : ℚ) := by rw [card_fun_bool]; norm_cast

private lemma sum_off_diag {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (∑ s : Fin n → Bool, (signOf s i * signOf s j)) = 0 := by
  have hinv : ∀ s : Fin n → Bool,
      Function.update (Function.update s i (!(s i))) i
        (!(Function.update s i (!(s i)) i)) = s := by
    intro s
    rw [Function.update_self, Bool.not_not, Function.update_idem,
      Function.update_eq_self]
  let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
    { toFun := fun s => Function.update s i (!(s i))
      invFun := fun s => Function.update s i (!(s i))
      left_inv := hinv
      right_inv := hinv }
  have hneg : ∀ s : Fin n → Bool,
      signOf (e s) i * signOf (e s) j = -(signOf s i * signOf s j) := by
    intro s
    have h1 : signOf (e s) i = -signOf s i := signOf_flip_self s i
    have h2 : signOf (e s) j = signOf s j :=
      signOf_flip_other s (Ne.symm hij)
    rw [h1, h2]
    ring
  have hcomp := Equiv.sum_comp e
    (fun s : Fin n → Bool => signOf s i * signOf s j)
  have h3 : (∑ s : Fin n → Bool, (signOf (e s) i * signOf (e s) j))
      = -(∑ s : Fin n → Bool, (signOf s i * signOf s j)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun s _ => hneg s)
  have h4 : (∑ s : Fin n → Bool, (signOf s i * signOf s j))
      = -(∑ s : Fin n → Bool, (signOf s i * signOf s j)) :=
    hcomp.symm.trans h3
  linarith

/-- Unbiasedness: the sum over all sign vectors of the
estimator is `2^n` times the second frequency moment. -/
theorem amsEst_sum {n : ℕ} (f : Fin n → ℚ) :
    ∑ s : Fin n → Bool, amsEst f s
      = 2 ^ n * ∑ i, (f i) ^ 2 := by
  have hexpand : ∀ s : Fin n → Bool, amsEst f s
      = ∑ i, ∑ j, ((signOf s i * f i) * (signOf s j * f j)) := by
    intro s
    unfold amsEst
    rw [pow_two, Fintype.sum_mul_sum]
  have hfactor : ∀ i j : Fin n,
      (∑ s : Fin n → Bool, ((signOf s i * f i) * (signOf s j * f j)))
      = (∑ s : Fin n → Bool, (signOf s i * signOf s j)) * (f i * f j) := by
    intro i j
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hcollapse : ∀ i : Fin n,
      (∑ j : Fin n, ((∑ s : Fin n → Bool, (signOf s i * signOf s j))
        * (f i * f j)))
      = (2 ^ n : ℚ) * (f i * f i) := by
    intro i
    have hsingle : (∑ j : Fin n, ((∑ s : Fin n → Bool,
          (signOf s i * signOf s j)) * (f i * f j)))
        = ((∑ s : Fin n → Bool, (signOf s i * signOf s i))
          * (f i * f i)) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        have hz : (∑ s : Fin n → Bool, (signOf s i * signOf s j)) = 0 :=
          sum_off_diag (Ne.symm hji)
        rw [hz, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsingle, sum_diag]
  calc (∑ s : Fin n → Bool, amsEst f s)
      = ∑ s : Fin n → Bool, ∑ i, ∑ j,
          ((signOf s i * f i) * (signOf s j * f j)) :=
        Finset.sum_congr rfl (fun s _ => hexpand s)
    _ = ∑ i, ∑ j, ∑ s : Fin n → Bool,
          ((signOf s i * f i) * (signOf s j * f j)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
    _ = ∑ i, ∑ j, ((∑ s : Fin n → Bool, (signOf s i * signOf s j))
          * (f i * f j)) :=
        Finset.sum_congr rfl
          (fun i _ => Finset.sum_congr rfl (fun j _ => hfactor i j))
    _ = ∑ i, ((2 ^ n : ℚ) * (f i * f i)) :=
        Finset.sum_congr rfl (fun i _ => hcollapse i)
    _ = (2 ^ n : ℚ) * ∑ i, (f i) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_two]

end
