/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Intertwining finite families of dyadically weighted projectors

Let V and W be modules over a commutative ℚ-algebra k. For orthogonal idempotent families p_i
and q_j supported in degrees at most N and M, form the weighted endomorphisms S_p = ∑ i =
0,…,N, 2^i p_i and S_q = ∑ j = 0,…,M, 2^j q_j, with the rational weights mapped into k.

If a k-linear map T satisfies T ∘ S_p = S_q ∘ T, every off-diagonal component q_j ∘ T ∘ p_i is
zero for i ≠ j. If both finite projector sums are the identity, T commutes with each matching
projector: T ∘ p_i = q_i ∘ T for every i : ℕ. The argument uses the inverse in ℚ of the
nonzero weight difference 2^i − 2^j.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

universe u v w

namespace LinearMap

variable {k : Type u} [CommRing k] [Algebra ℚ k]
  {V : Type v} [AddCommGroup V] [Module k V]
  {W : Type w} [AddCommGroup W] [Module k W]

/-- For a commutative ℚ-algebra k, a k-module V, an endomorphism family p : ℕ → Module.End k V and
N : ℕ, define dyadicProjectorSum p N = ∑ i : Fin (N + 1), algebraMap ℚ k (2^i.val) • p i.val.
The sum includes indices zero through N. -/
def dyadicProjectorSum (p : ℕ → Module.End k V) (N : ℕ) : Module.End k V :=
  ∑ i : Fin (N + 1), algebraMap ℚ k ((2 : ℚ) ^ i.val) • p i.val

private theorem twoPow_injective : Function.Injective (fun i : ℕ => (2 : ℚ) ^ i) := by
  apply StrictMono.injective
  apply strictMono_nat_of_lt_succ
  intro i
  rw [pow_succ]
  have hpos : (0 : ℚ) < 2 ^ i := pow_pos (by norm_num) i
  nlinarith

private theorem dyadicProjectorSum_comp (p : ℕ → Module.End k V) (N i : ℕ) (hi : i ≤ N)
    (hp : ∀ i j : ℕ, (p i).comp (p j) = if i = j then p i else 0) :
    (dyadicProjectorSum p N).comp (p i) = algebraMap ℚ k ((2 : ℚ) ^ i) • p i := by
  classical
  let i₀ : Fin (N + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
  change dyadicProjectorSum p N * p i = _
  rw [dyadicProjectorSum, Finset.sum_mul]
  simp only [smul_mul_assoc]
  change (∑ j : Fin (N + 1), algebraMap ℚ k ((2 : ℚ) ^ j.val) • (p j.val).comp (p i)) = _
  simp_rw [hp]
  rw [Finset.sum_eq_single i₀]
  · simp [i₀]
  · intro j hj hne
    have hji : j.val ≠ i := fun h => hne (Fin.ext h)
    simp [hji]
  · simp

private theorem comp_dyadicProjectorSum (p : ℕ → Module.End k V) (N i : ℕ) (hi : i ≤ N)
    (hp : ∀ i j : ℕ, (p i).comp (p j) = if i = j then p i else 0) :
    (p i).comp (dyadicProjectorSum p N) = algebraMap ℚ k ((2 : ℚ) ^ i) • p i := by
  classical
  let i₀ : Fin (N + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
  change p i * dyadicProjectorSum p N = _
  rw [dyadicProjectorSum, Finset.mul_sum]
  simp only [mul_smul_comm]
  change (∑ j : Fin (N + 1), algebraMap ℚ k ((2 : ℚ) ^ j.val) • (p i).comp (p j.val)) = _
  simp_rw [hp]
  rw [Finset.sum_eq_single i₀]
  · simp [i₀]
  · intro j hj hne
    have hji : i ≠ j.val := fun h => hne (Fin.ext h.symm)
    simp [hji]
  · simp

/-- Let k be a commutative ℚ-algebra, V and W k-modules, and p_i : V →ₗ[k] V and q_j : W →ₗ[k] W
families indexed by ℕ. Assume p_i ∘ p_j equals p_i when i = j and zero otherwise, and the same
orthogonality and idempotence equations hold for q. Suppose p_i = 0 for i > N and q_j = 0 for
j > M. If T : V →ₗ[k] W satisfies T ∘ dyadicProjectorSum p N = dyadicProjectorSum q M ∘ T,
then q_j ∘ T ∘ p_i = 0 for every i, j : ℕ with i ≠ j. Completeness of the two projector sums
is not needed for this conclusion. -/
theorem dyadicProjectorIntertwiner_cross_zero (p : ℕ → Module.End k V) (q : ℕ → Module.End k W)
    (N M : ℕ) (T : V →ₗ[k] W)
    (hp : ∀ i j : ℕ, (p i).comp (p j) = if i = j then p i else 0)
    (hq : ∀ i j : ℕ, (q i).comp (q j) = if i = j then q i else 0)
    (hpsupport : ∀ i : ℕ, N < i → p i = 0)
    (hqsupport : ∀ j : ℕ, M < j → q j = 0)
    (hT : T.comp (dyadicProjectorSum p N) = (dyadicProjectorSum q M).comp T)
    (i j : ℕ) (hij : i ≠ j) : (q j).comp (T.comp (p i)) = 0 := by
  classical
  by_cases hi : i ≤ N
  · by_cases hj : j ≤ M
    · let X : V →ₗ[k] W := (q j).comp (T.comp (p i))
      have h := congrArg (fun f => (q j).comp (f.comp (p i))) hT
      simp only [LinearMap.comp_assoc] at h
      rw [dyadicProjectorSum_comp p N i hi hp] at h
      rw [← LinearMap.comp_assoc (T.comp (p i)) (dyadicProjectorSum q M) (q j),
        comp_dyadicProjectorSum q M j hj hq] at h
      simp only [LinearMap.comp_smul, LinearMap.smul_comp] at h
      have hz : algebraMap ℚ k ((2 : ℚ) ^ i - (2 : ℚ) ^ j) • X = 0 := by
        rw [map_sub, sub_smul]
        exact sub_eq_zero.mpr h
      have hr : (2 : ℚ) ^ i - (2 : ℚ) ^ j ≠ 0 :=
        sub_ne_zero.mpr (fun heq => hij (twoPow_injective heq))
      have hcancel := congrArg (fun Y : V →ₗ[k] W =>
        algebraMap ℚ k (((2 : ℚ) ^ i - (2 : ℚ) ^ j)⁻¹) • Y) hz
      simpa only [smul_smul, ← map_mul, inv_mul_cancel₀ hr, map_one, one_smul,
        smul_zero, X] using hcancel
    · rw [hqsupport j (Nat.lt_of_not_ge hj), LinearMap.zero_comp]
  · rw [hpsupport i (Nat.lt_of_not_ge hi), LinearMap.comp_zero, LinearMap.comp_zero]

/-- Let k be a commutative ℚ-algebra, V and W k-modules, and p_i : V →ₗ[k] V and q_j : W →ₗ[k] W
families indexed by ℕ. Assume p_i ∘ p_j equals p_i when i = j and zero otherwise, and the same
orthogonality and idempotence equations hold for q. Suppose p_i = 0 for i > N and q_j = 0 for
j > M. Assume also ∑ i = 0,…,N, p_i = 𝟙 V and ∑ j = 0,…,M, q_j = 𝟙 W. If T : V →ₗ[k] W
satisfies T ∘ dyadicProjectorSum p N = dyadicProjectorSum q M ∘ T, then T ∘ p_i = q_i ∘ T for
every i : ℕ, including indices outside either support bound. -/
theorem dyadicProjectorIntertwiner_comp (p : ℕ → Module.End k V) (q : ℕ → Module.End k W)
    (N M : ℕ) (T : V →ₗ[k] W)
    (hp : ∀ i j : ℕ, (p i).comp (p j) = if i = j then p i else 0)
    (hq : ∀ i j : ℕ, (q i).comp (q j) = if i = j then q i else 0)
    (hpsupport : ∀ i : ℕ, N < i → p i = 0)
    (hqsupport : ∀ j : ℕ, M < j → q j = 0)
    (hpsum : (∑ i : Fin (N + 1), p i.val) = LinearMap.id)
    (hqsum : (∑ j : Fin (M + 1), q j.val) = LinearMap.id)
    (hT : T.comp (dyadicProjectorSum p N) = (dyadicProjectorSum q M).comp T) (i : ℕ) :
    T.comp (p i) = (q i).comp T := by
  classical
  have hcross := dyadicProjectorIntertwiner_cross_zero p q N M T hp hq hpsupport hqsupport hT
  have hleft : T.comp (p i) = (q i).comp (T.comp (p i)) := by
    calc
      _ = (∑ j : Fin (M + 1), q j.val).comp (T.comp (p i)) := by
        rw [hqsum, LinearMap.id_comp]
      _ = ∑ j : Fin (M + 1), (q j.val).comp (T.comp (p i)) := by
        apply LinearMap.ext
        intro x
        simp only [LinearMap.comp_apply, LinearMap.sum_apply]
      _ = (q i).comp (T.comp (p i)) := by
        by_cases hi : i ≤ M
        · let i₀ : Fin (M + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
          simpa only [i₀] using
            (Finset.sum_eq_single (s := Finset.univ)
              (f := fun j : Fin (M + 1) => (q j.val).comp (T.comp (p i))) i₀
              (fun j _ hne => hcross i j.val (fun he => hne (Fin.ext he.symm)))
              (fun hn => False.elim (hn (Finset.mem_univ i₀))))
        · rw [hqsupport i (Nat.lt_of_not_ge hi), LinearMap.zero_comp]
          apply Finset.sum_eq_zero
          intro j hj
          exact hcross i j.val (by have hjn := j.isLt; omega)
  have hright : (q i).comp T = (q i).comp (T.comp (p i)) := by
    calc
      _ = (q i).comp (T.comp (∑ j : Fin (N + 1), p j.val)) := by
        rw [hpsum, LinearMap.comp_id]
      _ = ∑ j : Fin (N + 1), (q i).comp (T.comp (p j.val)) := by
        apply LinearMap.ext
        intro x
        simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
      _ = (q i).comp (T.comp (p i)) := by
        by_cases hi : i ≤ N
        · let i₀ : Fin (N + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
          simpa only [i₀] using
            (Finset.sum_eq_single (s := Finset.univ)
              (f := fun j : Fin (N + 1) => (q i).comp (T.comp (p j.val))) i₀
              (fun j _ hne => hcross j.val i (fun he => hne (Fin.ext he)))
              (fun hn => False.elim (hn (Finset.mem_univ i₀))))
        · rw [hpsupport i (Nat.lt_of_not_ge hi), LinearMap.comp_zero, LinearMap.comp_zero]
          apply Finset.sum_eq_zero
          intro j hj
          exact hcross j.val i (by have hjn := j.isLt; omega)
  exact hleft.trans hright.symm

end LinearMap
