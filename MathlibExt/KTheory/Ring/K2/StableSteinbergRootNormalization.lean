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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergRootSubgroups
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteSupport

/-! # Stable Steinberg root normalization

Finite stage normalizes last-column and last-row subgroups.
-/

namespace AlgebraicKTheory

namespace StableSteinberg

open scoped commutatorElement

universe u

variable {R : Type u} [Ring R]

private lemma conj_x_lastColumn_generator_mem
    (n i j k : ℕ) (hij : i ≠ j) (hkn : k ≠ n) (a b : R)
    (hi : i < n) (hj : j < n) (hk : k < n) :
    x i j hij a * x k n hkn b * (x i j hij a)⁻¹ ∈
      lastColumnSubgroup (R := R) n := by
  by_cases hjk : j = k
  · subst hjk
    have hi_n : i ≠ n := Nat.ne_of_lt hi
    have hcomm : ⁅x i j hij a, x j n hkn b⁆ = x i n hi_n (a * b) :=
      x_chev i j n hij hkn hi_n a b
    have hconj : x i j hij a * x j n hkn b * (x i j hij a)⁻¹ =
        x i n hi_n (a * b) * x j n hkn b := by
      have h1 : x i j hij a * x j n hkn b * (x i j hij a)⁻¹ =
          (MulAut.conj (x i j hij a)) (x j n hkn b) := rfl
      have h2 : (MulAut.conj (x i j hij a)) (x j n hkn b) =
          ⁅x i j hij a, x j n hkn b⁆ * x j n hkn b :=
        conj_eq_commutatorElement_mul
      calc x i j hij a * x j n hkn b * (x i j hij a)⁻¹
          = (MulAut.conj (x i j hij a)) (x j n hkn b) := h1
        _ = ⁅x i j hij a, x j n hkn b⁆ * x j n hkn b := h2
        _ = x i n hi_n (a * b) * x j n hkn b := by rw [hcomm]
    rw [hconj]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure ⟨i, hi, hi_n, a * b, rfl⟩)
      (Subgroup.subset_closure ⟨j, hj, hkn, b, rfl⟩)
  · have hi_n : i ≠ n := Nat.ne_of_lt hi
    have hcomm : ⁅x i j hij a, x k n hkn b⁆ = 1 :=
      x_comm i j k n hij hkn hi_n hjk a b
    have hconj : x i j hij a * x k n hkn b * (x i j hij a)⁻¹ =
        x k n hkn b := by
      have h1 : x i j hij a * x k n hkn b * (x i j hij a)⁻¹ =
          (MulAut.conj (x i j hij a)) (x k n hkn b) := rfl
      have h2 : (MulAut.conj (x i j hij a)) (x k n hkn b) =
          ⁅x i j hij a, x k n hkn b⁆ * x k n hkn b :=
        conj_eq_commutatorElement_mul
      calc x i j hij a * x k n hkn b * (x i j hij a)⁻¹
          = (MulAut.conj (x i j hij a)) (x k n hkn b) := h1
        _ = ⁅x i j hij a, x k n hkn b⁆ * x k n hkn b := h2
        _ = 1 * x k n hkn b := by rw [hcomm]
        _ = x k n hkn b := by rw [one_mul]
    rw [hconj]
    exact Subgroup.subset_closure ⟨k, hk, hkn, b, rfl⟩

private lemma lastColumn_conj_mem
    (n i j : ℕ) (hij : i ≠ j) (a : R) (hi : i < n) (hj : j < n)
    (g : StableSteinberg R) (hg : g ∈ lastColumnSubgroup (R := R) n) :
    x i j hij a * g * (x i j hij a)⁻¹ ∈
      lastColumnSubgroup (R := R) n := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, hkn, b, rfl⟩ := hy
    exact conj_x_lastColumn_generator_mem n i j k hij hkn a b hi hj hk
  | one =>
    have h_eq :
        x i j hij a * (1 : StableSteinberg R) * (x i j hij a)⁻¹ = 1 := by
      simp
    rw [h_eq]
    exact Subgroup.one_mem _
  | mul g1 g2 _ _ ih1 ih2 =>
    have h_eq :
        x i j hij a * (g1 * g2) * (x i j hij a)⁻¹ =
        (x i j hij a * g1 * (x i j hij a)⁻¹) *
          (x i j hij a * g2 * (x i j hij a)⁻¹) := by
      rw [← conj_mul]
    rw [h_eq]
    exact Subgroup.mul_mem _ ih1 ih2
  | inv g _ ih =>
    have h_eq :
        x i j hij a * g⁻¹ * (x i j hij a)⁻¹ =
          (x i j hij a * g * (x i j hij a)⁻¹)⁻¹ := by
      rw [conj_inv]
    rw [h_eq]
    exact Subgroup.inv_mem _ ih

private lemma conj_x_lastRow_generator_mem
    (n i j k : ℕ) (hij : i ≠ j) (hnk : n ≠ k) (a b : R)
    (hi : i < n) (hj : j < n) (hk : k < n) :
    x i j hij a * x n k hnk b * (x i j hij a)⁻¹ ∈
      lastRowSubgroup (R := R) n := by
  by_cases hik : i = k
  · subst hik
    have hn_i : n ≠ i := Ne.symm (Nat.ne_of_lt hi)
    have hn_j : n ≠ j := Ne.symm (Nat.ne_of_lt hj)
    have hchev : ⁅x n i hn_i b, x i j hij a⁆ = x n j hn_j (b * a) :=
      x_chev n i j hn_i hij hn_j b a
    have hcomm_inv :
        ⁅x i j hij a, x n i hn_i b⁆ = (⁅x n i hn_i b, x i j hij a⁆)⁻¹ := by
      rw [← commutatorElement_inv]
    have hcomm : ⁅x i j hij a, x n i hn_i b⁆ = x n j hn_j (-(b * a)) := by
      calc ⁅x i j hij a, x n i hn_i b⁆
          = (⁅x n i hn_i b, x i j hij a⁆)⁻¹ := hcomm_inv
        _ = (x n j hn_j (b * a))⁻¹ := by rw [hchev]
        _ = x n j hn_j (-(b * a)) := by rw [← x_neg]
    have hconj : x i j hij a * x n i hn_i b * (x i j hij a)⁻¹ =
        x n j hn_j (-(b * a)) * x n i hn_i b := by
      have h1 : x i j hij a * x n i hn_i b * (x i j hij a)⁻¹ =
          (MulAut.conj (x i j hij a)) (x n i hn_i b) := rfl
      have h2 : (MulAut.conj (x i j hij a)) (x n i hn_i b) =
          ⁅x i j hij a, x n i hn_i b⁆ * x n i hn_i b :=
        conj_eq_commutatorElement_mul
      calc x i j hij a * x n i hn_i b * (x i j hij a)⁻¹
          = (MulAut.conj (x i j hij a)) (x n i hn_i b) := h1
        _ = ⁅x i j hij a, x n i hn_i b⁆ * x n i hn_i b := h2
        _ = x n j hn_j (-(b * a)) * x n i hn_i b := by rw [hcomm]
    rw [hconj]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure ⟨j, hj, hn_j, -(b * a), rfl⟩)
      (Subgroup.subset_closure ⟨i, hi, hn_i, b, rfl⟩)
  · have hcomm : ⁅x i j hij a, x n k hnk b⁆ = 1 := by
      have hj_n : j ≠ n := Nat.ne_of_lt hj
      exact x_comm i j n k hij hnk hik hj_n a b
    have hconj : x i j hij a * x n k hnk b * (x i j hij a)⁻¹ =
        x n k hnk b := by
      have h1 : x i j hij a * x n k hnk b * (x i j hij a)⁻¹ =
          (MulAut.conj (x i j hij a)) (x n k hnk b) := rfl
      have h2 : (MulAut.conj (x i j hij a)) (x n k hnk b) =
          ⁅x i j hij a, x n k hnk b⁆ * x n k hnk b :=
        conj_eq_commutatorElement_mul
      calc x i j hij a * x n k hnk b * (x i j hij a)⁻¹
          = (MulAut.conj (x i j hij a)) (x n k hnk b) := h1
        _ = ⁅x i j hij a, x n k hnk b⁆ * x n k hnk b := h2
        _ = 1 * x n k hnk b := by rw [hcomm]
        _ = x n k hnk b := by rw [one_mul]
    rw [hconj]
    exact Subgroup.subset_closure ⟨k, hk, hnk, b, rfl⟩

private lemma lastRow_conj_mem
    (n i j : ℕ) (hij : i ≠ j) (a : R) (hi : i < n) (hj : j < n)
    (g : StableSteinberg R) (hg : g ∈ lastRowSubgroup (R := R) n) :
    x i j hij a * g * (x i j hij a)⁻¹ ∈
      lastRowSubgroup (R := R) n := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, hnk, b, rfl⟩ := hy
    exact conj_x_lastRow_generator_mem n i j k hij hnk a b hi hj hk
  | one =>
    have h_eq :
        x i j hij a * (1 : StableSteinberg R) * (x i j hij a)⁻¹ = 1 := by
      simp
    rw [h_eq]
    exact Subgroup.one_mem _
  | mul g1 g2 _ _ ih1 ih2 =>
    have h_eq :
        x i j hij a * (g1 * g2) * (x i j hij a)⁻¹ =
        (x i j hij a * g1 * (x i j hij a)⁻¹) *
          (x i j hij a * g2 * (x i j hij a)⁻¹) := by
      rw [← conj_mul]
    rw [h_eq]
    exact Subgroup.mul_mem _ ih1 ih2
  | inv g _ ih =>
    have h_eq :
        x i j hij a * g⁻¹ * (x i j hij a)⁻¹ =
          (x i j hij a * g * (x i j hij a)⁻¹)⁻¹ := by
      rw [conj_inv]
    rw [h_eq]
    exact Subgroup.inv_mem _ ih

/-- `finiteStage n` normalizes `lastColumnSubgroup n`. -/
public theorem finiteStage_le_normalizer_lastColumnSubgroup
    (n : ℕ) :
    finiteStage (R := R) n ≤
      Subgroup.normalizer (lastColumnSubgroup (R := R) n) := by
  have h_eq : finiteStage (R := R) n =
      Subgroup.closure
        { g | ∃ (i j : ℕ) (hij : i ≠ j) (a : R),
          g = x i j hij a ∧ i < n ∧ j < n } := rfl
  rw [h_eq, Subgroup.closure_le]
  intro g hg
  obtain ⟨i, j, hij, a, rfl, hi, hj⟩ := hg
  change x i j hij a ∈ Subgroup.normalizer (lastColumnSubgroup (R := R) n)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact lastColumn_conj_mem n i j hij a hi hj h hh
  · intro hh
    have h_inv_mem :
        x i j hij (-a) * (x i j hij a * h * (x i j hij a)⁻¹) *
          (x i j hij (-a))⁻¹ ∈
          lastColumnSubgroup (R := R) n :=
      lastColumn_conj_mem n i j hij (-a) hi hj _ hh
    have h_eq2 : x i j hij (-a) * (x i j hij a * h * (x i j hij a)⁻¹) *
        (x i j hij (-a))⁻¹ = h := by
      calc x i j hij (-a) * (x i j hij a * h * (x i j hij a)⁻¹) *
            (x i j hij (-a))⁻¹
          = (x i j hij a)⁻¹ * (x i j hij a * h * (x i j hij a)⁻¹) *
            x i j hij a := by
            simp only [x_neg, inv_inv]
        _ = h := by
            rw [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul,
              mul_assoc, inv_mul_cancel, mul_one]
    rw [h_eq2] at h_inv_mem
    exact h_inv_mem

/-- `finiteStage n` normalizes `lastRowSubgroup n`. -/
public theorem finiteStage_le_normalizer_lastRowSubgroup
    (n : ℕ) :
    finiteStage (R := R) n ≤
      Subgroup.normalizer (lastRowSubgroup (R := R) n) := by
  have h_eq : finiteStage (R := R) n =
      Subgroup.closure
        { g | ∃ (i j : ℕ) (hij : i ≠ j) (a : R),
          g = x i j hij a ∧ i < n ∧ j < n } := rfl
  rw [h_eq, Subgroup.closure_le]
  intro g hg
  obtain ⟨i, j, hij, a, rfl, hi, hj⟩ := hg
  change x i j hij a ∈ Subgroup.normalizer (lastRowSubgroup (R := R) n)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact lastRow_conj_mem n i j hij a hi hj h hh
  · intro hh
    have h_inv_mem :
        x i j hij (-a) * (x i j hij a * h * (x i j hij a)⁻¹) *
          (x i j hij (-a))⁻¹ ∈
          lastRowSubgroup (R := R) n :=
      lastRow_conj_mem n i j hij (-a) hi hj _ hh
    have h_eq2 : x i j hij (-a) * (x i j hij a * h * (x i j hij a)⁻¹) *
        (x i j hij (-a))⁻¹ = h := by
      calc x i j hij (-a) * (x i j hij a * h * (x i j hij a)⁻¹) *
            (x i j hij (-a))⁻¹
          = (x i j hij a)⁻¹ * (x i j hij a * h * (x i j hij a)⁻¹) *
            x i j hij a := by
            simp only [x_neg, inv_inv]
        _ = h := by
            rw [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul,
              mul_assoc, inv_mul_cancel, mul_one]
    rw [h_eq2] at h_inv_mem
    exact h_inv_mem

end StableSteinberg

end AlgebraicKTheory
