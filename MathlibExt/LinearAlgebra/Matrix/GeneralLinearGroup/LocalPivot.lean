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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.ElementarySubgroup
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Data.Matrix.Basis

/-!
# Local-ring column pivot and elementary row operation

For a commutative local ring `R` and finite nonempty index type `n`,
every column of an invertible matrix `GL n R` contains a unit entry.
If the diagonal entry is not a unit, a single elementary transvection
adding a unit-entry row to the diagonal row makes the `(j,j)` entry a unit.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

open Matrix
open Finset

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Every column of `GL n R` over a commutative local ring contains a unit entry.

Uses `(j,j)` entry of `g⁻¹ * g = 1`, `Matrix.mul_apply`, `IsLocalRing.exists_of_isUnit_sum`
and `IsUnit.mul_iff` via `isUnit_of_mul_isUnit_right`. -/
theorem exists_isUnit_entry_in_column [Nonempty n] (g : GL n R) (j : n) :
    ∃ i, IsUnit ((↑g : Matrix n n R) i j) := by
  classical
  have h_mul : (↑g⁻¹ : Matrix n n R) * (↑g : Matrix n n R) = 1 := by
    have h_inv : (g⁻¹ * g : GL n R) = 1 := inv_mul_cancel g
    have h_val_mul : (↑(g⁻¹ * g) : Matrix n n R) =
        (↑g⁻¹ : Matrix n n R) * (↑g : Matrix n n R) := rfl
    have h_one_val : (↑(1 : GL n R) : Matrix n n R) = (1 : Matrix n n R) := rfl
    calc (↑g⁻¹ : Matrix n n R) * (↑g : Matrix n n R)
        = (↑(g⁻¹ * g) : Matrix n n R) := h_val_mul.symm
      _ = (↑(1 : GL n R) : Matrix n n R) := by rw [h_inv]
      _ = (1 : Matrix n n R) := h_one_val
  have h_jj : ((↑g⁻¹ : Matrix n n R) * (↑g : Matrix n n R)) j j = (1 : R) := by
    rw [h_mul, Matrix.one_apply_eq]
  have h_sum_eq :
      (∑ i : n, (↑g⁻¹ : Matrix n n R) j i * (↑g : Matrix n n R) i j) = (1 : R) := by
    have h_apply := Matrix.mul_apply (M := (↑g⁻¹ : Matrix n n R))
        (N := (↑g : Matrix n n R)) (i := j) (k := j)
    rw [h_apply] at h_jj
    exact h_jj
  have h_isUnit_sum :
      IsUnit (∑ i : n, (↑g⁻¹ : Matrix n n R) j i * (↑g : Matrix n n R) i j) := by
    rw [h_sum_eq]
    exact isUnit_one
  have h_isUnit_univ :
      IsUnit (∑ i ∈ (Finset.univ : Finset n),
        (↑g⁻¹ : Matrix n n R) j i * (↑g : Matrix n n R) i j) := by
    simpa using h_isUnit_sum
  obtain ⟨i, _, hi⟩ := IsLocalRing.exists_of_isUnit_sum (s := Finset.univ)
    (f := fun i => (↑g⁻¹ : Matrix n n R) j i * (↑g : Matrix n n R) i j) h_isUnit_univ
  exact ⟨i, isUnit_of_mul_isUnit_right hi⟩

/-- Make the `(j,j)` entry unit by left-multiplying with an element of the
elementary subgroup: if the diagonal is already a unit use `1`, otherwise add a
row containing a unit entry with a single elementary matrix. -/
theorem exists_elementary_mul_isUnit_entry [Nonempty n] (g : GL n R) (j : n) :
    ∃ e, e ∈ elementarySubgroup n R ∧
      IsUnit ((↑(e * g) : Matrix n n R) j j) := by
  classical
  obtain ⟨i₀, hi₀⟩ := exists_isUnit_entry_in_column g j
  by_cases h_diag : IsUnit ((↑g : Matrix n n R) j j)
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    have h_one_mul : (1 * g : GL n R) = g := one_mul g
    have h_coe : (↑(1 * g) : Matrix n n R) j j = (↑g : Matrix n n R) j j := by
      rw [h_one_mul]
    rw [h_coe]
    exact h_diag
  · have h_not_diag : ¬ IsUnit ((↑g : Matrix n n R) j j) := h_diag
    have h_neq : i₀ ≠ j := by
      intro h_eq
      subst h_eq
      exact h_not_diag hi₀
    have h_ji : j ≠ i₀ := Ne.symm h_neq
    let e : GL n R := elementary j i₀ h_ji (1 : R)
    have he_mem : e ∈ elementarySubgroup n R :=
      elementary_mem_elementarySubgroup j i₀ h_ji (1 : R)
    refine ⟨e, he_mem, ?_⟩
    have h_e_val : (↑e : Matrix n n R) = 1 + Matrix.single j i₀ (1 : R) := rfl
    have h_mul_val : (↑(e * g) : Matrix n n R) =
        (↑e : Matrix n n R) * (↑g : Matrix n n R) := rfl
    have h_add_mul : (↑e : Matrix n n R) * (↑g : Matrix n n R) =
        (↑g : Matrix n n R) + Matrix.single j i₀ (1 : R) * (↑g : Matrix n n R) := by
      rw [h_e_val, add_mul, one_mul]
    have h_entry :
        (↑(e * g) : Matrix n n R) j j =
          (↑g : Matrix n n R) j j + (↑g : Matrix n n R) i₀ j := by
      calc (↑(e * g) : Matrix n n R) j j
          = ((↑e : Matrix n n R) * (↑g : Matrix n n R)) j j := by
            rw [h_mul_val]
        _ = ((↑g : Matrix n n R) +
            Matrix.single j i₀ (1 : R) * (↑g : Matrix n n R)) j j := by
            rw [h_add_mul]
        _ = (↑g : Matrix n n R) j j +
            (Matrix.single j i₀ (1 : R) * (↑g : Matrix n n R)) j j := by
            rw [Matrix.add_apply]
        _ = (↑g : Matrix n n R) j j + (↑g : Matrix n n R) i₀ j := by
          have h_single : (Matrix.single j i₀ (1 : R) *
              (↑g : Matrix n n R)) j j = (↑g : Matrix n n R) i₀ j := by
            have hs := Matrix.single_mul_apply_same (i := j) (j := i₀) (b := j)
              (c := (1 : R)) (M := (↑g : Matrix n n R))
            simp [hs]
          rw [h_single]
    have h_sum_unit : IsUnit ((↑g : Matrix n n R) j j + (↑g : Matrix n n R) i₀ j) := by
      set a := (↑g : Matrix n n R) j j
      set b := (↑g : Matrix n n R) i₀ j
      have hb : IsUnit b := hi₀
      have ha_not : ¬ IsUnit a := h_not_diag
      by_contra h_not_sum
      have h_sum_nonunit : a + b ∈ nonunits R := by
        rw [mem_nonunits_iff]
        exact h_not_sum
      have ha_nonunit : a ∈ nonunits R := by
        rw [mem_nonunits_iff]
        exact ha_not
      have h_neg_a_nonunit : (-a) ∈ nonunits R := by
        rw [mem_nonunits_iff, IsUnit.neg_iff]
        exact ha_not
      have hb_eq : b = (a + b) + (-a) := by abel
      have hb_nonunit : b ∈ nonunits R := by
        rw [hb_eq]
        exact IsLocalRing.nonunits_add h_sum_nonunit h_neg_a_nonunit
      exact (mem_nonunits_iff.mp hb_nonunit) hb
    rw [h_entry]
    exact h_sum_unit

end Matrix.GeneralLinearGroup
