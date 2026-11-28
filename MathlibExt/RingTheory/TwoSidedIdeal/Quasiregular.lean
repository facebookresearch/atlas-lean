/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.LinearAlgebra.Matrix.Ideal
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Quasiregular two-sided ideals

A two-sided ideal is quasiregular when each of its elements is quasiregular,
equivalently when `1 + x` is a unit for every element `x` of the ideal.  Such
ideals are exactly the two-sided ideals contained in the Jacobson radical.

The terminology is deliberately distinct from Mathlib's commutative
`Ideal.IsRadical`, which concerns radical ideals in the prime-ideal sense.

## Main declarations

* `TwoSidedIdeal.IsQuasiregular`
* `TwoSidedIdeal.isQuasiregular_iff_exists_inverseCorrection`
* `TwoSidedIdeal.isQuasiregular_iff_le_jacobson_bot`
* `TwoSidedIdeal.IsQuasiregular.of_forall_isNilpotent`
* `TwoSidedIdeal.IsQuasiregular.matrix`
-/

@[expose] public section

universe u

namespace TwoSidedIdeal

variable {R : Type u} [Ring R]

/-- A two-sided ideal is quasiregular if each of its elements is
quasiregular. -/
def IsQuasiregular (I : TwoSidedIdeal R) : Prop :=
  ∀ ⦃x : R⦄, x ∈ I → _root_.IsQuasiregular x

/-- Ideal-level quasiregularity is equivalent to invertibility of `1 + x`
for every member of the ideal. -/
theorem isQuasiregular_iff_forall_isUnit_one_add {I : TwoSidedIdeal R} :
    I.IsQuasiregular ↔ ∀ x : R, x ∈ I → IsUnit (1 + x) := by
  constructor
  · intro h x hx
    exact _root_.isQuasiregular_iff_isUnit.mp (h hx)
  · intro h x hx
    exact _root_.isQuasiregular_iff_isUnit.mpr (h x hx)

/-- A two-sided ideal is quasiregular exactly when every member has a
two-sided quasiregular inverse correction which again belongs to the ideal. -/
theorem isQuasiregular_iff_exists_inverseCorrection {I : TwoSidedIdeal R} :
    I.IsQuasiregular ↔
      ∀ x : R, x ∈ I → ∃ y : R, y ∈ I ∧
        (y + x + x * y = 0 ∧ x + y + y * x = 0) := by
  constructor
  · intro h x hx
    obtain ⟨y, hy₁, hy₂⟩ := _root_.isQuasiregular_iff.mp (h hx)
    have hy_eq : y = -(x + x * y) :=
      eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using hy₁)
    have hyI : y ∈ I := by
      rw [hy_eq]
      exact I.neg_mem (I.add_mem hx (I.mul_mem_right x y hx))
    exact ⟨y, hyI, hy₁, hy₂⟩
  · intro h x hx
    obtain ⟨y, -, hy₁, hy₂⟩ := h x hx
    exact _root_.isQuasiregular_iff.mpr ⟨y, hy₁, hy₂⟩

/-- An element of the Jacobson radical has invertible `1 + x`.

The proof does not assume that the ambient multiplicative monoid is
Dedekind-finite: a left inverse is promoted to a two-sided inverse by showing
that its residual idempotent lies in the Jacobson radical and vanishes. -/
theorem isUnit_one_add_of_mem_jacobson_bot {x : R}
    (hx : x ∈ (jacobson (⊥ : TwoSidedIdeal R))) : IsUnit (1 + x) := by
  obtain ⟨z, hz⟩ := (mem_jacobson_iff.mp hx) 1
  have hz₀ : z * 1 * x + z - 1 = 0 := (TwoSidedIdeal.mem_bot R).mp hz
  have hz₁ : z * x + z = 1 := sub_eq_zero.mp (by simpa using hz₀)
  have hleft : z * (1 + x) = 1 := by
    rw [mul_add, mul_one, add_comm]
    exact hz₁
  let e : R := 1 - (1 + x) * z
  have he_eq : e = z * x - x * z := by
    dsimp [e]
    rw [add_mul, one_mul]
    calc
      1 - (z + x * z) = 1 - z - x * z := by abel
      _ = (z * x + z) - z - x * z := by rw [hz₁]
      _ = z * x - x * z := by abel
  have he_mem : e ∈ jacobson (⊥ : TwoSidedIdeal R) := by
    rw [he_eq]
    exact TwoSidedIdeal.sub_mem (jacobson (⊥ : TwoSidedIdeal R))
      (mul_mem_left (jacobson (⊥ : TwoSidedIdeal R)) z x hx)
      (mul_mem_right (jacobson (⊥ : TwoSidedIdeal R)) x z hx)
  have haz_idem : ((1 + x) * z) * ((1 + x) * z) = (1 + x) * z := by
    calc
      ((1 + x) * z) * ((1 + x) * z) =
          (1 + x) * (z * (1 + x)) * z := by ac_rfl
      _ = (1 + x) * z := by rw [hleft, mul_one]
  have he_idem : e * e = e := by
    dsimp [e]
    calc
      (1 - (1 + x) * z) * (1 - (1 + x) * z) =
          1 - (1 + x) * z - (1 + x) * z +
            ((1 + x) * z) * ((1 + x) * z) := by noncomm_ring
      _ = 1 - (1 + x) * z - (1 + x) * z + (1 + x) * z := by
        rw [haz_idem]
      _ = 1 - (1 + x) * z := by abel
  obtain ⟨w, hw⟩ := (mem_jacobson_iff.mp he_mem) (-1)
  have hw₀ : w * (-1) * e + w - 1 = 0 := (TwoSidedIdeal.mem_bot R).mp hw
  have hw₁ : w * (-1) * e + w = 1 := sub_eq_zero.mp hw₀
  have hwleft : w * (1 - e) = 1 := by
    calc
      w * (1 - e) = w * (-1) * e + w := by noncomm_ring
      _ = 1 := hw₁
  have he_zero : e = 0 := by
    calc
      e = 1 * e := (one_mul e).symm
      _ = (w * (1 - e)) * e := by rw [hwleft]
      _ = w * ((1 - e) * e) := by rw [mul_assoc]
      _ = 0 := by rw [sub_mul, one_mul, he_idem, sub_self, mul_zero]
  have he_zero' : 1 - (1 + x) * z = 0 := by
    simpa [e] using he_zero
  have hright : (1 + x) * z = 1 := (sub_eq_zero.mp he_zero').symm
  exact ⟨⟨1 + x, z, hright, hleft⟩, rfl⟩

/-- A two-sided ideal is quasiregular exactly when it is contained in the
Jacobson radical. -/
theorem isQuasiregular_iff_le_jacobson_bot {I : TwoSidedIdeal R} :
    I.IsQuasiregular ↔ I ≤ jacobson (⊥ : TwoSidedIdeal R) := by
  constructor
  · intro hI x hx
    rw [mem_jacobson_iff]
    intro y
    have hyx : y * x ∈ I := I.mul_mem_left y x hx
    have hu : IsUnit (1 + y * x) :=
      _root_.isQuasiregular_iff_isUnit.mp (hI hyx)
    refine ⟨↑hu.unit⁻¹, ?_⟩
    rw [mem_bot]
    calc
      (↑hu.unit⁻¹ : R) * y * x + ↑hu.unit⁻¹ - 1 =
          (↑hu.unit⁻¹ : R) * (1 + y * x) - 1 := by noncomm_ring
      _ = 0 := by rw [hu.val_inv_mul, sub_self]
  · intro hI x hx
    exact _root_.isQuasiregular_iff_isUnit.mpr
      (isUnit_one_add_of_mem_jacobson_bot (hI hx))

namespace IsQuasiregular

variable {I : TwoSidedIdeal R}

/-- An elementwise nil two-sided ideal is quasiregular. -/
theorem of_forall_isNilpotent
    (hI : ∀ x : R, x ∈ I → _root_.IsNilpotent x) : I.IsQuasiregular := by
  intro x hx
  exact _root_.isQuasiregular_iff_isUnit.mpr (hI x hx).isUnit_one_add

/-- A two-sided ideal whose underlying left ideal has a zero power is
quasiregular. -/
theorem of_pow_asIdeal_eq_bot (n : ℕ) (hI : I.asIdeal ^ n = ⊥) :
    I.IsQuasiregular := by
  apply of_forall_isNilpotent
  intro x hx
  refine ⟨n, ?_⟩
  have hxpow : x ^ n ∈ I.asIdeal ^ n := Ideal.pow_mem_pow hx n
  have : x ^ n ∈ (⊥ : Ideal R) := hI ▸ hxpow
  simpa using this

/-- Entrywise matrices over a quasiregular two-sided ideal again form a
quasiregular two-sided ideal. -/
theorem matrix (hI : I.IsQuasiregular) (n : Type*) [Fintype n] [DecidableEq n] :
    (I.matrix n).IsQuasiregular := by
  rw [isQuasiregular_iff_le_jacobson_bot] at hI ⊢
  calc
    I.matrix n ≤ (jacobson (⊥ : TwoSidedIdeal R)).matrix n :=
      matrix_monotone n hI
    _ = jacobson (⊥ : TwoSidedIdeal (Matrix n n R)) :=
      matrix_jacobson_bot

end IsQuasiregular

end TwoSidedIdeal

end
