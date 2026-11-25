/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.Matrix.ZeroExtension.Trace
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Data.Matrix.Basic

/-!
# Actual finite-matrix zero-corner Lie maps

The existing native zero extension is ground-linear and multiplicative.
Its commutator compatibility supplies the actual Lie embedding, including
size zero. Coefficient algebra maps act entrywise and commute with these
embeddings. The scalar trace-zero Lie algebra and its actual scalar inclusion
provide the finite-stage special-linear maps used by CE coinvariants.

The ring and coefficient-algebra worlds are independent. No unitality of
zero extension, matrix-stability result or desired Lie-map certificate is assumed.
-/

@[expose] public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

namespace Matrix

variable (k : Type u) [CommRing k]
variable (A : Type v) [Ring A] [Algebra k A]

/-- The actual upper-left zero extension as a ground-linear commutator Lie map. -/
def zeroExtendLieHom {m n : ℕ} (h : m ≤ n) :
    Matrix (Fin m) (Fin m) A →ₗ⁅k⁆ Matrix (Fin n) (Fin n) A where
  toLinearMap := zeroExtendLinear (k := k) (A := A) h
  map_lie' := by
    intro B C
    change zeroExtend h (B * C - C * B) =
      zeroExtend h B * zeroExtend h C - zeroExtend h C * zeroExtend h B
    have hs := map_sub (zeroExtendAlgHom (k := k) (A := A) h) (B * C) (C * B)
    simpa only [zeroExtendAlgHom_apply, zeroExtend_mul] using hs

@[simp]
theorem zeroExtendLieHom_apply {m n : ℕ} (h : m ≤ n) (B : Matrix (Fin m) (Fin m) A) :
    zeroExtendLieHom k A h B = zeroExtend h B := rfl

theorem zeroExtendLieHom_apply_entry {m n : ℕ} (h : m ≤ n)
    (B : Matrix (Fin m) (Fin m) A) (i j : Fin n) :
    zeroExtendLieHom k A h B i j = if hi : i.val < m then
      if hj : j.val < m then B ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else 0 := rfl

theorem zeroExtendLieHom_injective {m n : ℕ} (h : m ≤ n) :
    Function.Injective (zeroExtendLieHom k A h) := zeroExtend_injective h

@[simp]
theorem zeroExtendLieHom_id (m : ℕ) :
    zeroExtendLieHom k A (le_rfl : m ≤ m) = LieHom.id := by
  apply LieHom.ext
  intro B
  exact zeroExtend_self B

theorem zeroExtendLieHom_comp {m n p : ℕ} (h : m ≤ n) (h' : n ≤ p) :
    (zeroExtendLieHom k A h').comp (zeroExtendLieHom k A h) =
      zeroExtendLieHom k A (h.trans h') := by
  apply LieHom.ext
  intro B
  exact zeroExtend_comp h h' B

variable {B : Type w} [Ring B] [Algebra k B]

/-- Entrywise coefficient functoriality is an actual Lie map. -/
def coefficientLieHom (f : A →ₐ[k] B) (m : ℕ) :
    Matrix (Fin m) (Fin m) A →ₗ⁅k⁆ Matrix (Fin m) (Fin m) B :=
  (f.mapMatrix (m := Fin m)).toLieHom

@[simp]
theorem coefficientLieHom_apply_entry (f : A →ₐ[k] B) (m : ℕ)
    (C : Matrix (Fin m) (Fin m) A) (i j : Fin m) :
    coefficientLieHom k A f m C i j = f (C i j) := rfl

/-- The actual entrywise coefficient map commutes with every finite zero corner. -/
theorem coefficientLieHom_zeroExtend (f : A →ₐ[k] B) {m n : ℕ} (h : m ≤ n)
    (C : Matrix (Fin m) (Fin m) A) :
    coefficientLieHom k A f n (zeroExtend h C) =
      zeroExtend h (coefficientLieHom k A f m C) := by
  ext i j
  by_cases hi : i.val < m <;> by_cases hj : j.val < m <;>
    simp only [coefficientLieHom_apply_entry, zeroExtend_apply, hi, hj, ↓reduceDIte, map_zero]

/-- Simultaneous finite-size and coefficient naturality as an actual Lie-map equality. -/
theorem coefficientLieHom_zeroExtend_comp (f : A →ₐ[k] B) {m n : ℕ} (h : m ≤ n) :
    (coefficientLieHom k A f n).comp (zeroExtendLieHom k A h) =
      (zeroExtendLieHom k B h).comp (coefficientLieHom k A f m) := by
  apply LieHom.ext
  intro C
  exact coefficientLieHom_zeroExtend k A f h C

/-- The scalar special-linear carrier is the native trace-zero matrix Lie subalgebra. -/
abbrev ScalarSpecialLinear (m : ℕ) := ↥(LieAlgebra.SpecialLinear.sl (Fin m) k)

/-- The actual scalar inclusion of trace-zero matrices into matrices over the coefficient algebra. -/
def scalarLieHom (m : ℕ) : ScalarSpecialLinear k m →ₗ⁅k⁆ Matrix (Fin m) (Fin m) A :=
  (coefficientLieHom k k (Algebra.ofId k A) m).comp
    (LieAlgebra.SpecialLinear.sl (Fin m) k).incl

@[simp]
theorem scalarLieHom_apply_entry (m : ℕ) (s : ScalarSpecialLinear k m) (i j : Fin m) :
    scalarLieHom k A m s i j = algebraMap k A (s.val i j) := rfl

/-- Trace preservation makes actual zero extension a map of scalar special-linear Lie algebras. -/
def scalarZeroExtendLieHom {m n : ℕ} (h : m ≤ n) :
    ScalarSpecialLinear k m →ₗ⁅k⁆ ScalarSpecialLinear k n where
  toFun s := ⟨zeroExtend h s.val, by
    change Matrix.trace (zeroExtend h s.val) = 0
    rw [zeroExtend_trace]
    exact s.property⟩
  map_add' s t := by
    apply Subtype.ext
    exact (zeroExtendLinear (k := k) (A := k) h).map_add s.val t.val
  map_smul' r s := by
    apply Subtype.ext
    exact (zeroExtendLinear (k := k) (A := k) h).map_smul r s.val
  map_lie' := by
    intro s t
    apply Subtype.ext
    exact (zeroExtendLieHom k k h).map_lie s.val t.val

@[simp]
theorem scalarZeroExtendLieHom_coe {m n : ℕ} (h : m ≤ n) (s : ScalarSpecialLinear k m) :
    (scalarZeroExtendLieHom k h s).val = zeroExtend h s.val := rfl

/-- The actual scalar Lie inclusion commutes with the actual finite zero corners. -/
theorem scalarLieHom_zeroExtend {m n : ℕ} (h : m ≤ n) :
    (zeroExtendLieHom k A h).comp (scalarLieHom k A m) =
      (scalarLieHom k A n).comp (scalarZeroExtendLieHom k h) := by
  apply LieHom.ext
  intro s
  ext i j
  by_cases hi : i.val < m <;> by_cases hj : j.val < m <;>
    simp only [LieHom.comp_apply, zeroExtendLieHom_apply, scalarLieHom_apply_entry,
      scalarZeroExtendLieHom_coe, zeroExtend_apply, hi, hj, ↓reduceDIte, map_zero]

/-- The actual scalar Lie inclusion is natural in the coefficient algebra. -/
theorem scalarLieHom_coefficient (f : A →ₐ[k] B) (m : ℕ) :
    (coefficientLieHom k A f m).comp (scalarLieHom k A m) = scalarLieHom k B m := by
  apply LieHom.ext
  intro s
  ext i j
  simp only [LieHom.comp_apply, coefficientLieHom_apply_entry, scalarLieHom_apply_entry,
    AlgHom.commutes]

end Matrix
