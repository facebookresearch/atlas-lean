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

public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.ParityCompression
import Mathlib.Tactic.SplitIfs

/-!
# Finite algebraic parity-frame equations

The actual insertion and sampling maps satisfy their composition and row
partition identities, including size zero. The right-hand side is literal
zero padding, so only additive complex-module coefficients are needed.
No norm, unit, commutative multiplication, raw-limit or completed frame is used.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarMatrix

universe u

/-- Let `A` be a complex module. For natural numbers `N`, `ε` and `δ : Fin 2` and `X : CStarMatrix (Fin
N) (Fin N) A`. Sampling inserted parity rows recovers the padded for matching parities and is zero
for distinct parities.
-/
theorem parityRowCompressLinear_insert
    {A : Type u} [AddCommMonoid A] [Module ℂ A]
    (N : ℕ) (ε δ : Fin 2) (X : CStarMatrix (Fin N) (Fin N) A) :
    parityRowCompressLinear (2 * N) ε (parityRowInsertLinear N δ X) =
      if ε = δ then
        ofMatrix (Matrix.zeroExtend (by omega : N ≤ 2 * N) (ofMatrix.symm X))
      else 0 := by
  classical
  let entries : Fin N → Fin N → A := fun i j => X i j
  by_cases heq : ε = δ
  · rw [ite_eq_left heq]
    subst δ
    apply CStarMatrix.ext
    intro i j
    have hε := ε.is_lt
    have hdiv : (2 * i.val + ε.val) / 2 = i.val := by omega
    have hmod : (2 * i.val + ε.val) % 2 = ε.val := by omega
    change
      (if h : 2 * i.val + ε.val < 2 * N then
        (if hh : (2 * i.val + ε.val) / 2 < N ∧ j.val < N ∧
            (2 * i.val + ε.val) % 2 = ε.val then
          entries ⟨(2 * i.val + ε.val) / 2, hh.1⟩ ⟨j.val, hh.2.1⟩
        else (0 : A))
      else 0) =
        (if hi : i.val < N then
          if hj : j.val < N then entries ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
        else 0)
    by_cases hi : i.val < N
    · have hout : 2 * i.val + ε.val < 2 * N := by omega
      by_cases hj : j.val < N
      · have hin : (2 * i.val + ε.val) / 2 < N ∧ j.val < N ∧
            (2 * i.val + ε.val) % 2 = ε.val :=
          ⟨by rw [hdiv]; exact hi, hj, hmod⟩
        rw [dite_eq_left hout, dite_eq_left hin, dite_eq_left hi, dite_eq_left hj]
        apply congrArg (fun r : Fin N => entries r ⟨j.val, hj⟩)
        apply Fin.ext
        exact hdiv
      · have hin : ¬ ((2 * i.val + ε.val) / 2 < N ∧ j.val < N ∧
            (2 * i.val + ε.val) % 2 = ε.val) := fun h => hj h.2.1
        rw [dite_eq_left hout, dite_eq_right hin, dite_eq_left hi, dite_eq_right hj]
    · have hout : ¬ 2 * i.val + ε.val < 2 * N := by omega
      rw [dite_eq_right hout, dite_eq_right hi]
  · rw [ite_eq_right heq]
    apply CStarMatrix.ext
    intro i j
    have hε := ε.is_lt
    have hne : ε.val ≠ δ.val := fun h => heq (Fin.ext h)
    have hmod : (2 * i.val + ε.val) % 2 = ε.val := by omega
    change
      (if h : 2 * i.val + ε.val < 2 * N then
        (if hh : (2 * i.val + ε.val) / 2 < N ∧ j.val < N ∧
            (2 * i.val + ε.val) % 2 = δ.val then
          entries ⟨(2 * i.val + ε.val) / 2, hh.1⟩ ⟨j.val, hh.2.1⟩
        else (0 : A))
      else 0) = (0 : A)
    have hin : ¬ ((2 * i.val + ε.val) / 2 < N ∧ j.val < N ∧
        (2 * i.val + ε.val) % 2 = δ.val) := by
      intro h
      exact hne (hmod.symm.trans h.2.2)
    by_cases hout : 2 * i.val + ε.val < 2 * N
    · rw [dite_eq_left hout, dite_eq_right hin]
    · rw [dite_eq_right hout]

/-- Let `A` be a complex module. For natural numbers `N` and `X : CStarMatrix (Fin N) (Fin N) A`.
Reinsert the two sampled parities to obtain the exact padded source matrix.
-/
theorem parityRowInsertLinear_compress_partition
    {A : Type u} [AddCommMonoid A] [Module ℂ A]
    (N : ℕ) (X : CStarMatrix (Fin N) (Fin N) A) :
    parityRowInsertLinear N (0 : Fin 2) (parityRowCompressLinear N (0 : Fin 2) X) +
        parityRowInsertLinear N (1 : Fin 2) (parityRowCompressLinear N (1 : Fin 2) X) =
      ofMatrix (Matrix.zeroExtend (by omega : N ≤ 2 * N) (ofMatrix.symm X)) := by
  let entries : Fin N → Fin N → A := fun i j => X i j
  apply CStarMatrix.ext
  intro i j
  have hibound := i.is_lt
  change
    ((if h : i.val / 2 < N ∧ j.val < N ∧ i.val % 2 = 0 then
      (if hc : 2 * (i.val / 2) + 0 < N then
        entries ⟨2 * (i.val / 2) + 0, hc⟩ ⟨j.val, h.2.1⟩
      else (0 : A))
    else 0) +
    (if h : i.val / 2 < N ∧ j.val < N ∧ i.val % 2 = 1 then
      (if hc : 2 * (i.val / 2) + 1 < N then
        entries ⟨2 * (i.val / 2) + 1, hc⟩ ⟨j.val, h.2.1⟩
      else (0 : A))
    else 0)) =
      (if h : i.val < N then
        if hc : j.val < N then entries ⟨i.val, h⟩ ⟨j.val, hc⟩ else 0
      else 0)
  by_cases hi : i.val < N
  · by_cases hj : j.val < N
    · have hhalf : i.val / 2 < N := by omega
      have hparity : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
      rcases hparity with hp | hp
      · have hrow : 2 * (i.val / 2) + 0 = i.val := by omega
        have hout : i.val / 2 < N ∧ j.val < N ∧ i.val % 2 = 0 := ⟨hhalf, hj, hp⟩
        have hother : ¬ (i.val / 2 < N ∧ j.val < N ∧ i.val % 2 = 1) := by
          intro h
          have hh := h.2.2
          omega
        have hin : 2 * (i.val / 2) + 0 < N := by omega
        rw [dite_eq_left hout, dite_eq_left hin, dite_eq_right hother,
          add_zero, dite_eq_left hi, dite_eq_left hj]
        apply congrArg (fun r : Fin N => entries r ⟨j.val, hj⟩)
        apply Fin.ext
        exact hrow
      · have hrow : 2 * (i.val / 2) + 1 = i.val := by omega
        have hout : i.val / 2 < N ∧ j.val < N ∧ i.val % 2 = 1 := ⟨hhalf, hj, hp⟩
        have hother : ¬ (i.val / 2 < N ∧ j.val < N ∧ i.val % 2 = 0) := by
          intro h
          have hh := h.2.2
          omega
        have hin : 2 * (i.val / 2) + 1 < N := by omega
        rw [dite_eq_right hother, dite_eq_left hout, dite_eq_left hin,
          zero_add, dite_eq_left hi, dite_eq_left hj]
        apply congrArg (fun r : Fin N => entries r ⟨j.val, hj⟩)
        apply Fin.ext
        exact hrow
    · have hzero : ¬ (i.val / 2 < N ∧ j.val < N ∧ i.val % 2 = 0) :=
        fun h => hj h.2.1
      have hone : ¬ (i.val / 2 < N ∧ j.val < N ∧ i.val % 2 = 1) :=
        fun h => hj h.2.1
      rw [dite_eq_right hzero, dite_eq_right hone, zero_add,
        dite_eq_left hi, dite_eq_right hj]
  · by_cases hj : j.val < N
    · have hhalf : i.val / 2 < N := by omega
      have hparity : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
      rcases hparity with hp | hp
      · have hrow : 2 * (i.val / 2) + 0 = i.val := by omega
        have hout : i.val / 2 < N ∧ j.val < N ∧ i.val % 2 = 0 := ⟨hhalf, hj, hp⟩
        have hother : ¬ (i.val / 2 < N ∧ j.val < N ∧ i.val % 2 = 1) := by
          intro h
          have hh := h.2.2
          omega
        have hin : ¬ 2 * (i.val / 2) + 0 < N := by omega
        rw [dite_eq_left hout, dite_eq_right hin, dite_eq_right hother,
          zero_add, dite_eq_right hi]
      · have hrow : 2 * (i.val / 2) + 1 = i.val := by omega
        have hout : i.val / 2 < N ∧ j.val < N ∧ i.val % 2 = 1 := ⟨hhalf, hj, hp⟩
        have hother : ¬ (i.val / 2 < N ∧ j.val < N ∧ i.val % 2 = 0) := by
          intro h
          have hh := h.2.2
          omega
        have hin : ¬ 2 * (i.val / 2) + 1 < N := by omega
        rw [dite_eq_right hother, dite_eq_left hout, dite_eq_right hin,
          zero_add, dite_eq_right hi]
    · have hzero : ¬ (i.val / 2 < N ∧ j.val < N ∧ i.val % 2 = 0) :=
        fun h => hj h.2.1
      have hone : ¬ (i.val / 2 < N ∧ j.val < N ∧ i.val % 2 = 1) :=
        fun h => hj h.2.1
      rw [dite_eq_right hzero, dite_eq_right hone, zero_add, dite_eq_right hi]

end CStarMatrix
