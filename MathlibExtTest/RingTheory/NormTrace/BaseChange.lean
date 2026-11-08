/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.RingTheory.NormTrace.BaseChange

/-!
# Tests for norm and trace under base change

Generic API checks for `Algebra.norm_baseChange` and
`Algebra.trace_baseChange`, plus concrete evaluations along
`ℚ → ℝ` and `ℤ → ℚ` with the trivial algebra `B` equal to the base ring,
where both sides of each formula evaluate to the same number.
-/

@[expose] public section

open scoped TensorProduct

namespace MathlibExtTest.RingTheory.NormTrace.BaseChange

/-- Generic call to `Algebra.norm_baseChange`. -/
example {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] [Module.Free A B] [Module.Finite A B]
    (b : B) :
    algebraMap A A' (Algebra.norm A b) =
      Algebra.norm A'
        ((Algebra.TensorProduct.includeRight b : A' ⊗[A] B)) :=
  Algebra.norm_baseChange b

/-- Generic call to `Algebra.trace_baseChange`. -/
example {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] [Module.Free A B] [Module.Finite A B]
    (b : B) :
    algebraMap A A' (Algebra.trace A B b) =
      Algebra.trace A' (A' ⊗[A] B) (Algebra.TensorProduct.includeRight b) :=
  Algebra.trace_baseChange b

/-- Base change along `ℚ → ℝ` with `B = ℚ`: the norm of `1 ⊗ 2` is `2`. -/
example : Algebra.norm ℝ
    ((Algebra.TensorProduct.includeRight (2 : ℚ) : ℝ ⊗[ℚ] ℚ)) =
    (2 : ℝ) := by
  rw [← Algebra.norm_baseChange (A := ℚ) (A' := ℝ) (B := ℚ) (2 : ℚ)]
  simp [Algebra.norm_self]

/-- Base change along `ℚ → ℝ` with `B = ℚ`: the trace of `1 ⊗ 2` is `2`. -/
example : Algebra.trace ℝ (ℝ ⊗[ℚ] ℚ)
    (Algebra.TensorProduct.includeRight (2 : ℚ)) = (2 : ℝ) := by
  rw [← Algebra.trace_baseChange (A := ℚ) (A' := ℝ) (B := ℚ) (2 : ℚ)]
  simp

/-- Base change along `ℤ → ℚ` with `B = ℤ`: the norm of `1 ⊗ 5` is `5`. -/
example : Algebra.norm ℚ
    ((Algebra.TensorProduct.includeRight (5 : ℤ) : ℚ ⊗[ℤ] ℤ)) =
    (5 : ℚ) := by
  rw [← Algebra.norm_baseChange (A := ℤ) (A' := ℚ) (B := ℤ) (5 : ℤ)]
  simp [Algebra.norm_self]

/-- Base change along `ℤ → ℚ` with `B = ℤ`: the trace of `1 ⊗ 5` is `5`. -/
example : Algebra.trace ℚ (ℚ ⊗[ℤ] ℤ)
    (Algebra.TensorProduct.includeRight (5 : ℤ)) = (5 : ℚ) := by
  rw [← Algebra.trace_baseChange (A := ℤ) (A' := ℚ) (B := ℤ) (5 : ℤ)]
  simp

end MathlibExtTest.RingTheory.NormTrace.BaseChange
