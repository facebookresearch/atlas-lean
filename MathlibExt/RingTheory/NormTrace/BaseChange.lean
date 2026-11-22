/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Basic

/-!
# Norm and trace under base change

ATLAS `NumberTheoryI`, Lemma 4.49 (Section 4.3): if `B / A` is a ring
extension with `B` free of finite rank over `A` and `φ : A → A'` is a ring
homomorphism, then the base change `B' = B ⊗[A] A'` is free of the same rank
over `A'`, and `φ (N_{B/A} b) = N_{B'/A'} (b ⊗ 1)` and
`φ (T_{B/A} b) = T_{B'/A'} (b ⊗ 1)` for every `b : B`.

Mathlib orders the base-change factors as `A' ⊗[A] B`, where
`TensorProduct.includeRight b = 1 ⊗ b`. The tensor-factor swap identifies
this with the source's `b ⊗ 1` in `B ⊗[A] A'`.

The rank clause is Mathlib's `Module.finrank_baseChange`, so it is not
re-proved here. The norm and trace clauses are proved by identifying
multiplication by `1 ⊗ b` on Mathlib's base change with the base change of
multiplication by `b` (`Algebra.baseChange_lmul`) and then applying
Mathlib's determinant and trace base-change lemmas.

Source: `v1/Atlas/NumberTheoryI/targets.yaml`, Lemma 4.49, and the fully
proved formalization in
`v1/Atlas/NumberTheoryI/code/NormTrace.lean` (`norm_baseChange`,
`trace_baseChange`). The proof here replaces the source's left-multiplication
matrix computation with the `lmul` base-change identification above.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra

variable {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
  [Algebra A A'] [Algebra A B] [Module.Free A B] [Module.Finite A B]

/-- Norm commutes with base change: the image of `N_{B/A} b` under
`A → A'` is the norm of `1 ⊗ b` in `A' ⊗[A] B`. This is the norm clause of
ATLAS `NumberTheoryI`, Lemma 4.49. -/
theorem norm_baseChange (b : B) :
    algebraMap A A' (norm A b) =
      norm A' ((TensorProduct.includeRight b : A' ⊗[A] B)) := by
  rw [norm_apply A b, ← LinearMap.det_baseChange (A := A') (lmul A B b),
    baseChange_lmul b, ← TensorProduct.includeRight_apply (b := b),
    norm_apply A' ((TensorProduct.includeRight b : A' ⊗[A] B))]

/-- Trace commutes with base change: the image of `T_{B/A} b` under
`A → A'` is the trace of `1 ⊗ b` in `A' ⊗[A] B`. This is the trace clause
of ATLAS `NumberTheoryI`, Lemma 4.49. -/
theorem trace_baseChange (b : B) :
    algebraMap A A' (trace A B b) =
      trace A' (A' ⊗[A] B) (TensorProduct.includeRight b) := by
  rw [trace_apply A b, ← LinearMap.trace_baseChange (A := A') (lmul A B b),
    baseChange_lmul b, ← TensorProduct.includeRight_apply (b := b),
    trace_apply A' ((TensorProduct.includeRight b : A' ⊗[A] B))]

end Algebra
