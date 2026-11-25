/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AutomorphicForm_ConstantTerm.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open Matrix MeasureTheory

namespace AutomorphicForm

section Unipotent

variable {R : Type*} [CommRing R]

private theorem unipotent_mul_unipotent (x y : R) :
    !![1, x; 0, 1] * !![1, y; 0, 1] = !![1, x + y; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The unipotent matrix $\begin{pmatrix} 1 & x \\ 0 & 1 \end{pmatrix}$. -/
public def unipotentGL2 (x : R) : GL (Fin 2) R where
  val := !![1, x; 0, 1]
  inv := !![1, -x; 0, 1]
  val_inv := by rw [unipotent_mul_unipotent, add_neg_cancel, Matrix.one_fin_two]
  inv_val := by rw [unipotent_mul_unipotent, neg_add_cancel, Matrix.one_fin_two]

@[simp]
public theorem unipotentGL2_coe (x : R) :
    (unipotentGL2 x : Matrix (Fin 2) (Fin 2) R) = !![1, x; 0, 1] := rfl

@[simp]
public theorem unipotentGL2_zero : unipotentGL2 (0 : R) = 1 := by
  ext i j; simp [unipotentGL2, Matrix.one_fin_two]

public theorem unipotentGL2_add (x y : R) :
    unipotentGL2 (x + y) = unipotentGL2 x * unipotentGL2 y := by
  ext i j; simp only [unipotentGL2, Units.val_mul, unipotent_mul_unipotent]

/-- The additive-to-multiplicative homomorphism given by unipotent matrices. -/
public def unipotentGL2Hom : Multiplicative R →* GL (Fin 2) R where
  toFun x := unipotentGL2 x.toAdd
  map_one' := unipotentGL2_zero
  map_mul' x y := unipotentGL2_add x.toAdd y.toAdd

end Unipotent

section ConstantTerm

variable {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]

/-- The integrand of the constant term of `f` along `u` at `g`. -/
public def constantTermIntegrand (u : Q → G) (f : G → ℂ) (g : G) : Q → ℂ :=
  fun q => f (u q * g)

/-- The constant term of `f` along `u` at `g`, against the measure `μ`. -/
public noncomputable def constantTerm (μ : Measure Q) (u : Q → G) (f : G → ℂ)
    (g : G) : ℂ :=
  ∫ q, constantTermIntegrand u f g q ∂μ

@[simp]
public theorem constantTerm_zero (μ : Measure Q) (u : Q → G) (g : G) :
    constantTerm μ u (fun _ => (0 : ℂ)) g = 0 := by
  simp [constantTerm, constantTermIntegrand]

@[simp]
public theorem constantTerm_const (μ : Measure Q) [IsProbabilityMeasure μ]
    (u : Q → G) (c : ℂ) (g : G) : constantTerm μ u (fun _ => c) g = c := by
  simp [constantTerm, constantTermIntegrand, integral_const, measureReal_def]

/-- A function is cuspidal along `u` when, at every `g`, the constant-term integrand is
integrable and the constant term vanishes. Integrability is required because the Bochner
integral of a non-integrable function is `0`. -/
public def IsCuspidalFn (μ : Measure Q) (u : Q → G) (f : G → ℂ) : Prop :=
  ∀ g : G, Integrable (constantTermIntegrand u f g) μ ∧ constantTerm μ u f g = 0

end ConstantTerm

end AutomorphicForm
