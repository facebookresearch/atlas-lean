/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.ComplexIwasawa

@[expose] public section

open AutomorphicForm.ComplexIwasawa

/-- Source consumer with the original binders. -/
private theorem exactSource {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (z : ℂ) :
    kC g z ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  kC_mem_specialUnitaryGroup hg z

/-- The determinant and unitarity characterizations of the compact factor. -/
example {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (z : ℂ) :
    (kC g z).det = 1 ∧ (kC g z).conjTranspose * kC g z = 1 :=
  ⟨det_kC hg z, conjTranspose_mul_kC hg z⟩

/-- Without nonzero determinant the conclusion can fail: for `g = 0` the
radius vanishes, the normalized factor is `0`, and `0 ∉ SU(2)`. -/
example : ¬ (kC (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 ∈
    Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  intro h
  have hdet := (Matrix.mem_specialUnitaryGroup_iff.1 h).2
  simp [kC, botP, botQ, radC] at hdet
