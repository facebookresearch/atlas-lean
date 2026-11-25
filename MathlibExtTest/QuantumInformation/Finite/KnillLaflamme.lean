/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.QuantumInformation.Finite.KnillLaflamme
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Fin.VecNotation

/-!
# Knill–Laflamme checks

* A single unitary error on the whole space is correctable (recovery: its inverse), so
  `IsCorrectable` is satisfiable.
* The bit flip together with the identity is not correctable on the whole qubit space: the
  necessary condition fails because `X` is not a multiple of `1`.
* On two qubits, the code spanned by `|00⟩` and `|11⟩` satisfies the Knill–Laflamme conditions
  for the errors `{1, X ⊗ 1}`, so the hypotheses of the sufficiency theorem are jointly
  satisfiable by a nontrivial code, and the sufficiency theorem makes these errors correctable.
-/

@[expose] public section

open Matrix MathlibExt.QuantumInformation.Finite.KnillLaflamme
open scoped Matrix

namespace KnillLaflammeTest

/-- A unitary error is corrected by its adjoint. -/
example {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : IsCorrectable (1 : Matrix n n ℂ) (fun _ : Unit => U) := by
  refine ⟨1, fun _ => Uᴴ, ?_, fun _ _ => ⟨1, ?_⟩⟩
  · simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 hU
  · simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 hU

/-- The Pauli `X` (bit flip). -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- `{1, X}` is not correctable on the whole qubit space. -/
example : ¬ IsCorrectable (1 : Matrix (Fin 2) (Fin 2) ℂ) ![1, pauliX] := by
  intro h
  obtain ⟨c, hc⟩ := knillLaflamme_of_isCorrectable (by simp) (by simp) h 0 1
  have := congrFun (congrFun hc 0) 1
  simp [pauliX] at this

/-- Projector onto the span of `|00⟩` and `|11⟩` (basis order `00, 01, 10, 11`). -/
def codeP : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, 0, 0, 1]

/-- `X ⊗ 1`: flip the first qubit (`00 ↔ 10`, `01 ↔ 11`). -/
def flipFirst : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

/- The Knill–Laflamme conditions hold for the code `span {|00⟩, |11⟩}` and errors
`{1, X ⊗ 1}`. -/
private theorem codeP_knillLaflamme : codePᴴ = codeP ∧ codeP * codeP = codeP ∧
    ∀ a b : Fin 2, ∃ c : ℂ, codeP * (![1, flipFirst] a)ᴴ * ![1, flipFirst] b * codeP = c • codeP := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [codeP]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [codeP]
  · intro a b
    fin_cases a <;> fin_cases b
    · exact ⟨1, by ext i j; fin_cases i <;> fin_cases j <;> simp [codeP]⟩
    · exact ⟨0, by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [codeP, flipFirst, Matrix.mul_apply, Fin.sum_univ_four]⟩
    · exact ⟨0, by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [codeP, flipFirst, Matrix.mul_apply, Fin.sum_univ_four]⟩
    · exact ⟨1, by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [codeP, flipFirst, Matrix.mul_apply, Fin.sum_univ_four]⟩

/-- Sufficiency applied to a nontrivial code: `{1, X ⊗ 1}` is correctable on
`span {|00⟩, |11⟩}`. -/
example : IsCorrectable codeP ![1, flipFirst] :=
  MathlibExt.QuantumInformation.Finite.KnillLaflamme.isCorrectable_of_knillLaflamme codeP
    codeP_knillLaflamme.1 codeP_knillLaflamme.2.1 _ codeP_knillLaflamme.2.2

/-- The combined statement, read in the necessity direction on the same code. -/
example : ∀ a b : Fin 2, ∃ c : ℂ,
    codeP * (![1, flipFirst] a)ᴴ * ![1, flipFirst] b * codeP = c • codeP :=
  (isCorrectable_iff_knillLaflamme codeP_knillLaflamme.1 codeP_knillLaflamme.2.1).1
    (MathlibExt.QuantumInformation.Finite.KnillLaflamme.isCorrectable_of_knillLaflamme codeP
      codeP_knillLaflamme.1 codeP_knillLaflamme.2.1 _ codeP_knillLaflamme.2.2)

end KnillLaflammeTest
