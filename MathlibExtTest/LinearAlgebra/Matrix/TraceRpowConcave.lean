/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.TraceRpowConcave

/-!
# Tests for the one-variable cases of Lieb's concavity theorem
-/

open scoped ComplexOrder

namespace MathlibExtTest.LinearAlgebra.Matrix.TraceRpowConcave

open MathlibExt.LinearAlgebra.Matrix.TraceRpowConcave

/-- The square root case `q = 1/2` with a rectangular `K`. -/
example (K : Matrix (Fin 2) (Fin 3) ℂ) :
    ConcaveOn ℝ {A : Matrix (Fin 2) (Fin 2) ℂ | A.PosSemidef}
      (fun A => RCLike.re (K.conjTranspose * cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) A * K).trace) :=
  concaveOn_re_trace_conj_rpow K (by norm_num) (by norm_num)

/-- The case `r = 0` of the joint statement. -/
example (K : Matrix (Fin 2) (Fin 3) ℂ) :
    ConcaveOn ℝ {p : Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 3) (Fin 3) ℂ | p.1.PosDef ∧ p.2.PosDef}
      (fun p => RCLike.re (K.conjTranspose * cfc (· ^ (3⁻¹ : ℝ) : ℝ → ℝ) p.1 * K *
        cfc (· ^ (0 : ℝ) : ℝ → ℝ) p.2).trace) :=
  lieb_concavity_trace_rpow_of_right_eq_zero K (by norm_num) (by norm_num)

/-- The case `q = 0` of the joint statement, at the endpoint `r = 1`. -/
example (K : Matrix (Fin 2) (Fin 3) ℂ) :
    ConcaveOn ℝ {p : Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 3) (Fin 3) ℂ | p.1.PosDef ∧ p.2.PosDef}
      (fun p => RCLike.re (K.conjTranspose * cfc (· ^ (0 : ℝ) : ℝ → ℝ) p.1 * K *
        cfc (· ^ (1 : ℝ) : ℝ → ℝ) p.2).trace) :=
  lieb_concavity_trace_rpow_of_left_eq_zero K (by norm_num) le_rfl

/-- The domain of the joint statement is nonempty: `(1, 1)` is a pair of positive-definite
matrices. -/
example : ((1 : Matrix (Fin 2) (Fin 2) ℂ), (1 : Matrix (Fin 3) (Fin 3) ℂ)) ∈
    {p : Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 3) (Fin 3) ℂ | p.1.PosDef ∧ p.2.PosDef} :=
  ⟨Matrix.PosDef.one, Matrix.PosDef.one⟩

end MathlibExtTest.LinearAlgebra.Matrix.TraceRpowConcave
