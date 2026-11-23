/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.AuerbachBasis
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Basic

import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.NormNum

/-!
# Tests for Auerbach bases

* Auerbach's theorem on `Fin 2 → ℝ`, on `Fin 3 → 𝕜` for general `𝕜`
  (hence on `Fin 3 → ℂ`), and on the zero-dimensional space `Fin 0 → ℝ`
  (existence, via `exists_auerbach_basis`).
* The standard basis `Pi.basisFun ℝ (Fin 2)` is an Auerbach basis of
  `Fin 2 → ℝ` (unit vectors, coordinate functionals of norm `1`), and its
  coordinate functionals are evaluation.
* `#print axioms` for the `Fin 2 → ℝ` instance: standard triple only.
-/

open Set Filter Topology Metric
open MathlibExt.Analysis.FunctionalAnalysis.AuerbachBasis

@[expose] public section

namespace MathlibExtTest.Analysis.FunctionalAnalysis.AuerbachBasisTests

/-- Auerbach's theorem on `Fin 2 → ℝ`. -/
theorem auerbach_basis_exists_fin_two_real :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ (Fin 2 → ℝ))) ℝ (Fin 2 → ℝ), IsAuerbachBasis b :=
  exists_auerbach_basis

/-- Auerbach's theorem on `Fin 3 → ℂ`. -/
theorem auerbach_basis_exists_fin_three {𝕜 : Type*} [RCLike 𝕜] :
    ∃ b : Module.Basis (Fin (Module.finrank 𝕜 (Fin 3 → 𝕜))) 𝕜 (Fin 3 → 𝕜), IsAuerbachBasis b :=
  exists_auerbach_basis

/-- The generic statement specializes to `ℂ`: the instance search for
`RCLike ℂ` and the `Fin 3 → ℂ` normed-space structure succeeds, and the
resulting basis is an Auerbach basis. -/
example : True := by
  have _h := exists_auerbach_basis (𝕜 := ℂ) (E := Fin 3 → ℂ)
  trivial

/-- Auerbach's theorem on the zero-dimensional space `Fin 0 → ℝ`. -/
theorem auerbach_basis_exists_zero_dim :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ (Fin 0 → ℝ))) ℝ (Fin 0 → ℝ), IsAuerbachBasis b :=
  exists_auerbach_basis

/-- The standard basis of `Fin 2 → ℝ` is an Auerbach basis: its vectors are
unit vectors and its coordinate functionals have operator norm `1`. -/
theorem pi_basisFun_isAuerbachBasis : IsAuerbachBasis (Pi.basisFun ℝ (Fin 2)) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [Pi.basisFun_apply, Pi.norm_single, norm_one]
  · apply norm_coordCLM_eq_one
    · rw [Pi.basisFun_apply, Pi.norm_single, norm_one]
    · intro y
      have hcoord : (Pi.basisFun ℝ (Fin 2)).coord i y = y i := by
        simp [Module.Basis.coord_apply, Pi.basisFun_repr]
      rw [hcoord]
      exact norm_le_pi_norm y i

/-- The coordinate functionals of the standard basis are evaluation. -/
example (i : Fin 2) (y : Fin 2 → ℝ) :
    coordCLM (Pi.basisFun ℝ (Fin 2)) i y = y i := by
  simp [coordCLM_apply, Module.Basis.coord_apply, Pi.basisFun_repr]

#print axioms auerbach_basis_exists_fin_two_real

end MathlibExtTest.Analysis.FunctionalAnalysis.AuerbachBasisTests
