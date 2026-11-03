/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.StatisticalGenetics.Relatedness
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Tests for `MathlibExt.Biology.StatisticalGenetics.Relatedness` -/

open MeasureTheory MathlibExt.Biology.StatisticalGenetics.Relatedness

namespace MathlibExtTest.Relatedness

/-! ### Non-vacuity of `IBDModel`: a parent and an offspring

Three fair coins `u, v, w` (the bits of a uniform `ω : Fin 8`). Individual `0` carries alleles
`(u, v)`, individual `1` carries `(u, w)`: copy `(1, 0)` is identical by descent with copy
`(0, 0)`, all other distinct copies are independent. Then `p = 1/2`, `φ₀₁ = 1/4` and nobody is
inbred. -/

/-- The uniform probability on `Fin 8`. -/
noncomputable def unif8 : Measure (Fin 8) := (8 : ENNReal)⁻¹ • Measure.count

instance : IsProbabilityMeasure unif8 :=
  ⟨by simp [unif8, ENNReal.inv_mul_cancel]⟩

theorem integral_unif8 (f : Fin 8 → ℝ) : ∫ ω, f ω ∂unif8 = (∑ ω, f ω) / 8 := by
  rw [integral_fintype Integrable.of_finite, Finset.sum_div]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp [unif8, Measure.real]
  ring

/-- The allele indicators of the parent–offspring pair. -/
noncomputable def poAllele (c : Fin 2 × Fin 2) (ω : Fin 8) : ℝ :=
  ![![((ω.val % 2 : ℕ) : ℝ), ((ω.val / 2 % 2 : ℕ) : ℝ)],
    ![((ω.val % 2 : ℕ) : ℝ), ((ω.val / 4 : ℕ) : ℝ)]] c.1 c.2

/-- The parent–offspring IBD model. -/
noncomputable def parentOffspring : IBDModel unif8 (Fin 2) where
  p := 1 / 2
  p_pos := by norm_num
  p_lt_one := by norm_num
  allele := poAllele
  measurable_allele _ := measurable_of_finite _
  allele_mem c ω := by
    fin_cases c <;> fin_cases ω <;> simp [poAllele]
  ibd c d := if c = d ∨ (c.2 = 0 ∧ d.2 = 0) then 1 else 0
  integral_allele c := by
    rw [integral_unif8]
    fin_cases c <;> simp [poAllele, Fin.sum_univ_eight] <;> norm_num
  integral_allele_mul c d := by
    rw [integral_unif8]
    fin_cases c <;> fin_cases d <;> simp [poAllele, Fin.sum_univ_eight] <;> norm_num

example : parentOffspring.kinship 0 1 = 1 / 4 := by
  simp only [IBDModel.kinship, parentOffspring, Fin.sum_univ_two]
  norm_num [Prod.ext_iff]

example : parentOffspring.inbreeding 0 = 0 := by
  simp [IBDModel.inbreeding, parentOffspring]

/-- The GRM entry of a parent and an offspring has mean `2 φ = 1/2`. -/
example : ∫ ω, parentOffspring.grm 0 1 ω ∂unif8 = 1 / 2 := by
  rw [parentOffspring.integral_grm]
  simp only [IBDModel.kinship, parentOffspring, Fin.sum_univ_two]
  norm_num [Prod.ext_iff]

/-- The KING moment for a parent and an offspring: `4pq(1 - 2φ) = 1/2`. -/
example : ∫ ω, (parentOffspring.genotype 0 ω - parentOffspring.genotype 1 ω) ^ 2 ∂unif8 =
    1 / 2 := by
  rw [parentOffspring.integral_sub_sq_of_inbreeding_eq_zero
    (by simp [IBDModel.inbreeding, parentOffspring])
    (by simp [IBDModel.inbreeding, parentOffspring])]
  simp only [IBDModel.kinship, parentOffspring, Fin.sum_univ_two]
  norm_num [Prod.ext_iff]

/-- At a monomorphic locus (`p = 1`) the GRM denominator `2p(1 - p)` vanishes and the formula is
the junk value `0`; `IBDModel` excludes this case by `p < 1`. -/
example (x y : ℝ) : (x - 2 * 1) * (y - 2 * 1) / (2 * 1 * (1 - 1) : ℝ) = 0 := by simp

end MathlibExtTest.Relatedness
