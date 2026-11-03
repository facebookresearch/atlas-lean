/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.DominanceLD
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Biology.StatisticalGenetics.DominanceLD
open scoped ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.DominanceLD

/-! ### A non-vacuous model in linkage disequilibrium

Haplotypes are drawn from `Fin 4` uniformly, with allele indicators
`(0, 0), (0, 0), (1, 1), (0, 1)` at loci `A`, `B` (so `p = 1/4`, `q = 1/2`,
`D = 1/4 - 1/8 = 1/8`). A diploid individual is a pair of independent draws: the product measure
on `Fin 4 × Fin 4`. -/

/-- The uniform probability measure on `Fin 4`. -/
noncomputable def μ4 : Measure (Fin 4) := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ4 :=
  ⟨by simpa [μ4] using ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

/-- The haplotype allele indicators at loci `A` and `B`. -/
def hap : Fin 4 → ℝ × ℝ := ![(0, 0), (0, 0), (1, 1), (0, 1)]

/-- The witness: two independent uniform haplotype draws. -/
noncomputable def G : RandomUnion (μ4.prod μ4) where
  x1 := fun ω => (hap ω.1).1
  y1 := fun ω => (hap ω.1).2
  x2 := fun ω => (hap ω.2).1
  y2 := fun ω => (hap ω.2).2
  memLp_x1 := MemLp.of_discrete
  memLp_y1 := MemLp.of_discrete
  memLp_x2 := MemLp.of_discrete
  memLp_y2 := MemLp.of_discrete
  indep := indepFun_prod (X := hap) (Y := hap) (measurable_of_finite _) (measurable_of_finite _)
  ident := by
    refine ⟨(measurable_of_finite _).aemeasurable, (measurable_of_finite _).aemeasurable, ?_⟩
    change (μ4.prod μ4).map (hap ∘ Prod.fst) = (μ4.prod μ4).map (hap ∘ Prod.snd)
    rw [← Measure.map_map (measurable_of_finite _) measurable_fst,
      ← Measure.map_map (measurable_of_finite _) measurable_snd, Measure.map_fst_prod,
      Measure.map_snd_prod]

/-- On the witness the dominance correlation is the square of the additive correlation. -/
example :
    (∫ ω, G.domA ω * G.domB ω ∂(μ4.prod μ4)) /
        Real.sqrt ((∫ ω, G.domA ω ^ 2 ∂(μ4.prod μ4)) * ∫ ω, G.domB ω ^ 2 ∂(μ4.prod μ4)) =
      ((∫ ω, G.addA ω * G.addB ω ∂(μ4.prod μ4)) /
        Real.sqrt ((∫ ω, G.addA ω ^ 2 ∂(μ4.prod μ4)) * ∫ ω, G.addB ω ^ 2 ∂(μ4.prod μ4))) ^ 2 :=
  G.domCorr_eq_addCorr_sq

/-! ### The dominance encoding -/

/-- Genotype `0` (two copies of the other allele) is encoded `p²`. -/
example (p : ℝ) : (0 - p) * (0 - p) = dominanceEncoding p (0 + 0) :=
  domCode_eq_dominanceEncoding (Or.inl rfl) (Or.inl rfl) p

/-- Heterozygotes are encoded `-p (1 - p)` whichever haplotype carries the allele. -/
example (p : ℝ) : (1 - p) * (0 - p) = -(p * (1 - p)) := by
  rw [domCode_eq_dominanceEncoding (Or.inr rfl) (Or.inl rfl) p]
  norm_num [dominanceEncoding]

/-- Genotype `2` is encoded `(1 - p)²`. -/
example (p : ℝ) : dominanceEncoding p 2 = (1 - p) ^ 2 := by
  norm_num [dominanceEncoding]

/-- Scaling by `-1 / (p (1 - p))` gives Palmer et al.'s encoding: `p = 1/4` gives
`-1/3, 1, -3`. -/
example : dominanceEncoding (1 / 4) 0 / (-(1 / 4 * (1 - 1 / 4))) = -1 / 3 ∧
    dominanceEncoding (1 / 4) 2 / (-(1 / 4 * (1 - 1 / 4))) = -3 := by
  norm_num [dominanceEncoding]

end MathlibExtTest.Biology.StatisticalGenetics.DominanceLD
