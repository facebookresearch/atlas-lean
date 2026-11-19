/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Selection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The ploidy bridge for multiplicative fitness

If diploid genotype fitnesses are multiplicative across the two gene
copies, `w i j = v i * v j`, then one generation of diploid viability
selection under random mating is exactly one generation of haploid
selection with fitnesses `v`, and the diploid mean fitness is the square
of the haploid mean fitness. The two algebraic core identities are stated
in unfolded form first, then folded onto the `Selection` definitions.
-/

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Biology.PopulationGenetics.Classical

/-- Algebraic core of the ploidy bridge: with multiplicative genotype
fitnesses `w i j = v i * v j`, the diploid mean fitness is the square of the
haploid mean fitness of `v`. -/
theorem sum_sum_mul_mul_eq_sq {ι : Type*} [Fintype ι] (p v : ι → ℝ) :
    (∑ i, ∑ j, p i * p j * (v i * v j)) = (∑ i, p i * v i) ^ 2 := by
  have h : ∀ i j, p i * p j * (v i * v j) = (p i * v i) * (p j * v j) :=
    fun i j => by ac_rfl
  simp_rw [h, ← Fintype.sum_mul_sum, pow_two]

/-- Algebraic core of the ploidy bridge: with multiplicative genotype
fitnesses `w i j = v i * v j`, one generation of diploid viability
selection (symmetric marginal fitness `∑ j, (v i * v j) * p j`) equals one
generation of haploid selection with fitnesses `v`, whenever the haploid
mean fitness `∑ i, p i * v i` is nonzero. -/
theorem diploid_eq_haploid_of_mul {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hw : (∑ i, p i * v i) ≠ 0) (i : ι) :
    p i * (∑ j, (v i * v j) * p j) / (∑ i, ∑ j, p i * p j * (v i * v j)) =
      p i * v i / (∑ i, p i * v i) := by
  have hsum : (∑ j, (v i * v j) * p j) = v i * (∑ j, p j * v j) := by
    have h : ∀ j, (v i * v j) * p j = v i * (p j * v j) := fun j => by ac_rfl
    simp_rw [h, ← Finset.mul_sum]
  rw [hsum, sum_sum_mul_mul_eq_sq p v]
  have hS2 : (∑ i, p i * v i) ^ 2 ≠ 0 := pow_ne_zero 2 hw
  rw [div_eq_div_iff hS2 hw, pow_two]
  ac_rfl

end MathlibExt.Biology.PopulationGenetics.Classical

namespace MathlibExt.Biology.PopulationGenetics.Selection

open MathlibExt.Biology.PopulationGenetics.Classical

/-- With multiplicative genotype fitnesses `w i j = v i * v j`, the diploid
mean fitness is the square of the haploid mean fitness of `v`. -/
theorem diploidMeanFitness_eq_sq_of_mul {ι : Type*} [Fintype ι] (p v : ι → ℝ) :
    diploidMeanFitness p (fun i j => v i * v j) = (meanFitness p v) ^ 2 :=
  sum_sum_mul_mul_eq_sq p v

/-- **Ploidy bridge.** With multiplicative genotype fitnesses
`w i j = v i * v j` and nonzero haploid mean fitness, diploid viability
selection on `w` equals haploid selection on `v`. -/
theorem diploidSelect_eq_select_of_mul {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hw : meanFitness p v ≠ 0) (i : ι) :
    diploidSelect p (fun i j => v i * v j) i = select p v i := by
  rw [diploidSelect, select, marginalFitness_of_symm (fun a b => mul_comm (v a) (v b)),
    diploidMeanFitness]
  exact diploid_eq_haploid_of_mul p v hw i

end MathlibExt.Biology.PopulationGenetics.Selection
