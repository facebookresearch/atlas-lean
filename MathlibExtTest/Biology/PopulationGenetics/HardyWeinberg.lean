/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.HardyWeinberg

@[expose] public section

open MathlibExt.Biology.PopulationGenetics.HardyWeinberg
open scoped ENNReal

namespace MathlibExtTest.Biology.PopulationGenetics.HardyWeinberg

/-! ### Mendelian transmission -/

/-- A homozygote transmits its allele with probability `1`. -/
example : transmit (true, true) true = 1 := by
  rw [transmit_apply]
  simp [ENNReal.inv_two_add_inv_two]

/-- A heterozygote transmits each allele with probability `1/2`. -/
example : transmit (true, false) false = 2⁻¹ := by
  simp [transmit_apply]

/-! ### A population of heterozygotes (non-vacuity witness)

Every parent is the ordered heterozygote `(A, a)`. The parental genotype law is far from
Hardy–Weinberg proportions (no homozygotes although `p = 1/2`), so the deviation is `-1/4`;
one generation of random mating restores the proportions `1/4, 1/2, 1/4`. -/

/-- The all-heterozygote parental genotype law. -/
noncomputable def allHet : PMF (Bool × Bool) := PMF.pure (true, false)

/-- Its allele frequencies are `p = q = 1/2`. -/
theorem gamete_allHet (b : Bool) : gamete allHet b = 2⁻¹ := by
  rw [gamete_apply]
  cases b <;> simp [allHet, PMF.pure_apply]

/-- The parents deviate from Hardy–Weinberg proportions: `D = 0 - (1/2)² = -1/4`. -/
example : hwDeviation allHet = -1 / 4 := by
  rw [hwDeviation, gamete_allHet]
  norm_num [allHet, PMF.pure_apply]

/-- After one generation: `P(AA) = 1/4`. -/
example : (offspring allHet (true, true)).toReal = 1 / 4 := by
  rw [offspring_true_true, gamete_allHet]
  norm_num

/-- After one generation: `P(Aa) = 1/2` for the unordered heterozygote. -/
example : (offspring allHet (true, false)).toReal + (offspring allHet (false, true)).toReal =
    1 / 2 := by
  rw [offspring_heterozygote, gamete_allHet, gamete_allHet]
  norm_num

/-- After one generation the deviation vanishes, and the frequencies are unchanged. -/
example : hwDeviation (offspring allHet) = 0 ∧ gamete (offspring allHet) = gamete allHet :=
  ⟨hwDeviation_offspring _, gamete_offspring _⟩

/-! ### General statements on an arbitrary finite allele type -/

example {A : Type*} (G : PMF (A × A)) (a b : A) :
    offspring G (a, b) = gamete G a * gamete G b ∧
      offspring (offspring G) = offspring G :=
  ⟨offspring_apply G a b, offspring_offspring G⟩

example (G : PMF (Bool × Bool)) :
    (gamete G true).toReal + (gamete G false).toReal = 1 ∧
      (offspring G (false, false)).toReal = (gamete G false).toReal ^ 2 :=
  ⟨freq_true_add_freq_false G, offspring_false_false G⟩

/-- A fixed (monomorphic) population stays fixed: boundary case `p = 1`. -/
example : offspring (PMF.pure (true, true)) (true, true) = 1 := by
  rw [offspring_apply, gamete_apply]
  simp [PMF.pure_apply, ENNReal.inv_two_add_inv_two]

#print axioms gamete_offspring
#print axioms offspring_offspring
#print axioms hwDeviation_offspring

end MathlibExtTest.Biology.PopulationGenetics.HardyWeinberg
