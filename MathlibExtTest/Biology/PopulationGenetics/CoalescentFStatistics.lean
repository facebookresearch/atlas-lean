/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.CoalescentFStatistics

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
open MathlibExt.Biology.PopulationGenetics.CoalescentFStatistics

namespace MathlibExtTest.Biology.PopulationGenetics.CoalescentFStatistics

/-! ### Heterozygosities -/

/-- Boundary cases: identical fixed populations never differ; populations fixed for different
alleles always differ. -/
example : hetPair 0 0 = 0 ∧ hetPair 1 1 = 0 ∧ hetPair 0 1 = 1 := by
  norm_num [hetPair]

/-- Within-population heterozygosity `2 a (1 - a)`. -/
example (a : ℝ) : hetPair a a = 2 * a * (1 - a) := by
  unfold hetPair
  ring

/-! ### A non-vacuous coalescent model

Three populations with frequencies `1/5`, `1/2`, `9/10` at a single outcome, `θ = 2`, and
expected coalescence times `hetPair / 2`. -/

/-- Frequencies of the witness populations. -/
noncomputable def pW : Fin 3 → Unit → ℝ := fun X _ => ![1/5, 1/2, 9/10] X

/-- The witness model. -/
noncomputable def W : CoalescentModel (Measure.dirac ()) (Fin 3) where
  freq := pW
  theta := 2
  coalTime X Y := hetPair (pW X ()) (pW Y ()) / 2
  memLp_freq _ := MemLp.of_discrete
  meanHet_eq X Y := by
    simp [meanHet]
    ring

/-- Peter's form of `f2` on the witness: `(1/5 - 1/2) ^ 2 = 9/100`. -/
example : f2 (Measure.dirac ()) pW 0 1 = 9 / 100 := by
  rw [show pW = W.freq from rfl, W.f2_eq]
  simp [W, pW, hetPair]
  norm_num

example : f2 (Measure.dirac ()) pW 0 1 = 9 / 100 := by
  simp [f2, pW]
  norm_num

/-- `f3` from coalescence times agrees with the direct value
`(1/2 - 1/5) (1/2 - 9/10) = -3/25`. -/
example : f3 (Measure.dirac ()) W.freq 1 0 2 = -3 / 25 := by
  rw [W.f3_eq]
  simp [W, pW, hetPair]
  norm_num

example : f3 (Measure.dirac ()) W.freq 1 0 2 = -3 / 25 := by
  simp [f3, W, pW]
  norm_num

/-- `f4` from coalescence times agrees with the direct value
`(1/5 - 1/2) (9/10 - 1/5) = -21/100`. -/
example : f4 (Measure.dirac ()) W.freq 0 1 2 0 = -21 / 100 := by
  rw [W.f4_eq]
  simp [W, pW, hetPair]
  norm_num

/-! ### McVean's identity -/

/-- Three haplotypes at two loci: `(0, 1)`, `(1, 1)`, `(1, 0)`. -/
def Z3 : Fin 3 → Fin 2 → ℝ := ![![0, 1], ![1, 1], ![1, 0]]

/-- Pairwise differences: samples `0` and `2` differ at both loci. -/
example : pairDiff Z3 0 2 = 2 := by
  simp [pairDiff, Z3, Fin.sum_univ_two]
  norm_num

/-- The covariance of samples `0` and `2` computed directly: column means `2/3`, `2/3`;
centred rows `(-2/3, 1/3)`, `(1/3, -2/3)`; `C = (-2/9 - 2/9) / 2 = -2/9`. -/
theorem genCov_Z3 : genCov Z3 0 2 = -2 / 9 := by
  simp [genCov, centered, colMean, Z3, Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num

/-- The same value from the double-centred pairwise differences. -/
example : doubleCenter (pairDiff Z3) 0 2 / (2 * Fintype.card (Fin 2)) = -2 / 9 := by
  rw [← genCov_eq_doubleCenter, genCov_Z3]

/-- A non-vacuous McVean model: fixed genotypes `Z3`, `θ = 1`, coalescence times equal to the
pairwise differences. -/
noncomputable def MV : McVeanModel (Measure.dirac ()) (Fin 3) (Fin 2) where
  geno i s _ := Z3 i s
  theta := 1
  coalTime := pairDiff Z3
  memLp_geno _ _ := MemLp.of_discrete
  integral_pairDiff i j := by simp

/-- McVean's identity on the witness. -/
example : ∫ ω, genCov (fun k s => MV.geno k s ω) 0 2 ∂(Measure.dirac ()) =
    1 / (2 * 2) * doubleCenter (pairDiff Z3) 0 2 := by
  rw [MV.integral_genCov]
  simp [MV]

end MathlibExtTest.Biology.PopulationGenetics.CoalescentFStatistics
