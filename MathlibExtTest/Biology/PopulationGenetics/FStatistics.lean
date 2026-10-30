/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatistics

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
open scoped ENNReal symmDiff

namespace MathlibExtTest.Biology.PopulationGenetics.FStatistics

/-! ### Model-free identities on a Dirac measure -/

section Dirac

/-- Three populations with frequencies `0.2`, `0.5`, `0.9` at a single fixed outcome. -/
noncomputable def pDirac : Fin 3 → Unit → ℝ := fun X _ => ![1/5, 1/2, 9/10] X

/-- Under a Dirac measure, `f2` is the squared frequency difference. -/
example : f2 (Measure.dirac ()) pDirac 0 2 = 49 / 100 := by
  simp [f2, pDirac]
  norm_num

/-- Under a Dirac measure, `f3` is the product of the two differences. -/
example : f3 (Measure.dirac ()) pDirac 1 0 2 = -3 / 25 := by
  simp [f3, pDirac]
  norm_num

/-- `f3_eq_f2` on a Dirac measure. -/
example : f3 (Measure.dirac ()) pDirac 1 0 2 =
    (f2 (Measure.dirac ()) pDirac 1 0 + f2 (Measure.dirac ()) pDirac 1 2 -
      f2 (Measure.dirac ()) pDirac 0 2) / 2 :=
  f3_eq_f2 (fun _ => MemLp.of_discrete) 1 0 2

/-- `f4_eq_f2` on a Dirac measure, and its direct evaluation. -/
example : f4 (Measure.dirac ()) pDirac 0 1 2 0 =
    (f2 (Measure.dirac ()) pDirac 0 0 + f2 (Measure.dirac ()) pDirac 1 2 -
      f2 (Measure.dirac ()) pDirac 0 2 - f2 (Measure.dirac ()) pDirac 1 0) / 2 :=
  f4_eq_f2 (fun _ => MemLp.of_discrete) 0 1 2 0

example : f4 (Measure.dirac ()) pDirac 0 1 2 0 = -21 / 100 := by
  simp [f4, pDirac]
  norm_num

/-- Boundary cases: `f2 X X = 0`, and the symmetries hold for arbitrary measures. -/
example : f2 (Measure.dirac ()) pDirac 2 2 = 0 := f2_self 2

example {Ω P : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : P → Ω → ℝ) (A B C D : P) :
    f4 μ p A B C D = f4 μ p C D A B ∧ f4 μ p A B C D = -f4 μ p B A C D ∧
      f2 μ p A B = f2 μ p B A ∧ 0 ≤ f2 μ p A B ∧ f2 μ p A B = f4 μ p A B A B ∧
      f3 μ p C A B = f4 μ p C A C B :=
  ⟨f4_comm_pairs A B C D, f4_swap_left A B C D, f2_comm A B, f2_nonneg A B, f2_eq_f4 A B,
    f3_eq_f4 C A B⟩

end Dirac

/-! ### A non-vacuous drift model

`Ω = Fin 4` with the uniform probability measure, two edges with orthogonal increments
`±1/4` (drift length `1/16` each), root frequency `1/2`. Population `0` (`A`) sits on edge `0`,
population `1` (`B`) on edge `1`, population `2` (`C`) is a `1/2 : 1/2` mixture of `A` and `B`,
and population `3` is the root itself. All frequencies lie in `[1/4, 3/4]`. -/

section Witness

/-- The uniform probability measure on `Fin 4`. -/
noncomputable def μ4 : Measure (Fin 4) := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ4 :=
  ⟨by simpa [μ4] using ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

/-- Integration against `μ4` is averaging over the four outcomes. -/
theorem integral_μ4 (f : Fin 4 → ℝ) : ∫ ω, f ω ∂μ4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  simp only [μ4, integral_smul_measure, integral_count, Fin.sum_univ_four]
  norm_num
  ring

/-- The drift increments: orthogonal, each with second moment `1/16`. -/
noncomputable def incr4 : Fin 2 → Fin 4 → ℝ :=
  ![![1/4, 1/4, -1/4, -1/4], ![1/4, -1/4, 1/4, -1/4]]

/-- The witness drift model. -/
noncomputable def M : DriftModel μ4 (Fin 2) (Fin 4) where
  root := fun _ => 1/2
  incr := incr4
  len := fun _ => 1/16
  weight := ![![1, 0], ![0, 1], ![1/2, 1/2], ![0, 0]]
  memLp_root := MemLp.of_discrete
  memLp_incr := fun _ => MemLp.of_discrete
  inner_incr := by
    intro e f h
    fin_cases e <;> fin_cases f <;> simp_all [integral_μ4, incr4] <;> norm_num
  sq_incr := by
    intro e
    fin_cases e <;> simp [integral_μ4, incr4] <;> norm_num

/-- Both edges have positive drift length. -/
example : ∀ e, 0 < M.len e := fun _ => by norm_num [M]

/-- `f2 A B = 1/8`, the sum of the two edge lengths (computed from `f2_freq`). -/
theorem f2_AB : f2 μ4 M.freq 0 1 = 1 / 8 := by
  rw [M.f2_freq]
  simp [M, Fin.sum_univ_two]
  norm_num

/-- `C` is a `1/2 : 1/2` mixture of `A` and `B`. -/
theorem weight_C : M.weight 2 = (1/2 : ℝ) • M.weight 0 + (1 - 1/2 : ℝ) • M.weight 1 := by
  ext e
  fin_cases e <;> simp [M]
  norm_num

/-- The admixed population has `f3 C A B = -(1/4) * (1/8) = -1/32 < 0` by `f3_admixture`. -/
example : f3 μ4 M.freq 2 0 1 = -1 / 32 := by
  rw [M.f3_admixture weight_C, f2_AB]
  norm_num

/-- The same value by direct computation of the integral. -/
example : f3 μ4 M.freq 2 0 1 = -1 / 32 := by
  simp [f3, integral_μ4, DriftModel.freq, M, incr4, Fin.sum_univ_two]
  norm_num

/-- The three-population test fires: `f3 C A B < 0`, so the model is not a tree. -/
example : f3 μ4 M.freq 2 0 1 < 0 :=
  M.f3_neg_of_admixture (by norm_num) (by norm_num) (by rw [f2_AB]; norm_num) weight_C

example : ¬ M.IsUnadmixed :=
  M.not_isUnadmixed_of_f3_neg
    (M.f3_neg_of_admixture (by norm_num) (by norm_num) (by rw [f2_AB]; norm_num) weight_C)

/-- f4-ratio with `A = 1`, outgroup `O = 3` (the root), admixed `X = 2` mixing `Y = 0` and
`C = 1`, and sampled sister `B = Y = 0`: the ratio recovers `α = 1/2`. -/
example : f4 μ4 M.freq 1 3 2 1 / f4 μ4 M.freq 1 3 0 1 = 1 / 2 := by
  have h : M.weight 2 = (1/2 : ℝ) • M.weight 0 + (1 - 1/2 : ℝ) • M.weight 1 := weight_C
  refine M.f4_ratio h rfl ?_
  rw [M.f4_freq]
  simp [M, Fin.sum_univ_two]

end Witness

/-! ### A tree (unadmixed) model -/

section Tree

/-- A tree on the same space: populations `0` and `1` share edge `0`, population `1` also
has the private edge `1`, population `2` is the root. -/
noncomputable def T : DriftModel μ4 (Fin 2) (Fin 3) :=
  { M with weight := ![![1, 0], ![1, 1], ![0, 0]] }

/-- `T` is unadmixed. -/
theorem T_isUnadmixed : T.IsUnadmixed := by
  intro X e
  fin_cases X <;> fin_cases e <;> simp [T]

/-- On a tree `f3 ≥ 0`. -/
example : 0 ≤ f3 μ4 T.freq 0 1 2 := T.f3_nonneg_of_isUnadmixed T_isUnadmixed 0 1 2

/-- On a tree `f2` is the tree distance: populations `0` and `1` differ by edge `1` only. -/
example : f2 μ4 T.freq 0 1 = 1 / 16 := by
  rw [T.f2_eq_sum_symmDiff T_isUnadmixed]
  have h0 : T.lineage 0 = {0} := by
    ext e; fin_cases e <;> simp [DriftModel.lineage, T]
  have h1 : T.lineage 1 = Finset.univ := by
    ext e; fin_cases e <;> simp [DriftModel.lineage, T]
  have h2 : ({0} : Finset (Fin 2)) ∆ Finset.univ = {1} := by decide
  rw [h0, h1, h2]
  simp [T, M]

/-- A vanishing `f4` on disjoint paths: `f4 0 2 1 0` pairs path `0–2` (edge `0`) with path
`1–0` (edge `1`). -/
example : f4 μ4 T.freq 0 2 1 0 = 0 :=
  T.f4_eq_zero_of_disjoint fun e => by fin_cases e <;> simp [T]

end Tree

/-! ### Wahlund effect -/

section Wahlund

/-- Two equal-size subpopulations fixed for different alleles: `H_S = 0`, `H_T = 1/2`. -/
example : hetSub ![1/2, 1/2] ![0, 1] = 0 ∧ hetTotal ![1/2, 1/2] ![0, 1] = 1 / 2 := by
  constructor <;> simp [hetSub, hetTotal, meanFreq, Fin.sum_univ_two]
  norm_num

example : hetTotal ![1/2, 1/2] ![0, 1] - hetSub ![1/2, 1/2] ![0, 1] =
    2 * ∑ i, ![1/2, 1/2] i * (![0, 1] i - meanFreq ![1/2, 1/2] ![0, 1]) ^ 2 :=
  wahlund _ _ (by simp [Fin.sum_univ_two]; norm_num)

/-- Boundary case: identical subpopulations show no Wahlund effect. -/
example (q : ℝ) : hetSub ![1/3, 2/3] ![q, q] = hetTotal ![1/3, 2/3] ![q, q] := by
  simp [hetSub, hetTotal, meanFreq, Fin.sum_univ_two]
  ring

end Wahlund

end MathlibExtTest.Biology.PopulationGenetics.FStatistics
