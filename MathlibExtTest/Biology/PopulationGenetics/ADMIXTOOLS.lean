/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.ADMIXTOOLS

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.ADMIXTOOLS
open scoped unitInterval

namespace MathlibExtTest.Biology.PopulationGenetics.ADMIXTOOLS

/-! ### Site patterns -/

/-- `ABBA` (P1 and O ancestral, P2 and P3 derived) is an `ABBA` site. -/
example : abba ![false, true, true, false] = 1 := by simp [abba]

/-- The unpolarized `ABBA` class also contains `BAAB`. -/
example : abba ![true, false, false, true] = 1 := by simp [abba]

/-- `BABA` is not an `ABBA` site, and it is a `BABA` site. -/
example : abba ![true, false, true, false] = 0 ∧ baba ![true, false, true, false] = 1 := by
  simp [abba, baba]

/-- The unpolarized `BABA` class also contains `ABAB`, which is not a polarized `BABA` site. -/
example : baba ![false, true, false, true] = 1 ∧ babaPol ![false, true, false, true] = 0 := by
  simp [baba, babaPol]

/-- A monomorphic configuration is neither pattern. -/
example : abba ![true, true, true, true] = 0 ∧ baba ![true, true, true, true] = 0 := by
  simp [abba, baba]

/-- The configuration probabilities at concrete frequencies sum to `1`. -/
example : ∑ x, configProb ![1 / 2, 1 / 4, 1, 0] x = 1 := sum_configProb _

/-- `E[BABA - ABBA]` at frequencies `(1/2, 1/4, 1, 0)` is `(1/2 - 1/4) (1 - 0) = 1/4`. -/
example : sampleExpect (fun x => baba x - abba x) ![1 / 2, 1 / 4, 1, 0] = 1 / 4 := by
  rw [sampleExpect_baba_sub_abba]
  norm_num

/-- When the outgroup is fixed for the ancestral allele, the polarized and unpolarized
expectations agree. -/
example (q : Fin 4 → ℝ) (h : q 3 = 0) :
    sampleExpect (fun x => babaPol x - abbaPol x) q =
      sampleExpect (fun x => baba x - abba x) q := by
  rw [sampleExpect_babaPol_sub_abbaPol, sampleExpect_baba_sub_abba, h]
  ring

/-- When the outgroup is polymorphic the polarized expectation differs from the unpolarized
one (here `1/16` versus `0`). -/
example : sampleExpect (fun x => babaPol x - abbaPol x) ![1 / 2, 1 / 4, 1 / 2, 1 / 2] = 1 / 16 ∧
    sampleExpect (fun x => baba x - abba x) ![1 / 2, 1 / 4, 1 / 2, 1 / 2] = 0 := by
  rw [sampleExpect_babaPol_sub_abbaPol, sampleExpect_baba_sub_abba]
  norm_num

/-- With all four frequencies equal there is no excess of either pattern. -/
example (t : ℝ) : sampleExpect (fun x => baba x - abba x) ![t, t, t, t] = 0 := by
  rw [sampleExpect_baba_sub_abba]
  simp

/-! ### `E[BABA - ABBA] = f4` on a Dirac measure -/

/-- Five populations with frequencies `0.2`, `0.5`, `0.9`, `0.1`, `0.9` at a single fixed
outcome. -/
noncomputable def pDirac : Fin 5 → Unit → ℝ := fun X _ => ![1/5, 1/2, 9/10, 1/10, 9/10] X

/-- The ABBA–BABA identity on a Dirac measure: both sides are `(0.2 - 0.5) (0.9 - 0.1)`. -/
example : ∫ ω, sampleExpect (fun x => baba x - abba x)
      ![pDirac 0 ω, pDirac 1 ω, pDirac 2 ω, pDirac 3 ω] ∂(Measure.dirac ()) =
    f4 (Measure.dirac ()) pDirac 0 1 2 3 :=
  integral_sampleExpect_baba_sub_abba 0 1 2 3

/-- Every frequency is square integrable under a Dirac measure. -/
theorem memLp_pDirac (X : Fin 5) : MemLp (pDirac X) 2 (Measure.dirac ()) := MemLp.of_discrete

/-- qpAdm with a negative weight: population `4` (frequency `0.9`) is the affine combination
`2 · 0.5 - 1 · 0.1` of populations `1` and `3`, so its `f4` is the same combination. -/
example : f4 (Measure.dirac ()) pDirac 4 0 2 3 =
    2 * f4 (Measure.dirac ()) pDirac 1 0 2 3 + (-1) * f4 (Measure.dirac ()) pDirac 3 0 2 3 := by
  have h := f4_affine_combination (μ := Measure.dirac ()) (p := pDirac) memLp_pDirac
    (T := 4) (X := 0) (Y := 2) (Z := 3) ![1, 3] ![2, -1] (by norm_num [Fin.sum_univ_two])
    (fun ω => by simp [pDirac, Fin.sum_univ_two]; norm_num)
  simpa [Fin.sum_univ_two] using h

/-! ### The D-statistic on a tree: the hypotheses are satisfiable -/

/-- A one-edge drift model on a Dirac measure: `P1` and `P2` (populations `0`, `1`) share an
edge with increment `1/4` below the root (frequency `1/2`); `P3` and `O` (populations `2`, `3`)
sit at the root. The paths `P1–P2` and `P3–O` share no edge. -/
noncomputable def treeModel : DriftModel (Measure.dirac ()) Unit (Fin 4) where
  root := fun _ => 1 / 2
  incr := fun _ _ => 1 / 4
  len := fun _ => 1 / 16
  weight := ![fun _ => 1, fun _ => 1, fun _ => 0, fun _ => 0]
  memLp_root := MemLp.of_discrete
  memLp_incr := fun _ => MemLp.of_discrete
  inner_incr := fun e f h => absurd (Subsingleton.elim e f) h
  sq_incr := fun _ => by norm_num

/-- On the tree model the expected numbers of `ABBA` and `BABA` sites agree. -/
example : ∫ ω, sampleExpect abba ![treeModel.freq 0 ω, treeModel.freq 1 ω, treeModel.freq 2 ω,
      treeModel.freq 3 ω] ∂(Measure.dirac ()) =
    ∫ ω, sampleExpect baba ![treeModel.freq 0 ω, treeModel.freq 1 ω, treeModel.freq 2 ω,
      treeModel.freq 3 ω] ∂(Measure.dirac ()) :=
  treeModel.integral_sampleExpect_abba_eq_baba (fun e => by simp [treeModel])
    Integrable.of_finite Integrable.of_finite

/-! ### `sampleExpect` is an expectation -/

/-- Deterministic indicators (a Dirac measure) are independent; with `X = (true, false)` the
expectation of `g` is `g (true, false)`, matching `sampleExpect g ![1, 0]`. -/
example (g : (Fin 2 → Bool) → ℝ) :
    ∫ ω, g (fun i => (![fun _ => true, fun _ => false] : Fin 2 → Unit → Bool) i ω)
      ∂(Measure.dirac ()) = sampleExpect g ![1, 0] :=
  integral_eq_sampleExpect (fun _ => Measurable.of_discrete) (by
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets _
    simp only [Measure.dirac_apply', MeasurableSet.of_discrete,
      Set.indicator, Set.mem_iInter, Set.mem_preimage, Pi.one_apply]
    split_ifs with h <;> simp_all [Finset.prod_ite_zero])
    (fun i => by fin_cases i <;> simp [Measure.real]) g

/-! ### Estimators -/

/-- `hetHat` with `1` derived copy among `2`: `1 · 1 / (2 · 1) = 1/2`. -/
example : hetHat 2 1 = 1 / 2 := by norm_num [hetHat]

/-- Domain edge: for `m = 1` the denominator `m (m - 1)` vanishes and Lean returns the junk
value `0`; `integral_hetHat` therefore assumes `m ≥ 2`. -/
example : hetHat 1 1 = 0 := by norm_num [hetHat]

/-- A sample fixed for one allele has `hetHat = 0`. -/
example (m : ℕ) : hetHat m m = 0 := by simp [hetHat]

/-- `f2Hat` with `x_A = 2` of `4` and `x_B = 0` of `2`: `(1/2)² - (2·2/(4·3))/4 - 0 = 1/6`. -/
example : f2Hat 4 2 2 0 = 1 / 6 := by norm_num [f2Hat, hetHat]

/-- `f2Hat` can be negative (an unbiased estimator of a nonnegative quantity need not be
nonnegative): identical samples `1` of `2` give `-1/2`. -/
example : f2Hat 2 2 1 1 = -1 / 2 := by norm_num [f2Hat, hetHat]

/-- `f3Hat` and `f4Hat` at concrete counts. -/
example : f3Hat 2 1 1 1 0 1 = -1 / 2 ∧ f4Hat 1 1 1 1 1 0 1 0 = 1 := by
  norm_num [f3Hat, f4Hat, hetHat]

/-- Hudson's denominator with sample frequencies `1/2` and `1`: `1/2 · 0 + 1 · 1/2 = 1/2`. -/
example : hudsonDenHat 2 1 1 1 = 1 / 2 := by norm_num [hudsonDenHat]

/-- Hudson's `F_ST` of two sites with frequencies `(1, 0)` and `(1/2, 1/2)`:
`(1 + 0) / (1 + 1/2) = 2/3`. -/
example : hudsonFst Finset.univ ![1, 1 / 2] ![0, 1 / 2] = 2 / 3 := by
  norm_num [hudsonFst, hudsonDen, Fin.sum_univ_two]

/-- Fixed differences at every site give the maximal value `F_ST = 1`. -/
example : hudsonFst Finset.univ ![1, 0] ![0, 1] = 1 := by
  norm_num [hudsonFst, hudsonDen, Fin.sum_univ_two]

/-- Domain edge: if both populations are fixed for the same allele at every site the
denominator vanishes and Lean's totalized division returns `0`; `hudsonFst_mem_Icc` includes this
case without a positive-denominator hypothesis. -/
example : hudsonFst Finset.univ ![1, 1] ![1, 1] = 0 := by
  norm_num [hudsonFst, hudsonDen, Fin.sum_univ_two]

/-- The bounds `0 ≤ F_ST ≤ 1` at concrete frequencies. -/
example : hudsonFst Finset.univ ![1, 1 / 2] ![0, 1 / 2] ∈ Set.Icc (0 : ℝ) 1 :=
  hudsonFst_mem_Icc _ _ _ (by intro i _; fin_cases i <;> norm_num)
    (by intro i _; fin_cases i <;> norm_num)

/-! ### The binomial-sampling hypotheses are satisfiable -/

/-- The identity has law `Bin(ℝ, 2, 1/2)` under that law, so `integral_hetHat` applies:
`E[X (2 - X) / 2] = 1/4`. -/
example : (Bin(ℝ, 2, ⟨1 / 2, by norm_num, by norm_num⟩))[fun x => hetHat 2 (id x)] = 1 / 4 := by
  rw [integral_hetHat HasLaw.id le_rfl]
  norm_num

/-- Two independent binomial samples: the coordinates of the product of two binomial laws.
Witness that the hypotheses of `integral_f2Hat` hold together. -/
example (mA mB : ℕ) (qA qB : I) :
    HasLaw Prod.fst Bin(ℝ, mA, qA) (Bin(ℝ, mA, qA).prod Bin(ℝ, mB, qB)) ∧
    HasLaw Prod.snd Bin(ℝ, mB, qB) (Bin(ℝ, mA, qA).prod Bin(ℝ, mB, qB)) ∧
    IndepFun Prod.fst Prod.snd (Bin(ℝ, mA, qA).prod Bin(ℝ, mB, qB)) := by
  refine ⟨⟨measurable_fst.aemeasurable, by simp⟩, ⟨measurable_snd.aemeasurable, by simp⟩, ?_⟩
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable]
  simp

end MathlibExtTest.Biology.PopulationGenetics.ADMIXTOOLS
