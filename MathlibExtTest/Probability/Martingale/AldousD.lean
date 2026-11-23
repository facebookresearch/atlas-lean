/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.AldousD
public import MathlibExtTest.Probability.Martingale.MartingaleTightness

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
open MathlibExt.Probability.Martingale
open MathlibExtTest.Probability.Martingale.MartingaleTightness

namespace MathlibExtTest.Probability.Martingale.AldousD

noncomputable section

/-! ### A deterministic array with jumps of size `1/n` -/

/-- Row `n` has `n` increments `1/n`; its step process is `t ↦ ⌊n t⌋ / n`. -/
def meshArray : ℕ → ℕ → Unit → ℝ := fun n _ _ => 1 / n

def half : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

def threeEighths : Set.Icc (0 : ℝ) 1 := ⟨3 / 8, by norm_num, by norm_num⟩

def endTime : Set.Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩

-- The step paths are genuinely discontinuous (so tightness in `D` is not tightness in `C` in
-- disguise): row `1` is `0` at `t = 1/2` and jumps to `1` at `t = 1`.
example : arrayStepProcess 1 meshArray () half = 0 := by
  rw [arrayStepProcess_apply]
  simp only [half, Nat.cast_one, one_mul]
  rw [Nat.floor_eq_zero.2 (by norm_num : (1 / 2 : ℝ) < 1)]
  simp

example : arrayStepProcess 1 meshArray () endTime = 1 := by
  rw [arrayStepProcess_apply]
  simp [endTime, meshArray]

-- At a grid time (`t = 1/2`, row `4`) the step path agrees with the polygon, ...
example : arrayStepProcess 4 meshArray () half = 1 / 2 := by
  rw [arrayStepProcess_apply]
  simp only [half, show ((4 : ℕ) : ℝ) * (1 / 2) = (2 : ℕ) by norm_num, Nat.floor_natCast]
  norm_num [meshArray]

example : arrayPolygon 4 meshArray () half = 1 / 2 := by
  rw [arrayPolygon_apply]
  simp only [half, show ((4 : ℕ) : ℝ) * (1 / 2) = (2 : ℕ) by norm_num, Nat.floor_natCast]
  norm_num [meshArray]

-- ... while off the grid (`t = 3/8`) the step path lags the polygon by half a jump.
example : arrayStepProcess 4 meshArray () threeEighths = 1 / 4 := by
  rw [arrayStepProcess_apply]
  simp only [threeEighths, show ((4 : ℕ) : ℝ) * (3 / 8) = 3 / 2 by norm_num]
  rw [show ⌊(3 / 2 : ℝ)⌋₊ = 1 from Nat.floor_eq_iff (by norm_num) |>.2 ⟨by norm_num, by norm_num⟩]
  norm_num [meshArray]

example : arrayPolygon 4 meshArray () threeEighths = 3 / 8 := by
  rw [arrayPolygon_apply]
  simp only [threeEighths, show ((4 : ℕ) : ℝ) * (3 / 8) = 3 / 2 by norm_num]
  rw [show ⌊(3 / 2 : ℝ)⌋₊ = 1 from Nat.floor_eq_iff (by norm_num) |>.2 ⟨by norm_num, by norm_num⟩]
  norm_num [meshArray]

/-- The jumps `1/n` of `meshArray` are eventually below every `ε > 0` (checked directly). -/
lemma meshArray_hjump (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (Measure.dirac ()) {ω : Unit | ∃ i < n, ε < |meshArray n i ω|}) atTop
      (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop ⌈1 / ε⌉₊] with n hn
  have hnε : 1 / ε < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) < n := lt_trans (by positivity) hnε
  have hlt : 1 / (n : ℝ) < ε := by
    rw [div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hε] at hnε
    linarith
  have : {ω : Unit | ∃ i < n, ε < |meshArray n i ω|} = ∅ := by
    ext ω
    simp only [meshArray, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists,
      not_and, not_lt]
    intro _ _
    rw [abs_of_pos (by positivity)]
    exact hlt.le
  rw [this, measure_empty]

/-- `meshArray` satisfies Aldous's condition (checked directly from the definition): over a
window of `⌊n θ⌋` grid steps its partial sums move by at most `θ`. -/
lemma meshArray_aldous : AldousCondition topFiltration meshArray (Measure.dirac ()) := by
  intro ε hε η _
  refine ⟨ε / 2, by positivity, 1, fun n hn σ ρ _ _ hσρ => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ ω, |∑ i ∈ Finset.range (ρ ω), meshArray n i ω -
      ∑ i ∈ Finset.range (σ ω), meshArray n i ω| ≤ ε / 2 := by
    intro ω
    obtain ⟨h1, h2, -⟩ := hσρ ω
    have hfl : (⌊(n : ℝ) * (ε / 2)⌋₊ : ℝ) ≤ n * (ε / 2) := Nat.floor_le (by positivity)
    have h1' : (σ ω : ℝ) ≤ ρ ω := by exact_mod_cast h1
    have h2' : (ρ ω : ℝ) ≤ σ ω + ⌊(n : ℝ) * (ε / 2)⌋₊ := by exact_mod_cast h2
    simp only [meshArray, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← sub_mul, mul_one_div, abs_div, abs_of_pos hnR, div_le_iff₀ hnR, abs_le]
    have : 0 ≤ ε / 2 * n := by positivity
    constructor <;> nlinarith
  have : {ω : Unit | ε ≤ |∑ i ∈ Finset.range (ρ ω), meshArray n i ω -
      ∑ i ∈ Finset.range (σ ω), meshArray n i ω|} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact (key ω).trans_lt (half_lt_self hε)
  rw [this, measure_empty]
  exact zero_le

-- **Aldous's criterion in `D`**, all hypotheses discharged, for an array with nonzero jumps.
example : IsTightMeasureSet (Set.range fun n =>
    (Measure.dirac ()).map (arrayStepProcess n meshArray)) :=
  isTightMeasureSet_arrayStepProcess_of_aldousCondition (𝓕 := topFiltration)
    (fun _ _ => measurable_const) meshArray_hjump meshArray_aldous

/-! ### The Rademacher martingale array (fixture from the `MartingaleTightness` tests) -/

-- Tightness of the Rademacher step processes in `D([0,1])` from the martingale hypotheses
-- alone (no finite-dimensional input).
theorem isTightMeasureSet_radArray :
    IsTightMeasureSet (Set.range fun n => coinSeq.map (arrayStepProcess n radArray)) :=
  isTightMeasureSet_arrayStepProcess_of_martingaleDifference radArray_stronglyMeasurable
    radArray_condExp radArray_memLp radArray_hQV radArray_lindeberg

-- The transfer route: the polygons' `C`-tightness gives the same `D`-tightness.
example : IsTightMeasureSet (Set.range fun n => coinSeq.map (arrayStepProcess n radArray)) :=
  isTightMeasureSet_arrayStepProcess_of_isTightMeasureSet_arrayPolygon
    (fun n i => ((radArray_stronglyMeasurable n i).mono ((coinFiltration n).le _)).measurable)
    (isTightMeasureSet_arrayPolygon_of_aldousCondition
      (fun n i => (radArray_stronglyMeasurable n i).measurable)
      (tendsto_measure_exists_abs_gt_of_lindeberg
        (fun n i => ((radArray_stronglyMeasurable n i).mono
          ((coinFiltration n).le _)).measurable) radArray_memLp radArray_lindeberg)
      (aldousCondition_of_martingaleDifference radArray_stronglyMeasurable radArray_condExp
        radArray_memLp radArray_hQV))

-- The conclusion in its compact-set form: one compact set of `D([0,1])` carries at least
-- `9/10` of the mass of every step process.
example : ∃ K : Set (SkorokhodSpace 1), IsCompact K ∧
    ∀ n, coinSeq.map (arrayStepProcess n radArray) Kᶜ ≤ 10⁻¹ := by
  obtain ⟨K, hK, hKμ⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
    isTightMeasureSet_radArray) 10⁻¹ (by simp)
  exact ⟨K, hK, fun n => hKμ _ ⟨n, rfl⟩⟩

end

end MathlibExtTest.Probability.Martingale.AldousD
