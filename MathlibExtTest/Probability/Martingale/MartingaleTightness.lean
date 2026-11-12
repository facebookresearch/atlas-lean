/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.MartingaleTightness

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
open MathlibExt.Probability.Martingale

namespace MathlibExtTest.Probability.Martingale.MartingaleTightness

noncomputable section

/-! ### Step and polygonal paths, computed from the definitions -/

/-- The constant array with all increments `1`, on a one-point sample space. -/
def onesArray : ℕ → ℕ → Unit → ℝ := fun _ _ _ => 1

def quarter : Set.Icc (0 : ℝ) 1 := ⟨1 / 4, by norm_num, by norm_num⟩

def one : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num, le_rfl⟩

-- At `t = 1` the step path of row `2` has summed both increments.
example : arrayStepProcess 2 onesArray () one = 2 := by
  rw [arrayStepProcess_apply]
  norm_num [one, onesArray]

-- Boundary between the two paths: at `t = 1/4` in row `2` no increment has been placed yet
-- (`⌊2 · 1/4⌋ = 0`), so the step path is still `0` ...
example : arrayStepProcess 2 onesArray () quarter = 0 := by
  rw [arrayStepProcess_apply]
  simp only [quarter]
  rw [show ((2 : ℕ) : ℝ) * (1 / 4) = 1 / 2 by norm_num,
    Nat.floor_eq_zero.2 (by norm_num : (1 / 2 : ℝ) < 1)]
  simp

-- ... while the polygon has already interpolated half of the first increment.
example : arrayPolygon 2 onesArray () quarter = 1 / 2 := by
  rw [arrayPolygon_apply]
  simp only [quarter, show ((2 : ℕ) : ℝ) * (1 / 4) = 1 / 2 by norm_num,
    Nat.floor_eq_zero.2 (by norm_num : (1 / 2 : ℝ) < 1)]
  norm_num [onesArray]

-- The two paths differ by at most the largest increment (here `1`).
example (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    |arrayStepProcess n onesArray () t - arrayPolygon n onesArray () t| ≤ 1 :=
  abs_arrayStepProcess_sub_arrayPolygon_le n onesArray () zero_le_one (fun _ _ => by
    simp [onesArray]) t

-- The polygon is pinned at `0`.
example (n : ℕ) : arrayPolygon n onesArray () ⟨0, le_rfl, zero_le_one⟩ = 0 :=
  arrayPolygon_zero n onesArray ()

/-! ### Aldous's condition is not vacuous -/

/-- The trivial filtration on the one-point space, in every row. -/
def topFiltration : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Unit) := fun _ => ⊤

-- The zero array satisfies Aldous's condition: every increment vanishes.
example : AldousCondition topFiltration (fun _ _ _ => (0 : ℝ)) (Measure.dirac ()) := by
  intro ε hε η _
  refine ⟨1, one_pos, 0, fun n _ σ ρ _ _ _ => ?_⟩
  have : {ω : Unit | ε ≤ |∑ i ∈ Finset.range (ρ ω), (0 : ℝ) - ∑ i ∈ Finset.range (σ ω), 0|} =
      ∅ := by
    ext ω; simp [not_le.2 hε]
  rw [this, measure_empty]
  exact zero_le

/-- Every row has a deterministic unit jump at its first increment. -/
def firstJumpArray : ℕ → ℕ → Unit → ℝ := fun _ i _ => if i = 0 then 1 else 0

-- Boundary: a deterministic unit jump at time `1/n` violates Aldous's condition. The stopping
-- times `σ = 0 ≤ ρ = 1` lie in every window `⌊n θ⌋ ≥ 1`, and the increment is `1`.
example : ¬ AldousCondition topFiltration firstJumpArray (Measure.dirac ()) := by
  intro h
  obtain ⟨θ, hθ, N, hN⟩ := h (1 / 2) (by norm_num) (1 / 2) (by norm_num)
  set n := max N (⌈1 / θ⌉₊ + 1) with hn
  have hnθ : 1 ≤ ⌊(n : ℝ) * θ⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : (1 / θ : ℝ) ≤ n := by
      have := Nat.le_ceil (1 / θ)
      have h2 : ((⌈1 / θ⌉₊ : ℕ) : ℝ) ≤ n := by
        exact_mod_cast (Nat.le_succ _).trans (le_max_right _ _)
      linarith
    rw [div_le_iff₀ hθ] at h1
    push_cast; linarith
  have hn1 : 1 ≤ n := (Nat.le_add_left 1 _).trans (le_max_right _ _)
  have key := hN n (le_max_left _ _) (fun _ => 0) (fun _ => 1)
    (isStoppingTime_natCast_iff.2 fun i => MeasurableSet.of_discrete)
    (isStoppingTime_natCast_iff.2 fun i => MeasurableSet.of_discrete)
    (fun _ => ⟨Nat.zero_le 1, by simpa using hnθ, hn1⟩)
  have hset : {ω : Unit | (1 / 2 : ℝ) ≤ |∑ i ∈ Finset.range 1, firstJumpArray n i ω -
      ∑ i ∈ Finset.range 0, firstJumpArray n i ω|} = Set.univ := by
    ext ω; norm_num [firstJumpArray]
  rw [hset, measure_univ] at key
  have : ENNReal.ofReal (1 / 2) < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by norm_num)
  exact absurd key (not_le.2 this)

/-! ### Aldous's criterion and the modulus criterion, on a concrete array -/

-- The modulus criterion for the constant zero process.
example : IsTightMeasureSet (Set.range fun _ : ℕ =>
    (Measure.dirac ()).map (fun _ : Unit => (0 : C(Set.Icc (0 : ℝ) 1, ℝ)))) :=
  isTightMeasureSet_of_modulus (P := Measure.dirac ()) (fun _ _ => 0)
    (fun _ => measurable_const) (fun _ _ => rfl)
    (fun ε hε b hb => ⟨1, one_pos, Eventually.of_forall fun _ => by
      have : {ω : Unit | ∃ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ 1 ∧
          ε ≤ dist ((0 : C(Set.Icc (0 : ℝ) 1, ℝ)) s) ((0 : C(Set.Icc (0 : ℝ) 1, ℝ)) t)} = ∅ := by
        ext ω; simp [not_le.2 hε]
      rw [this, measureReal_empty]; exact hb.le⟩)

-- Aldous's criterion, all hypotheses discharged, for the zero array.
example : IsTightMeasureSet (Set.range fun n =>
    (Measure.dirac ()).map (arrayPolygon n (fun _ _ (_ : Unit) => (0 : ℝ)))) := by
  refine isTightMeasureSet_arrayPolygon_of_aldousCondition (𝓕 := topFiltration)
    (fun _ _ => measurable_const) (fun ε hε => ?_) ?_
  · have : ∀ n : ℕ, {ω : Unit | ∃ i < n, ε < |(0 : ℝ)|} = ∅ := by
      intro n; ext ω; simp [not_lt.2 hε.le]
    simp only [this, measure_empty]
    exact tendsto_const_nhds
  · intro ε hε η _
    refine ⟨1, one_pos, 0, fun n _ σ ρ _ _ _ => ?_⟩
    have : {ω : Unit | ε ≤ |∑ i ∈ Finset.range (ρ ω), (0 : ℝ) -
        ∑ i ∈ Finset.range (σ ω), 0|} = ∅ := by
      ext ω; simp [not_le.2 hε]
    rw [this, measure_empty]
    exact zero_le

/-! ### The martingale results, instantiated on their hypotheses -/

section Martingale

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}

-- Martingale difference arrays with converging quadratic variation satisfy Aldous's condition,
-- hence (with negligible jumps) have tight polygons.
example (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i))
    (hmds : ∀ n i, μ[ξ n i | 𝓕 n i] =ᵐ[μ] 0) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hQV : ∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)
      atTop (fun _ => t))
    (hLind : LindebergConditionTriangular ξ μ) :
    IsTightMeasureSet (Set.range fun n => μ.map (arrayPolygon n ξ)) :=
  isTightMeasureSet_arrayPolygon_of_aldousCondition (fun n i => (hξ n i).measurable)
    (tendsto_measure_exists_abs_gt_of_lindeberg
      (fun n i => ((hξ n i).mono ((𝓕 n).le _)).measurable) hL2 hLind)
    (aldousCondition_of_martingaleDifference hξ hmds hL2 hQV)

-- The functional CLT for martingale arrays, with T81's finite-dimensional convergence as the
-- explicit hypothesis `hT81`.
example {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i))
    (hmds : ∀ n i, μ[ξ n i | 𝓕 n i] =ᵐ[μ] 0) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hQV : ∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)
      atTop (fun _ => t))
    (hLind : LindebergConditionTriangular ξ μ)
    (W : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ)) (hW : AEMeasurable W P')
    (hT81 : ∀ I : Finset (Set.Icc (0 : ℝ) 1), TendstoInDistribution
      (fun (n : ℕ) ω => I.restrict (fun t => ∑ i ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, ξ n i ω))
      atTop (fun ω => I.restrict (fun t => W ω t)) (fun _ => μ) P') :
    TendstoInDistribution (fun n => arrayStepProcess n ξ) atTop
      (fun ω => SkorokhodSpace.ofContinuous (W ω)) (fun _ => μ) P' :=
  tendstoInDistribution_arrayStepProcess hξ hmds hL2 hQV hLind W hW hT81

end Martingale

end

end MathlibExtTest.Probability.Martingale.MartingaleTightness
