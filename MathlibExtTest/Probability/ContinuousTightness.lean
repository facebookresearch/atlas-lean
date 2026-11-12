/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ContinuousTightness
import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal
open MathlibExt.Probability.ContinuousTightness

namespace MathlibExtTest.Probability.ContinuousTightness

noncomputable section

local notation "I" => Set.Icc (0 : ℝ) 1

/-- The time origin of `[0,1]`. -/
def zeroT : I := ⟨0, le_rfl, zero_le_one⟩

/-- The right endpoint of `[0,1]`. -/
def oneT : I := ⟨1, zero_le_one, le_rfl⟩

/-- The linear path `t ↦ a * t`. -/
def linPath (a : ℝ) : C(I, ℝ) := ⟨fun t => a * t.1, by fun_prop⟩

/-- The constant path with value `c`. -/
def constPath (c : ℝ) : C(I, ℝ) := ContinuousMap.const I c

lemma dist_linPath (a : ℝ) (s t : I) : dist (linPath a s) (linPath a t) = |a| * dist s t := by
  simp only [linPath, ContinuousMap.coe_mk, Real.dist_eq, Subtype.dist_eq, ← mul_sub, abs_mul]

/-! ### Arzelà–Ascoli helpers -/

-- A compact set of paths (here a two-point set) is equicontinuous.
example : Equicontinuous ((↑) : ({linPath 1, linPath 2} : Set C(I, ℝ)) → I → ℝ) :=
  equicontinuous_of_isCompact ((Set.finite_singleton _).insert _).isCompact

-- Arzelà–Ascoli on the uniformly bounded, equicontinuous family of constant paths with values
-- in `[-1, 1]`.
example : IsCompact (closure (constPath '' Set.Icc (-1) 1)) := by
  refine isCompact_closure_of_bounded_equicontinuous (R := 1) ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    refine (ContinuousMap.norm_le _ zero_le_one).2 fun _ => ?_
    simpa [constPath, abs_le] using hc
  · intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    refine ⟨1, one_pos, fun y _ f => ?_⟩
    obtain ⟨_, ⟨c, _, rfl⟩⟩ := f
    simpa [constPath] using hε

-- Compact capture for one random path: for a point mass the event has probability at most `b`.
example {b : ℝ} (hb : 0 < b) : ∃ C : Set C(I, ℝ), IsCompact C ∧
    (Measure.dirac ()).real {_ω : Unit | linPath 1 ∉ C} ≤ b :=
  exists_isCompact_measureReal_notMem_le (W := fun _ : Unit => linPath 1) measurable_const hb

/-! ### `norm_le_of_modulus`: the bound `⌈1/δ⌉` is attained -/

-- `t ↦ 2t` has increments `≤ 1` over gaps `≤ 1/2`, so its norm is at most `⌈2⌉ = 2` ...
example : ‖linPath 2‖ ≤ 2 := by
  have h := norm_le_of_modulus (linPath 2) (by simp [linPath]) (δ := 1 / 2) (by norm_num)
    fun s t hst => by rw [dist_linPath]; norm_num; linarith
  norm_num at h
  exact h

-- ... and the value at `t = 1` is `2`, so the bound cannot be improved.
example : 2 ≤ ‖linPath 2‖ := by
  have h := (linPath 2).norm_coe_le_norm oneT
  simpa [linPath, oneT] using h

-- The pinning `f 0 = 0` cannot be dropped: the constant path `5` has zero increments but norm
-- `5 > ⌈1/1⌉ = 1`.
example : ¬ ∀ f : C(I, ℝ), (∀ s t : I, dist s t ≤ 1 → dist (f s) (f t) ≤ 1) →
    ‖f‖ ≤ (⌈1 / (1 : ℝ)⌉₊ : ℝ) := by
  intro h
  have h5 := h (constPath 5) fun s t _ => by simp [constPath]
  have hv := (constPath 5).norm_coe_le_norm zeroT
  norm_num [constPath] at h5 hv
  linarith

/-! ### `isTightMeasureSet_of_modulus` -/

-- An `n`-dependent family: the paths `t ↦ t / (n + 1)`, pinned at `0`, are tight.
example : IsTightMeasureSet (Set.range fun n : ℕ =>
    (Measure.dirac ()).map (fun _ : Unit => linPath (1 / ((n : ℝ) + 1)))) := by
  refine isTightMeasureSet_of_modulus (P := Measure.dirac ())
    (fun n _ => linPath (1 / ((n : ℝ) + 1))) (fun _ => measurable_const)
    (fun _ _ => by simp [linPath]) fun ε hε b hb => ⟨ε / 2, by positivity,
      Eventually.of_forall fun n => ?_⟩
  have hempty : {ω : Unit | ∃ s t : I, dist s t ≤ ε / 2 ∧
      ε ≤ dist (linPath (1 / ((n : ℝ) + 1)) s) (linPath (1 / ((n : ℝ) + 1)) t)} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
      not_le]
    intro s t hst
    rw [dist_linPath]
    have ha : |1 / ((n : ℝ) + 1)| ≤ 1 := by
      rw [abs_of_pos (by positivity)]
      exact div_le_one_of_le₀ (by linarith [n.cast_nonneg (α := ℝ)]) (by positivity)
    calc |1 / ((n : ℝ) + 1)| * dist s t ≤ 1 * (ε / 2) :=
          mul_le_mul ha hst dist_nonneg zero_le_one
      _ < ε := by linarith
  rw [hempty, measureReal_empty]
  exact hb.le

-- The pinning hypothesis `W n 0 = 0` is needed: the constant paths `n` satisfy the modulus
-- bound trivially, but their laws escape every compact set.
example : ¬ IsTightMeasureSet (Set.range fun n : ℕ =>
    (Measure.dirac ()).map (fun _ : Unit => constPath n)) := by
  intro htight
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  obtain ⟨K, hK, hle⟩ := htight (1 / 2) (by norm_num)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : C(I, ℝ))
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hnK : constPath n ∉ K := by
    intro hmem
    have h1 := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : ‖(constPath (n : ℝ)) zeroT‖ ≤ ‖constPath (n : ℝ)‖ :=
      ContinuousMap.norm_coe_le_norm _ _
    rw [show (constPath (n : ℝ)) zeroT = n from rfl, Real.norm_natCast] at h2
    linarith
  have h := hle _ ⟨n, rfl⟩
  have hset : (fun _ : Unit => constPath (n : ℝ)) ⁻¹' Kᶜ = Set.univ := by
    ext
    simpa using hnK
  rw [Measure.map_apply measurable_const hK.isClosed.measurableSet.compl, hset,
    measure_univ] at h
  exact absurd h (by norm_num)

end

end MathlibExtTest.Probability.ContinuousTightness
