/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.KingmanSigned.Basic

/-!
# Tests for `MathlibExt.Dynamics.Ergodic.KingmanSigned.Basic`

* `StatMech.Kingman.SubadditiveCocycle`: proved for a strictly subadditive cocycle over the
  identity map of a probability space, `X 0 = 0` and `X n = 1` for `n ≥ 1`
  (`X (m + n) = 1 < 2 = X m + X n` when `m, n ≥ 1`).
* `StatMech.Kingman.SubadditiveCocycle.expSeq` is computed for it, `bddBelow_of_nonneg`
  supplies the time-constant hypothesis, and `gamma` is identified as `0` through
  `tendsto_expSeq_div` (Fekete's lemma); `gamma_le_expSeq_one` gives `0 ≤ 1`.
* `StatMech.Kingman.integral_comp_iterate` on the identity map.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Dynamics.Ergodic.KingmanSigned.Basic

open MeasureTheory Filter Topology
open _root_.StatMech _root_.StatMech.Kingman

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

/-- The cocycle `X 0 = 0`, `X n = 1` for `n ≥ 1`. -/
noncomputable def oneCoc : ℕ → α → ℝ := fun n _ => if n = 0 then 0 else 1

omit [MeasurableSpace α] in
lemma oneCoc_nonneg (n : ℕ) (x : α) : 0 ≤ oneCoc n x := by
  unfold oneCoc; split_ifs <;> norm_num

/-- `oneCoc` is a subadditive cocycle over the identity, with strict inequality for `m, n ≥ 1`. -/
theorem oneCoc_subadditiveCocycle : SubadditiveCocycle (id : α → α) μ oneCoc where
  measurePreserving := MeasurePreserving.id μ
  integrable n := integrable_const _
  subadditive m n := Eventually.of_forall fun x => by
    simp only [oneCoc]
    split_ifs <;> first | omega | norm_num

/-- The strict inequality for `m = n = 1`: `X 2 = 1 < 2 = X 1 + X 1`. -/
example (x : α) : oneCoc 2 x < oneCoc 1 x + oneCoc 1 (id^[1] x) := by
  norm_num [oneCoc]

/-- The expectations are `∫ X n dμ = 1` for `n ≥ 1` and `0` for `n = 0`. -/
theorem expSeq_oneCoc (n : ℕ) :
    SubadditiveCocycle.expSeq (oneCoc (α := α)) μ n = if n = 0 then 0 else 1 := by
  simp only [SubadditiveCocycle.expSeq, oneCoc]
  split_ifs <;> simp

/-- Fekete's limit (the time constant) of the witness is `0`, since `expSeq n / n = 1 / n`. -/
theorem gamma_oneCoc : SubadditiveCocycle.gamma (oneCoc_subadditiveCocycle μ) = 0 := by
  have hbdd := SubadditiveCocycle.bddBelow_of_nonneg (oneCoc_subadditiveCocycle μ)
    (fun n => Eventually.of_forall fun x => oneCoc_nonneg n x)
  have h1 := SubadditiveCocycle.tendsto_expSeq_div (oneCoc_subadditiveCocycle μ) hbdd
  have h2 : Tendsto (fun n : ℕ => SubadditiveCocycle.expSeq (oneCoc (α := α)) μ n / n) atTop
      (𝓝 0) := by
    refine tendsto_one_div_atTop_nhds_zero_nat.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [expSeq_oneCoc]; simp [show n ≠ 0 by omega]
  exact tendsto_nhds_unique h1 h2

/-- `gamma ≤ ∫ X 1 dμ`, here `0 ≤ 1`. -/
example : SubadditiveCocycle.gamma (oneCoc_subadditiveCocycle μ) ≤
    SubadditiveCocycle.expSeq (oneCoc (α := α)) μ 1 :=
  SubadditiveCocycle.gamma_le_expSeq_one _ (SubadditiveCocycle.bddBelow_of_nonneg
    (oneCoc_subadditiveCocycle μ) fun n => Eventually.of_forall fun x => oneCoc_nonneg n x)

/-- Integrals are invariant under iterates of the identity map. -/
example (g : α → ℝ) (hg : AEStronglyMeasurable g μ) (m : ℕ) :
    ∫ x, g (id^[m] x) ∂μ = ∫ x, g x ∂μ :=
  integral_comp_iterate id (MeasurePreserving.id μ) g hg m

end MathlibExtTest.StatMech.Dynamics.Ergodic.KingmanSigned.Basic
