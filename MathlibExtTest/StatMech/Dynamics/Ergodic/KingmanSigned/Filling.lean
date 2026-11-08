/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.KingmanSigned.Filling

/-!
# Tests for `MathlibExt.Dynamics.Ergodic.KingmanSigned.Filling`

Witness: the identity map on a probability space with the strictly subadditive nonnegative
cocycle `X 0 = 0`, `X n = 1` for `n ≥ 1`.

* `StatMech.KingmanFilling.tendsto_div_kingmanLimit_ae_of_nonneg` (Kingman's theorem for
  nonnegative cocycles): applied, and the limit identified as `0` almost everywhere.
* `StatMech.KingmanFilling.gStar_le_gStarLow_ae` and
  `StatMech.KingmanFilling.gamma_le_integral_gLow`: applied.
* `StatMech.KingmanFilling.badSet`: for `ε = 1` the bad set of the witness is empty.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Dynamics.Ergodic.KingmanSigned.Filling

open MeasureTheory Filter Topology
open _root_.StatMech _root_.StatMech.Kingman _root_.StatMech.KingmanAE
  _root_.StatMech.KingmanFilling

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

/-- The cocycle `X 0 = 0`, `X n = 1` for `n ≥ 1`. -/
noncomputable def oneCoc : ℕ → α → ℝ := fun n _ => if n = 0 then 0 else 1

omit [MeasurableSpace α] in
lemma oneCoc_nonneg (n : ℕ) (x : α) : 0 ≤ oneCoc n x := by
  unfold oneCoc; split_ifs <;> norm_num

/-- `oneCoc` is a subadditive cocycle over the identity. -/
theorem oneCoc_subadditiveCocycle : SubadditiveCocycle (id : α → α) μ oneCoc where
  measurePreserving := MeasurePreserving.id μ
  integrable n := integrable_const _
  subadditive m n := Eventually.of_forall fun x => by
    simp only [oneCoc]
    split_ifs <;> first | omega | norm_num

omit [IsProbabilityMeasure μ] in
lemma oneCoc_nonneg_ae (n : ℕ) : 0 ≤ᵐ[μ] oneCoc (α := α) n :=
  Eventually.of_forall fun x => oneCoc_nonneg n x

omit [MeasurableSpace α] in
/-- `X n x / n = 1 / n → 0`. -/
lemma tendsto_oneCoc_div (x : α) : Tendsto (fun n : ℕ => oneCoc n x / n) atTop (𝓝 0) := by
  refine tendsto_one_div_atTop_nhds_zero_nat.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp [oneCoc, show n ≠ 0 by omega]

/-- Kingman's theorem for the nonnegative witness: the limit is `0` almost everywhere. -/
example : ∀ᵐ x ∂μ, kingmanLimit id (oneCoc (α := α)) x = 0 := by
  filter_upwards [tendsto_div_kingmanLimit_ae_of_nonneg (oneCoc_subadditiveCocycle μ)
    (oneCoc_nonneg_ae μ)] with x hx
  exact tendsto_nhds_unique hx (tendsto_oneCoc_div x)

/-- The lower bound `g* ≤ g_*` a.e. for the witness. -/
example : ∀ᵐ x ∂μ, gStar id (oneCoc (α := α)) x ≤ gStarLow id oneCoc x :=
  gStar_le_gStarLow_ae (oneCoc_subadditiveCocycle μ) (oneCoc_nonneg_ae μ)

/-- `gamma ≤ ∫ g_*` for the witness. -/
example : SubadditiveCocycle.gamma (oneCoc_subadditiveCocycle μ) ≤
    ∫ x, gLow id (oneCoc (α := α)) x ∂μ :=
  gamma_le_integral_gLow (oneCoc_subadditiveCocycle μ) (oneCoc_nonneg_ae μ)

omit [MeasurableSpace α] in
/-- `g_* = 0` for the witness, so for `ε = 1` no point is bad: `X 1 = 1 ≤ (0 + 1) * 1`. -/
example (N : ℕ) (hN : 1 ≤ N) : badSet id (oneCoc (α := α)) 1 N = ∅ := by
  ext x
  have hlow : gLow id (oneCoc (α := α)) x = 0 := by
    have h := (EReal.tendsto_coe.2 (tendsto_oneCoc_div x)).liminf_eq
    simp [gLow, gStarLow, h]
  simp only [badSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall, not_lt]
  exact ⟨1, le_rfl, hN, by simp [hlow, oneCoc]⟩

end MathlibExtTest.StatMech.Dynamics.Ergodic.KingmanSigned.Filling
