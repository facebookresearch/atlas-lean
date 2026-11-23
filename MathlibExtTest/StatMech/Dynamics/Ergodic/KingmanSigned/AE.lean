/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.KingmanSigned.AE

/-!
# Tests for `MathlibExt.Dynamics.Ergodic.KingmanSigned.AE`

Witness: the identity map on a probability space with the additive cocycle `X n x = n * c`.

* `StatMech.KingmanAE.gStar`, `StatMech.KingmanAE.gStarLow`, `StatMech.KingmanAE.kingmanLimit`:
  computed to be `c`.
* `StatMech.KingmanAE.tendsto_div_kingmanLimit_ae`: both side hypotheses (`g* ≤ g_*` and
  `g* > ⊥` a.e.) are proved for the witness and the theorem is applied.
* `StatMech.KingmanAE.gStar_lt_top_ae` and, for `c ≥ 0`,
  `StatMech.KingmanAE.integral_kingmanLimit_le_gamma` (`∫ kingmanLimit ≤ gamma`).
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Dynamics.Ergodic.KingmanSigned.AE

open MeasureTheory Filter Topology
open _root_.StatMech _root_.StatMech.Kingman _root_.StatMech.KingmanAE

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

/-- The additive cocycle `X n x = n * c`. -/
noncomputable def linCoc (c : ℝ) : ℕ → α → ℝ := fun n _ => (n : ℝ) * c

/-- `X n x = n * c` is a subadditive cocycle over the identity map. -/
theorem linCoc_subadditiveCocycle (c : ℝ) :
    SubadditiveCocycle (id : α → α) μ (linCoc c) where
  measurePreserving := MeasurePreserving.id μ
  integrable n := integrable_const _
  subadditive m n := Eventually.of_forall fun x => by
    simp only [linCoc, Nat.cast_add]; linarith

omit [MeasurableSpace α] in
/-- `X n x / n → c` in `EReal`. -/
lemma tendsto_linCoc_div (c : ℝ) (x : α) :
    Tendsto (fun n : ℕ => ((linCoc c n x / n : ℝ) : EReal)) atTop (𝓝 (c : EReal)) := by
  rw [EReal.tendsto_coe]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp [linCoc, mul_div_cancel_left₀ c hn']

omit [MeasurableSpace α] in
/-- `g* = c` for the witness. -/
lemma gStar_linCoc (c : ℝ) (x : α) : gStar id (linCoc c) x = c :=
  (tendsto_linCoc_div c x).limsup_eq

omit [MeasurableSpace α] in
/-- `g_* = c` for the witness. -/
lemma gStarLow_linCoc (c : ℝ) (x : α) : gStarLow id (linCoc c) x = c :=
  (tendsto_linCoc_div c x).liminf_eq

omit [MeasurableSpace α] in
/-- `kingmanLimit = c` for the witness. -/
example (c : ℝ) (x : α) : kingmanLimit id (linCoc c) x = c := by
  simp [kingmanLimit, gStar_linCoc]

/-- The conditional form of Kingman's theorem, with both side hypotheses proved. -/
example (c : ℝ) : ∀ᵐ x ∂μ, Tendsto (fun n => linCoc c n x / n) atTop
    (𝓝 (kingmanLimit id (linCoc c) x)) :=
  tendsto_div_kingmanLimit_ae (linCoc_subadditiveCocycle μ c)
    (Eventually.of_forall fun x => by rw [gStar_linCoc, gStarLow_linCoc])
    (Eventually.of_forall fun x => by rw [gStar_linCoc]; exact EReal.bot_lt_coe c)

/-- `g* < ⊤` almost everywhere. -/
example (c : ℝ) : ∀ᵐ x ∂μ, gStar id (linCoc c) x < ⊤ :=
  gStar_lt_top_ae (linCoc_subadditiveCocycle μ c)

/-- `∫ kingmanLimit ≤ gamma` for the nonnegative witness `c = 2`; the left side is `2`. -/
example : (2 : ℝ) ≤ SubadditiveCocycle.gamma (linCoc_subadditiveCocycle μ 2) := by
  have h := integral_kingmanLimit_le_gamma (linCoc_subadditiveCocycle μ 2)
    (fun n => Eventually.of_forall fun x => by unfold linCoc; positivity)
  simpa [kingmanLimit, gStar_linCoc] using h

end MathlibExtTest.StatMech.Dynamics.Ergodic.KingmanSigned.AE
