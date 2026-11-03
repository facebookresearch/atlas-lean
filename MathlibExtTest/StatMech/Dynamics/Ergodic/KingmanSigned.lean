/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.KingmanSigned

/-!
# Tests for `MathlibExt.Dynamics.Ergodic.KingmanSigned`

* `StatMech.KingmanSigned.kingman_ae_general`: non-vacuity on an arbitrary probability space with
  the identity map and the additive (signed) cocycle `X n x = n * c`, for any real `c` (negative
  values included). The structure `SubadditiveCocycle` and the lower bound on `expSeq n / n` are
  proved for this witness, and the conclusion identifies `kingmanLimit id X = c` almost
  everywhere.
* `StatMech.KingmanSigned.exists_invariant_limit_of_nonneg`: the same witness with `c ≥ 0`.
* The defect `Zc` of the witness vanishes and `addCoc` is computed.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Dynamics.Ergodic.KingmanSigned

open MeasureTheory Filter Topology
open _root_.StatMech _root_.StatMech.Kingman _root_.StatMech.KingmanAE
  _root_.StatMech.KingmanSigned

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

/-- The additive cocycle `X n x = n * c` over any map. -/
noncomputable def linCoc (c : ℝ) : ℕ → α → ℝ := fun n _ => (n : ℝ) * c

/-- `X n x = n * c` is a subadditive cocycle over the identity map (with equality in the cocycle
inequality). -/
theorem linCoc_subadditiveCocycle (c : ℝ) :
    SubadditiveCocycle (id : α → α) μ (linCoc c) where
  measurePreserving := MeasurePreserving.id μ
  integrable n := integrable_const _
  subadditive m n := Eventually.of_forall fun x => by
    simp only [linCoc, Nat.cast_add]; linarith

/-- The expectations of the witness are `∫ X n dμ = n * c`. -/
theorem expSeq_linCoc (c : ℝ) (n : ℕ) :
    SubadditiveCocycle.expSeq (linCoc (α := α) c) μ n = n * c := by
  simp [SubadditiveCocycle.expSeq, linCoc]

/-- The time-constant hypothesis `BddBelow (range (expSeq n / n))` holds for the witness. -/
theorem bddBelow_linCoc (c : ℝ) :
    BddBelow (Set.range fun n => SubadditiveCocycle.expSeq (linCoc (α := α) c) μ n / n) := by
  refine ⟨min c 0, ?_⟩
  rintro _ ⟨n, rfl⟩
  simp only [expSeq_linCoc]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (n : ℝ) ≠ 0 := by positivity
    rw [mul_div_cancel_left₀ c hn']
    exact min_le_left _ _

omit [MeasurableSpace α] in
/-- `X n x / n` is eventually the constant `c`. -/
theorem tendsto_linCoc_div (c : ℝ) (x : α) :
    Tendsto (fun n : ℕ => linCoc c n x / n) atTop (𝓝 c) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp [linCoc, mul_div_cancel_left₀ c hn']

/-- Kingman's theorem applies to the signed witness (all hypotheses instantiated), and its
limit is `c` almost everywhere. -/
example (c : ℝ) : ∀ᵐ x ∂μ, kingmanLimit id (linCoc c) x = c := by
  filter_upwards [kingman_ae_general (linCoc_subadditiveCocycle μ c) (bddBelow_linCoc μ c)]
    with x hx
  exact tendsto_nhds_unique hx (tendsto_linCoc_div c x)

/-- A concrete negative case: with `c = -3` the Kingman limit is `-3` almost everywhere. -/
example : ∀ᵐ x ∂μ, kingmanLimit id (linCoc (-3)) x = -3 := by
  filter_upwards [kingman_ae_general (linCoc_subadditiveCocycle μ (-3)) (bddBelow_linCoc μ _)]
    with x hx
  exact tendsto_nhds_unique hx (tendsto_linCoc_div (-3) x)

/-- The nonnegative form: for `c ≥ 0` the witness has an integrable invariant limit, and that
limit is `c` almost everywhere. -/
example (c : ℝ) (hc : 0 ≤ c) :
    ∃ g : α → ℝ, Integrable g μ ∧ ∀ᵐ x ∂μ, g x = c := by
  obtain ⟨g, hg, -, hlim⟩ := exists_invariant_limit_of_nonneg (μ := μ) (T := id)
    (X := linCoc c) (MeasurePreserving.id μ) (fun _ => integrable_const _)
    (fun n => Eventually.of_forall fun _ => by unfold linCoc; positivity)
    (linCoc_subadditiveCocycle μ c).subadditive
  refine ⟨g, hg, ?_⟩
  filter_upwards [hlim] with x hx
  exact tendsto_nhds_unique hx (tendsto_linCoc_div c x)

/-- `addCoc` of the witness is the Birkhoff sum of `X 1`, here `n * c`. -/
example (c : ℝ) (n : ℕ) (x : α) : addCoc id (linCoc c) n x = n * c := by
  simp [addCoc, linCoc, birkhoffSum]

/-- The defect `Zc = addCoc - X` of an additive cocycle is zero. -/
example (c : ℝ) (n : ℕ) (x : α) : Zc id (linCoc c) n x = 0 := by
  simp [Zc, addCoc, linCoc, birkhoffSum]

end MathlibExtTest.StatMech.Dynamics.Ergodic.KingmanSigned
