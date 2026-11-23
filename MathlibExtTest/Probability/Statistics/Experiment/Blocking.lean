/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Experiment.Blocking
public import MathlibExt.Probability.Causality.CausalIdentification

/-!
# Tests for blocked randomization

Two-block unbiasedness, single-block reduction, singleton-block impossibility,
and the empty-block zero weight.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Probability.Statistics.Experiment
open MathlibExt.Probability.Causality

namespace MathlibExtTest.Probability.Statistics.Experiment

open MathlibExt.Probability.Statistics.Experiment
open MathlibExt.Probability.Causality

/-- Positive: a two-block fixture on `Fin 6` (blocks of size 4 and 2).
The worker discharges the partition hypotheses and applies
`integral_blockContrast`. -/
example (y₀ y₁ : Fin 6 → ℝ) :
    ∫ S, blockContrast y₀ y₁ ![{0, 1, 2, 3}, {4, 5}] S
      ∂(blockRandomization 2 ![{0, 1, 2, 3}, {4, 5}] ![2, 1]) =
      ate y₀ y₁ := by
  refine integral_blockContrast y₀ y₁ _ _ ?_ ?_ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · show Disjoint ({0, 1, 2, 3} : Finset (Fin 6)) {4, 5}
      rw [Finset.disjoint_left]
      decide
    · show Disjoint ({4, 5} : Finset (Fin 6)) {0, 1, 2, 3}
      rw [Finset.disjoint_left]
      decide
    · exact absurd rfl hij
  · decide
  · decide
  · decide

/-- Bridge non-vacuity: with `B = 1` and the single block equal to `univ`,
`blockContrast` is the ordinary difference in means of the embedded set. -/
example (y₀ y₁ : Fin 4 → ℝ) (S₀ : Finset ↥(Finset.univ : Finset (Fin 4))) :
    blockContrast y₀ y₁ (fun _ : Fin 1 => Finset.univ) (fun _ => S₀) =
      diffInMeans y₀ y₁ (Finset.image Subtype.val S₀) := by
  have hinj : Function.Injective
      (Subtype.val : ↥(Finset.univ : Finset (Fin 4)) → Fin 4) :=
    Subtype.val_injective
  have hcard : ∀ T : Finset ↥(Finset.univ : Finset (Fin 4)),
      (Finset.image Subtype.val T).card = T.card := fun T =>
    Finset.card_image_of_injective T hinj
  have hcompl : Finset.image Subtype.val S₀ᶜ = (Finset.image Subtype.val S₀)ᶜ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_compl]
    constructor
    · rintro ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have e : y = x := hinj hxy
      subst e
      exact hx hy
    · intro h
      exact ⟨⟨i, Finset.mem_univ i⟩, fun hm => h ⟨_, hm, rfl⟩, rfl⟩
  have h1 : sampleMean (y₁ ∘ Subtype.val) S₀ =
      sampleMean y₁ (Finset.image Subtype.val S₀) := by
    simp only [sampleMean, Finset.sum_image (fun x _ y _ h => hinj h), hcard,
      Function.comp_apply]
  have h0 : sampleMean (y₀ ∘ Subtype.val) S₀ᶜ =
      sampleMean y₀ (Finset.image Subtype.val S₀)ᶜ := by
    rw [← hcompl]
    simp only [sampleMean, Finset.sum_image (fun x _ y _ h => hinj h), hcard,
      Function.comp_apply]
  unfold blockContrast
  rw [Fin.sum_univ_one]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [diffInMeans, diffInMeans, h1, h0]
  ring

/-- Negative: a one-subject block cannot satisfy both arm hypotheses. -/
example : ¬ ∃ n : Fin 1 → ℕ, (∀ b, 1 ≤ n b) ∧
    (∀ b, n b + 1 ≤ (((fun _ : Fin 1 => ({0} : Finset (Fin 3))) b).card)) := by
  rintro ⟨n, h1, h0⟩
  have h1' := h1 0
  have h0' := h0 0
  simp only [Finset.card_singleton] at h0'
  omega

/-- Degenerate weight: the summand of an empty block is zero for every
per-block statistic value. -/
example (y₀ y₁ : Fin 4 → ℝ) (S₀ : Finset ↥(∅ : Finset (Fin 4))) :
    ((∅ : Finset (Fin 4)).card : ℝ) * diffInMeans (y₀ ∘ Subtype.val)
      (y₁ ∘ Subtype.val) S₀ = 0 := by
  simp only [Finset.card_empty, Nat.cast_zero, zero_mul]

/-- Non-improvement: a fully concrete two-block fixture on `Fin 8` (blocks
`{0, 1, 2, 3}` and `{4, 5, 6, 7}`, two treated per block, so the two-per-arm
hypotheses `2 ≤ 2`, `2 + 2 ≤ 4` hold and the fixture is admissible for both
targets; unblocked comparison at total treated count `4`). Block
`{0, 1, 2, 3}` carries effect heterogeneity while block `{4, 5, 6, 7}` is
constant-effect. Closed-form values from the exact finite-population
formulas: per-block `S1^2 = 9/4,
S0^2 = 19/12, Sτ^2 = 2/3` on `{0, 1, 2, 3}` and `S1^2 = 3, S0^2 = 3,
Sτ^2 = 0` on `{4, 5, 6, 7}`, giving blocked variance `7/16 + 3/4 = 19/16`;
overall `S1^2 = 127/56, S0^2 = 111/56, Sτ^2 = 2/7`, giving unblocked variance
`115/112`. Since `19/16 - 115/112 = 9/56 > 0`, blocking strictly hurts here.
Both sides are rewritten with `variance_blockContrast` and
`variance_diffInMeans_completeRandomization`, the `popVar` terms are evaluated
by computation, and `19/16 > 115/112` closes by `norm_num`. -/
example :
    ProbabilityTheory.variance
        (blockContrast (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ)
          (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ)
          (![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8)))
        (blockRandomization 2
          (![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8))
          (![2, 2] : Fin 2 → ℕ)) >
      ProbabilityTheory.variance
        (diffInMeans (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ)
          (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ))
        (completeRandomization (Fin 8) 4) := by
  have hmean_y0 : popMean (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) = 13 / 8 := by
    rw [popMean]
    simp [Fin.sum_univ_eight, Fintype.card_fin]
    norm_num
  have hvar_y0 : popVar (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) = 111 / 56 := by
    rw [popVar, hmean_y0]
    simp [Fin.sum_univ_eight, Fintype.card_fin]
    norm_num
  have hmean_y1 : popMean (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) = 13 / 8 := by
    rw [popMean]
    simp [Fin.sum_univ_eight, Fintype.card_fin]
    norm_num
  have hvar_y1 : popVar (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) = 127 / 56 := by
    rw [popVar, hmean_y1]
    simp [Fin.sum_univ_eight, Fintype.card_fin]
    norm_num
  have hmean_tau : popMean (fun i => (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i) = 0 := by
    rw [popMean]
    simp [Fin.sum_univ_eight, Fintype.card_fin]
    norm_num
  have hvar_tau : popVar (fun i => (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i) = 2 / 7 := by
    rw [popVar, hmean_tau]
    simp [Fin.sum_univ_eight, Fintype.card_fin]
    norm_num
  have hblk0 : (((![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8))) 0) = ({0, 1, 2, 3} : Finset (Fin 8)) := by
    decide
  have hblk1 : (((![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8))) 1) = ({4, 5, 6, 7} : Finset (Fin 8)) := by
    decide
  have hcard_b0 : Fintype.card ↥(({0, 1, 2, 3} : Finset (Fin 8))) = 4 := by
    rw [Fintype.card_coe]
    decide
  have hcard_b1 : Fintype.card ↥(({4, 5, 6, 7} : Finset (Fin 8))) = 4 := by
    rw [Fintype.card_coe]
    decide
  have hsum_b0_y0 : ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i = 7 := by
    rw [show ({0, 1, 2, 3} : Finset (Fin 8)) = insert 0 {1, 2, 3} from rfl, Finset.sum_insert (by decide), show ({1, 2, 3} : Finset (Fin 8)) = insert 1 {2, 3} from rfl, Finset.sum_insert (by decide), show ({2, 3} : Finset (Fin 8)) = insert 2 {3} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hmean_b0_y0 : popMean (((![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val : ↥(({0, 1, 2, 3} : Finset (Fin 8))) → ℝ)) = 7 / 4 := by
    have hsum : (∑ x : ↥(({0, 1, 2, 3} : Finset (Fin 8))), ((![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val) x) = ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i :=
      Finset.sum_coe_sort ({0, 1, 2, 3} : Finset (Fin 8)) (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ)
    rw [popMean, hsum, hsum_b0_y0, hcard_b0]
    norm_num
  have hsq_b0_y0 : ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i - 7 / 4) ^ 2) = 19 / 4 := by
    rw [show ({0, 1, 2, 3} : Finset (Fin 8)) = insert 0 {1, 2, 3} from rfl, Finset.sum_insert (by decide), show ({1, 2, 3} : Finset (Fin 8)) = insert 1 {2, 3} from rfl, Finset.sum_insert (by decide), show ({2, 3} : Finset (Fin 8)) = insert 2 {3} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hvar_b0_y0 : popVar (((![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val : ↥(({0, 1, 2, 3} : Finset (Fin 8))) → ℝ)) = 19 / 12 := by
    have hsum : (∑ x : ↥(({0, 1, 2, 3} : Finset (Fin 8))), (((((![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val) x - 7 / 4) ^ 2))) = ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i - 7 / 4) ^ 2) :=
      Finset.sum_coe_sort ({0, 1, 2, 3} : Finset (Fin 8)) (fun i => (((![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i - 7 / 4) ^ 2))
    rw [popVar, hmean_b0_y0]
    simp only [Function.comp_apply] at hsum ⊢
    rw [hsum, hsq_b0_y0, hcard_b0]
    norm_num
  have hsum_b0_y1 : ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i = 7 := by
    rw [show ({0, 1, 2, 3} : Finset (Fin 8)) = insert 0 {1, 2, 3} from rfl, Finset.sum_insert (by decide), show ({1, 2, 3} : Finset (Fin 8)) = insert 1 {2, 3} from rfl, Finset.sum_insert (by decide), show ({2, 3} : Finset (Fin 8)) = insert 2 {3} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hmean_b0_y1 : popMean (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val : ↥(({0, 1, 2, 3} : Finset (Fin 8))) → ℝ)) = 7 / 4 := by
    have hsum : (∑ x : ↥(({0, 1, 2, 3} : Finset (Fin 8))), ((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val) x) = ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i :=
      Finset.sum_coe_sort ({0, 1, 2, 3} : Finset (Fin 8)) (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ)
    rw [popMean, hsum, hsum_b0_y1, hcard_b0]
    norm_num
  have hsq_b0_y1 : ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - 7 / 4) ^ 2) = 27 / 4 := by
    rw [show ({0, 1, 2, 3} : Finset (Fin 8)) = insert 0 {1, 2, 3} from rfl, Finset.sum_insert (by decide), show ({1, 2, 3} : Finset (Fin 8)) = insert 1 {2, 3} from rfl, Finset.sum_insert (by decide), show ({2, 3} : Finset (Fin 8)) = insert 2 {3} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hvar_b0_y1 : popVar (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val : ↥(({0, 1, 2, 3} : Finset (Fin 8))) → ℝ)) = 9 / 4 := by
    have hsum : (∑ x : ↥(({0, 1, 2, 3} : Finset (Fin 8))), (((((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val) x - 7 / 4) ^ 2))) = ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - 7 / 4) ^ 2) :=
      Finset.sum_coe_sort ({0, 1, 2, 3} : Finset (Fin 8)) (fun i => (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - 7 / 4) ^ 2))
    rw [popVar, hmean_b0_y1]
    simp only [Function.comp_apply] at hsum ⊢
    rw [hsum, hsq_b0_y1, hcard_b0]
    norm_num
  have hsum_b0_tau : ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i)) = 0 := by
    rw [show ({0, 1, 2, 3} : Finset (Fin 8)) = insert 0 {1, 2, 3} from rfl, Finset.sum_insert (by decide), show ({1, 2, 3} : Finset (Fin 8)) = insert 1 {2, 3} from rfl, Finset.sum_insert (by decide), show ({2, 3} : Finset (Fin 8)) = insert 2 {3} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hmean_b0_tau : popMean (fun i : ↥(({0, 1, 2, 3} : Finset (Fin 8))) => (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i) = 0 := by
    have hsum : (∑ x : ↥(({0, 1, 2, 3} : Finset (Fin 8))), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) x - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) x))) = ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i)) :=
      Finset.sum_coe_sort ({0, 1, 2, 3} : Finset (Fin 8)) (fun i => (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i)
    rw [popMean, hsum, hsum_b0_tau, hcard_b0]
    norm_num
  have hsq_b0_tau : ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i - 0) ^ 2) = 2 := by
    rw [show ({0, 1, 2, 3} : Finset (Fin 8)) = insert 0 {1, 2, 3} from rfl, Finset.sum_insert (by decide), show ({1, 2, 3} : Finset (Fin 8)) = insert 1 {2, 3} from rfl, Finset.sum_insert (by decide), show ({2, 3} : Finset (Fin 8)) = insert 2 {3} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hvar_b0_tau : popVar (fun i : ↥(({0, 1, 2, 3} : Finset (Fin 8))) => (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i) = 2 / 3 := by
    have hsum : (∑ x : ↥(({0, 1, 2, 3} : Finset (Fin 8))), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) x - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) x - 0) ^ 2)) = ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i - 0) ^ 2) :=
      Finset.sum_coe_sort ({0, 1, 2, 3} : Finset (Fin 8)) (fun i => (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i - 0) ^ 2))
    rw [popVar, hmean_b0_tau]
    rw [hsum, hsq_b0_tau, hcard_b0]
    norm_num
  have hsum_b1_y0 : ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i = 6 := by
    rw [show ({4, 5, 6, 7} : Finset (Fin 8)) = insert 4 {5, 6, 7} from rfl, Finset.sum_insert (by decide), show ({5, 6, 7} : Finset (Fin 8)) = insert 5 {6, 7} from rfl, Finset.sum_insert (by decide), show ({6, 7} : Finset (Fin 8)) = insert 6 {7} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp
    norm_num
  have hmean_b1_y0 : popMean (((![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val : ↥(({4, 5, 6, 7} : Finset (Fin 8))) → ℝ)) = 3 / 2 := by
    have hsum : (∑ x : ↥(({4, 5, 6, 7} : Finset (Fin 8))), ((![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val) x) = ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i :=
      Finset.sum_coe_sort ({4, 5, 6, 7} : Finset (Fin 8)) (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ)
    rw [popMean, hsum, hsum_b1_y0, hcard_b1]
    norm_num
  have hsq_b1_y0 : ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i - 3 / 2) ^ 2) = 9 := by
    rw [show ({4, 5, 6, 7} : Finset (Fin 8)) = insert 4 {5, 6, 7} from rfl, Finset.sum_insert (by decide), show ({5, 6, 7} : Finset (Fin 8)) = insert 5 {6, 7} from rfl, Finset.sum_insert (by decide), show ({6, 7} : Finset (Fin 8)) = insert 6 {7} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp
    norm_num
  have hvar_b1_y0 : popVar (((![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val : ↥(({4, 5, 6, 7} : Finset (Fin 8))) → ℝ)) = 3 := by
    have hsum : (∑ x : ↥(({4, 5, 6, 7} : Finset (Fin 8))), (((((![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val) x - 3 / 2) ^ 2))) = ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i - 3 / 2) ^ 2) :=
      Finset.sum_coe_sort ({4, 5, 6, 7} : Finset (Fin 8)) (fun i => (((![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i - 3 / 2) ^ 2))
    rw [popVar, hmean_b1_y0]
    simp only [Function.comp_apply] at hsum ⊢
    rw [hsum, hsq_b1_y0, hcard_b1]
    norm_num
  have hsum_b1_y1 : ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i = 6 := by
    rw [show ({4, 5, 6, 7} : Finset (Fin 8)) = insert 4 {5, 6, 7} from rfl, Finset.sum_insert (by decide), show ({5, 6, 7} : Finset (Fin 8)) = insert 5 {6, 7} from rfl, Finset.sum_insert (by decide), show ({6, 7} : Finset (Fin 8)) = insert 6 {7} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp
    norm_num
  have hmean_b1_y1 : popMean (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val : ↥(({4, 5, 6, 7} : Finset (Fin 8))) → ℝ)) = 3 / 2 := by
    have hsum : (∑ x : ↥(({4, 5, 6, 7} : Finset (Fin 8))), ((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val) x) = ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i :=
      Finset.sum_coe_sort ({4, 5, 6, 7} : Finset (Fin 8)) (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ)
    rw [popMean, hsum, hsum_b1_y1, hcard_b1]
    norm_num
  have hsq_b1_y1 : ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - 3 / 2) ^ 2) = 9 := by
    rw [show ({4, 5, 6, 7} : Finset (Fin 8)) = insert 4 {5, 6, 7} from rfl, Finset.sum_insert (by decide), show ({5, 6, 7} : Finset (Fin 8)) = insert 5 {6, 7} from rfl, Finset.sum_insert (by decide), show ({6, 7} : Finset (Fin 8)) = insert 6 {7} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp
    norm_num
  have hvar_b1_y1 : popVar (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val : ↥(({4, 5, 6, 7} : Finset (Fin 8))) → ℝ)) = 3 := by
    have hsum : (∑ x : ↥(({4, 5, 6, 7} : Finset (Fin 8))), (((((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) ∘ Subtype.val) x - 3 / 2) ^ 2))) = ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - 3 / 2) ^ 2) :=
      Finset.sum_coe_sort ({4, 5, 6, 7} : Finset (Fin 8)) (fun i => (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - 3 / 2) ^ 2))
    rw [popVar, hmean_b1_y1]
    simp only [Function.comp_apply] at hsum ⊢
    rw [hsum, hsq_b1_y1, hcard_b1]
    norm_num
  have hsum_b1_tau : ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i)) = 0 := by
    rw [show ({4, 5, 6, 7} : Finset (Fin 8)) = insert 4 {5, 6, 7} from rfl, Finset.sum_insert (by decide), show ({5, 6, 7} : Finset (Fin 8)) = insert 5 {6, 7} from rfl, Finset.sum_insert (by decide), show ({6, 7} : Finset (Fin 8)) = insert 6 {7} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp
  have hmean_b1_tau : popMean (fun i : ↥(({4, 5, 6, 7} : Finset (Fin 8))) => (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i) = 0 := by
    have hsum : (∑ x : ↥(({4, 5, 6, 7} : Finset (Fin 8))), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) x - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) x))) = ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i)) :=
      Finset.sum_coe_sort ({4, 5, 6, 7} : Finset (Fin 8)) (fun i => (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i)
    rw [popMean, hsum, hsum_b1_tau, hcard_b1]
    norm_num
  have hsq_b1_tau : ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i - 0) ^ 2) = 0 := by
    rw [show ({4, 5, 6, 7} : Finset (Fin 8)) = insert 4 {5, 6, 7} from rfl, Finset.sum_insert (by decide), show ({5, 6, 7} : Finset (Fin 8)) = insert 5 {6, 7} from rfl, Finset.sum_insert (by decide), show ({6, 7} : Finset (Fin 8)) = insert 6 {7} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp
  have hvar_b1_tau : popVar (fun i : ↥(({4, 5, 6, 7} : Finset (Fin 8))) => (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i) = 0 := by
    have hsum : (∑ x : ↥(({4, 5, 6, 7} : Finset (Fin 8))), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) x - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) x - 0) ^ 2)) = ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i - 0) ^ 2) :=
      Finset.sum_coe_sort ({4, 5, 6, 7} : Finset (Fin 8)) (fun i => (((![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ) i - (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ) i - 0) ^ 2))
    rw [popVar, hmean_b1_tau]
    rw [hsum, hsq_b1_tau, hcard_b1]
    norm_num
  have hn0 : (((![2, 2] : Fin 2 → ℕ)) 0) = 2 := by decide
  have hn1 : (((![2, 2] : Fin 2 → ℕ)) 1) = 2 := by decide
  have hcard0 : ({0, 1, 2, 3} : Finset (Fin 8)).card = 4 := by decide
  have hcard1 : ({4, 5, 6, 7} : Finset (Fin 8)).card = 4 := by decide
  have hLHS : ProbabilityTheory.variance
        (blockContrast (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ)
          (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ)
          (![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8)))
        (blockRandomization 2
          (![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8))
          (![2, 2] : Fin 2 → ℕ)) = 19 / 16 := by
    rw [variance_blockContrast _ _ _ _ (by decide) (by decide), Fin.sum_univ_two, hblk0, hblk1, hn0, hn1, hcard0, hcard1, hvar_b0_y1, hvar_b0_y0, hvar_b0_tau, hvar_b1_y1, hvar_b1_y0, hvar_b1_tau]
    simp only [Fintype.card_fin]
    norm_num
  have hRHS : ProbabilityTheory.variance
        (diffInMeans (![2, 3, 0, 2, 3, 0, 3, 0] : Fin 8 → ℝ)
          (![1, 3, 0, 3, 3, 0, 3, 0] : Fin 8 → ℝ))
        (completeRandomization (Fin 8) 4) = 115 / 112 := by
    rw [variance_diffInMeans_completeRandomization _ _ (by decide) (by decide), hvar_y1, hvar_y0, hvar_tau]
    simp only [Fintype.card_fin]
    norm_num
  rw [hLHS, hRHS]
  norm_num

/-- Constant effects: a fully concrete fixture on `Fin 8` (blocks
`{0, 1, 2, 3}` and `{4, 5, 6, 7}`, two treated per block, so both estimator
hypotheses `2 ≤ 2`, `2 + 2 ≤ 4` hold). Outcomes `y₀ = [0, 1, 2, 3, 0, 1, 2,
3]` with constant shift `c = 1` give `y₁ = [1, 2, 3, 4, 1, 2, 3, 4]`.
Closed-form values from the exact finite-population formulas: per block
`S1^2 = S0^2 = 5/3`, `Sτ^2 = 0`, so each block contributes
`(1/4) * (5/6 + 5/6) = 5/12` to both the estimator expectation and the
variance, giving `E[blockNeyman] = Var(blockContrast) = 5/12 + 5/12 = 5/6`.
Both sides are rewritten with `integral_blockNeyman` and
`variance_blockContrast` and the `popVar` terms are evaluated by
computation. -/
example :
    (∫ S, blockNeyman (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ)
        (fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1)
        (![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8)) S
      ∂(blockRandomization 2
        (![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8))
        (![2, 2] : Fin 2 → ℕ))) =
    ProbabilityTheory.variance
      (blockContrast (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ)
        (fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1)
        (![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8)))
      (blockRandomization 2
        (![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8))
        (![2, 2] : Fin 2 → ℕ)) := by
  have hblk0 : (((![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8))) 0) = ({0, 1, 2, 3} : Finset (Fin 8)) := by
    decide
  have hblk1 : (((![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8))) 1) = ({4, 5, 6, 7} : Finset (Fin 8)) := by
    decide
  have hcard_b0 : Fintype.card ↥(({0, 1, 2, 3} : Finset (Fin 8))) = 4 := by
    rw [Fintype.card_coe]
    decide
  have hcard_b1 : Fintype.card ↥(({4, 5, 6, 7} : Finset (Fin 8))) = 4 := by
    rw [Fintype.card_coe]
    decide
  have hsum_b0_y0 : ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i = 6 := by
    rw [show ({0, 1, 2, 3} : Finset (Fin 8)) = insert 0 {1, 2, 3} from rfl, Finset.sum_insert (by decide), show ({1, 2, 3} : Finset (Fin 8)) = insert 1 {2, 3} from rfl, Finset.sum_insert (by decide), show ({2, 3} : Finset (Fin 8)) = insert 2 {3} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hmean_b0_y0 : popMean (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) ∘ Subtype.val : ↥(({0, 1, 2, 3} : Finset (Fin 8))) → ℝ)) = 3 / 2 := by
    have hsum : (∑ x : ↥(({0, 1, 2, 3} : Finset (Fin 8))), ((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) ∘ Subtype.val) x) = ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i :=
      Finset.sum_coe_sort ({0, 1, 2, 3} : Finset (Fin 8)) (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ)
    rw [popMean, hsum, hsum_b0_y0, hcard_b0]
    norm_num
  have hsq_b0_y0 : ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i - 3 / 2) ^ 2) = 5 := by
    rw [show ({0, 1, 2, 3} : Finset (Fin 8)) = insert 0 {1, 2, 3} from rfl, Finset.sum_insert (by decide), show ({1, 2, 3} : Finset (Fin 8)) = insert 1 {2, 3} from rfl, Finset.sum_insert (by decide), show ({2, 3} : Finset (Fin 8)) = insert 2 {3} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hvar_b0_y0 : popVar (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) ∘ Subtype.val : ↥(({0, 1, 2, 3} : Finset (Fin 8))) → ℝ)) = 5 / 3 := by
    have hsum : (∑ x : ↥(({0, 1, 2, 3} : Finset (Fin 8))), (((((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) ∘ Subtype.val) x - 3 / 2) ^ 2))) = ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i - 3 / 2) ^ 2) :=
      Finset.sum_coe_sort ({0, 1, 2, 3} : Finset (Fin 8)) (fun i => (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i - 3 / 2) ^ 2))
    rw [popVar, hmean_b0_y0]
    simp only [Function.comp_apply] at hsum ⊢
    rw [hsum, hsq_b0_y0, hcard_b0]
    norm_num
  have hsum_b0_y1 : ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1)) = 10 := by
    rw [show ({0, 1, 2, 3} : Finset (Fin 8)) = insert 0 {1, 2, 3} from rfl, Finset.sum_insert (by decide), show ({1, 2, 3} : Finset (Fin 8)) = insert 1 {2, 3} from rfl, Finset.sum_insert (by decide), show ({2, 3} : Finset (Fin 8)) = insert 2 {3} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hmean_b0_y1 : popMean (((fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1) ∘ Subtype.val : ↥(({0, 1, 2, 3} : Finset (Fin 8))) → ℝ)) = 5 / 2 := by
    have hsum : (∑ x : ↥(({0, 1, 2, 3} : Finset (Fin 8))), ((fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1) ∘ Subtype.val) x) = ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1)) :=
      Finset.sum_coe_sort ({0, 1, 2, 3} : Finset (Fin 8)) (fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1)
    rw [popMean, hsum, hsum_b0_y1, hcard_b0]
    norm_num
  have hsq_b0_y1 : ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - 5 / 2) ^ 2) = 5 := by
    rw [show ({0, 1, 2, 3} : Finset (Fin 8)) = insert 0 {1, 2, 3} from rfl, Finset.sum_insert (by decide), show ({1, 2, 3} : Finset (Fin 8)) = insert 1 {2, 3} from rfl, Finset.sum_insert (by decide), show ({2, 3} : Finset (Fin 8)) = insert 2 {3} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hvar_b0_y1 : popVar (((fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1) ∘ Subtype.val : ↥(({0, 1, 2, 3} : Finset (Fin 8))) → ℝ)) = 5 / 3 := by
    have hsum : (∑ x : ↥(({0, 1, 2, 3} : Finset (Fin 8))), (((((fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1) ∘ Subtype.val) x - 5 / 2) ^ 2))) = ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - 5 / 2) ^ 2) :=
      Finset.sum_coe_sort ({0, 1, 2, 3} : Finset (Fin 8)) (fun i => (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - 5 / 2) ^ 2))
    rw [popVar, hmean_b0_y1]
    simp only [Function.comp_apply] at hsum ⊢
    rw [hsum, hsq_b0_y1, hcard_b0]
    norm_num
  have hsum_b0_tau : ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i)) = 4 := by
    rw [show ({0, 1, 2, 3} : Finset (Fin 8)) = insert 0 {1, 2, 3} from rfl, Finset.sum_insert (by decide), show ({1, 2, 3} : Finset (Fin 8)) = insert 1 {2, 3} from rfl, Finset.sum_insert (by decide), show ({2, 3} : Finset (Fin 8)) = insert 2 {3} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hmean_b0_tau : popMean (fun i : ↥(({0, 1, 2, 3} : Finset (Fin 8))) => (fun j => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) j + 1) i - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i) = 1 := by
    have hsum : (∑ x : ↥(({0, 1, 2, 3} : Finset (Fin 8))), ((fun j => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) j + 1) x - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) x)) = ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i)) :=
      Finset.sum_coe_sort ({0, 1, 2, 3} : Finset (Fin 8)) (fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i)
    rw [popMean, hsum, hsum_b0_tau, hcard_b0]
    norm_num
  have hsq_b0_tau : ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i - 1) ^ 2) = 0 := by
    rw [show ({0, 1, 2, 3} : Finset (Fin 8)) = insert 0 {1, 2, 3} from rfl, Finset.sum_insert (by decide), show ({1, 2, 3} : Finset (Fin 8)) = insert 1 {2, 3} from rfl, Finset.sum_insert (by decide), show ({2, 3} : Finset (Fin 8)) = insert 2 {3} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hvar_b0_tau : popVar (fun i : ↥(({0, 1, 2, 3} : Finset (Fin 8))) => (fun j => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) j + 1) i - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i) = 0 := by
    have hsum : (∑ x : ↥(({0, 1, 2, 3} : Finset (Fin 8))), (((fun j => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) j + 1) x - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) x - 1) ^ 2)) = ∑ i ∈ ({0, 1, 2, 3} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i - 1) ^ 2) :=
      Finset.sum_coe_sort ({0, 1, 2, 3} : Finset (Fin 8)) (fun i => (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i - 1) ^ 2))
    rw [popVar, hmean_b0_tau]
    simp only [] at hsum ⊢
    rw [hsum, hsq_b0_tau, hcard_b0]
    norm_num
  have hsum_b1_y0 : ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i = 6 := by
    rw [show ({4, 5, 6, 7} : Finset (Fin 8)) = insert 4 {5, 6, 7} from rfl, Finset.sum_insert (by decide), show ({5, 6, 7} : Finset (Fin 8)) = insert 5 {6, 7} from rfl, Finset.sum_insert (by decide), show ({6, 7} : Finset (Fin 8)) = insert 6 {7} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp
    norm_num
  have hmean_b1_y0 : popMean (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) ∘ Subtype.val : ↥(({4, 5, 6, 7} : Finset (Fin 8))) → ℝ)) = 3 / 2 := by
    have hsum : (∑ x : ↥(({4, 5, 6, 7} : Finset (Fin 8))), ((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) ∘ Subtype.val) x) = ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i :=
      Finset.sum_coe_sort ({4, 5, 6, 7} : Finset (Fin 8)) (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ)
    rw [popMean, hsum, hsum_b1_y0, hcard_b1]
    norm_num
  have hsq_b1_y0 : ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i - 3 / 2) ^ 2) = 5 := by
    rw [show ({4, 5, 6, 7} : Finset (Fin 8)) = insert 4 {5, 6, 7} from rfl, Finset.sum_insert (by decide), show ({5, 6, 7} : Finset (Fin 8)) = insert 5 {6, 7} from rfl, Finset.sum_insert (by decide), show ({6, 7} : Finset (Fin 8)) = insert 6 {7} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp
    norm_num
  have hvar_b1_y0 : popVar (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) ∘ Subtype.val : ↥(({4, 5, 6, 7} : Finset (Fin 8))) → ℝ)) = 5 / 3 := by
    have hsum : (∑ x : ↥(({4, 5, 6, 7} : Finset (Fin 8))), (((((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) ∘ Subtype.val) x - 3 / 2) ^ 2))) = ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i - 3 / 2) ^ 2) :=
      Finset.sum_coe_sort ({4, 5, 6, 7} : Finset (Fin 8)) (fun i => (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i - 3 / 2) ^ 2))
    rw [popVar, hmean_b1_y0]
    simp only [Function.comp_apply] at hsum ⊢
    rw [hsum, hsq_b1_y0, hcard_b1]
    norm_num
  have hsum_b1_y1 : ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1)) = 10 := by
    rw [show ({4, 5, 6, 7} : Finset (Fin 8)) = insert 4 {5, 6, 7} from rfl, Finset.sum_insert (by decide), show ({5, 6, 7} : Finset (Fin 8)) = insert 5 {6, 7} from rfl, Finset.sum_insert (by decide), show ({6, 7} : Finset (Fin 8)) = insert 6 {7} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp
    norm_num
  have hmean_b1_y1 : popMean (((fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1) ∘ Subtype.val : ↥(({4, 5, 6, 7} : Finset (Fin 8))) → ℝ)) = 5 / 2 := by
    have hsum : (∑ x : ↥(({4, 5, 6, 7} : Finset (Fin 8))), ((fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1) ∘ Subtype.val) x) = ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1)) :=
      Finset.sum_coe_sort ({4, 5, 6, 7} : Finset (Fin 8)) (fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1)
    rw [popMean, hsum, hsum_b1_y1, hcard_b1]
    norm_num
  have hsq_b1_y1 : ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - 5 / 2) ^ 2) = 5 := by
    rw [show ({4, 5, 6, 7} : Finset (Fin 8)) = insert 4 {5, 6, 7} from rfl, Finset.sum_insert (by decide), show ({5, 6, 7} : Finset (Fin 8)) = insert 5 {6, 7} from rfl, Finset.sum_insert (by decide), show ({6, 7} : Finset (Fin 8)) = insert 6 {7} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp
    norm_num
  have hvar_b1_y1 : popVar (((fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1) ∘ Subtype.val : ↥(({4, 5, 6, 7} : Finset (Fin 8))) → ℝ)) = 5 / 3 := by
    have hsum : (∑ x : ↥(({4, 5, 6, 7} : Finset (Fin 8))), (((((fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1) ∘ Subtype.val) x - 5 / 2) ^ 2))) = ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - 5 / 2) ^ 2) :=
      Finset.sum_coe_sort ({4, 5, 6, 7} : Finset (Fin 8)) (fun i => (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - 5 / 2) ^ 2))
    rw [popVar, hmean_b1_y1]
    simp only [Function.comp_apply] at hsum ⊢
    rw [hsum, hsq_b1_y1, hcard_b1]
    norm_num
  have hsum_b1_tau : ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i)) = 4 := by
    rw [show ({4, 5, 6, 7} : Finset (Fin 8)) = insert 4 {5, 6, 7} from rfl, Finset.sum_insert (by decide), show ({5, 6, 7} : Finset (Fin 8)) = insert 5 {6, 7} from rfl, Finset.sum_insert (by decide), show ({6, 7} : Finset (Fin 8)) = insert 6 {7} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp
    norm_num
  have hmean_b1_tau : popMean (fun i : ↥(({4, 5, 6, 7} : Finset (Fin 8))) => (fun j => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) j + 1) i - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i) = 1 := by
    have hsum : (∑ x : ↥(({4, 5, 6, 7} : Finset (Fin 8))), ((fun j => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) j + 1) x - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) x)) = ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i)) :=
      Finset.sum_coe_sort ({4, 5, 6, 7} : Finset (Fin 8)) (fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i)
    rw [popMean, hsum, hsum_b1_tau, hcard_b1]
    norm_num
  have hsq_b1_tau : ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i - 1) ^ 2) = 0 := by
    rw [show ({4, 5, 6, 7} : Finset (Fin 8)) = insert 4 {5, 6, 7} from rfl, Finset.sum_insert (by decide), show ({5, 6, 7} : Finset (Fin 8)) = insert 5 {6, 7} from rfl, Finset.sum_insert (by decide), show ({6, 7} : Finset (Fin 8)) = insert 6 {7} from rfl, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp
  have hvar_b1_tau : popVar (fun i : ↥(({4, 5, 6, 7} : Finset (Fin 8))) => (fun j => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) j + 1) i - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i) = 0 := by
    have hsum : (∑ x : ↥(({4, 5, 6, 7} : Finset (Fin 8))), (((fun j => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) j + 1) x - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) x - 1) ^ 2)) = ∑ i ∈ ({4, 5, 6, 7} : Finset (Fin 8)), (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i - 1) ^ 2) :=
      Finset.sum_coe_sort ({4, 5, 6, 7} : Finset (Fin 8)) (fun i => (((![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1 - (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i - 1) ^ 2))
    rw [popVar, hmean_b1_tau]
    simp only [] at hsum ⊢
    rw [hsum, hsq_b1_tau, hcard_b1]
    norm_num
  have hn0 : (((![2, 2] : Fin 2 → ℕ)) 0) = 2 := by decide
  have hn1 : (((![2, 2] : Fin 2 → ℕ)) 1) = 2 := by decide
  have hcard0 : ({0, 1, 2, 3} : Finset (Fin 8)).card = 4 := by decide
  have hcard1 : ({4, 5, 6, 7} : Finset (Fin 8)).card = 4 := by decide
  have hL : (∫ S, blockNeyman (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ)
        (fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1)
        (![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8)) S
      ∂(blockRandomization 2
        (![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8))
        (![2, 2] : Fin 2 → ℕ))) = 5 / 6 := by
    rw [integral_blockNeyman _ _ _ _ (by decide) (by decide), Fin.sum_univ_two, hblk0, hblk1, hn0, hn1, hcard0, hcard1, hvar_b0_y1, hvar_b0_y0, hvar_b1_y1, hvar_b1_y0]
    simp only [Fintype.card_fin]
    norm_num
  have hR : ProbabilityTheory.variance
      (blockContrast (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ)
        (fun i => (![0, 1, 2, 3, 0, 1, 2, 3] : Fin 8 → ℝ) i + 1)
        (![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8)))
      (blockRandomization 2
        (![{0, 1, 2, 3}, {4, 5, 6, 7}] : Fin 2 → Finset (Fin 8))
        (![2, 2] : Fin 2 → ℕ)) = 5 / 6 := by
    rw [variance_blockContrast _ _ _ _ (by decide) (by decide), Fin.sum_univ_two, hblk0, hblk1, hn0, hn1, hcard0, hcard1, hvar_b0_y1, hvar_b0_y0, hvar_b0_tau, hvar_b1_y1, hvar_b1_y0, hvar_b1_tau]
    simp only [Fintype.card_fin]
    norm_num
  rw [hL, hR]

/-- Arm of size one: the population variance identity applies directly at
`n b = 1` (one-per-arm hypotheses `1 ≤ 1`, `1 + 1 ≤ 2` hold by `decide`), so
this example is a direct instance of `variance_blockContrast`. The next
example shows the estimator hypotheses fail for the same setup, so
`integral_blockNeyman` does not apply there. -/
example (y₀ y₁ : Fin 4 → ℝ) :
    ProbabilityTheory.variance
        (blockContrast y₀ y₁ ![{0, 1}, {2, 3}])
        (blockRandomization 2 ![{0, 1}, {2, 3}] ![1, 1]) =
      ∑ b, ((((![{0, 1}, {2, 3}] : Fin 2 → Finset (Fin 4)) b).card : ℝ) /
        Fintype.card (Fin 4)) ^ 2 *
        (popVar ((y₁ ∘ Subtype.val :
            ↥((![{0, 1}, {2, 3}] : Fin 2 → Finset (Fin 4)) b) → ℝ)) /
            ((![1, 1] : Fin 2 → ℕ) b : ℝ) +
          popVar ((y₀ ∘ Subtype.val :
            ↥((![{0, 1}, {2, 3}] : Fin 2 → Finset (Fin 4)) b) → ℝ)) /
            ((((![{0, 1}, {2, 3}] : Fin 2 → Finset (Fin 4)) b).card : ℝ) -
              ((![1, 1] : Fin 2 → ℕ) b : ℝ)) -
          popVar (fun i :
            ↥((![{0, 1}, {2, 3}] : Fin 2 → Finset (Fin 4)) b) => y₁ i - y₀ i) /
            (((![{0, 1}, {2, 3}] : Fin 2 → Finset (Fin 4)) b).card : ℝ)) := by
  exact variance_blockContrast y₀ y₁ _ _ (by decide) (by decide)

/-- Estimator hypotheses fail at arm size one: `2 ≤ n b` is false for
`n = ![1, 1]`, so `integral_blockNeyman` has no instance here; block `0`
witnesses the failure (`1 + 2 = 3 > card {0, 1} = 2`). -/
example : ¬ ∀ b : Fin 2, 2 ≤ (![1, 1] : Fin 2 → ℕ) b ∧
    (![1, 1] : Fin 2 → ℕ) b + 2 ≤
      (((![{0, 1}, {2, 3}] : Fin 2 → Finset (Fin 4)) b).card) := by
  decide

end MathlibExtTest.Probability.Statistics.Experiment
