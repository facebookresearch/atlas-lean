/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.ConcaveScore

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Real
open MathlibExt.Probability.Statistics.ConcaveScore

namespace MathlibExtTest.Probability.Statistics.ConcaveScore

/-! ### The quadratic criterion

`ℓ(b) = -(s / 2) (b - a)²` has score `U(b) = -s (b - a)` and information `-U' = s`. It is a
concave score criterion exactly when `s ≥ 0`. -/

/-- The quadratic criterion with curvature `s` and center `a`. -/
noncomputable def quadCrit (s a b : ℝ) : ℝ := -(s / 2) * (b - a) ^ 2

/-- Its score. -/
noncomputable def quadScore (s a b : ℝ) : ℝ := -s * (b - a)

theorem hasDerivAt_quadCrit (s a b : ℝ) : HasDerivAt (quadCrit s a) (quadScore s a b) b := by
  show HasDerivAt (fun b => -(s / 2) * (b - a) ^ 2) (-s * (b - a)) b
  convert (((hasDerivAt_id' b).sub_const a).pow 2).const_mul (-(s / 2)) using 1
  ring

theorem hasDerivAt_quadScore (s a b : ℝ) : HasDerivAt (quadScore s a) (-s) b := by
  show HasDerivAt (fun b => -s * (b - a)) (-s) b
  simpa using ((hasDerivAt_id' b).sub_const a).const_mul (-s)

/-- **Concave instance**, from the definitions: for `s ≥ 0` the quadratic criterion is a
concave score criterion with constant information `s`. -/
theorem isConcaveScore_quad {s : ℝ} (a : ℝ) (hs : 0 ≤ s) :
    IsConcaveScore (quadCrit s a) (quadScore s a) (fun _ => s) :=
  ⟨hasDerivAt_quadCrit s a, hasDerivAt_quadScore s a, fun _ => hs⟩

/-! ### Deterministic machinery on a concrete concave criterion (`s = 1`, `a = 1/4`) -/

/-- The root of the score is a maximizer, through `isMaxOn_of_score_eq_zero`. -/
example : IsMaxOn (quadCrit 1 (1 / 4)) Set.univ (1 / 4) :=
  (isConcaveScore_quad (1 / 4) zero_le_one).isMaxOn_of_score_eq_zero (by norm_num [quadScore])

/-- Cross-check from the definition: `1/4` does maximize `-(b - 1/4)² / 2`. -/
example (b : ℝ) : quadCrit 1 (1 / 4) b ≤ quadCrit 1 (1 / 4) (1 / 4) := by
  simp only [quadCrit]
  nlinarith [sq_nonneg (b - 1 / 4)]

/-- `score_eq_zero_and_abs_sub_lt` with `β₀ = 0`, `ε = 1`, `m = 1/2`: the information `1`
exceeds `m`, and `|U(0)| = 1/4 < ε m`, so every maximizer selection is a root within `1` of
`0`; the root is computed to be `1/4`. -/
example (bh : ℝ) (hbh : (∃ b, IsMaxOn (quadCrit 1 (1 / 4)) Set.univ b) →
    IsMaxOn (quadCrit 1 (1 / 4)) Set.univ bh) : bh = 1 / 4 ∧ |bh - 0| < 1 := by
  obtain ⟨hroot, hlt⟩ := (isConcaveScore_quad (1 / 4) zero_le_one).score_eq_zero_and_abs_sub_lt
    (β₀ := 0) (m := 1 / 2) one_pos (fun _ _ => by norm_num) (by norm_num [quadScore, abs_of_pos])
    hbh
  refine ⟨?_, hlt⟩
  simp only [quadScore] at hroot
  linarith

/-- The mean value form on the concrete criterion: `U(1) - U(0) = -I(c) (1 - 0)` with `I ≡ 1`. -/
example : quadScore 1 (1 / 4) 1 - quadScore 1 (1 / 4) 0 = -1 * (1 - 0) := by
  obtain ⟨c, -, hc⟩ := (isConcaveScore_quad (1 / 4) zero_le_one).exists_score_sub_eq 0 1
  exact hc

/-! ### Random concave criteria: the asymptotic theorems on a concrete sequence

On the one-point space, `ℓₙ = quadCrit n 0` (curvature `n`, center `β₀ = 0`): score
`Uₙ(b) = -n b`, information `Iₙ ≡ n`, so `Uₙ(0) / √n = 0` and `Iₙ / n = 1` for `n > 0`. Every
hypothesis is discharged from the definitions, with `i ≡ 1`, `v = 1`, `r = 1`. -/

theorem hC_seq : ∀ (n : ℕ) (_ : Unit),
    IsConcaveScore (quadCrit n 0) (quadScore n 0) (fun _ => (n : ℝ)) :=
  fun n _ => isConcaveScore_quad 0 (Nat.cast_nonneg n)

theorem hscore_seq : TendstoInDistribution
    (fun (n : ℕ) (_ : Unit) ↦ quadScore n 0 0 / √(n : ℝ)) atTop
    (fun _ => (0 : ℝ)) (fun _ ↦ Measure.dirac ()) (Measure.dirac ()) := by
  simp only [quadScore, sub_self, mul_zero, zero_div]
  exact tendstoInDistribution_const aemeasurable_const

theorem hinfo_seq : ∀ η > 0, Tendsto (fun n : ℕ => Measure.dirac () {_ω : Unit |
    ∃ b ∈ Set.Icc ((0 : ℝ) - 1) (0 + 1), η ≤ |(n : ℝ) / n - (fun _ => (1 : ℝ)) b|})
    atTop (𝓝 0) := by
  intro η hη
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  symm
  convert measure_empty (μ := Measure.dirac ())
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ω ⟨b, -, hb⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_self hn', sub_self, abs_zero] at hb
  linarith

theorem hiv_seq : (fun _ => (1 : ℝ)) 0 = ((1 : NNReal) : ℝ) := by simp

/-- The maximizer selection `βhat ≡ 0` satisfies the estimator hypothesis (non-vacuity). -/
theorem hβhat_seq : ∀ (n : ℕ) (ω : Unit), (∃ b, IsMaxOn (quadCrit n 0) Set.univ b) →
    IsMaxOn (quadCrit n 0) Set.univ ((fun _ _ => (0 : ℝ)) n ω) :=
  fun n ω _ => (hC_seq n ω).isMaxOn_of_score_eq_zero (by simp [quadScore])

/-- Existence of a maximizer with probability tending to one. -/
example : Tendsto (fun n : ℕ => Measure.dirac ()
    {_ω : Unit | ¬ ∃ b, IsMaxOn (quadCrit n 0) Set.univ b}) atTop (𝓝 0) :=
  tendsto_measure_not_exists_isMaxOn (I := fun n _ _ => (n : ℝ)) (i := fun _ => 1) (v := 1)
    (r := 1) hC_seq one_ne_zero hscore_seq continuousAt_const hiv_seq hinfo_seq one_pos

/-- Consistency for every maximizer selection. -/
example (βhat : ℕ → Unit → ℝ) (hβhat : ∀ (n : ℕ) ω, (∃ b, IsMaxOn (quadCrit n 0) Set.univ b) →
    IsMaxOn (quadCrit n 0) Set.univ (βhat n ω)) :
    TendstoInMeasure (Measure.dirac ()) βhat atTop (fun _ => (0 : ℝ)) :=
  tendstoInMeasure_argmax (I := fun n _ _ => (n : ℝ)) (i := fun _ => 1) (v := 1) (r := 1)
    hC_seq one_ne_zero hβhat hscore_seq continuousAt_const hiv_seq hinfo_seq one_pos

/-- The limit law `√n (βhat n - 0) ⟶ 0 / 1`, for the concrete selection `βhat ≡ 0`. -/
example : TendstoInDistribution (fun (n : ℕ) (_ : Unit) ↦ √(n : ℝ) * ((0 : ℝ) - 0)) atTop
    (fun _ => (0 : ℝ) / ((1 : NNReal) : ℝ)) (fun _ ↦ Measure.dirac ()) (Measure.dirac ()) :=
  tendstoInDistribution_argmax (I := fun n _ _ => (n : ℝ)) (i := fun _ => 1) (v := 1) (r := 1)
    hC_seq one_ne_zero hβhat_seq (fun _ => aemeasurable_const) hscore_seq continuousAt_const
    hiv_seq hinfo_seq one_pos

/-- The normalized information at the estimator converges to `v = 1`. -/
example : TendstoInMeasure (Measure.dirac ()) (fun (n : ℕ) (_ : Unit) => (n : ℝ) / n) atTop
    (fun _ => ((1 : NNReal) : ℝ)) :=
  tendstoInMeasure_info_argmax (I := fun n _ _ => (n : ℝ)) (i := fun _ => 1) (v := 1) (r := 1)
    (βhat := fun _ _ => 0) hC_seq one_ne_zero hβhat_seq hscore_seq continuousAt_const hiv_seq
    hinfo_seq one_pos

/-- `tendstoInMeasure_div_sqrt` on the constant sequence `Xₙ ≡ 1`: `1 / √n → 0`. -/
example : TendstoInMeasure (Measure.dirac ()) (fun (n : ℕ) (_ : Unit) => (1 : ℝ) / √(n : ℝ))
    atTop 0 :=
  tendstoInMeasure_div_sqrt (X := fun _ _ => (1 : ℝ)) (P' := Measure.dirac ())
    (tendstoInDistribution_const aemeasurable_const)

/-! ### A non-concave criterion: the theorems do not apply

For `s < 0` the quadratic criterion is convex. Its score `-s (b - a)` has derivative `-s`, so the
only candidate information is `I ≡ s < 0`, and **no** `I` makes it a concave score criterion.
The conclusion of `isMaxOn_of_score_eq_zero` indeed fails: the root `a` of the score is a
minimizer, not a maximizer. -/

/-- No information function makes a convex quadratic a concave score criterion. -/
theorem not_isConcaveScore_quad {s : ℝ} (a : ℝ) (hs : s < 0) (I : ℝ → ℝ) :
    ¬ IsConcaveScore (quadCrit s a) (quadScore s a) I := fun h => by
  have hI : -I 0 = -s := (h.hasDerivAt_score 0).unique (hasDerivAt_quadScore s a 0)
  linarith [h.info_nonneg 0]

/-- For `s = -1`, `a = 0`: the score vanishes at `0`, yet `0` is not a maximizer, since
`ℓ(1) = 1/2 > 0 = ℓ(0)`, computed from the definition. -/
example : quadScore (-1) 0 0 = 0 ∧ ¬ IsMaxOn (quadCrit (-1) 0) Set.univ 0 := by
  refine ⟨by simp [quadScore], fun h => ?_⟩
  have h1 : quadCrit (-1) 0 1 ≤ quadCrit (-1) 0 0 := h (Set.mem_univ 1)
  norm_num [quadCrit] at h1

example : ¬ IsConcaveScore (quadCrit (-1) 0) (quadScore (-1) 0) (fun _ => -1) :=
  not_isConcaveScore_quad 0 (by norm_num) _

#print axioms IsConcaveScore.antitone_score
#print axioms IsConcaveScore.isMaxOn_of_score_eq_zero
#print axioms IsConcaveScore.score_add_neg_and_sub_pos
#print axioms IsConcaveScore.score_eq_zero_and_abs_sub_lt
#print axioms IsConcaveScore.abs_sqrt_mul_sub_sub_le
#print axioms tendstoInMeasure_div_sqrt
#print axioms tendsto_measure_not_exists_isMaxOn
#print axioms tendstoInMeasure_argmax
#print axioms tendstoInDistribution_argmax
#print axioms tendstoInMeasure_info_argmax
#print axioms isConcaveScore_quad
#print axioms not_isConcaveScore_quad

end MathlibExtTest.Probability.Statistics.ConcaveScore
