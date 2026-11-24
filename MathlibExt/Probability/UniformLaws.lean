/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import MathlibExt.Probability.Concentration.McDiarmidPi

/-!
# Uniform laws of large numbers via Rademacher complexity

Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint* (Cambridge University
Press, 2019), Chapter 4, controls the uniform deviation `‖P_n - P‖_F = sup_{f ∈ F} |P_n f - P f|`
of empirical means over a function class `F` by its Rademacher complexity
`R_n(F) = E_{X, ε}[sup_{f ∈ F} |(1/n) ∑ εᵢ f(Xᵢ)|]`, where the `εᵢ` are independent uniform
signs. This module defines both quantities for a countable class, which makes the suprema
measurable, and proves, for a class of measurable functions bounded by `b` and `n ≥ 1`
independent samples from a probability measure `P`:

* `integral_uniformDeviation_le_two_mul_rademacherComplexity` (symmetrization):
  `E[‖P_n - P‖_F] ≤ 2 R_n(F)`;
* `uniformDeviation_le_two_mul_rademacherComplexity_add` (uniform law): for `b > 0` and
  `δ ≥ 0`, `‖P_n - P‖_F ≤ 2 R_n(F) + δ` with probability at least `1 - exp (-n δ² / (2 b²))`.

The signs are averaged explicitly over the `2ⁿ` sign vectors `s : Fin n → Bool`, with
`εₖ = 1` when `s k` holds and `εₖ = -1` otherwise.

Intermediate results: the uniform deviation is measurable (`measurable_uniformDeviation`), has
bounded differences `2 b / n` (`abs_uniformDeviation_update_sub_le`), and is therefore
concentrated around its mean (`uniformDeviation_le_integral_uniformDeviation_add`), by McDiarmid's
inequality for product measures
(`ProbabilityTheory.measureReal_sub_integral_ge_le_of_bounded_differences`).

## Proof outline

* Symmetrization, with a ghost sample `x'` independent of the sample `x` and with the same law.
  For each `i`, `(1/n) ∑ₖ F i (xₖ) - E[F i] = E_{x'}[(1/n) ∑ₖ (F i (xₖ) - F i (x'ₖ))]`, so
  `‖P_n - P‖_F (x) ≤ E_{x'}[D (x, x')]` with `D (x, x') = sup_i |(1/n) ∑ₖ (F i (xₖ) - F i (x'ₖ))|`,
  and `E[‖P_n - P‖_F] ≤ E[D]` by Fubini's theorem. For a sign vector `s`, exchanging `xₖ` and
  `x'ₖ` for the `k` with `εₖ = -1` preserves the law of `(x, x')` and turns `D` into
  `sup_i |(1/n) ∑ₖ εₖ (F i (xₖ) - F i (x'ₖ))|`, which is at most the sum of the signed sample
  suprema at `x` and at `x'`. Averaging over the `2ⁿ` sign vectors gives `E[D] ≤ 2 R_n(F)`.
* Uniform law. Changing one sample point changes every empirical mean by at most `2 b / n`, hence
  the uniform deviation too, so McDiarmid's inequality gives
  `P(‖P_n - P‖_F ≥ E[‖P_n - P‖_F] + δ) ≤ exp (-2 δ² / (n (2 b / n)²)) = exp (-n δ² / (2 b²))`,
  and the symmetrization bound replaces the mean by `2 R_n(F)`.

## Implementation notes

The definitions and the two theorems keep the full names they had in the former wanted module
`WantedExt/Probability/UniformLawsWanted.lean`, so their namespace still reads
`UniformLawsWanted`; the intermediate results share it.

## References

* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge
  University Press, 2019, §4.1.2 and §4.2 (the uniform law via Rademacher complexity and its
  proof).
-/

open MeasureTheory

namespace MathlibExt.Probability.UniformLawsWanted

@[expose] public section

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {ι : Type*}

/-- The uniform deviation `‖P_n - P‖_F = sup_{f ∈ F} |(1/n) ∑ₖ f(xₖ) - E_P[f]|` of the empirical
means of a sample `x : Fin n → 𝓧` of size `n ≥ 1` from their expectations under a probability
measure `P`, for a class `F = {F i | i : ι}` (Wainwright, *High-Dimensional Statistics*, 2019,
§4.1.2). For a measure of infinite mass the expectation would be read as `0`, and for an empty
sample the empirical mean would be `0`. -/
noncomputable def uniformDeviation (P : Measure 𝓧) [IsProbabilityMeasure P] (F : ι → 𝓧 → ℝ)
    {n : ℕ} (_hn : 1 ≤ n) (x : Fin n → 𝓧) : ℝ :=
  ⨆ i, |(1 / (n : ℝ)) * ∑ k, F i (x k) - ∫ y, F i y ∂P|

/-- The Rademacher complexity `R_n(F) = E_{X, ε}[sup_{f ∈ F} |(1/n) ∑ₖ εₖ f(Xₖ)|]` of a class
`F = {F i | i : ι}` for `n ≥ 1` independent samples from a probability measure `P`, the
expectation over the uniform signs being the average over the `2ⁿ` sign vectors (Wainwright,
*High-Dimensional Statistics*, 2019, §4.2). For the zero measure or an empty sample it would be
`0` for every class. -/
noncomputable def rademacherComplexity (P : Measure 𝓧) [IsProbabilityMeasure P] (F : ι → 𝓧 → ℝ)
    {n : ℕ} (_hn : 1 ≤ n) : ℝ :=
  ∫ x, ((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool,
      ⨆ i, |(1 / (n : ℝ)) * ∑ k, (if s k then (1 : ℝ) else -1) * F i (x k)|
    ∂(Measure.pi fun _ : Fin n => P)

/-! ### Auxiliary bounds -/

/-- Two suprema of real families that are bounded above and pointwise `δ`-close are `δ`-close. -/
private lemma abs_ciSup_sub_ciSup_le {g h : ι → ℝ} (hg : BddAbove (Set.range g))
    (hh : BddAbove (Set.range h)) {δ : ℝ} (hδ : 0 ≤ δ) (hgh : ∀ i, |g i - h i| ≤ δ) :
    |(⨆ i, g i) - ⨆ i, h i| ≤ δ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simpa [Real.iSup_of_isEmpty] using hδ
  rw [abs_sub_le_iff, sub_le_iff_le_add, sub_le_iff_le_add]
  exact ⟨ciSup_le fun i => by linarith [(abs_le.1 (hgh i)).2, le_ciSup hh i],
    ciSup_le fun i => by linarith [(abs_le.1 (hgh i)).1, le_ciSup hg i]⟩

/-- A family of reals bounded in absolute value by `B` is bounded above. -/
private lemma bddAbove_range_of_abs_le {g : ι → ℝ} {B : ℝ} (hg : ∀ i, |g i| ≤ B) :
    BddAbove (Set.range g) :=
  ⟨B, by rintro _ ⟨i, rfl⟩; exact (le_abs_self _).trans (hg i)⟩

/-- The supremum of a nonempty real family bounded in absolute value by `B` is bounded in absolute
value by `B`. -/
private lemma abs_ciSup_le [Nonempty ι] {g : ι → ℝ} {B : ℝ} (hg : ∀ i, |g i| ≤ B) :
    |⨆ i, g i| ≤ B := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact abs_le.2 ⟨(neg_le_of_abs_le (hg i)).trans (le_ciSup (bddAbove_range_of_abs_le hg) i),
    ciSup_le fun j => (le_abs_self _).trans (hg j)⟩

/-- The mean of `n ≥ 1` reals bounded in absolute value by `b` is bounded in absolute value by
`b`. -/
private lemma abs_one_div_mul_sum_le {n : ℕ} (hn : 1 ≤ n) {g : Fin n → ℝ} {b : ℝ}
    (hg : ∀ k, |g k| ≤ b) : |1 / (n : ℝ) * ∑ k, g k| ≤ b := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
  calc 1 / (n : ℝ) * |∑ k, g k| ≤ 1 / n * ∑ _k : Fin n, b := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hg k)
    _ = b := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- A sign `±1` does not change absolute values. -/
private lemma abs_sign_mul (s : Bool) (a : ℝ) : |(if s then (1 : ℝ) else -1) * a| = |a| := by
  cases s <;> simp

/-- A bounded measurable real function is integrable for a finite measure. -/
private lemma integrable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {g : α → ℝ} (hg : Measurable g) {B : ℝ} (hgB : ∀ x, |g x| ≤ B) :
    Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => (Real.norm_eq_abs (g x)).trans_le (hgB x))

variable {P : Measure 𝓧} [IsProbabilityMeasure P] {F : ι → 𝓧 → ℝ} {b : ℝ}

/-- The expectation of a function bounded by `b` is bounded by `b`. -/
private lemma abs_integral_le (hb : ∀ i y, |F i y| ≤ b) (i : ι) : |∫ y, F i y ∂P| ≤ b := by
  simpa [probReal_univ] using norm_integral_le_of_norm_le_const (μ := P)
    (Filter.Eventually.of_forall fun y => (Real.norm_eq_abs (F i y)).trans_le (hb i y))

/-- Each deviation of an empirical mean from its expectation is bounded by `2 b`. -/
private lemma abs_deviation_le (hb : ∀ i y, |F i y| ≤ b) {n : ℕ} (hn : 1 ≤ n)
    (x : Fin n → 𝓧) (i : ι) : |1 / (n : ℝ) * ∑ k, F i (x k) - ∫ y, F i y ∂P| ≤ b + b :=
  (abs_sub _ _).trans (add_le_add (abs_one_div_mul_sum_le hn fun k => hb i (x k))
    (abs_integral_le hb i))

/-! ### The uniform deviation -/

/-- **Measurability of the uniform deviation.** For a probability measure $P$ on $\mathcal{X}$, a
countable class $F = \{F_i : i \in I\}$ of measurable real functions on $\mathcal{X}$ and
$n \ge 1$, the uniform deviation $x \mapsto \|P_n - P\|_F$ is a measurable function of the
sample $x \in \mathcal{X}^n$. -/
theorem measurable_uniformDeviation [Countable ι] (hF : ∀ i, Measurable (F i)) {n : ℕ}
    (hn : 1 ≤ n) : Measurable (uniformDeviation P F hn) :=
  Measurable.iSup fun i => by fun_prop

/-- **Bounded differences of the uniform deviation.** For a probability measure $P$ on
$\mathcal{X}$, a class $F = \{F_i : i \in I\}$ of real functions with $|F_i| \le b$ for some
$b \ge 0$, and a sample $x \in \mathcal{X}^n$ with $n \ge 1$, replacing one point $x_k$ of the
sample by any $y \in \mathcal{X}$ changes the uniform deviation $\|P_n - P\|_F$ by at most
$2b/n$. -/
theorem abs_uniformDeviation_update_sub_le (hb0 : 0 ≤ b) (hb : ∀ i y, |F i y| ≤ b) {n : ℕ}
    (hn : 1 ≤ n) (x : Fin n → 𝓧) (k : Fin n) (y : 𝓧) :
    |uniformDeviation P F hn (Function.update x k y) - uniformDeviation P F hn x| ≤
      2 * b / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∀ i, ∑ j, F i (Function.update x k y j) - ∑ j, F i (x j) = F i y - F i (x k) := by
    intro i
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Function.update_of_ne hj]
    · simp
  refine abs_ciSup_sub_ciSup_le (bddAbove_range_of_abs_le (B := b + b) fun i => by
      rw [abs_abs]; exact abs_deviation_le hb hn _ i)
    (bddAbove_range_of_abs_le (B := b + b) fun i => by
      rw [abs_abs]; exact abs_deviation_le hb hn _ i)
    (by positivity) fun i => (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
  rw [show 1 / (n : ℝ) * ∑ j, F i (Function.update x k y j) - ∫ z, F i z ∂P -
      (1 / (n : ℝ) * ∑ j, F i (x j) - ∫ z, F i z ∂P) = 1 / (n : ℝ) * (F i y - F i (x k)) by
    rw [← hsum i]; ring, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
  calc 1 / (n : ℝ) * |F i y - F i (x k)| ≤ 1 / n * (b + b) := by
        gcongr
        exact (abs_sub _ _).trans (add_le_add (hb i y) (hb i (x k)))
    _ = 2 * b / n := by ring

/-- **Concentration of the uniform deviation** (Wainwright, *High-Dimensional Statistics*, 2019,
§4.2, the concentration step of the uniform law via Rademacher complexity): for a countable class
$F$ of measurable functions with $|f| \le b$ for some $b > 0$, every $n \ge 1$ and every
$\delta \ge 0$, with probability at least $1 - e^{-n \delta^2 / (2 b^2)}$ over $n$ independent
samples from a probability measure $P$,
$\|P_n - P\|_F \le \mathbb{E}\big[\|P_n - P\|_F\big] + \delta$. -/
theorem uniformDeviation_le_integral_uniformDeviation_add [Countable ι]
    (hF : ∀ i, Measurable (F i)) (hb0 : 0 < b) (hb : ∀ i y, |F i y| ≤ b) {n : ℕ} (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    1 - Real.exp (-(n : ℝ) * δ ^ 2 / (2 * b ^ 2)) ≤
      (Measure.pi fun _ : Fin n => P).real
        {x | uniformDeviation P F hn x ≤
          ∫ x', uniformDeviation P F hn x' ∂(Measure.pi fun _ : Fin n => P) + δ} := by
  set μ := Measure.pi fun _ : Fin n => P
  set Z := uniformDeviation P F hn
  set m := ∫ x', Z x' ∂μ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hZ : Measurable Z := measurable_uniformDeviation hF hn
  have htail := ProbabilityTheory.measureReal_sub_integral_ge_le_of_bounded_differences
    (μ := fun _ : Fin n => P) (c := fun _ => ⟨2 * b / n, by positivity⟩) hZ
    (fun x k y => abs_uniformDeviation_update_sub_le hb0.le hb hn x k y) hδ
  replace htail : μ.real {x | δ ≤ Z x - m} ≤ Real.exp (-(n : ℝ) * δ ^ 2 / (2 * b ^ 2)) := by
    refine htail.trans_eq (congrArg Real.exp ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change -2 * δ ^ 2 / ((n : ℝ) * (2 * b / n) ^ 2) = _
    field_simp
  have hmeas : MeasurableSet {x | δ ≤ Z x - m} := measurableSet_le measurable_const (hZ.sub_const _)
  calc 1 - Real.exp (-(n : ℝ) * δ ^ 2 / (2 * b ^ 2)) ≤ 1 - μ.real {x | δ ≤ Z x - m} := by
        linarith
    _ = μ.real {x | δ ≤ Z x - m}ᶜ := by rw [measureReal_compl hmeas, probReal_univ]
    _ ≤ μ.real {x | Z x ≤ m + δ} := measureReal_mono fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx ⊢
        linarith

/-! ### Symmetrization -/

/-- **Symmetrization** (Wainwright, *High-Dimensional Statistics*, 2019, §4.2, the symmetrization
step, upper bound in expectation): for a countable class of measurable functions bounded by `b` and
`n ≥ 1` independent
samples from a probability measure `P`, `E[‖P_n - P‖_F] ≤ 2 R_n(F)`. -/
theorem integral_uniformDeviation_le_two_mul_rademacherComplexity
    (P : Measure 𝓧) [IsProbabilityMeasure P] [Countable ι] (F : ι → 𝓧 → ℝ)
    (hF : ∀ i, Measurable (F i)) {b : ℝ} (hb : ∀ i y, |F i y| ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    ∫ x, uniformDeviation P F hn x ∂(Measure.pi fun _ : Fin n => P) ≤
      2 * rademacherComplexity P F hn := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [uniformDeviation, rademacherComplexity]
  set μ := Measure.pi fun _ : Fin n => P
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- the ghost deviation `D` and the signed sample suprema `S s`
  set D : (Fin n → 𝓧) × (Fin n → 𝓧) → ℝ :=
    fun p => ⨆ i, |1 / (n : ℝ) * ∑ k, (F i (p.1 k) - F i (p.2 k))| with hD
  set S : (Fin n → Bool) → (Fin n → 𝓧) → ℝ :=
    fun s x => ⨆ i, |1 / (n : ℝ) * ∑ k, (if s k then (1 : ℝ) else -1) * F i (x k)| with hS
  have hDi : ∀ (p : (Fin n → 𝓧) × (Fin n → 𝓧)) (i : ι),
      |1 / (n : ℝ) * ∑ k, (F i (p.1 k) - F i (p.2 k))| ≤ b + b := fun p i =>
    abs_one_div_mul_sum_le hn fun k => (abs_sub _ _).trans (add_le_add (hb i _) (hb i _))
  have hSi : ∀ (s : Fin n → Bool) (x : Fin n → 𝓧) (i : ι),
      |1 / (n : ℝ) * ∑ k, (if s k then (1 : ℝ) else -1) * F i (x k)| ≤ b :=
    fun s x i => abs_one_div_mul_sum_le hn fun k => by rw [abs_sign_mul]; exact hb i _
  have hDmeas : Measurable D := Measurable.iSup fun i => by fun_prop
  have hSmeas : ∀ s, Measurable (S s) := fun s => Measurable.iSup fun i => by fun_prop
  have hDb : ∀ p, |D p| ≤ b + b := fun p => abs_ciSup_le fun i => by rw [abs_abs]; exact hDi p i
  have hSb : ∀ s x, |S s x| ≤ b := fun s x => abs_ciSup_le fun i => by rw [abs_abs]; exact hSi s x i
  have hDint : Integrable D (μ.prod μ) := integrable_of_abs_le hDmeas hDb
  have hSint : ∀ s, Integrable (S s) μ := fun s => integrable_of_abs_le (hSmeas s) (hSb s)
  -- step 1: the uniform deviation at `x` is at most the mean of `D (x, ·)` over the ghost sample
  have h1 : ∀ x, uniformDeviation P F hn x ≤ ∫ x', D (x, x') ∂μ := by
    intro x
    refine ciSup_le fun i => ?_
    have hev : ∀ k, Integrable (fun x' : Fin n → 𝓧 => F i (x' k)) μ := fun k =>
      integrable_of_abs_le ((hF i).comp (measurable_pi_apply k)) fun x' => hb i (x' k)
    have hrepr : 1 / (n : ℝ) * ∑ k, F i (x k) - ∫ y, F i y ∂P =
        ∫ x', 1 / (n : ℝ) * ∑ k, (F i (x k) - F i (x' k)) ∂μ := by
      rw [integral_const_mul, integral_finsetSum (f := fun k (x' : Fin n → 𝓧) =>
        F i (x k) - F i (x' k)) _ fun k _ => (integrable_const _).sub (hev k)]
      simp_rw [integral_sub (integrable_const _) (hev _), integral_const, probReal_univ,
        one_smul]
      rw [Finset.sum_sub_distrib]
      have hcomp : ∀ k, ∫ x', F i (x' k) ∂μ = ∫ y, F i y ∂P := fun k =>
        integral_comp_eval (μ := fun _ : Fin n => P) (hF i).aestronglyMeasurable
      simp_rw [hcomp]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [hrepr]
    refine abs_integral_le_integral_abs.trans (integral_mono ?_ ?_ fun x' => ?_)
    · exact integrable_of_abs_le (by fun_prop) fun x' => by
        rw [abs_abs]; exact hDi (x, x') i
    · exact integrable_of_abs_le (hDmeas.comp measurable_prodMk_left) fun x' => hDb (x, x')
    · exact le_ciSup (bddAbove_range_of_abs_le (B := b + b) fun j => by
        rw [abs_abs]; exact hDi (x, x') j) i
  -- step 2: integrate over the sample
  have h2 : ∫ x, uniformDeviation P F hn x ∂μ ≤ ∫ p, D p ∂(μ.prod μ) := by
    rw [integral_prod D hDint]
    exact integral_mono (integrable_of_abs_le (measurable_uniformDeviation hF hn) fun x =>
      abs_ciSup_le fun i => by rw [abs_abs]; exact abs_deviation_le hb hn x i)
      hDint.integral_prod_left h1
  -- step 3: for each sign vector, exchange the coordinates of the two samples with sign `-1`
  have h3 : ∀ s : Fin n → Bool, ∫ p, D p ∂(μ.prod μ) ≤ 2 * ∫ x, S s x ∂μ := by
    intro s
    let σ : Fin n → 𝓧 × 𝓧 → 𝓧 × 𝓧 := fun k q => if s k then q else q.swap
    have hσ : ∀ k, MeasurePreserving (σ k) (P.prod P) (P.prod P) := by
      intro k
      by_cases hk : s k
      · rw [show σ k = id from funext fun q => by simp [σ, hk]]
        exact MeasurePreserving.id _
      · rw [show σ k = Prod.swap from funext fun q => by simp [σ, hk]]
        exact Measure.measurePreserving_swap
    set e := MeasurableEquiv.arrowProdEquivProdArrow 𝓧 𝓧 (Fin n)
    have he : MeasurePreserving e (Measure.pi fun _ => P.prod P) (μ.prod μ) :=
      measurePreserving_arrowProdEquivProdArrow 𝓧 𝓧 (Fin n) (fun _ => P) (fun _ => P)
    let T : (Fin n → 𝓧) × (Fin n → 𝓧) → (Fin n → 𝓧) × (Fin n → 𝓧) :=
      fun p => e (fun k => σ k (e.symm p k))
    have hT : MeasurePreserving T (μ.prod μ) (μ.prod μ) :=
      he.comp ((measurePreserving_pi _ _ hσ).comp he.symm)
    have hDT : ∀ p, D (T p) ≤ S s p.1 + S s p.2 := by
      intro p
      refine ciSup_le fun i => ?_
      have hterm : ∀ k, F i ((T p).1 k) - F i ((T p).2 k) =
          (if s k then (1 : ℝ) else -1) * F i (p.1 k) -
            (if s k then (1 : ℝ) else -1) * F i (p.2 k) := by
        intro k
        by_cases hk : s k
        · simp [T, σ, e, hk, MeasurableEquiv.arrowProdEquivProdArrow]
        · simp [T, σ, e, hk, MeasurableEquiv.arrowProdEquivProdArrow]
          ring
      simp_rw [hterm, Finset.sum_sub_distrib, mul_sub]
      exact (abs_sub _ _).trans (add_le_add
        (le_ciSup (bddAbove_range_of_abs_le (B := b) fun j => by
          rw [abs_abs]; exact hSi s p.1 j) i)
        (le_ciSup (bddAbove_range_of_abs_le (B := b) fun j => by
          rw [abs_abs]; exact hSi s p.2 j) i))
    calc ∫ p, D p ∂(μ.prod μ) = ∫ p, D (T p) ∂(μ.prod μ) := by
          conv_lhs => rw [← hT.map_eq]
          exact integral_map hT.measurable.aemeasurable
            (by rw [hT.map_eq]; exact hDmeas.aestronglyMeasurable)
      _ ≤ ∫ p, (S s p.1 + S s p.2) ∂(μ.prod μ) :=
          integral_mono (integrable_of_abs_le (hDmeas.comp hT.measurable) fun p => hDb (T p))
            (((hSint s).comp_fst μ).add ((hSint s).comp_snd μ)) hDT
      _ = 2 * ∫ x, S s x ∂μ := by
          rw [integral_add ((hSint s).comp_fst μ) ((hSint s).comp_snd μ), integral_fun_fst,
            integral_fun_snd]
          simp only [probReal_univ, one_smul]
          ring
  -- step 4: average over the sign vectors
  have hcard : ((2 : ℝ) ^ n)⁻¹ * ∑ _s : Fin n → Bool, ∫ p, D p ∂(μ.prod μ) =
      ∫ p, D p ∂(μ.prod μ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  refine h2.trans ?_
  rw [← hcard]
  unfold rademacherComplexity
  rw [integral_const_mul, integral_finsetSum _ fun s _ => hSint s]
  calc ((2 : ℝ) ^ n)⁻¹ * ∑ _s : Fin n → Bool, ∫ p, D p ∂(μ.prod μ) ≤
      ((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, 2 * ∫ x, S s x ∂μ := by
        gcongr with s
        exact h3 s
    _ = 2 * (((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, ∫ x, S s x ∂μ) := by
        rw [← Finset.mul_sum]
        ring

/-- **Uniform law via Rademacher complexity** (Wainwright, *High-Dimensional Statistics*, 2019,
§4.2, the uniform law via Rademacher complexity): for a countable class of measurable functions
with `|f| ≤ b`, every `n ≥ 1` and
every `δ ≥ 0`, with probability at least `1 - exp (-n δ² / (2 b²))` over `n` independent samples
from a probability measure `P`, `‖P_n - P‖_F ≤ 2 R_n(F) + δ`. -/
theorem uniformDeviation_le_two_mul_rademacherComplexity_add
    (P : Measure 𝓧) [IsProbabilityMeasure P] [Countable ι] (F : ι → 𝓧 → ℝ)
    (hF : ∀ i, Measurable (F i)) {b : ℝ} (hb0 : 0 < b) (hb : ∀ i y, |F i y| ≤ b) {n : ℕ}
    (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ) :
    1 - Real.exp (-(n : ℝ) * δ ^ 2 / (2 * b ^ 2)) ≤
      (Measure.pi fun _ : Fin n => P).real
        {x | uniformDeviation P F hn x ≤ 2 * rademacherComplexity P F hn + δ} := by
  refine (uniformDeviation_le_integral_uniformDeviation_add hF hb0 hb hn hδ).trans
    (measureReal_mono fun x hx => ?_)
  have hsym := integral_uniformDeviation_le_two_mul_rademacherComplexity P F hF hb hn
  simp only [Set.mem_ofPred_eq] at hx ⊢
  linarith

end

end MathlibExt.Probability.UniformLawsWanted
