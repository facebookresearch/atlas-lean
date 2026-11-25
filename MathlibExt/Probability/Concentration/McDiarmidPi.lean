/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.SubGaussian

/-!
# McDiarmid's inequality for product probability measures

Let `μ i` be probability measures on measurable spaces `Ω i`, `i : Fin n`, and let
`f : (∀ i, Ω i) → ℝ` be measurable with bounded differences: changing the `i`-th coordinate
changes `f` by at most `c i`. McDiarmid's bounded-differences inequality says that `f` is
concentrated around its mean under the product measure `Measure.pi μ`:

* `ProbabilityTheory.hasSubgaussianMGF_sub_integral_of_bounded_differences`: `f - E[f]` has a
  sub-Gaussian moment-generating function with parameter `∑ i, c i ^ 2 / 4`;
* `ProbabilityTheory.measureReal_sub_integral_ge_le_of_bounded_differences` and
  `ProbabilityTheory.measureReal_integral_sub_ge_le_of_bounded_differences`: for `ε ≥ 0`, the
  upper and lower tails `P(f - E[f] ≥ ε)` and `P(E[f] - f ≥ ε)` are at most
  `exp (-2 ε ^ 2 / ∑ i, c i ^ 2)`.

Along the way, `ProbabilityTheory.abs_sub_le_sum_of_bounded_differences` shows that a function
with bounded differences is bounded: `|f x - f y| ≤ ∑ i, c i`.

The finite-space versions are `MathlibExt.Probability.McDiarmid.mcdiarmid_one_sided_finite_iid`
and `mcdiarmid_product`; the results here hold for arbitrary probability spaces, with the
moment-generating function bound of Mathlib's `HasSubgaussianMGF`.

## Proof outline

The proof is by induction on `n`, splitting off the first coordinate with
`MeasurableEquiv.piFinSuccAbove`. Writing `x = (a, r)` and `g r = ∫ f (a, r) dμ₀(a)`, for each
`r` the function `a ↦ f (a, r)` takes values in an interval of length `c 0`, so Hoeffding's lemma
(`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`) bounds `∫ exp (t (f (a, r) - g r)) dμ₀(a)` by
`exp (c 0 ^ 2 t ^ 2 / 8)`. The function `g` of the remaining coordinates has the same mean as `f`
and bounded differences `c (Fin.succ j)`, so the induction hypothesis applies to it, and Fubini's
theorem combines the two bounds. This is the martingale argument of McDiarmid, with the
conditional expectations written as partial integrals of the product measure.

## References

* C. McDiarmid, *On the method of bounded differences*, Surveys in Combinatorics 1989,
  London Mathematical Society Lecture Note Series 141, Cambridge University Press, 1989,
  148–188.
* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge
  University Press, 2019, §2.2 (the bounded differences inequality).
-/

@[expose] public section

open MeasureTheory Real

open scoped NNReal

namespace ProbabilityTheory

section BoundedDifferences

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} {f : (∀ i, Ω i) → ℝ}
  {c : ι → ℝ}

/-- **Functions with bounded differences are bounded.** Let $\iota$ be a finite type and let
$f : \prod_{i \in \iota} \Omega_i \to \mathbb{R}$ be such that $|f(x') - f(x)| \le c_i$ whenever
$x'$ is obtained from $x$ by changing its $i$-th coordinate only. Then
$|f(x) - f(y)| \le \sum_{i \in \iota} c_i$ for all points $x$ and $y$: changing the coordinates
of $x$ one at a time leads to $y$. -/
theorem abs_sub_le_sum_of_bounded_differences
    (hfc : ∀ x i y, |f (Function.update x i y) - f x| ≤ c i) (x y : ∀ i, Ω i) :
    |f x - f y| ≤ ∑ i, c i := by
  suffices h : ∀ s : Finset ι, ∀ x y : ∀ i, Ω i, (∀ j ∉ s, x j = y j) →
      |f x - f y| ≤ ∑ i ∈ s, c i from h Finset.univ x y fun j hj => absurd (Finset.mem_univ j) hj
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro x y hxy
    rw [funext fun j => hxy j (Finset.notMem_empty j), sub_self, abs_zero, Finset.sum_empty]
  | insert i s hi ih =>
    intro x y hxy
    have hz : ∀ j ∉ s, Function.update x i (y i) j = y j := by
      intro j hj
      rcases eq_or_ne j i with rfl | hji
      · simp
      · rw [Function.update_of_ne hji]
        exact hxy j (by simp [hji, hj])
    rw [Finset.sum_insert hi]
    calc |f x - f y| ≤ |f x - f (Function.update x i (y i))| +
          |f (Function.update x i (y i)) - f y| := abs_sub_le _ _ _
      _ ≤ c i + ∑ i ∈ s, c i := by
        gcongr
        · rw [abs_sub_comm]
          exact hfc x i (y i)
        · exact ih _ _ hz

end BoundedDifferences

section Integrability

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {g : α → ℝ} {M : ℝ}

/-- A bounded measurable real function is integrable for a finite measure. -/
private lemma integrable_of_abs_le (hg : Measurable g) (hgM : ∀ x, |g x| ≤ M) :
    Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => (Real.norm_eq_abs _).trans_le (hgM x))

/-- The exponential of a multiple of a bounded measurable real function is integrable for a finite
measure. -/
private lemma integrable_exp_mul_sub_of_abs_le (hg : Measurable g) (hgM : ∀ x, |g x| ≤ M)
    (t m : ℝ) : Integrable (fun x => exp (t * (g x - m))) μ := by
  refine Integrable.of_bound (by fun_prop) (exp (|t| * (M + |m|)))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_exp]
  calc t * (g x - m) ≤ |t * (g x - m)| := le_abs_self _
    _ = |t| * |g x - m| := abs_mul _ _
    _ ≤ |t| * (M + |m|) := by
      gcongr
      exact (abs_sub _ _).trans (by linarith [hgM x])

/-- The integral of a real function bounded by `M` for a probability measure is bounded by `M`. -/
private lemma abs_integral_le_of_abs_le [IsProbabilityMeasure μ] (hgM : ∀ x, |g x| ≤ M) :
    |∫ x, g x ∂μ| ≤ M := by
  simpa [probReal_univ] using
    norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall fun x => (Real.norm_eq_abs (g x)).trans_le (hgM x))

end Integrability

/-- One step of the martingale argument: integrating out the first factor of a product of
probability measures. If `a ↦ F (a, b)` takes values in an interval of length `c` for each `b`,
Hoeffding's lemma bounds the moment-generating function of `F` by `exp (c ^ 2 t ^ 2 / 8)` times
that of the partial integral `b ↦ ∫ F (a, b) dμ(a)`. -/
private lemma integral_exp_mul_sub_integral_prod_le {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {F : α × β → ℝ} (hF : Measurable F) {M : ℝ}
    (hFM : ∀ p, |F p| ≤ M) {c : ℝ≥0} (hFc : ∀ a a' b, F (a, b) - F (a', b) ≤ c) (t : ℝ) :
    ∫ p, exp (t * (F p - ∫ q, F q ∂(μ.prod ν))) ∂(μ.prod ν) ≤
      exp ((c : ℝ) ^ 2 * t ^ 2 / 8) *
        ∫ b, exp (t * (∫ a, F (a, b) ∂μ - ∫ q, F q ∂(μ.prod ν))) ∂ν := by
  set m := ∫ q, F q ∂(μ.prod ν)
  have hα : Nonempty α := μ.nonempty_of_neZero
  -- the partial integral `G` and its bound
  set G : β → ℝ := fun b => ∫ a, F (a, b) ∂μ with hG
  have hGmeas : Measurable G := hF.stronglyMeasurable.integral_prod_left'.measurable
  have hGM : ∀ b, |G b| ≤ M := fun b => abs_integral_le_of_abs_le (μ := μ) fun a => hFM (a, b)
  -- Hoeffding's lemma on each fibre
  have hfibre : ∀ b, ∫ a, exp (t * (F (a, b) - G b)) ∂μ ≤ exp ((c : ℝ) ^ 2 * t ^ 2 / 8) := by
    intro b
    have hFb : Measurable fun a => F (a, b) := hF.comp measurable_prodMk_right
    have hbdd : BddBelow (Set.range fun a => F (a, b)) :=
      ⟨-M, by rintro _ ⟨a, rfl⟩; linarith [(abs_le.1 (hFM (a, b))).1]⟩
    have hIcc : ∀ a, F (a, b) ∈ Set.Icc (⨅ a', F (a', b)) ((⨅ a', F (a', b)) + c) := by
      intro a
      refine ⟨ciInf_le hbdd a, ?_⟩
      have : F (a, b) - c ≤ ⨅ a', F (a', b) :=
        le_ciInf fun a' => by linarith [hFc a a' b]
      linarith
    have h := (hasSubgaussianMGF_of_mem_Icc (μ := μ) hFb.aemeasurable
      (Filter.Eventually.of_forall hIcc)).mgf_le t
    refine h.trans_eq ?_
    congr 1
    simp only [add_sub_cancel_left, NNReal.coe_pow, NNReal.coe_div, coe_nnNorm, Real.norm_eq_abs,
      NNReal.abs_eq, NNReal.coe_ofNat]
    ring
  have hint : Integrable (fun p => exp (t * (F p - m))) (μ.prod ν) :=
    integrable_exp_mul_sub_of_abs_le hF hFM t m
  rw [integral_prod_symm _ hint, ← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun b =>
    integral_nonneg fun a => (exp_pos _).le)
    ((integrable_exp_mul_sub_of_abs_le hGmeas hGM t m).const_mul _)
    (Filter.Eventually.of_forall fun b => ?_)
  have hsplit : ∀ a, exp (t * (F (a, b) - m)) = exp (t * (G b - m)) * exp (t * (F (a, b) - G b)) :=
    fun a => by rw [← exp_add]; ring_nf
  dsimp only
  simp_rw [hsplit, integral_const_mul]
  rw [mul_comm (exp ((c : ℝ) ^ 2 * t ^ 2 / 8))]
  exact mul_le_mul_of_nonneg_left (hfibre b) (exp_pos _).le

/-- The moment-generating function bound behind McDiarmid's inequality, by induction on the number
of coordinates. -/
private lemma integral_exp_mul_sub_integral_pi_le : ∀ (n : ℕ) {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ i, Ω i) → ℝ) (c : Fin n → ℝ≥0) (M : ℝ), Measurable f → (∀ x, |f x| ≤ M) →
    (∀ x i y, |f (Function.update x i y) - f x| ≤ c i) → ∀ t : ℝ,
    ∫ x, exp (t * (f x - ∫ y, f y ∂Measure.pi μ)) ∂Measure.pi μ ≤
      exp ((∑ i, (c i : ℝ) ^ 2) * t ^ 2 / 8)
  | 0, Ω, _, μ, _, f, c, M, hf, hfM, hfc, t => by
    have hconst : ∀ x, f x = f default := fun x => congrArg f (Subsingleton.elim x default)
    simp [hconst]
  | n + 1, Ω, _, μ, _, f, c, M, hf, hfM, hfc, t => by
    set e := MeasurableEquiv.piFinSuccAbove Ω 0
    have he := measurePreserving_piFinSuccAbove μ 0
    set ν := Measure.pi fun j => μ (Fin.succAbove 0 j)
    set F : Ω 0 × (∀ j, Ω (Fin.succAbove 0 j)) → ℝ := fun p => f (e.symm p) with hF
    have hfF : ∀ x, f x = F (e x) := fun x => by
      simp only [hF, MeasurableEquiv.symm_apply_apply]
    have hsymm : ∀ a r, e.symm (a, r) = Fin.insertNth 0 a r := fun _ _ => rfl
    have hFmeas : Measurable F := hf.comp e.symm.measurable
    have hFM : ∀ p, |F p| ≤ M := fun p => hfM _
    have hFc : ∀ a a' r, F (a, r) - F (a', r) ≤ c 0 := by
      intro a a' r
      have h := hfc (e.symm (a, r)) 0 a'
      simp only [hsymm, Fin.update_insertNth] at h
      simp only [hF, hsymm]
      rw [abs_sub_comm] at h
      exact (le_abs_self _).trans h
    -- transfer the integrals to the product `μ 0 × ν`
    have hmean : ∫ y, f y ∂Measure.pi μ = ∫ q, F q ∂((μ 0).prod ν) := by
      simp_rw [hfF]
      exact he.integral_comp' F
    have hlhs : ∫ x, exp (t * (f x - ∫ y, f y ∂Measure.pi μ)) ∂Measure.pi μ =
        ∫ p, exp (t * (F p - ∫ q, F q ∂((μ 0).prod ν))) ∂((μ 0).prod ν) := by
      rw [hmean]
      simp_rw [hfF]
      exact he.integral_comp' (fun p => exp (t * (F p - ∫ q, F q ∂((μ 0).prod ν))))
    -- the partial integral `G` over the first coordinate
    set G : (∀ j, Ω (Fin.succAbove 0 j)) → ℝ := fun r => ∫ a, F (a, r) ∂(μ 0) with hG
    have hGmeas : Measurable G := hFmeas.stronglyMeasurable.integral_prod_left'.measurable
    have hGM : ∀ r, |G r| ≤ M := fun r =>
      abs_integral_le_of_abs_le (μ := μ 0) fun a => hFM (a, r)
    have hGmean : ∫ r, G r ∂ν = ∫ q, F q ∂((μ 0).prod ν) :=
      (integral_prod_symm F (integrable_of_abs_le hFmeas hFM)).symm
    have hGc : ∀ r j y, |G (Function.update r j y) - G r| ≤ c (Fin.succAbove 0 j) := by
      intro r j y
      have hFr : ∀ r', Integrable (fun a => F (a, r')) (μ 0) := fun r' =>
        integrable_of_abs_le (hFmeas.comp measurable_prodMk_right) fun a => hFM (a, r')
      simp only [hG]
      rw [← integral_sub (hFr _) (hFr _)]
      refine abs_integral_le_of_abs_le fun a => ?_
      have h := hfc (e.symm (a, r)) (Fin.succAbove 0 j) y
      simpa only [hF, hsymm, Fin.insertNth_update] using h
    have ih := integral_exp_mul_sub_integral_pi_le n (fun j => μ (Fin.succAbove 0 j)) G
      (fun j => c (Fin.succAbove 0 j)) M hGmeas hGM hGc t
    rw [hGmean] at ih
    rw [hlhs]
    refine (integral_exp_mul_sub_integral_prod_le hFmeas hFM hFc t).trans ?_
    refine (mul_le_mul_of_nonneg_left ih (exp_pos _).le).trans_eq ?_
    rw [← exp_add, Fin.sum_univ_succAbove (fun i => (c i : ℝ) ^ 2) 0]
    ring_nf

variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)] {μ : ∀ i, Measure (Ω i)}
  [∀ i, IsProbabilityMeasure (μ i)] {f : (∀ i, Ω i) → ℝ} {c : Fin n → ℝ≥0}

/-- **McDiarmid's inequality, sub-Gaussian form.** Let $\mu_0, \dots, \mu_{n-1}$ be probability
measures on measurable spaces $\Omega_0, \dots, \Omega_{n-1}$ and $\mu$ their product measure on
$\prod_{i<n} \Omega_i$, let $c_0, \dots, c_{n-1} \ge 0$, and let
$f : \prod_{i<n} \Omega_i \to \mathbb{R}$ be measurable with $|f(x') - f(x)| \le c_i$ whenever
$x'$ is obtained from $x$ by changing its $i$-th coordinate only. Then $f - \mathbb{E}_\mu[f]$ is
sub-Gaussian with parameter $\frac14 \sum_{i<n} c_i^2$: for every real $t$,
$e^{t (f - \mathbb{E}_\mu[f])}$ is $\mu$-integrable and
$$
\mathbb{E}_\mu\big[e^{t (f - \mathbb{E}_\mu[f])}\big] \le
  \exp\Big(\frac{t^2}{8} \sum_{i<n} c_i^2\Big).
$$
-/
theorem hasSubgaussianMGF_sub_integral_of_bounded_differences (hf : Measurable f)
    (hfc : ∀ x i y, |f (Function.update x i y) - f x| ≤ c i) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂Measure.pi μ) (∑ i, c i ^ 2 / 4)
      (Measure.pi μ) := by
  have hne : Nonempty (∀ i, Ω i) := (Measure.pi μ).nonempty_of_neZero
  obtain ⟨x₀⟩ := hne
  set M := |f x₀| + ∑ i, (c i : ℝ)
  have hfM : ∀ x, |f x| ≤ M := fun x => by
    have h := abs_sub_le_sum_of_bounded_differences (c := fun i => (c i : ℝ)) hfc x x₀
    have := abs_sub_abs_le_abs_sub (f x) (f x₀)
    simp only [M]
    linarith
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simpa only [one_mul] using
      integrable_exp_mul_sub_of_abs_le hf hfM t (∫ y, f y ∂Measure.pi μ)
  · refine (integral_exp_mul_sub_integral_pi_le n μ f c M hf hfM hfc t).trans_eq ?_
    congr 1
    push_cast
    rw [← Finset.sum_div]
    ring

/-- **McDiarmid's inequality, upper tail.** Let $\mu_0, \dots, \mu_{n-1}$ be probability
measures on measurable spaces $\Omega_0, \dots, \Omega_{n-1}$ and $\mu$ their product measure on
$\prod_{i<n} \Omega_i$, let $c_0, \dots, c_{n-1} \ge 0$, and let
$f : \prod_{i<n} \Omega_i \to \mathbb{R}$ be measurable with $|f(x') - f(x)| \le c_i$ whenever
$x'$ is obtained from $x$ by changing its $i$-th coordinate only. Then for every
$\varepsilon \ge 0$,
$$
\mu\big(\{x : f(x) - \mathbb{E}_\mu[f] \ge \varepsilon\}\big) \le
  \exp\Big(-\frac{2 \varepsilon^2}{\sum_{i<n} c_i^2}\Big),
$$
where the right-hand side is read as $1$ when every $c_i$ is $0$. -/
theorem measureReal_sub_integral_ge_le_of_bounded_differences (hf : Measurable f)
    (hfc : ∀ x i y, |f (Function.update x i y) - f x| ≤ c i) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi μ).real {x | ε ≤ f x - ∫ y, f y ∂Measure.pi μ} ≤
      exp (-2 * ε ^ 2 / ∑ i, (c i : ℝ) ^ 2) := by
  refine ((hasSubgaussianMGF_sub_integral_of_bounded_differences hf hfc).measure_ge_le
    hε).trans_eq ?_
  congr 1
  push_cast
  rw [← Finset.sum_div, show (2 : ℝ) * ((∑ i, (c i : ℝ) ^ 2) / 4) = (∑ i, (c i : ℝ) ^ 2) / 2 by
    ring, div_div_eq_mul_div]
  ring

/-- **McDiarmid's inequality, lower tail.** Let $\mu_0, \dots, \mu_{n-1}$ be probability
measures on measurable spaces $\Omega_0, \dots, \Omega_{n-1}$ and $\mu$ their product measure on
$\prod_{i<n} \Omega_i$, let $c_0, \dots, c_{n-1} \ge 0$, and let
$f : \prod_{i<n} \Omega_i \to \mathbb{R}$ be measurable with $|f(x') - f(x)| \le c_i$ whenever
$x'$ is obtained from $x$ by changing its $i$-th coordinate only. Then for every
$\varepsilon \ge 0$,
$$
\mu\big(\{x : \mathbb{E}_\mu[f] - f(x) \ge \varepsilon\}\big) \le
  \exp\Big(-\frac{2 \varepsilon^2}{\sum_{i<n} c_i^2}\Big),
$$
where the right-hand side is read as $1$ when every $c_i$ is $0$. -/
theorem measureReal_integral_sub_ge_le_of_bounded_differences (hf : Measurable f)
    (hfc : ∀ x i y, |f (Function.update x i y) - f x| ≤ c i) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi μ).real {x | ε ≤ ∫ y, f y ∂Measure.pi μ - f x} ≤
      exp (-2 * ε ^ 2 / ∑ i, (c i : ℝ) ^ 2) := by
  have h := measureReal_sub_integral_ge_le_of_bounded_differences (μ := μ) (f := fun x => -f x)
    hf.neg
    (fun x i y => by rw [← abs_neg]; simpa only [neg_sub_neg, neg_sub] using hfc x i y) hε
  simp only [integral_neg, sub_neg_eq_add, neg_add_eq_sub] at h
  exact h

end ProbabilityTheory
