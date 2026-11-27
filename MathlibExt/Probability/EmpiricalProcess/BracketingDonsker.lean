/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Probability.Moments.SubGaussian
public import MathlibExt.Probability.Statistics.MultivariateCLT

/-!
# Donsker conditions under uniform bracketing entropy

Let `X 0, X 1, …` be i.i.d. with law `μ` on `S`, and let `F : ι → S → ℝ` be a class of measurable
square-integrable functions. The empirical process is
`𝔾ₙ f = n^{-1/2} ∑_{k<n} (f (X k) - ∫ f dμ)`. A bracket `[l, u]` is a pair of measurable functions
with `l ≤ u`; it has uniform width at most `ε` if `u x - l x ≤ ε` at every point. The uniform
bracketing number `N_[](ε, F, ‖·‖_∞)` is the least number of such brackets covering `F`.

If the uniform bracketing entropy integral `∫₀¹ √(log N_[](ε, F, ‖·‖_∞)) dε` is finite, then `F`
satisfies the Donsker conditions: finite-dimensional convergence of `𝔾ₙ` to centered Gaussian
vectors, total boundedness of `F` in the standard-deviation semimetric
`ρ_μ(f, g) = √(Var_μ[f - g])`, and asymptotic uniform `ρ_μ`-equicontinuity of `𝔾ₙ` in (outer)
probability. By van der Vaart and Wellner (1996), Theorems 1.5.4 and 1.5.7, these conditions are
equivalent to weak convergence of `𝔾ₙ` in `ℓ^∞(F)` to a tight Brownian bridge; that equivalence is
not formalized here.

## Main definitions

* `IsUniformBracketCover F ε n`: `n` measurable brackets of uniform width at most `ε` cover `F`.
* `uniformBracketingNumber F ε : ℕ∞`: the uniform bracketing number, `⊤` without a finite cover.
* `uniformBracketingEntropy F ε : ℝ≥0∞`: `√(log N_[](ε, F, ‖·‖_∞))`, `⊤` without a finite cover.
* `empiricalProcess μ X n f ω`: the empirical process `𝔾ₙ f` at `ω`.
* `DonskerConditions μ P X F`: the three Donsker conditions above.

## Main statements

* `measure_exists_abs_empiricalProcess_sub_gt_le`: asymptotic equicontinuity, with a bound that
  holds for every sample size `n`.
* `exists_finset_variance_lt`: total boundedness in `ρ_μ`.
* `exists_tendstoInDistribution_empiricalProcess`: finite-dimensional convergence, from the
  multivariate central limit theorem.
* `donskerConditions_of_uniformBracketingEntropy`: the Donsker conditions under a finite uniform
  bracketing entropy integral.

## Proof

Finiteness of the entropy integral gives covers at the dyadic widths `2⁻ᵏ` with
`∑ₖ 2⁻ᵏ √(log Nₖ) < ∞` (`exists_dyadic_covers`). Each `f ∈ F` is chained through the lower ends
`lₖ f` of its brackets. A link `lₖ₊₁ f - lₖ f` is bounded by `2⁻ᵏ` and takes at most `Nₖ Nₖ₊₁`
values, so Hoeffding's inequality and a union bound control all links of level `k` at threshold
`tₖ ≍ 2⁻ᵏ (√(log Nₖ) + √(log Nₖ₊₁) + √(k + 1) + √c)`, with total failure probability `2 e⁻ᶜ`.
The remainder `f - lₖ f` lies in `[0, 2⁻ᵏ]`, so it moves `𝔾ₙ` by at most `√n 2⁻ᵏ`, which vanishes
as `k → ∞` for fixed `n`. Hence, outside one event of small probability,
`|𝔾ₙ f - 𝔾ₙ (l_q f)| ≤ ∑_{k ≥ q} tₖ` for all `f`, and this tail is small for large `q`. Two
functions `ρ_μ`-close to each other are then compared through one witness pair per pair of
level-`q` brackets; Chebyshev's inequality controls these finitely many pairs once `δ` is small.

## Scope

The brackets here have small uniform (sup-norm) width. Ossiander's theorem (van der Vaart and
Wellner, Theorem 2.5.6) needs only brackets of small `L²(μ)` width, a weaker hypothesis since
`N_[](ε, F, L²(μ)) ≤ N_[](ε, F, ‖·‖_∞)` for a probability measure `μ`; it covers, for example, the
indicators of half-lines behind the classical empirical distribution function, which have no
finite uniform bracketing at widths below `1`. Its proof replaces Hoeffding's inequality by
Bernstein's inequality with adaptive truncation, and is not formalized here.

## References

* M. Ossiander, A central limit theorem under metric entropy with `L₂` bracketing,
  Ann. Probab. 15 (1987), 897–919.
* A. W. van der Vaart and J. A. Wellner, *Weak Convergence and Empirical Processes*, Springer
  (1996), §§1.5, 2.1.2, 2.5.2 and Theorem 2.5.6.
* R. M. Dudley, Central limit theorems for empirical measures, Ann. Probab. 6 (1978), 899–929.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal

namespace MathlibExt.Probability.EmpiricalProcess.BracketingDonsker

variable {S ι Ω : Type*} [MeasurableSpace S]

/-! ### Uniform bracketing numbers -/

/-- `IsUniformBracketCover F ε n`: there are `n` brackets `[l j, u j]` of measurable functions,
each with `l j x ≤ u j x` and of uniform width `u j x - l j x ≤ ε` at every point, such that
every `F i` lies in one of them. -/
def IsUniformBracketCover (F : ι → S → ℝ) (ε : ℝ) (n : ℕ) : Prop :=
  ∃ l u : Fin n → S → ℝ, (∀ j, Measurable (l j)) ∧ (∀ j, Measurable (u j)) ∧
    (∀ j x, l j x ≤ u j x) ∧ (∀ j x, u j x - l j x ≤ ε) ∧
    ∀ i, ∃ j, ∀ x, l j x ≤ F i x ∧ F i x ≤ u j x

/-- The uniform (sup-norm) bracketing number `N_[](ε, F, ‖·‖_∞)`: the least number of brackets
of uniform width at most `ε` covering `F`, and `⊤` when no finite cover exists. -/
noncomputable def uniformBracketingNumber (F : ι → S → ℝ) (ε : ℝ) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : IsUniformBracketCover F ε n), (n : ℕ∞)

/-- The uniform bracketing entropy `√(log N_[](ε, F, ‖·‖_∞))`, valued in `ℝ≥0∞`, and `⊤` when no
finite cover exists. -/
noncomputable def uniformBracketingEntropy (F : ι → S → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (_ : IsUniformBracketCover F ε n), ENNReal.ofReal √(Real.log n)

theorem IsUniformBracketCover.mono {F : ι → S → ℝ} {ε ε' : ℝ} {n : ℕ}
    (h : IsUniformBracketCover F ε n) (hε : ε ≤ ε') : IsUniformBracketCover F ε' n := by
  obtain ⟨l, u, hl, hu, hlu, hw, hc⟩ := h
  exact ⟨l, u, hl, hu, hlu, fun j x ↦ (hw j x).trans hε, hc⟩

theorem uniformBracketingEntropy_antitone (F : ι → S → ℝ) :
    Antitone (uniformBracketingEntropy F) := fun _ _ hε ↦
  iInf_mono fun _ ↦ iInf_mono' fun h ↦ ⟨h.mono hε, le_rfl⟩

theorem uniformBracketingNumber_le {F : ι → S → ℝ} {ε : ℝ} {n : ℕ}
    (h : IsUniformBracketCover F ε n) : uniformBracketingNumber F ε ≤ n :=
  iInf₂_le n h

theorem uniformBracketingEntropy_le {F : ι → S → ℝ} {ε : ℝ} {n : ℕ}
    (h : IsUniformBracketCover F ε n) :
    uniformBracketingEntropy F ε ≤ ENNReal.ofReal √(Real.log n) :=
  iInf₂_le n h

theorem uniformBracketingNumber_eq_top_iff {F : ι → S → ℝ} {ε : ℝ} :
    uniformBracketingNumber F ε = ⊤ ↔ ∀ n, ¬ IsUniformBracketCover F ε n := by
  simp [uniformBracketingNumber]

theorem uniformBracketingEntropy_eq_top_iff {F : ι → S → ℝ} {ε : ℝ} :
    uniformBracketingEntropy F ε = ⊤ ↔ ∀ n, ¬ IsUniformBracketCover F ε n := by
  simp [uniformBracketingEntropy]

private lemma log_natCast_le_log_natCast {n m : ℕ} (h : n ≤ m) :
    Real.log n ≤ Real.log m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using Real.log_natCast_nonneg m
  · exact Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast h)

/-- A minimal cover realizes the entropy: `√(log N)` for the least admissible `N`. -/
theorem exists_isUniformBracketCover_ofReal_le {F : ι → S → ℝ} {ε : ℝ}
    (h : uniformBracketingEntropy F ε ≠ ⊤) :
    ∃ n, IsUniformBracketCover F ε n ∧
      ENNReal.ofReal √(Real.log n) ≤ uniformBracketingEntropy F ε := by
  classical
  have hex : ∃ n, IsUniformBracketCover F ε n := by
    by_contra hne
    push Not at hne
    exact h (uniformBracketingEntropy_eq_top_iff.2 hne)
  refine ⟨Nat.find hex, Nat.find_spec hex, le_iInf₂ fun m hm ↦ ?_⟩
  exact ENNReal.ofReal_le_ofReal
    (Real.sqrt_le_sqrt (log_natCast_le_log_natCast (Nat.find_min' hex hm)))

/-! ### The empirical process -/

/-- The empirical process `𝔾ₙ f = n^{-1/2} ∑_{k<n} (f (X k) - ∫ f dμ)` of the sample
`X 0, …, X (n - 1)` from `μ`, evaluated at `f`. -/
noncomputable def empiricalProcess (μ : Measure S) (X : ℕ → Ω → S) (n : ℕ) (f : S → ℝ)
    (ω : Ω) : ℝ :=
  (√n)⁻¹ * ∑ k ∈ range n, (f (X k ω) - ∫ x, f x ∂μ)

variable {μ : Measure S} {X : ℕ → Ω → S}

theorem empiricalProcess_sub {f g : S → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (n : ℕ)
    (ω : Ω) :
    empiricalProcess μ X n f ω - empiricalProcess μ X n g ω =
      empiricalProcess μ X n (f - g) ω := by
  simp only [empiricalProcess, Pi.sub_apply, integral_sub hf hg, ← mul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

theorem empiricalProcess_neg (f : S → ℝ) (n : ℕ) (ω : Ω) :
    empiricalProcess μ X n (-f) ω = -empiricalProcess μ X n f ω := by
  simp only [empiricalProcess, Pi.neg_apply, integral_neg, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- A function with values in `[0, w]` moves the empirical process by at most `√n * w`. -/
theorem abs_empiricalProcess_le [IsProbabilityMeasure μ] {h : S → ℝ} (hi : Integrable h μ)
    {w : ℝ} (h0 : ∀ x, 0 ≤ h x) (hw : ∀ x, h x ≤ w) (n : ℕ) (ω : Ω) :
    |empiricalProcess μ X n h ω| ≤ √n * w := by
  have hI0 : 0 ≤ ∫ x, h x ∂μ := integral_nonneg h0
  have hIw : ∫ x, h x ∂μ ≤ w := by
    simpa using integral_mono hi (integrable_const w) hw
  have hterm : ∀ k ∈ range n, |h (X k ω) - ∫ x, h x ∂μ| ≤ w := fun k _ ↦
    abs_sub_le_iff.2 ⟨by linarith [h0 (X k ω), hw (X k ω)], by linarith [h0 (X k ω)]⟩
  have hsum : |∑ k ∈ range n, (h (X k ω) - ∫ x, h x ∂μ)| ≤ n * w :=
    (Finset.abs_sum_le_sum_abs _ _).trans (by simpa using Finset.sum_le_sum hterm)
  rw [empiricalProcess, abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  rw [inv_mul_le_iff₀ hs]
  calc _ ≤ (n : ℝ) * w := hsum
    _ = √n * (√n * w) := by rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

omit [IsProbabilityMeasure μ] in
/-- One-sided Hoeffding bound for the empirical process at a function bounded by `c`. -/
private lemma measure_le_empiricalProcess_le (hlaw : ∀ k, HasLaw (X k) μ P)
    (hindep : iIndepFun X P) {h : S → ℝ} (hm : Measurable h) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x, |h x| ≤ c) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    P {ω | t ≤ empiricalProcess μ X n h ω} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * c ^ 2))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases ht.eq_or_lt with rfl | ht
    · simpa using prob_le_one
    · simp [empiricalProcess, not_le.2 ht]
  have hY : ∀ k, HasSubgaussianMGF (fun ω ↦ h (X k ω) - ∫ x, h x ∂μ)
      ((‖c - -c‖₊ / 2) ^ 2) P := by
    intro k
    have hmk : AEMeasurable (fun ω ↦ h (X k ω)) P := hm.comp_aemeasurable (hlaw k).aemeasurable
    have hsub := hasSubgaussianMGF_of_mem_Icc (μ := P) hmk (a := -c) (b := c)
      (ae_of_all _ fun ω ↦ abs_le.1 (hc _))
    have hint : P[fun ω ↦ h (X k ω)] = ∫ x, h x ∂μ :=
      (hlaw k).integral_comp hm.aestronglyMeasurable
    rwa [hint] at hsub
  have hind : iIndepFun (fun k ω ↦ h (X k ω) - ∫ x, h x ∂μ) P :=
    hindep.comp (fun _ x ↦ h x - ∫ y, h y ∂μ) fun _ ↦ hm.sub_const _
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hH := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind (n := n) (fun k _ ↦ hY k)
    (ε := t * √n) (by positivity)
  have hset : {ω | t ≤ empiricalProcess μ X n h ω} =
      {ω | t * √n ≤ ∑ k ∈ range n, (h (X k ω) - ∫ x, h x ∂μ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, empiricalProcess]
    rw [inv_mul_eq_div, le_div_iff₀ hs]
  have hc' : (((‖c - -c‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = c ^ 2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, sub_neg_eq_add]
    rw [abs_of_nonneg (by linarith)]
    norm_num
  rw [hset, ← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (hH.trans_eq ?_)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hc', mul_pow, Real.sq_sqrt (Nat.cast_nonneg n),
    show 2 * (n : ℝ) * c ^ 2 = n * (2 * c ^ 2) by ring,
    show -(t ^ 2 * n) = n * (-t ^ 2) by ring, mul_div_mul_left _ _ hn']

omit [IsProbabilityMeasure μ] in
/-- **Hoeffding's inequality** for the empirical process at a measurable function bounded
by `c`. -/
theorem measure_le_abs_empiricalProcess_le (hlaw : ∀ k, HasLaw (X k) μ P)
    (hindep : iIndepFun X P) {h : S → ℝ} (hm : Measurable h) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x, |h x| ≤ c) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    P {ω | t ≤ |empiricalProcess μ X n h ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * c ^ 2))) := by
  have hsub : {ω | t ≤ |empiricalProcess μ X n h ω|} ⊆
      {ω | t ≤ empiricalProcess μ X n h ω} ∪ {ω | t ≤ empiricalProcess μ X n (-h) ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union, empiricalProcess_neg] at hω ⊢
    rcases le_abs'.1 hω with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl h
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * c ^ 2))) +
        ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * c ^ 2))) := by
      gcongr
      · exact measure_le_empiricalProcess_le hlaw hindep hm hc0 hc ht n
      · exact measure_le_empiricalProcess_le hlaw hindep hm.neg hc0
          (fun x ↦ by simpa using hc x) ht n
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

omit [IsProbabilityMeasure μ] in
/-- **Chebyshev's inequality** for the empirical process at a square-integrable function. -/
theorem measure_le_abs_empiricalProcess_le_variance (hlaw : ∀ k, HasLaw (X k) μ P)
    (hindep : iIndepFun X P) {h : S → ℝ} (hm : Measurable h) (h2 : MemLp h 2 μ) {t : ℝ}
    (ht : 0 < t) (n : ℕ) :
    P {ω | t ≤ |empiricalProcess μ X n h ω|} ≤ ENNReal.ofReal (Var[h; μ] / t ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [empiricalProcess, not_le.2 ht]
  have hk2 : ∀ k, MemLp (fun ω ↦ h (X k ω)) 2 P := fun k ↦
    MemLp.comp_of_map ((hlaw k).map_eq ▸ h2) (hlaw k).aemeasurable
  set Y : Ω → ℝ := ∑ k ∈ range n, fun ω ↦ h (X k ω) with hYdef
  have hYapp : ∀ ω, Y ω = ∑ k ∈ range n, h (X k ω) := fun ω ↦ Finset.sum_apply _ _ _
  have hY2 : MemLp Y 2 P := memLp_finsetSum' _ fun k _ ↦ hk2 k
  have hEY : ∫ ω, Y ω ∂P = n * ∫ x, h x ∂μ := by
    simp_rw [hYapp]
    have hk : ∀ k, ∫ ω, h (X k ω) ∂P = ∫ x, h x ∂μ := fun k ↦
      (hlaw k).integral_comp (f := h) hm.aestronglyMeasurable
    rw [integral_finsetSum _ (fun k _ ↦ (hk2 k).integrable one_le_two)]
    simp [hk]
  have hVY : Var[Y; P] = n * Var[h; μ] := by
    rw [hYdef, IndepFun.variance_sum (fun k _ ↦ hk2 k) (fun i _ j _ hij ↦
      (hindep.comp (fun _ ↦ h) fun _ ↦ hm).indepFun hij)]
    have hvk : ∀ k, Var[fun ω ↦ h (X k ω); P] = Var[h; μ] := fun k ↦ by
      rw [← (hlaw k).map_eq, variance_map ((hlaw k).map_eq ▸ hm.aemeasurable)
        (hlaw k).aemeasurable]
      rfl
    simp [hvk]
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hset : {ω | t ≤ |empiricalProcess μ X n h ω|} =
      {ω | t * √n ≤ |Y ω - ∫ ω, Y ω ∂P|} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [hEY, hYapp]
    simp only [empiricalProcess, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, abs_mul, abs_inv,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [inv_mul_eq_div, le_div_iff₀ hs]
  rw [hset]
  refine (meas_ge_le_variance_div_sq hY2 (by positivity)).trans (le_of_eq ?_)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hVY, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), mul_comm (t ^ 2), mul_div_mul_left _ _ hn']

/-! ### Dyadic covers from a finite entropy integral -/

private lemma pairwise_disjoint_dyadic :
    Pairwise (Function.onFun Disjoint
      fun k : ℕ ↦ Set.Ioc ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2) ^ k)) := by
  refine (pairwise_disjoint_on _).2 fun m k hmk ↦ Set.disjoint_left.2 fun x hx hx' ↦ ?_
  have : ((1 : ℝ) / 2) ^ k ≤ (1 / 2) ^ (m + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmk
  linarith [hx.1, hx'.2]

/-- A finite uniform bracketing entropy integral gives covers at every dyadic width `2⁻ᵏ` whose
sizes `N k` satisfy `∑ₖ 2⁻ᵏ √(log (N k)) < ∞`. -/
theorem exists_dyadic_covers {F : ι → S → ℝ}
    (hJ : ∫⁻ ε in Set.Ioc 0 1, uniformBracketingEntropy F ε ≠ ⊤) :
    ∃ N : ℕ → ℕ, (∀ k, IsUniformBracketCover F ((1 / 2) ^ k) (N k)) ∧
      Summable fun k ↦ (1 / 2 : ℝ) ^ k * √(Real.log (N k)) := by
  set E := uniformBracketingEntropy F
  set A : ℕ → Set ℝ := fun k ↦ Set.Ioc ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2) ^ k)
  have hlow : ∀ k, ENNReal.ofReal ((1 / 2) ^ (k + 1)) * E ((1 / 2) ^ k) ≤ ∫⁻ ε in A k, E ε := by
    intro k
    calc _ = ∫⁻ _ in A k, E ((1 / 2) ^ k) := by
          rw [setLIntegral_const, Real.volume_Ioc, mul_comm]
          congr 2
          ring
      _ ≤ _ := lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).2
          (ae_of_all _ fun ε hε ↦ uniformBracketingEntropy_antitone F hε.2))
  have hsum : ∑' k, ENNReal.ofReal ((1 / 2) ^ (k + 1)) * E ((1 / 2) ^ k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hJ ?_
    calc _ ≤ ∑' k, ∫⁻ ε in A k, E ε := ENNReal.tsum_le_tsum hlow
      _ = ∫⁻ ε in ⋃ k, A k, E ε :=
          (lintegral_iUnion (fun _ ↦ measurableSet_Ioc) pairwise_disjoint_dyadic _).symm
      _ ≤ _ := lintegral_mono_set (Set.iUnion_subset fun k ↦
          Set.Ioc_subset_Ioc (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)))
  have hfin : ∀ k, E ((1 / 2) ^ k) ≠ ⊤ := fun k h ↦ by
    have := ENNReal.ne_top_of_tsum_ne_top hsum k
    rw [h, ENNReal.mul_top (by simp)] at this
    exact this rfl
  choose N hN hNle using fun k ↦ exists_isUniformBracketCover_ofReal_le (hfin k)
  refine ⟨N, hN, ?_⟩
  have hle : ∀ k, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1) * √(Real.log (N k))) ≤
      ENNReal.ofReal ((1 / 2) ^ (k + 1)) * E ((1 / 2) ^ k) := fun k ↦ by
    rw [ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact hNle k
  have hs : Summable fun k ↦ (1 / 2 : ℝ) ^ (k + 1) * √(Real.log (N k)) :=
    (ENNReal.summable_toReal (ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hle))).congr
      fun k ↦ ENNReal.toReal_ofReal (by positivity)
  convert hs.mul_left 2 using 1
  ext k
  ring

/-! ### Chaining -/

/-- Deterministic chaining: a chain `g 0, g 1, …` with links bounded by a summable `s` and
remainders `|a - g K| ≤ C 2⁻ᴷ` stays within `∑ s` of its start. -/
private lemma abs_sub_le_tsum_of_chain {a C : ℝ} {g s : ℕ → ℝ} (hs : Summable s)
    (hs0 : ∀ k, 0 ≤ s k) (hlink : ∀ k, |g (k + 1) - g k| ≤ s k)
    (hrem : ∀ K, |a - g K| ≤ C * (1 / 2) ^ K) : |a - g 0| ≤ ∑' k, s k := by
  have hK : ∀ K, |a - g 0| ≤ ∑' k, s k + C * (1 / 2) ^ K := by
    intro K
    have hsplit : a - g 0 = ∑ m ∈ range K, (g (m + 1) - g m) + (a - g K) := by
      rw [Finset.sum_range_sub]
      ring
    calc |a - g 0| ≤ |∑ m ∈ range K, (g (m + 1) - g m)| + |a - g K| := by
          rw [hsplit]
          exact abs_add_le _ _
      _ ≤ ∑ m ∈ range K, s m + C * (1 / 2) ^ K := by
          gcongr
          · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ ↦ hlink m)
          · exact hrem K
      _ ≤ _ := by
          gcongr
          exact hs.sum_le_tsum _ fun m _ ↦ hs0 m
  refine ge_of_tendsto' (x := atTop) ?_ hK
  simpa using tendsto_const_nhds.add
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul C)

/-- The chaining threshold at level `k` for covers of sizes `N`. -/
private noncomputable def chainThreshold (N : ℕ → ℕ) (c : ℝ) (k : ℕ) : ℝ :=
  (1 / 2) ^ k * √2 *
    (√(Real.log (N k)) + √(Real.log (N (k + 1))) + √((k : ℝ) + 1) + √c)

private lemma chainThreshold_nonneg (N : ℕ → ℕ) (c : ℝ) (k : ℕ) :
    0 ≤ chainThreshold N c k := by
  unfold chainThreshold
  positivity

private lemma summable_chainThreshold {N : ℕ → ℕ}
    (hN : Summable fun k ↦ (1 / 2 : ℝ) ^ k * √(Real.log (N k))) (c : ℝ) :
    Summable (chainThreshold N c) := by
  have h1 : Summable fun k ↦ (1 / 2 : ℝ) ^ k * √(Real.log (N (k + 1))) := by
    have := ((summable_nat_add_iff 1).2 hN).mul_left 2
    refine this.congr fun k ↦ ?_
    rw [pow_succ]
    ring
  have hgeo : Summable fun k : ℕ ↦ (1 / 2 : ℝ) ^ k :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hk : Summable fun k : ℕ ↦ (1 / 2 : ℝ) ^ k * √((k : ℝ) + 1) := by
    have hpow : Summable fun k : ℕ ↦ (k : ℝ) ^ 1 * (1 / 2 : ℝ) ^ k :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_) (hpow.add hgeo)
    have : √((k : ℝ) + 1) ≤ (k : ℝ) + 1 :=
      (Real.sqrt_le_left (by positivity)).2 (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    calc (1 / 2 : ℝ) ^ k * √((k : ℝ) + 1) ≤ (1 / 2) ^ k * ((k : ℝ) + 1) := by gcongr
      _ = _ := by ring
  have := ((hN.add h1).add hk |>.add (hgeo.mul_right √c)).mul_left √2
  refine this.congr fun k ↦ ?_
  simp only [chainThreshold]
  ring

/-- The real-number bound behind the union bound at one level. -/
private lemma card_mul_exp_le {a b m : ℕ} (hm : m ≤ a * b) (k : ℕ) {c t : ℝ}
    (ht : (1 / 2 : ℝ) ^ k * √2 *
      (√(Real.log a) + √(Real.log b) + √((k : ℝ) + 1) + √c) ≤ t) (hc : 0 ≤ c) :
    (m : ℝ) * (2 * Real.exp (-t ^ 2 / (2 * ((1 / 2) ^ k) ^ 2))) ≤
      (1 / 2) ^ k * Real.exp (-c) := by
  set L := Real.log a + Real.log b + ((k : ℝ) + 1) + c
  have ha := Real.log_natCast_nonneg a
  have hb := Real.log_natCast_nonneg b
  have hL : -t ^ 2 / (2 * ((1 / 2) ^ k) ^ 2) ≤ -L := by
    have hq : 0 < 2 * ((1 / 2 : ℝ) ^ k) ^ 2 := by positivity
    rw [div_le_iff₀ hq]
    set x := √(Real.log a); set y := √(Real.log b); set z := √((k : ℝ) + 1); set w := √c
    have hx : x ^ 2 = Real.log a := Real.sq_sqrt ha
    have hy : y ^ 2 = Real.log b := Real.sq_sqrt hb
    have hz : z ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hw : w ^ 2 = c := Real.sq_sqrt hc
    have hsum : L ≤ (x + y + z + w) ^ 2 := by
      have : 0 ≤ x := Real.sqrt_nonneg _
      have : 0 ≤ y := Real.sqrt_nonneg _
      have : 0 ≤ z := Real.sqrt_nonneg _
      have : 0 ≤ w := Real.sqrt_nonneg _
      simp only [L]
      nlinarith [mul_nonneg ‹0 ≤ x› ‹0 ≤ y›, mul_nonneg ‹0 ≤ x› ‹0 ≤ z›,
        mul_nonneg ‹0 ≤ x› ‹0 ≤ w›, mul_nonneg ‹0 ≤ y› ‹0 ≤ z›, mul_nonneg ‹0 ≤ y› ‹0 ≤ w›,
        mul_nonneg ‹0 ≤ z› ‹0 ≤ w›]
    have h0 : 0 ≤ (1 / 2 : ℝ) ^ k * √2 * (x + y + z + w) := by positivity
    have htsq : ((1 / 2 : ℝ) ^ k * √2 * (x + y + z + w)) ^ 2 ≤ t ^ 2 :=
      pow_le_pow_left₀ h0 ht 2
    have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hexp : ((1 / 2 : ℝ) ^ k * √2 * (x + y + z + w)) ^ 2 =
        2 * ((1 / 2) ^ k) ^ 2 * (x + y + z + w) ^ 2 := by
      rw [mul_pow, mul_pow, h2]
      ring
    nlinarith [mul_le_mul_of_nonneg_left hsum hq.le]
  have hnat : ∀ n : ℕ, (n : ℝ) * Real.exp (-Real.log n) ≤ 1 := fun n ↦ by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hn)]
      exact (mul_inv_cancel₀ (by exact_mod_cast hn.ne')).le
  have hk : Real.exp (-((k : ℝ) + 1)) ≤ (1 / 2) ^ (k + 1) := by
    rw [show -((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) * (-1) by push_cast; ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_half.le _
  have hsplit : Real.exp (-L) = Real.exp (-Real.log a) * Real.exp (-Real.log b) *
      Real.exp (-((k : ℝ) + 1)) * Real.exp (-c) := by
    simp only [L, ← Real.exp_add]
    ring_nf
  calc (m : ℝ) * (2 * Real.exp (-t ^ 2 / (2 * ((1 / 2) ^ k) ^ 2)))
      ≤ ((a : ℝ) * b) * (2 * Real.exp (-L)) := by
        gcongr
        exact_mod_cast hm
    _ = 2 * (((a * Real.exp (-Real.log a)) * (b * Real.exp (-Real.log b))) *
        Real.exp (-((k : ℝ) + 1)) * Real.exp (-c)) := by rw [hsplit]; ring
    _ ≤ 2 * ((1 * 1) * (1 / 2) ^ (k + 1) * Real.exp (-c)) := by
        have hb0 : 0 ≤ (b : ℝ) * Real.exp (-Real.log b) := by positivity
        have hAB := mul_le_mul (hnat a) (hnat b) hb0 zero_le_one
        have h3 := mul_le_mul hAB hk (Real.exp_pos _).le (by norm_num)
        have h4 := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (-c)).le
        linarith
    _ = _ := by ring

section Chain

variable {F : ι → S → ℝ} {N : ℕ → ℕ} {l : ∀ k, Fin (N k) → S → ℝ} {β : ∀ k, ι → Fin (N k)}

/-- The link `l (k + 1) (β (k + 1) i) - l k (β k i)` between consecutive dyadic lower brackets
of `F i`. -/
private noncomputable def chainLink (l : ∀ k, Fin (N k) → S → ℝ) (β : ∀ k, ι → Fin (N k))
    (k : ℕ) (i : ι) : S → ℝ :=
  l (k + 1) (β (k + 1) i) - l k (β k i)

omit [IsProbabilityMeasure μ] in
/-- Union bound at one level of the chain: the links take at most `N k * N (k + 1)` values,
each bounded by `2⁻ᵏ`, and Hoeffding's inequality applies to each. -/
private lemma measure_level_le (hlaw : ∀ k, HasLaw (X k) μ P) (hindep : iIndepFun X P)
    (hl : ∀ k j, Measurable (l k j))
    (hβ : ∀ k i x, 0 ≤ F i x - l k (β k i) x ∧ F i x - l k (β k i) x ≤ (1 / 2) ^ k)
    {c : ℝ} (hc : 0 ≤ c) (k n : ℕ) :
    P (⋃ i, {ω | chainThreshold N c k ≤ |empiricalProcess μ X n (chainLink l β k i) ω|}) ≤
      ENNReal.ofReal ((1 / 2) ^ k * Real.exp (-c)) := by
  classical
  set R := (Finset.univ : Finset (Fin (N k) × Fin (N (k + 1)))).filter
    fun p ↦ ∃ i, β k i = p.1 ∧ β (k + 1) i = p.2
  set A : Fin (N k) × Fin (N (k + 1)) → Set Ω := fun p ↦
    {ω | chainThreshold N c k ≤ |empiricalProcess μ X n (l (k + 1) p.2 - l k p.1) ω|}
  have hsub : (⋃ i, {ω | chainThreshold N c k ≤
      |empiricalProcess μ X n (chainLink l β k i) ω|}) ⊆ ⋃ p ∈ R, A p := by
    intro ω hω
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hω
    exact Set.mem_biUnion (x := (β k i, β (k + 1) i))
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, i, rfl, rfl⟩) hi
  have hA : ∀ p ∈ R, P (A p) ≤ ENNReal.ofReal
      (2 * Real.exp (-chainThreshold N c k ^ 2 / (2 * ((1 / 2) ^ k) ^ 2))) := by
    intro p hp
    obtain ⟨i, hi1, hi2⟩ := (Finset.mem_filter.1 hp).2
    refine measure_le_abs_empiricalProcess_le hlaw hindep ((hl _ _).sub (hl _ _))
      (by positivity) (fun x ↦ ?_) (chainThreshold_nonneg N c k) n
    have h1 := hβ k i x
    have h2 := hβ (k + 1) i x
    have hpow : ((1 : ℝ) / 2) ^ (k + 1) ≤ (1 / 2) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)
    rw [← hi1, ← hi2, Pi.sub_apply, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hcard : R.card ≤ N k * N (k + 1) :=
    (Finset.card_filter_le _ _).trans (by simp)
  calc _ ≤ P (⋃ p ∈ R, A p) := measure_mono hsub
    _ ≤ ∑ p ∈ R, P (A p) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ R, ENNReal.ofReal
        (2 * Real.exp (-chainThreshold N c k ^ 2 / (2 * ((1 / 2) ^ k) ^ 2))) :=
      Finset.sum_le_sum hA
    _ = ENNReal.ofReal (R.card *
        (2 * Real.exp (-chainThreshold N c k ^ 2 / (2 * ((1 / 2) ^ k) ^ 2)))) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (card_mul_exp_le hcard k le_rfl hc)

omit [IsProbabilityMeasure μ] in
/-- The whole chain from level `q` on is bad with probability at most `2 e⁻ᶜ`. -/
private lemma measure_chain_le (hlaw : ∀ k, HasLaw (X k) μ P) (hindep : iIndepFun X P)
    (hl : ∀ k j, Measurable (l k j))
    (hβ : ∀ k i x, 0 ≤ F i x - l k (β k i) x ∧ F i x - l k (β k i) x ≤ (1 / 2) ^ k)
    {c : ℝ} (hc : 0 ≤ c) (q n : ℕ) :
    P (⋃ k, ⋃ i, {ω | chainThreshold N c (q + k) ≤
        |empiricalProcess μ X n (chainLink l β (q + k) i) ω|}) ≤
      ENNReal.ofReal (2 * Real.exp (-c)) := by
  have hgeo : Summable fun k : ℕ ↦ (1 / 2 : ℝ) ^ k * Real.exp (-c) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  calc _ ≤ ∑' k, P (⋃ i, {ω | chainThreshold N c (q + k) ≤
        |empiricalProcess μ X n (chainLink l β (q + k) i) ω|}) := measure_iUnion_le _
    _ ≤ ∑' k, ENNReal.ofReal ((1 / 2) ^ k * Real.exp (-c)) := by
      refine ENNReal.tsum_le_tsum fun k ↦
        (measure_level_le hlaw hindep hl hβ hc (q + k) n).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left k q))
        (Real.exp_pos _).le
    _ = ENNReal.ofReal (2 * Real.exp (-c)) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hgeo, tsum_mul_right,
        tsum_geometric_two]

omit [MeasurableSpace Ω] in
/-- Off the bad chain event, every `F i` is within `∑_{k ≥ q}` thresholds of its level-`q` lower
bracket, uniformly in `i`. -/
private lemma abs_sub_le_of_not_mem_chain (hFi : ∀ i, Integrable (F i) μ)
    (hFm : ∀ i, Measurable (F i)) (hl : ∀ k j, Measurable (l k j))
    (hβ : ∀ k i x, 0 ≤ F i x - l k (β k i) x ∧ F i x - l k (β k i) x ≤ (1 / 2) ^ k)
    {c : ℝ} (hsum : Summable (chainThreshold N c)) (q n : ℕ) {ω : Ω}
    (hω : ω ∉ ⋃ k, ⋃ i, {ω | chainThreshold N c (q + k) ≤
        |empiricalProcess μ X n (chainLink l β (q + k) i) ω|}) (i : ι) :
    |empiricalProcess μ X n (F i) ω - empiricalProcess μ X n (l q (β q i)) ω| ≤
      ∑' k, chainThreshold N c (q + k) := by
  have hd : ∀ k, Integrable (F i - l k (β k i)) μ := fun k ↦
    Integrable.of_mem_Icc 0 ((1 / 2) ^ k) ((hFm i).sub (hl _ _)).aemeasurable
      (ae_of_all _ fun x ↦ hβ k i x)
  have hli : ∀ k, Integrable (l k (β k i)) μ := fun k ↦ by
    simpa using (hFi i).sub (hd k)
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hω
  refine abs_sub_le_tsum_of_chain (g := fun m ↦ empiricalProcess μ X n (l (q + m) (β (q + m) i)) ω)
    (C := √n * (1 / 2) ^ q) ((summable_nat_add_iff q).2 hsum |>.congr fun k ↦ by rw [add_comm])
    (fun k ↦ chainThreshold_nonneg N c _) (fun m ↦ ?_) (fun K ↦ ?_)
  · rw [empiricalProcess_sub (hli _) (hli _)]
    exact (hω m i).le
  · rw [empiricalProcess_sub (hFi i) (hli _), mul_assoc, ← pow_add]
    exact abs_empiricalProcess_le (hd _) (fun x ↦ (hβ _ i x).1) (fun x ↦ (hβ _ i x).2) n ω

end Chain

/-! ### Asymptotic equicontinuity -/

/-- **Asymptotic equicontinuity of the empirical process under uniform bracketing entropy.**
Let `X 0, X 1, …` be i.i.d. with law `μ` and let `F` be a class of measurable square-integrable
functions whose uniform bracketing entropy integral `∫₀¹ √(log N_[](ε, F, ‖·‖_∞)) dε` is finite.
For every `ε, η > 0` there is `δ > 0` such that, for every sample size `n`, the (outer)
probability that two members of `F` at standard-deviation distance `ρ_μ(f, g) < δ` have
empirical-process values more than `ε` apart is at most `η`.

Here `ρ_μ(f, g)² = Var_μ[f - g]` is the standard-deviation semimetric of the Donsker theory, and
`P` of a non-measurable event is its outer measure, so no measurability of the supremum over an
uncountable class is needed. The bound holds for every `n`, which is stronger than the usual
`lim sup` form. -/
theorem measure_exists_abs_empiricalProcess_sub_gt_le (hlaw : ∀ k, HasLaw (X k) μ P)
    (hindep : iIndepFun X P) {F : ι → S → ℝ} (hFm : ∀ i, Measurable (F i))
    (hF2 : ∀ i, MemLp (F i) 2 μ)
    (hJ : ∫⁻ ε in Set.Ioc 0 1, uniformBracketingEntropy F ε ≠ ⊤) {ε η : ℝ} (hε : 0 < ε)
    (hη : 0 < η) :
    ∃ δ > 0, ∀ n, P {ω | ∃ i j, Var[F i - F j; μ] < δ ^ 2 ∧
      ε < |empiricalProcess μ X n (F i) ω - empiricalProcess μ X n (F j) ω|} ≤
        ENNReal.ofReal η := by
  classical
  obtain ⟨N, hN, hNsum⟩ := exists_dyadic_covers hJ
  choose l u hl hu _ hw hcov using hN
  choose β hβ' using hcov
  have hβ : ∀ k i x, 0 ≤ F i x - l k (β k i) x ∧ F i x - l k (β k i) x ≤ (1 / 2) ^ k :=
    fun k i x ↦ ⟨by linarith [(hβ' k i x).1], by linarith [(hβ' k i x).2, hw k (β k i) x]⟩
  have hFi : ∀ i, Integrable (F i) μ := fun i ↦ (hF2 i).integrable one_le_two
  set c := |Real.log (4 / η)|
  have hc : 0 ≤ c := abs_nonneg _
  have hec : Real.exp (-c) ≤ η / 4 := by
    calc Real.exp (-c) ≤ Real.exp (-Real.log (4 / η)) :=
          Real.exp_le_exp.2 (neg_le_neg (le_abs_self _))
      _ = η / 4 := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]
          field_simp
  have hsum := summable_chainThreshold hNsum c
  have htail : Tendsto (fun q ↦ ∑' k, chainThreshold N c (q + k)) atTop (nhds 0) := by
    simpa [add_comm] using tendsto_sum_nat_add (chainThreshold N c)
  obtain ⟨q, hq⟩ := (htail.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 8))).exists
  set T := ∑' k, chainThreshold N c (q + k)
  set M := N q
  set δ := ε * √η / (4 * ((M : ℝ) + 1))
  have hδ : 0 < δ := by positivity
  refine ⟨δ, hδ, fun n ↦ ?_⟩
  set W : Fin M × Fin M → Prop := fun p ↦
    ∃ ij : ι × ι, β q ij.1 = p.1 ∧ β q ij.2 = p.2 ∧ Var[F ij.1 - F ij.2; μ] < δ ^ 2
  choose w hw1 hw2 hw3 using fun p (hp : W p) ↦ hp
  set Bchain := ⋃ k, ⋃ i, {ω | chainThreshold N c (q + k) ≤
    |empiricalProcess μ X n (chainLink l β (q + k) i) ω|}
  set Bpair := ⋃ p, ⋃ hp : W p,
    {ω | ε / 2 ≤ |empiricalProcess μ X n (F (w p hp).1 - F (w p hp).2) ω|}
  have hsub : {ω | ∃ i j, Var[F i - F j; μ] < δ ^ 2 ∧
      ε < |empiricalProcess μ X n (F i) ω - empiricalProcess μ X n (F j) ω|} ⊆
      Bchain ∪ Bpair := by
    rintro ω ⟨i, j, hij, hgt⟩
    by_contra hω
    simp only [Set.mem_union, not_or] at hω
    obtain ⟨hω1, hω2⟩ := hω
    have hT := abs_sub_le_of_not_mem_chain hFi hFm hl hβ hsum q n hω1
    have hp : W (β q i, β q j) := ⟨(i, j), rfl, rfl, hij⟩
    have hpair : |empiricalProcess μ X n (F (w _ hp).1 - F (w _ hp).2) ω| < ε / 2 := by
      simp only [Bpair, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hω2
      exact hω2 _ hp
    rw [← empiricalProcess_sub (hFi _) (hFi _)] at hpair
    have h1 := hT i
    have h2 := hT (w _ hp).1
    have h3 := hT j
    have h4 := hT (w _ hp).2
    rw [hw1 _ hp] at h2
    rw [hw2 _ hp] at h4
    rw [abs_le] at h1 h2 h3 h4
    rw [abs_lt] at hpair
    have hlt : |empiricalProcess μ X n (F i) ω - empiricalProcess μ X n (F j) ω| < ε :=
      abs_lt.2 ⟨by linarith, by linarith⟩
    exact absurd hgt (not_lt.2 hlt.le)
  have hchain : P Bchain ≤ ENNReal.ofReal (η / 2) :=
    (measure_chain_le hlaw hindep hl hβ hc q n).trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hpairs : P Bpair ≤ ENNReal.ofReal (η / 2) := by
    have hone : ∀ p, P (⋃ hp : W p, {ω | ε / 2 ≤
        |empiricalProcess μ X n (F (w p hp).1 - F (w p hp).2) ω|}) ≤
        ENNReal.ofReal (δ ^ 2 / (ε / 2) ^ 2) := by
      intro p
      by_cases hp : W p
      · refine (measure_mono (Set.iUnion_subset fun _ ↦ subset_rfl)).trans
          ((measure_le_abs_empiricalProcess_le_variance (h := F (w p hp).1 - F (w p hp).2)
            hlaw hindep
          ((hFm _).sub (hFm _)) ((hF2 _).sub (hF2 _)) (by positivity) n).trans
          (ENNReal.ofReal_le_ofReal ?_))
        gcongr
        exact (hw3 p hp).le
      · refine (measure_mono (Set.iUnion_subset (t := ∅) fun h ↦ (hp h).elim)).trans ?_
        simp
    calc P Bpair ≤ ∑ p, P (⋃ hp : W p, {ω | ε / 2 ≤
          |empiricalProcess μ X n (F (w p hp).1 - F (w p hp).2) ω|}) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ _p : Fin M × Fin M, ENNReal.ofReal (δ ^ 2 / (ε / 2) ^ 2) :=
          Finset.sum_le_sum fun p _ ↦ hone p
      _ = ENNReal.ofReal ((M : ℝ) * M * (δ ^ 2 / (ε / 2) ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_natCast]
          simp
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hM : (M : ℝ) * M ≤ ((M : ℝ) + 1) ^ 2 := by
            nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
          have hval : δ ^ 2 / (ε / 2) ^ 2 = η / (4 * ((M : ℝ) + 1) ^ 2) := by
            simp only [δ]
            rw [div_pow, mul_pow, Real.sq_sqrt hη.le]
            field_simp
            ring
          rw [hval]
          calc (M : ℝ) * M * (η / (4 * ((M : ℝ) + 1) ^ 2))
              ≤ ((M : ℝ) + 1) ^ 2 * (η / (4 * ((M : ℝ) + 1) ^ 2)) := by gcongr
            _ = η / 4 := by field_simp
            _ ≤ η / 2 := by linarith
  calc _ ≤ P (Bchain ∪ Bpair) := measure_mono hsub
    _ ≤ P Bchain + P Bpair := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add hchain hpairs
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      ring_nf

/-! ### Total boundedness -/

omit [MeasurableSpace Ω] in
/-- **Total boundedness.** A class with a finite uniform bracketing entropy integral is totally
bounded in the standard-deviation semimetric: for every `δ > 0`, finitely many members of `F` are
`δ`-dense, measured by `Var[F i - F j; μ] < δ ^ 2`. Since `Var[f; μ]` is `0` when `f ∉ L²(μ)`,
square-integrable members suffice for the semimetric reading; for this distance it is enough
that the pairwise differences are square-integrable. -/
theorem exists_finset_variance_lt {F : ι → S → ℝ} (hFm : ∀ i, Measurable (F i))
    (hJ : ∫⁻ ε in Set.Ioc 0 1, uniformBracketingEntropy F ε ≠ ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Finset ι, ∀ i, ∃ j ∈ s, Var[F i - F j; μ] < δ ^ 2 := by
  classical
  obtain ⟨N, hN, -⟩ := exists_dyadic_covers hJ
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨l, u, -, -, -, hw, hcov⟩ := hN k
  choose β hβ using hcov
  set T := (Finset.univ : Finset (Fin (N k))).filter fun a ↦ ∃ i, β i = a
  refine ⟨T.attach.image fun a ↦ (Finset.mem_filter.1 a.2).2.choose, fun i ↦ ?_⟩
  have hi : β i ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ _, i, rfl⟩
  set j := (Finset.mem_filter.1 hi).2.choose
  have hj : β j = β i := (Finset.mem_filter.1 hi).2.choose_spec
  refine ⟨j, Finset.mem_image.2 ⟨⟨β i, hi⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
  have hb : ∀ x, F i x - F j x ∈ Set.Icc (-(1 / 2 : ℝ) ^ k) ((1 / 2) ^ k) := fun x ↦ by
    have h1 := hβ i x
    have h2 := hβ j x
    have h3 := hw (β i) x
    rw [hj] at h2
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  calc Var[F i - F j; μ] ≤ (((1 / 2 : ℝ) ^ k - -(1 / 2) ^ k) / 2) ^ 2 :=
        variance_le_sq_of_bounded (ae_of_all _ hb) ((hFm i).sub (hFm j)).aemeasurable
    _ = ((1 / 2 : ℝ) ^ k) ^ 2 := by ring
    _ < δ ^ 2 := by gcongr

/-! ### Finite-dimensional convergence -/

omit [IsProbabilityMeasure μ] in
/-- **Finite-dimensional convergence.** For finitely many members `F (idx 0), …, F (idx (m - 1))`
of a class of measurable square-integrable functions, the vector of empirical-process values
converges in distribution to a centered Gaussian vector `A` whose projection on `t` has variance
`Var_μ[∑ₐ tₐ F (idx a)]`. This is the multivariate central limit theorem
`ProbabilityTheory.exists_tendstoInDistribution_inv_sqrt_smul_sum_sub` applied to
`(F (idx a) (X k))ₐ`. -/
theorem exists_tendstoInDistribution_empiricalProcess (hlaw : ∀ k, HasLaw (X k) μ P)
    (hindep : iIndepFun X P) {F : ι → S → ℝ} (hFm : ∀ i, Measurable (F i))
    (hF2 : ∀ i, MemLp (F i) 2 μ) {m : ℕ} (idx : Fin m → ι) :
    ∃ A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
      HasGaussianLaw A (stdGaussian (EuclideanSpace ℝ (Fin m))) ∧
      (∀ t : EuclideanSpace ℝ (Fin m), HasLaw (fun z ↦ inner ℝ (A z) t)
        (gaussianReal 0 (Var[fun x ↦ ∑ a, t a * F (idx a) x; μ]).toNNReal)
        (stdGaussian (EuclideanSpace ℝ (Fin m)))) ∧
      TendstoInDistribution
        (fun n ω ↦ WithLp.toLp 2 fun a ↦ empiricalProcess μ X n (F (idx a)) ω)
        atTop A (fun _ ↦ P) (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  set φ : S → EuclideanSpace ℝ (Fin m) := fun x ↦ WithLp.toLp 2 fun a ↦ F (idx a) x
  have hφ : Measurable φ :=
    (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval fun a ↦ hFm (idx a))
  set Y : ℕ → Ω → EuclideanSpace ℝ (Fin m) := fun k ω ↦ φ (X k ω)
  have hYlaw : ∀ k, HasLaw (Y k) (μ.map φ) P := fun k ↦
    (⟨hφ.aemeasurable, rfl⟩ : HasLaw φ (μ.map φ) μ).comp (hlaw k)
  have hY2 : MemLp (Y 0) 2 P := by
    have hpi : MemLp (fun ω (a : Fin m) ↦ F (idx a) (X 0 ω)) 2 P :=
      MemLp.of_eval fun a ↦ MemLp.comp_of_map ((hlaw 0).map_eq ▸ hF2 (idx a))
        (hlaw 0).aemeasurable
    exact (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin m ↦ ℝ).symm.toContinuousLinearMap.comp_memLp'
      hpi
  have hYind : iIndepFun Y P := hindep.comp (fun _ ↦ φ) fun _ ↦ hφ
  have hYid : ∀ k, IdentDistrib (Y k) (Y 0) P P := fun k ↦ (hYlaw k).identDistrib (hYlaw 0)
  obtain ⟨A, hA, hAlaw, hconv⟩ := exists_tendstoInDistribution_inv_sqrt_smul_sum_sub hY2 hYind hYid
  have hvar : ∀ t : EuclideanSpace ℝ (Fin m),
      Var[fun ω ↦ inner ℝ (Y 0 ω) t; P] = Var[fun x ↦ ∑ a, t a * F (idx a) x; μ] := by
    intro t
    have hg : Measurable fun x ↦ ∑ a, t a * F (idx a) x :=
      Finset.measurable_sum _ fun a _ ↦ (hFm (idx a)).const_mul _
    have heq : (fun ω ↦ inner ℝ (Y 0 ω) t) = (fun x ↦ ∑ a, t a * F (idx a) x) ∘ X 0 := by
      ext ω
      simp [Y, φ, PiLp.inner_apply, mul_comm]
    rw [heq, ← variance_map (by rw [(hlaw 0).map_eq]; exact hg.aemeasurable)
      (hlaw 0).aemeasurable, (hlaw 0).map_eq]
  refine ⟨A, hA, fun t ↦ by simpa [hvar t] using hAlaw t, ?_⟩
  have hmean : ∀ a, (∫ ω, Y 0 ω ∂P) a = ∫ x, F (idx a) x ∂μ := by
    intro a
    have := (EuclideanSpace.proj (𝕜 := ℝ) a).integral_comp_comm (hY2.integrable one_le_two)
    rw [← (hlaw 0).integral_comp (hFm (idx a)).aestronglyMeasurable]
    simpa [Y, φ] using this.symm
  convert hconv using 3 with n ω
  ext a
  simp [empiricalProcess, Finset.sum_sub_distrib, hmean, Y, φ]

/-! ### The Donsker conditions -/

/-- The **Donsker conditions** for a class `F` of functions under the law `μ` of an i.i.d. sample
`X`: finite-dimensional convergence of the empirical process to centered Gaussian vectors with the
covariance of `F` under `μ`, total boundedness of `F` in the standard-deviation semimetric
`ρ_μ(f, g) = √(Var_μ[f - g])`, and asymptotic uniform `ρ_μ`-equicontinuity of the empirical process
in (outer) probability. Here `Var_μ` is the real part (`ENNReal.toReal`) of the extended variance:
for a finite `μ` it is `0` on an a.e. strongly measurable `f ∉ L²(μ)`. Square-integrable members
suffice for the semimetric reading; for this distance it is enough that the pairwise differences
are square-integrable.

By van der Vaart and Wellner, *Weak Convergence and Empirical Processes*, Theorems 1.5.4 and 1.5.7
(see also §2.1.2), these three conditions are equivalent to `F` being `μ`-Donsker, that is, to
weak convergence of the empirical process in `ℓ^∞(F)` to a tight Brownian bridge. That
equivalence, which needs weak convergence with outer integrals in the non-separable space
`ℓ^∞(F)`, is not formalized here. -/
structure DonskerConditions (μ : Measure S) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → S) (F : ι → S → ℝ) : Prop where
  /-- Finite-dimensional convergence to centered Gaussian vectors with covariance `Cov_μ`. -/
  fidi : ∀ (m : ℕ) (idx : Fin m → ι),
    ∃ A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
      HasGaussianLaw A (stdGaussian (EuclideanSpace ℝ (Fin m))) ∧
      (∀ t : EuclideanSpace ℝ (Fin m), HasLaw (fun z ↦ inner ℝ (A z) t)
        (gaussianReal 0 (Var[fun x ↦ ∑ a, t a * F (idx a) x; μ]).toNNReal)
        (stdGaussian (EuclideanSpace ℝ (Fin m)))) ∧
      TendstoInDistribution
        (fun n ω ↦ WithLp.toLp 2 fun a ↦ empiricalProcess μ X n (F (idx a)) ω)
        atTop A (fun _ ↦ P) (stdGaussian (EuclideanSpace ℝ (Fin m)))
  /-- Total boundedness in the standard-deviation semimetric. -/
  totallyBounded : ∀ δ > 0, ∃ s : Finset ι, ∀ i, ∃ j ∈ s, Var[F i - F j; μ] < δ ^ 2
  /-- Asymptotic uniform equicontinuity in (outer) probability. -/
  equicontinuous : ∀ ε > 0, ∀ η > 0, ∃ δ > 0, ∀ᶠ n in atTop,
    P {ω | ∃ i j, Var[F i - F j; μ] < δ ^ 2 ∧
      ε < |empiricalProcess μ X n (F i) ω - empiricalProcess μ X n (F j) ω|} ≤ ENNReal.ofReal η

/-- **Donsker theorem under uniform bracketing entropy.** A class `F` of measurable
square-integrable functions whose uniform bracketing entropy integral
`∫₀¹ √(log N_[](ε, F, ‖·‖_∞)) dε` is finite satisfies the Donsker conditions for every i.i.d.
sample with law `μ`. -/
theorem donskerConditions_of_uniformBracketingEntropy (hlaw : ∀ k, HasLaw (X k) μ P)
    (hindep : iIndepFun X P) {F : ι → S → ℝ} (hFm : ∀ i, Measurable (F i))
    (hF2 : ∀ i, MemLp (F i) 2 μ)
    (hJ : ∫⁻ ε in Set.Ioc 0 1, uniformBracketingEntropy F ε ≠ ⊤) :
    DonskerConditions μ P X F where
  fidi _ idx := exists_tendstoInDistribution_empiricalProcess hlaw hindep hFm hF2 idx
  totallyBounded _ hδ := exists_finset_variance_lt hFm hJ hδ
  equicontinuous _ hε _ hη := by
    obtain ⟨δ, hδ, h⟩ := measure_exists_abs_empiricalProcess_sub_gt_le hlaw hindep hFm hF2 hJ hε hη
    exact ⟨δ, hδ, Eventually.of_forall h⟩

end MathlibExt.Probability.EmpiricalProcess.BracketingDonsker
