/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BerryEsseen
public import Mathlib.Probability.Moments.Variance

/-!
# A Berry–Esseen bound for Mendelian segregation

At `M` biallelic loci with additive effects `a l`, the offspring's segregation deviation
`R_M = ∑_{l < M} a l (X l - E X l)` (the centred Mendelian sampling term of the infinitesimal
model) is a sum of independent centred variables, each bounded by `2 |a l|`. The Lyapunov form
of the Berry–Esseen theorem (`berry_esseen_finsetSum_gaussian`, constant `42`) then bounds the
Kolmogorov distance of `R_M / σ` to the standard Gaussian by `336 · (∑ |a l|³) / σ³`, whenever
`σ² = Var R_M > 0`: the constant is `42 · 2³`. At one locus with parental counts `g₁, g₂ ∈ {0, 1, 2}`,
`mendelLaw g₁ g₂` is the transmission law of the focal-allele count; it is a probability
measure with variance `p₁(1 - p₁) + p₂(1 - p₂)` (`pᵢ = gᵢ / 2`), which makes
the per-locus variance in the bound completely explicit.

## Main results

* `segregationDeviation`, `mendelLaw`: the centred segregation sum and the one-locus
  transmission law.
* `variance_segregationDeviation`: `Var R_M = ∑_{l < M} (a l)² Var (X l)`.
* `abs_segregation_cdf_sub_le`: the Berry–Esseen bound with explicit constant `336`.
* `isProbabilityMeasure_mendelLaw`, `integral_mendelLaw`, `variance_mendelLaw`: the law,
  mean and variance at one locus.
* `abs_mendelian_segregation_cdf_sub_le`: the bound specialized to Mendelian loci.

## References

* N. H. Barton, A. M. Etheridge and A. Véber, *The infinitesimal model: definition,
  derivation, and implications*, Theor. Popul. Biol. 118 (2017), 50–73.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace MathlibExt.Biology.PopulationGenetics.Classical.InfinitesimalLimit

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The offspring **segregation deviation** at `M` loci, `R_M = ∑_{l < M} a_l (X_l - E X_l)`:
`X l` is the offspring's allele count at locus `l` (a Mendelian draw given the parents) and
`a l` is the additive effect of the locus. -/
noncomputable def segregationDeviation (P : Measure Ω) (M : ℕ) (a : ℕ → ℝ) (X : ℕ → Ω → ℝ) :
    Ω → ℝ :=
  fun ω => ∑ l ∈ range M, a l * (X l ω - P[X l])

/-- The law of the offspring's count of the focal allele at one biallelic locus when the parents
carry `g₁` and `g₂` copies (`gᵢ ∈ {0, 1, 2}`): each parent transmits the focal allele
independently with probability `gᵢ / 2` (Mendel's first law), so the count is `0`, `1` or `2`. -/
noncomputable def mendelLaw (g₁ g₂ : ℕ) : Measure ℝ :=
  ENNReal.ofReal ((1 - (g₁ : ℝ) / 2) * (1 - (g₂ : ℝ) / 2)) • Measure.dirac 0 +
    ENNReal.ofReal ((g₁ : ℝ) / 2 * (1 - (g₂ : ℝ) / 2) + (1 - (g₁ : ℝ) / 2) * ((g₂ : ℝ) / 2)) •
      Measure.dirac 1 +
    ENNReal.ofReal ((g₁ : ℝ) / 2 * ((g₂ : ℝ) / 2)) • Measure.dirac 2

section Helpers

variable {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}

private lemma integral_mem_Icc (hXm : ∀ l, Measurable (X l))
    (hX : ∀ l, ∀ᵐ ω ∂P, X l ω ∈ Set.Icc (0 : ℝ) 2) (l : ℕ) : P[X l] ∈ Set.Icc (0 : ℝ) 2 := by
  have hint : Integrable (X l) P := (memLp_of_bounded (hX l) (hXm l).aestronglyMeasurable 1).integrable le_rfl
  constructor
  · exact integral_nonneg_of_ae ((hX l).mono fun ω h => h.1)
  · calc P[X l] ≤ ∫ _, (2 : ℝ) ∂P := integral_mono_ae hint (integrable_const 2) ((hX l).mono fun ω h => h.2)
      _ = 2 := by simp

private lemma abs_centered_le (hXm : ∀ l, Measurable (X l))
    (hX : ∀ l, ∀ᵐ ω ∂P, X l ω ∈ Set.Icc (0 : ℝ) 2) (a : ℕ → ℝ) (l : ℕ) :
    ∀ᵐ ω ∂P, |a l * (X l ω - P[X l])| ≤ 2 * |a l| := by
  have hm := integral_mem_Icc hXm hX l
  filter_upwards [hX l] with ω hω
  rw [abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [abs_le]
  constructor <;> linarith [hω.1, hω.2, hm.1, hm.2]

private lemma memLp_centered (hXm : ∀ l, Measurable (X l))
    (hX : ∀ l, ∀ᵐ ω ∂P, X l ω ∈ Set.Icc (0 : ℝ) 2) (a : ℕ → ℝ) (l : ℕ) (p : ℝ≥0∞) :
    MemLp (fun ω => a l * (X l ω - P[X l])) p P :=
  MemLp.of_bound (((hXm l).sub_const _).const_mul _).aestronglyMeasurable (2 * |a l|)
    ((abs_centered_le hXm hX a l).mono fun ω h => by rwa [Real.norm_eq_abs])

private lemma integral_centered (hXm : ∀ l, Measurable (X l))
    (hX : ∀ l, ∀ᵐ ω ∂P, X l ω ∈ Set.Icc (0 : ℝ) 2) (a : ℕ → ℝ) (l : ℕ) :
    P[fun ω => a l * (X l ω - P[X l])] = 0 := by
  have hint : Integrable (X l) P := (memLp_of_bounded (hX l) (hXm l).aestronglyMeasurable 1).integrable le_rfl
  rw [integral_const_mul, integral_sub hint (integrable_const _), integral_const]
  simp

omit [IsProbabilityMeasure P] in
private lemma iIndepFun_centered (hind : iIndepFun X P) (a : ℕ → ℝ) (c : ℝ) :
    iIndepFun (fun l ω => a l * (X l ω - P[X l]) / c) P := by
  have h := hind.comp (fun l (t : ℝ) => a l * (t - ∫ ω, X l ω ∂P) / c) (fun l => by fun_prop)
  exact h

end Helpers

/-- **Variance of the segregation deviation.** For independent (unlinked) loci with allele
counts in `[0, 2]`, `Var(R_M) = ∑_{l < M} a_l² Var(X_l)`. -/
theorem variance_segregationDeviation {P : Measure Ω} [IsProbabilityMeasure P] {M : ℕ}
    {a : ℕ → ℝ} {X : ℕ → Ω → ℝ} (hXm : ∀ l, Measurable (X l)) (hind : iIndepFun X P)
    (hX : ∀ l, ∀ᵐ ω ∂P, X l ω ∈ Set.Icc (0 : ℝ) 2) :
    Var[segregationDeviation P M a X; P] = ∑ l ∈ range M, a l ^ 2 * Var[X l; P] := by
  have hsum : segregationDeviation P M a X =
      ∑ l ∈ range M, fun ω => a l * (X l ω - P[X l]) := by
    funext ω
    simp [segregationDeviation, Finset.sum_apply]
  have hind' := iIndepFun_centered hind a 1
  simp only [div_one] at hind'
  rw [hsum, IndepFun.variance_sum (fun l _ => memLp_centered hXm hX a l 2)
    (fun i _ j _ hij => hind'.indepFun hij)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [variance_const_mul, variance_sub_const (hXm l).aestronglyMeasurable]

/-- **Segregation Berry–Esseen bound.** Conditional on the parents (the probability space),
let the offspring allele counts `X l ∈ [0, 2]` at unlinked loci be independent, with additive
effects `|a l| ≤ B / √M`. If `σ² = Var(R_M) > 0`, then for every `x`,
`|P(R_M ≤ x) - Φ(x / σ)| ≤ 336 B³ / (σ³ √M)`, where `Φ` is the standard normal distribution
function. The constant is `42 · 2³`, from Atlas's Lyapunov-form Berry–Esseen bound with
constant `42`. -/
theorem abs_segregation_cdf_sub_le {P : Measure Ω} [IsProbabilityMeasure P] {M : ℕ}
    {B σ : ℝ} {a : ℕ → ℝ} {X : ℕ → Ω → ℝ} (hXm : ∀ l, Measurable (X l))
    (hind : iIndepFun X P) (hX : ∀ l, ∀ᵐ ω ∂P, X l ω ∈ Set.Icc (0 : ℝ) 2)
    (ha : ∀ l < M, |a l| ≤ B / √M) (hσ : 0 < σ)
    (hvar : Var[segregationDeviation P M a X; P] = σ ^ 2) (x : ℝ) :
    |P.real {ω | segregationDeviation P M a X ω ≤ x} -
        (gaussianReal 0 1).real (Set.Iic (x / σ))| ≤ 336 * B ^ 3 / (σ ^ 3 * √M) := by
  -- `M ≥ 1`, since the empty sum has variance zero
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · subst h0
      have : segregationDeviation P 0 a X = 0 := by funext ω; simp [segregationDeviation]
      rw [this, variance_zero] at hvar
      nlinarith
    · exact h0
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hsM : 0 < √(M : ℝ) := Real.sqrt_pos.2 hMr
  have hB : 0 ≤ B := by
    have h0 := ha 0 hM
    have := abs_nonneg (a 0)
    have : 0 ≤ B / √M := le_trans (abs_nonneg _) h0
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 hsM)
  set ξ : ℕ → Ω → ℝ := fun l ω => a l * (X l ω - P[X l]) / σ with hξ
  have hξm : ∀ j, Measurable (ξ j) := fun j => by
    simp only [hξ]; fun_prop
  have hξind : iIndepFun ξ P := iIndepFun_centered hind a σ
  have hξmem : ∀ j ∈ range M, MemLp (ξ j) 3 P := fun j _ => by
    simpa [hξ, div_eq_mul_inv, mul_comm] using (memLp_centered hXm hX a j 3).const_mul σ⁻¹
  have hξmean : ∀ j ∈ range M, P[ξ j] = 0 := fun j _ => by
    simp only [hξ]
    rw [integral_div, integral_centered hXm hX a j, zero_div]
  have hξvar : ∑ j ∈ range M, P[fun ω => (ξ j ω) ^ 2] = 1 := by
    have hv := variance_segregationDeviation (M := M) (a := a) hXm hind hX
    have heach : ∀ j ∈ range M, P[fun ω => (ξ j ω) ^ 2] = a j ^ 2 * Var[X j; P] / σ ^ 2 := by
      intro j _
      have hc := variance_of_integral_eq_zero
        (((hXm j).sub_const _).const_mul (a j)).aemeasurable (integral_centered hXm hX a j)
      rw [variance_const_mul, variance_sub_const (hXm j).aestronglyMeasurable] at hc
      simp only [hξ, div_pow]
      rw [integral_div, ← hc]
    rw [Finset.sum_congr rfl heach, ← Finset.sum_div, ← hv, hvar, div_self (by positivity)]
  set γ : ℝ := 8 * B ^ 3 / (σ ^ 3 * √M) with hγ
  have hγ0 : 0 ≤ γ := by positivity
  have hξ3 : ∑ j ∈ range M, P[fun ω => |ξ j ω| ^ 3] ≤ γ := by
    have heach : ∀ j ∈ range M, P[fun ω => |ξ j ω| ^ 3] ≤ 8 * B ^ 3 / (σ ^ 3 * (√M) ^ 3) := by
      intro j hj
      have hbd : ∀ᵐ ω ∂P, |ξ j ω| ^ 3 ≤ 8 * B ^ 3 / (σ ^ 3 * (√M) ^ 3) := by
        filter_upwards [abs_centered_le hXm hX a j] with ω hω
        have haj := ha j (Finset.mem_range.1 hj)
        have h1 : |ξ j ω| ≤ 2 * B / (σ * √M) := by
          simp only [hξ]
          rw [abs_div, abs_of_pos hσ, div_le_div_iff₀ hσ (by positivity)]
          have : 2 * |a j| * √M ≤ 2 * B := by
            rw [le_div_iff₀ hsM] at haj; linarith
          calc |a j * (X j ω - P[X j])| * (σ * √M) ≤ 2 * |a j| * (σ * √M) :=
                mul_le_mul_of_nonneg_right hω (by positivity)
            _ = (2 * |a j| * √M) * σ := by ring
            _ ≤ (2 * B) * σ := mul_le_mul_of_nonneg_right this hσ.le
        calc |ξ j ω| ^ 3 ≤ (2 * B / (σ * √M)) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h1 3
          _ = 8 * B ^ 3 / (σ ^ 3 * (√M) ^ 3) := by ring
      calc P[fun ω => |ξ j ω| ^ 3] ≤ ∫ _, 8 * B ^ 3 / (σ ^ 3 * (√M) ^ 3) ∂P :=
            integral_mono_of_nonneg (f := fun ω => |ξ j ω| ^ 3)
              (g := fun _ => 8 * B ^ 3 / (σ ^ 3 * (√M) ^ 3))
              (Filter.Eventually.of_forall fun _ => by positivity) (integrable_const _) hbd
        _ = 8 * B ^ 3 / (σ ^ 3 * (√M) ^ 3) := by simp
    calc ∑ j ∈ range M, P[fun ω => |ξ j ω| ^ 3]
        ≤ ∑ _j ∈ range M, 8 * B ^ 3 / (σ ^ 3 * (√M) ^ 3) := Finset.sum_le_sum heach
      _ = γ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hγ]
        have hsq : (√(M : ℝ)) ^ 2 = M := Real.sq_sqrt hMr.le
        set s := √(M : ℝ) with hs
        have hs0 : s ≠ 0 := hsM.ne'
        rw [← hsq]
        field_simp
  have hmain := MathlibExt.Probability.BerryEsseenWanted.berry_esseen_finsetSum_gaussian
    hξm hξind hξmem hξmean hξvar hγ0 hξ3 (x / σ)
  have hset : {ω | ∑ j ∈ range M, ξ j ω ≤ x / σ} = {ω | segregationDeviation P M a X ω ≤ x} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hξ, segregationDeviation]
    rw [← Finset.sum_div, div_le_div_iff_of_pos_right hσ]
  rw [hset] at hmain
  calc _ ≤ 42 * γ := hmain
    _ = 336 * B ^ 3 / (σ ^ 3 * √M) := by rw [hγ]; ring

/-- A Mendelian draw lies in `{0, 1, 2} ⊆ [0, 2]`: the law gives no mass outside `[0, 2]`. -/
theorem mendelLaw_compl_Icc (g₁ g₂ : ℕ) : mendelLaw g₁ g₂ (Set.Icc (0 : ℝ) 2)ᶜ = 0 := by
  simp [mendelLaw, Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator_of_notMem]

/-- The Mendelian offspring law is a probability measure when `g₁, g₂ ≤ 2`. -/
theorem isProbabilityMeasure_mendelLaw {g₁ g₂ : ℕ} (h₁ : g₁ ≤ 2) (h₂ : g₂ ≤ 2) :
    IsProbabilityMeasure (mendelLaw g₁ g₂) := by
  have h₁' : (g₁ : ℝ) ≤ 2 := by exact_mod_cast h₁
  have h₂' : (g₂ : ℝ) ≤ 2 := by exact_mod_cast h₂
  have hg₁ : (0 : ℝ) ≤ g₁ := Nat.cast_nonneg _
  have hg₂ : (0 : ℝ) ≤ g₂ := Nat.cast_nonneg _
  constructor
  simp only [mendelLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by nlinarith) (by nlinarith), ← ENNReal.ofReal_add (by nlinarith)
    (by nlinarith), ← ENNReal.ofReal_one]
  congr 1
  ring


private lemma integrable_mendelLaw (f : ℝ → ℝ) (g₁ g₂ : ℕ) : Integrable f (mendelLaw g₁ g₂) := by
  unfold mendelLaw
  refine ((Integrable.smul_measure ?_ ENNReal.ofReal_ne_top).add_measure
    (Integrable.smul_measure ?_ ENNReal.ofReal_ne_top)).add_measure
    (Integrable.smul_measure ?_ ENNReal.ofReal_ne_top) <;>
  exact integrable_dirac enorm_lt_top

/-- Integrals against the Mendelian offspring law. -/
theorem integral_mendelLaw (f : ℝ → ℝ) {g₁ g₂ : ℕ} (h₁ : g₁ ≤ 2) (h₂ : g₂ ≤ 2) :
    ∫ x, f x ∂mendelLaw g₁ g₂ =
      (1 - (g₁ : ℝ) / 2) * (1 - (g₂ : ℝ) / 2) * f 0 +
        ((g₁ : ℝ) / 2 * (1 - (g₂ : ℝ) / 2) + (1 - (g₁ : ℝ) / 2) * ((g₂ : ℝ) / 2)) * f 1 +
        (g₁ : ℝ) / 2 * ((g₂ : ℝ) / 2) * f 2 := by
  have h₁' : (g₁ : ℝ) ≤ 2 := by exact_mod_cast h₁
  have h₂' : (g₂ : ℝ) ≤ 2 := by exact_mod_cast h₂
  have hg₁ : (0 : ℝ) ≤ g₁ := Nat.cast_nonneg _
  have hg₂ : (0 : ℝ) ≤ g₂ := Nat.cast_nonneg _
  have hi : ∀ a : ℝ, ∀ c : ℝ≥0∞, c ≠ ⊤ → Integrable f (c • Measure.dirac a) :=
    fun a c hc => (integrable_dirac enorm_lt_top).smul_measure hc
  unfold mendelLaw
  rw [integral_add_measure ((hi _ _ ENNReal.ofReal_ne_top).add_measure (hi _ _ ENNReal.ofReal_ne_top))
      (hi _ _ ENNReal.ofReal_ne_top),
    integral_add_measure (hi _ _ ENNReal.ofReal_ne_top) (hi _ _ ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (by nlinarith), ENNReal.toReal_ofReal (by nlinarith),
    ENNReal.toReal_ofReal (by nlinarith)]
  simp only [smul_eq_mul]

/-- **Per-locus segregation variance.** A Mendelian draw from parents carrying `g₁, g₂ ≤ 2`
focal alleles has variance `p₁ (1 - p₁) + p₂ (1 - p₂)` with `pᵢ = gᵢ / 2`. -/
theorem variance_mendelLaw {g₁ g₂ : ℕ} (h₁ : g₁ ≤ 2) (h₂ : g₂ ≤ 2) :
    Var[id; mendelLaw g₁ g₂] =
      (g₁ : ℝ) / 2 * (1 - (g₁ : ℝ) / 2) + (g₂ : ℝ) / 2 * (1 - (g₂ : ℝ) / 2) := by
  have := isProbabilityMeasure_mendelLaw h₁ h₂
  have hae : ∀ᵐ x ∂(mendelLaw g₁ g₂), (id : ℝ → ℝ) x ∈ Set.Icc (0 : ℝ) 2 :=
    ae_iff.2 (mendelLaw_compl_Icc g₁ g₂)
  have hmem : MemLp (id : ℝ → ℝ) 2 (mendelLaw g₁ g₂) :=
    memLp_of_bounded hae measurable_id.aestronglyMeasurable 2
  rw [variance_eq_sub hmem]
  have e1 := integral_mendelLaw (fun x => x) h₁ h₂
  have e2 := integral_mendelLaw (fun x => x ^ 2) h₁ h₂
  simp only [Pi.pow_apply, id] at e1 e2 ⊢
  rw [e1, e2]
  ring

/-- **Segregation Berry–Esseen bound for Mendelian draws.** If the offspring allele count at
locus `l` has the Mendelian law of parents carrying `g₁ l` and `g₂ l` focal alleles, the loci are
unlinked (independent), and `|a l| ≤ B / √M`, then whenever `σ² = Var(R_M) > 0`,
`|P(R_M ≤ x) - Φ(x / σ)| ≤ 336 B³ / (σ³ √M)`. -/
theorem abs_mendelian_segregation_cdf_sub_le {P : Measure Ω} [IsProbabilityMeasure P] {M : ℕ}
    {B σ : ℝ} {a : ℕ → ℝ} {X : ℕ → Ω → ℝ} {g₁ g₂ : ℕ → ℕ} (hXm : ∀ l, Measurable (X l))
    (hind : iIndepFun X P) (hlaw : ∀ l, P.map (X l) = mendelLaw (g₁ l) (g₂ l))
    (ha : ∀ l < M, |a l| ≤ B / √M) (hσ : 0 < σ)
    (hvar : Var[segregationDeviation P M a X; P] = σ ^ 2) (x : ℝ) :
    |P.real {ω | segregationDeviation P M a X ω ≤ x} -
        (gaussianReal 0 1).real (Set.Iic (x / σ))| ≤ 336 * B ^ 3 / (σ ^ 3 * √M) := by
  refine abs_segregation_cdf_sub_le hXm hind (fun l => ?_) ha hσ hvar x
  have h := mendelLaw_compl_Icc (g₁ l) (g₂ l)
  rw [← hlaw l, Measure.map_apply (hXm l) measurableSet_Icc.compl] at h
  exact ae_iff.2 h

/-- **Segregation Berry–Esseen bound for Mendelian draws, explicit variance form.** As in
`abs_mendelian_segregation_cdf_sub_le`, but with the variance premise replaced by its
explicit Mendelian value: if `g₁ l, g₂ l ≤ 2` at every locus and
`∑ l ∈ range M, a l ^ 2 * (g₁ l / 2 * (1 - g₁ l / 2) + g₂ l / 2 * (1 - g₂ l / 2)) = σ ^ 2`,
then the same bound `336 B³ / (σ³ √M)` holds. -/
theorem abs_mendelian_segregation_cdf_sub_le_of_variance_eq {P : Measure Ω}
    [IsProbabilityMeasure P] {M : ℕ} {B σ : ℝ} {a : ℕ → ℝ} {X : ℕ → Ω → ℝ} {g₁ g₂ : ℕ → ℕ}
    (hXm : ∀ l, Measurable (X l)) (hind : iIndepFun X P)
    (hlaw : ∀ l, P.map (X l) = mendelLaw (g₁ l) (g₂ l)) (hg₁ : ∀ l, g₁ l ≤ 2)
    (hg₂ : ∀ l, g₂ l ≤ 2) (ha : ∀ l < M, |a l| ≤ B / √M) (hσ : 0 < σ)
    (hvar : ∑ l ∈ range M, a l ^ 2 * ((g₁ l : ℝ) / 2 * (1 - (g₁ l : ℝ) / 2) +
      (g₂ l : ℝ) / 2 * (1 - (g₂ l : ℝ) / 2)) = σ ^ 2) (x : ℝ) :
    |P.real {ω | segregationDeviation P M a X ω ≤ x} -
        (gaussianReal 0 1).real (Set.Iic (x / σ))| ≤ 336 * B ^ 3 / (σ ^ 3 * √M) := by
  have hX : ∀ l, ∀ᵐ ω ∂P, X l ω ∈ Set.Icc (0 : ℝ) 2 := fun l => by
    have h := mendelLaw_compl_Icc (g₁ l) (g₂ l)
    rw [← hlaw l, Measure.map_apply (hXm l) measurableSet_Icc.compl] at h
    exact ae_iff.2 h
  have hvar' : Var[segregationDeviation P M a X; P] = σ ^ 2 := by
    rw [variance_segregationDeviation hXm hind hX]
    refine (Finset.sum_congr rfl fun l _ => ?_).trans hvar
    rw [← variance_id_map (hXm l).aemeasurable, hlaw l, variance_mendelLaw (hg₁ l) (hg₂ l)]
  exact abs_mendelian_segregation_cdf_sub_le hXm hind hlaw ha hσ hvar' x

end MathlibExt.Biology.PopulationGenetics.Classical.InfinitesimalLimit
