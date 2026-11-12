/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFS
public import Mathlib.Probability.Moments.Covariance
import Mathlib.Data.Nat.Choose.Cast

/-!
# Covariances of the site frequency spectrum

The expected unfolded site frequency spectrum `E ξ_i = θ / i` (Fu 1995) is
`SiteFrequencySpectrum.integral_sfs`. This file computes the second moments
`Cov(ξ_i, ξ_j)` from the covariances of the branch lengths and records which of those
covariances each classical estimator of `θ` needs.

## Model

Time is in units of `2N` generations and mutations fall at rate `θ / 2` per lineage
(`θ = 4Nu`), as in `Coalescent/Kingman.lean`. The genealogy of a sample of `n` copies is
summarized by the branch-length classes `L_i`, the total length of the branches subtending
exactly `i` copies. Under Kingman's coalescent, `L_i = sfsLength n i τ T` with holding times
`T = K.T` and an independent random-joining block-size history `τ`, exactly as in
`SiteFrequencySpectrum.integral_sfs`.

Neutral infinite-sites mutation is Poisson along the branches: given the genealogy, the
numbers of mutations on disjoint sets of branches are independent Poisson variables with mean
`θ / 2` times the length. A mutation on a branch subtending `i` copies is a site with derived
allele count `i`, and the branch classes for different `i` are disjoint, so given the genealogy
the `ξ_i` are independent `Poisson((θ / 2) L_i)`. The structure `SFSCondMoments` records the
first two conditional moments this implies, together with square integrability; these are the
hypotheses (the mutation model is not constructed here, as in `Coalescent/TajimaVariance.lean`).

## Results

* `SFSCondMoments.covariance_count`: the law of total covariance gives
  `Cov(ξ_i, ξ_j) = δ_{ij} (θ / 2) E L_i + (θ / 2)² Cov(L_i, L_j)` (Fu 1995).
* `SFSCondMoments.covariance_sum`, `SFSCondMoments.variance_sum`: for linear statistics,
  `Var(∑ a_i ξ_i) = (θ / 2) ∑ a_i² E L_i + (θ / 2)² Var(∑ a_i L_i)`. The second-order term
  depends on the branch-length covariance matrix only through the variance of the *same*
  linear combination of branch lengths, `∑_{i,j} a_i a_j Cov(L_i, L_j)`
  (`variance_sum_eq_sum_covariance`).
* Under Kingman's coalescent the first-order term comes from Fu's expected spectrum
  (`covariance_count_kingman`, `variance_sum_kingman`):
  `Cov(ξ_i, ξ_j) = δ_{ij} θ / i + (θ / 2)² Cov(L_i, L_j)`. The branch lengths are square
  integrable (`memLp_sfsLength`, `sfsCondMoments_kingman`).

Which branch-length covariances each estimator needs:

* **Watterson** `θ_W = S / a₁`, `S = ∑_i ξ_i` (`variance_watterson_kingman`):
  `Var θ_W = θ / a₁ + (θ / (2 a₁))² Var(∑_i L_i)`; only the total `∑_{i,j} Cov(L_i, L_j)`.
* **Achaz's weighted estimators** `θ_ω = ∑_i ω_i i ξ_i` (`variance_thetaWeighted_kingman`):
  `Var θ_ω = θ ∑_i ω_i² i + (θ / 2)² Var(∑_i ω_i i L_i)`; the covariances weighted by
  `ω_i ω_j i j`.
* **Tajima's** `θ_π = ∑_i i (n - i) ξ_i / C(n, 2)` (`variance_thetaPi_kingman`):
  `Var θ_π = b₁ θ + (θ / 2)² Var(θ_π[L])`, with Tajima's `b₁` (`sum_piWeight_sq_mul`); the
  covariances weighted by `i (n - i) j (n - j) / C(n, 2)²`.
* **Tajima's `D` numerator** `θ_π - S / a₁ = ∑_i w_i ξ_i`, `w_i = i (n - i) / C(n, 2) - 1 / a₁`
  (`variance_tajimaNumerator_kingman`): `Var = c₁ θ + (θ / 2)² Var(∑_i w_i L_i)`, with
  Tajima's `c₁` (`sum_tajimaNumWeight_sq_div`); the covariances weighted by `w_i w_j`.

The `θ`-linear coefficients `1 / a₁`, `b₁`, `c₁` agree with `Coalescent/Tajima.lean` and
`Coalescent/TajimaVariance.lean`. Fu's closed form of `σ_{ij} = Cov(L_i, L_j) / 4` (and hence
the `θ²` coefficients `a₂ / a₁²`, `b₂`, `c₂` from the SFS side) is not derived here; it needs
the joint second moments of the random-joining block counts. The identity `∑_i L_i = L` (total
branch length) is also not proved here.

## References

* Y.-X. Fu, *Statistical properties of segregating sites*, Theor. Popul. Biol. 48 (1995),
  172–197.
* G. Achaz, *Frequency spectrum neutrality tests: one for all and all for one*, Genetics 183
  (2009), 249–258.
* F. Tajima, *Evolutionary relationship of DNA sequences in finite populations*, Genetics 105
  (1983), 437–460.
* F. Tajima, *Statistical method for testing the neutral mutation hypothesis by DNA
  polymorphism*, Genetics 123 (1989), 585–595.
* G. A. Watterson, *On the number of segregating sites in genetical models without
  recombination*, Theor. Popul. Biol. 7 (1975), 256–276.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.SFSCovariance

open SiteFrequencySpectrum VariableSFS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Conditional moments of the site frequency spectrum given the genealogy.** Given the
genealogy σ-algebra `m`, the counts `ξ i` (sites whose derived allele is carried by exactly `i`
sample copies) are independent Poisson variables with means `(θ / 2) L i`, where `L i` is the
total length of the branches subtending exactly `i` copies. Only the first two conditional
moments are recorded:

* `E[ξ_i | m] = (θ / 2) L_i`;
* `E[ξ_i ξ_j | m] = (θ / 2)² L_i L_j + δ_{ij} (θ / 2) L_i` (conditional covariance
  `δ_{ij} (θ / 2) L_i`: distinct size classes occupy disjoint sets of branches, so their
  mutation counts are conditionally independent; a Poisson count has variance equal to its
  mean),

together with square integrability of the counts and of the branch lengths. -/
structure SFSCondMoments (μ : Measure Ω) (m : MeasurableSpace Ω) (θ : ℝ)
    (ξ L : ℕ → Ω → ℝ) : Prop where
  /-- Each count is square integrable. -/
  memLp_count : ∀ i, MemLp (ξ i) 2 μ
  /-- Each branch-length class is square integrable. -/
  memLp_length : ∀ i, MemLp (L i) 2 μ
  /-- Conditional mean `(θ / 2) L_i`. -/
  condExp_count : ∀ i, μ[ξ i | m] =ᵐ[μ] fun ω => θ / 2 * L i ω
  /-- Conditional second moments of independent Poisson counts. -/
  condExp_count_mul : ∀ i j, μ[fun ω => ξ i ω * ξ j ω | m] =ᵐ[μ]
    fun ω => (θ / 2) ^ 2 * (L i ω * L j ω) + if i = j then θ / 2 * L i ω else 0

namespace SFSCondMoments

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} {θ : ℝ}
  {ξ L : ℕ → Ω → ℝ}

/-- The mean of a count is `(θ / 2)` times the mean branch length of its class. -/
theorem integral_count (h : SFSCondMoments μ m θ ξ L) (hm : m ≤ mΩ) (i : ℕ) :
    μ[ξ i] = θ / 2 * μ[L i] := by
  rw [← integral_condExp hm, integral_congr_ae (h.condExp_count i), integral_const_mul]

/-- **Covariance of two SFS entries** (Fu 1995): by the law of total covariance,
`Cov(ξ_i, ξ_j) = δ_{ij} (θ / 2) E L_i + (θ / 2)² Cov(L_i, L_j)`. For `i ≠ j` the covariance
comes entirely from the covariance of the branch lengths. -/
theorem covariance_count (h : SFSCondMoments μ m θ ξ L) (hm : m ≤ mΩ) (i j : ℕ) :
    cov[ξ i, ξ j; μ] =
      (if i = j then θ / 2 * μ[L i] else 0) + (θ / 2) ^ 2 * cov[L i, L j; μ] := by
  have hLL : Integrable (fun ω => L i ω * L j ω) μ :=
    (h.memLp_length i).integrable_mul (h.memLp_length j)
  have hprod : μ[fun ω => ξ i ω * ξ j ω] =
      (θ / 2) ^ 2 * μ[fun ω => L i ω * L j ω] + if i = j then θ / 2 * μ[L i] else 0 := by
    rw [← integral_condExp hm, integral_congr_ae (h.condExp_count_mul i j)]
    split_ifs with hij
    · rw [integral_add (hLL.const_mul _) ((h.memLp_length i).integrable one_le_two |>.const_mul _),
        integral_const_mul, integral_const_mul]
    · simp only [add_zero]
      rw [integral_const_mul]
  rw [covariance_eq_sub (h.memLp_count i) (h.memLp_count j),
    covariance_eq_sub (h.memLp_length i) (h.memLp_length j)]
  change μ[fun ω => ξ i ω * ξ j ω] - _ = _ + _ * (μ[fun ω => L i ω * L j ω] - _)
  rw [hprod, h.integral_count hm i, h.integral_count hm j]
  ring

/-- **Covariance of two linear SFS statistics**:
`Cov(∑ a_i ξ_i, ∑ b_j ξ_j) = (θ / 2) ∑ a_i b_i E L_i + (θ / 2)² Cov(∑ a_i L_i, ∑ b_j L_j)`.
The branch-length covariance matrix enters only through the covariance of the *same* linear
combinations of the branch lengths. -/
theorem covariance_sum (h : SFSCondMoments μ m θ ξ L) (hm : m ≤ mΩ) (s : Finset ℕ)
    (a b : ℕ → ℝ) :
    cov[fun ω => ∑ i ∈ s, a i * ξ i ω, fun ω => ∑ j ∈ s, b j * ξ j ω; μ] =
      θ / 2 * ∑ i ∈ s, a i * b i * μ[L i] +
        (θ / 2) ^ 2 * cov[fun ω => ∑ i ∈ s, a i * L i ω, fun ω => ∑ j ∈ s, b j * L j ω; μ] := by
  rw [covariance_fun_sum_fun_sum' (X := fun i ω => a i * ξ i ω) (Y := fun j ω => b j * ξ j ω)
      (fun i _ => (h.memLp_count i).const_mul _) (fun j _ => (h.memLp_count j).const_mul _),
    covariance_fun_sum_fun_sum' (X := fun i ω => a i * L i ω) (Y := fun j ω => b j * L j ω)
      (fun i _ => (h.memLp_length i).const_mul _) (fun j _ => (h.memLp_length j).const_mul _)]
  simp only [covariance_const_mul_left, covariance_const_mul_right, h.covariance_count hm,
    mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq, mul_sum]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    simp only [hi, ↓reduceIte]
    ring
  · refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    ring

/-- **Variance of a linear SFS statistic**:
`Var(∑ a_i ξ_i) = (θ / 2) ∑ a_i² E L_i + (θ / 2)² Var(∑ a_i L_i)`. -/
theorem variance_sum (h : SFSCondMoments μ m θ ξ L) (hm : m ≤ mΩ) (s : Finset ℕ)
    (a : ℕ → ℝ) :
    Var[fun ω => ∑ i ∈ s, a i * ξ i ω; μ] =
      θ / 2 * ∑ i ∈ s, a i ^ 2 * μ[L i] +
        (θ / 2) ^ 2 * Var[fun ω => ∑ i ∈ s, a i * L i ω; μ] := by
  have hξ : MemLp (fun ω => ∑ i ∈ s, a i * ξ i ω) 2 μ :=
    memLp_finsetSum s fun i _ => (h.memLp_count i).const_mul _
  have hL : MemLp (fun ω => ∑ i ∈ s, a i * L i ω) 2 μ :=
    memLp_finsetSum s fun i _ => (h.memLp_length i).const_mul _
  rw [← covariance_self hξ.aestronglyMeasurable.aemeasurable,
    ← covariance_self hL.aestronglyMeasurable.aemeasurable, h.covariance_sum hm s a a]
  simp only [sq]

end SFSCondMoments

/-- The variance of a linear combination of branch lengths, expanded into the branch-length
covariance matrix: `Var(∑ c_i L_i) = ∑_i ∑_j c_i c_j Cov(L_i, L_j)`. -/
theorem variance_sum_eq_sum_covariance {μ : Measure Ω} [IsProbabilityMeasure μ]
    {L : ℕ → Ω → ℝ} (hL : ∀ i, MemLp (L i) 2 μ) (s : Finset ℕ) (c : ℕ → ℝ) :
    Var[fun ω => ∑ i ∈ s, c i * L i ω; μ] =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * cov[L i, L j; μ] := by
  have hc : MemLp (fun ω => ∑ i ∈ s, c i * L i ω) 2 μ :=
    memLp_finsetSum s fun i _ => (hL i).const_mul _
  rw [← covariance_self hc.aestronglyMeasurable.aemeasurable,
    covariance_fun_sum_fun_sum' (X := fun i ω => c i * L i ω) (Y := fun j ω => c j * L j ω)
      (fun i _ => (hL i).const_mul _) (fun j _ => (hL j).const_mul _)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

/-! ### Weights of Watterson's, Tajima's and the `D`-numerator statistics -/

/-- The coefficient of `ξ_i` in Tajima's `D` numerator `θ_π - S / a₁` written on the SFS:
`i (n - i) / C(n, 2) - 1 / a₁`. -/
noncomputable def tajimaNumWeight (n i : ℕ) : ℝ :=
  ((n : ℝ) - i) / (n.choose 2 : ℝ) * i - (tajimaA1 n)⁻¹

private lemma sum_Ico_one_eq_range {f : ℕ → ℝ} (hf : f 0 = 0) (n : ℕ) :
    ∑ i ∈ Ico 1 n, f i = ∑ i ∈ range n, f i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hn, hf, zero_add]

private lemma sum_range_cast_pow (n : ℕ) :
    ∑ i ∈ range n, (i : ℝ) = n * (n - 1) / 2 ∧
    ∑ i ∈ range n, (i : ℝ) ^ 2 = n * (n - 1) * (2 * n - 1) / 6 ∧
    ∑ i ∈ range n, (i : ℝ) ^ 3 = (n * (n - 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_⟩ <;> rw [sum_range_succ] <;> push_cast
    · rw [h1]; ring
    · rw [h2]; ring
    · rw [h3]; ring

/-- `∑_{i=1}^{n-1} i (n - i)² = n² (n² - 1) / 12`. -/
private lemma sum_mul_sub_sq (n : ℕ) :
    ∑ i ∈ Ico 1 n, (i : ℝ) * ((n : ℝ) - i) ^ 2 = (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 - 1) / 12 := by
  rw [sum_Ico_one_eq_range (f := fun i : ℕ => (i : ℝ) * ((n : ℝ) - i) ^ 2) (by simp)]
  obtain ⟨h1, h2, h3⟩ := sum_range_cast_pow n
  have : ∀ i : ℕ, (i : ℝ) * ((n : ℝ) - i) ^ 2 =
      (n : ℝ) ^ 2 * i - 2 * n * (i : ℝ) ^ 2 + (i : ℝ) ^ 3 := fun i => by ring
  simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, h1, h2, h3]
  ring

private lemma choose_two_cast_pos {n : ℕ} (hn : 2 ≤ n) : (0 : ℝ) < (n.choose 2 : ℝ) := by
  exact_mod_cast Nat.choose_pos hn

/-- The weights of `θ_π` sum to one: `∑_{i=1}^{n-1} (n - i) / C(n, 2) = 1`. -/
private lemma sum_piWeight {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ Ico 1 n, ((n : ℝ) - i) / (n.choose 2 : ℝ) = 1 := by
  have hC := choose_two_cast_pos hn
  have hs : ∑ i ∈ Ico 1 n, ((n : ℝ) - i) = n * (n - 1) / 2 := by
    have h0 := sum_Ico_one_eq_range (f := fun i : ℕ => (i : ℝ)) (by simp) n
    rw [sum_sub_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul, h0, (sum_range_cast_pow n).1,
      Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← sum_div, hs, Nat.cast_choose_two, div_self (by rw [← Nat.cast_choose_two]; exact hC.ne')]

private lemma tajimaA1_pos {n : ℕ} (hn : 2 ≤ n) : 0 < tajimaA1 n :=
  sum_pos (fun i hi => by have := (mem_Ico.1 hi).1; positivity) ⟨1, mem_Ico.2 ⟨le_rfl, hn⟩⟩

/-- The `θ`-linear coefficient of `Var θ_π` from the SFS:
`∑_{i=1}^{n-1} ((n - i) / C(n, 2))² i = b₁ = (n + 1) / (3 (n - 1))` (Tajima 1983). -/
theorem sum_piWeight_sq_mul {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ Ico 1 n, (((n : ℝ) - i) / (n.choose 2 : ℝ)) ^ 2 * i = tajimaB1 n := by
  have hC := choose_two_cast_pos hn
  have hn1 : (0 : ℝ) < n - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h : ∀ i : ℕ, (((n : ℝ) - i) / (n.choose 2 : ℝ)) ^ 2 * i =
      ((n.choose 2 : ℝ) ^ 2)⁻¹ * ((i : ℝ) * ((n : ℝ) - i) ^ 2) := fun i => by
    field_simp
  have hC2 : (n.choose 2 : ℝ) = n * (n - 1) / 2 := Nat.cast_choose_two ℝ n
  rw [sum_congr rfl fun i _ => h i, ← mul_sum, sum_mul_sub_sq, tajimaB1, hC2]
  field_simp
  ring

/-- The `θ`-linear coefficient of the variance of Tajima's `D` numerator from the SFS:
`∑_{i=1}^{n-1} w_i² / i = c₁ = b₁ - 1 / a₁` with `w_i = tajimaNumWeight n i` (Tajima 1989). -/
theorem sum_tajimaNumWeight_sq_div {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ Ico 1 n, tajimaNumWeight n i ^ 2 / i = tajimaC1 n := by
  have hC := choose_two_cast_pos hn
  have ha := tajimaA1_pos hn
  have h : ∀ i ∈ Ico 1 n, tajimaNumWeight n i ^ 2 / i =
      (((n : ℝ) - i) / (n.choose 2 : ℝ)) ^ 2 * i
        - 2 * (tajimaA1 n)⁻¹ * (((n : ℝ) - i) / (n.choose 2 : ℝ))
        + (tajimaA1 n)⁻¹ ^ 2 * (i : ℝ)⁻¹ := fun i hi => by
    have : (i : ℝ) ≠ 0 := by have := (mem_Ico.1 hi).1; positivity
    unfold tajimaNumWeight
    field_simp
    ring
  rw [sum_congr rfl h, sum_add_distrib, sum_sub_distrib, sum_piWeight_sq_mul hn, ← mul_sum,
    ← mul_sum, ← tajimaA1, sum_piWeight hn, tajimaC1]
  field_simp
  ring

/-! ### Kingman's coalescent -/

section Kingman

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {K : KingmanTimes μ n}
  {τ : Ω → List (List ℕ)} {θ : ℝ} {ξ : ℕ → Ω → ℝ}

/-- Under the hypotheses of `SiteFrequencySpectrum.integral_sfs`, `(θ / 2) E L_i = θ / i` for
`1 ≤ i ≤ n - 1`. -/
private lemma half_mul_integral_sfsLength (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)))
    {i : ℕ} (hi : i ∈ Ico 1 n) :
    θ / 2 * μ[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω)] = θ / i := by
  rw [← h.integral_count (sup_le hτ (measurable_pi_iff.2 hT).comap_le) i]
  exact integral_sfs K hT hτ hτ_law h_indep (fun j => (h.memLp_count j).integrable one_le_two)
    h.condExp_count (mem_Ico.1 hi).1 (mem_Ico.1 hi).2

omit [IsProbabilityMeasure μ] in
/-- Each Kingman holding time is square integrable. -/
private lemma memLp_T {k : ℕ} (hk : k ∈ Icc 2 n) : MemLp (K.T k) 2 μ :=
  (K.hasLaw k hk).memLp_comp (f := id)
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (by simpa using integrable_pow_expMeasure (KingmanTimes.choose_two_pos hk) 2))

/-- Under Kingman's coalescent with a random-joining block-size history, each branch-length
class `L_i = sfsLength n i τ T` is square integrable (the block counts are a.s. bounded, the
holding times are exponential). -/
theorem memLp_sfsLength (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (i : ℕ) : MemLp (fun ω => sfsLength n i (τ ω) (fun k => K.T k ω)) 2 μ := by
  obtain ⟨F, hF0, -⟩ := exists_finset_randomJoining (n - 1) (List.replicate n 1)
  have hae : ∀ᵐ ω ∂μ, τ ω ∈ F := by
    rw [ae_iff]
    have : {ω | ¬ τ ω ∈ F} = ⋃ ps : {ps // ps ∉ F}, τ ⁻¹' {ps.1} := by
      ext ω; simp
    rw [this]
    refine measure_iUnion_null fun ps => ?_
    rw [← measureReal_eq_zero_iff, hτ_law, hF0 _ ps.2]
  refine memLp_finsetSum _ fun k hk => ?_
  set g : List (List ℕ) → ℝ := fun ps => ((ps.getD (n - k) []).count i : ℝ)
  have hg : Measurable (fun ω => g (τ ω)) := by
    rw [measurable_iff_comap_le]
    refine le_trans ?_ hτ
    rw [show (fun ω => g (τ ω)) = g ∘ τ from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono le_top
  have hbd : MemLp (fun ω => g (τ ω)) ⊤ μ := by
    refine memLp_top_of_bound hg.aestronglyMeasurable (∑ ps ∈ F, g ps) ?_
    filter_upwards [hae] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact single_le_sum (f := g) (fun _ _ => by positivity) hω
  exact hbd.fun_mul (memLp_T hk)

/-- Build `SFSCondMoments` for the Kingman genealogy: square integrability of the branch-length
classes is automatic (`memLp_sfsLength`). -/
theorem sfsCondMoments_kingman (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (hξ2 : ∀ i, MemLp (ξ i) 2 μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => K.T k ω))
    (hξξ : ∀ i j, μ[fun ω => ξ i ω * ξ j ω | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => (θ / 2) ^ 2 * (sfsLength n i (τ ω) (fun k => K.T k ω) *
        sfsLength n j (τ ω) (fun k => K.T k ω)) +
        if i = j then θ / 2 * sfsLength n i (τ ω) (fun k => K.T k ω) else 0) :
    SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)) :=
  ⟨hξ2, memLp_sfsLength hτ hτ_law, hξ, hξξ⟩

/-- **Covariance of SFS entries under Kingman's coalescent** (Fu 1995): with the genealogy
(holding times `K.T` and an independent random-joining block-size history `τ`) and the
conditionally Poisson counts of `SFSCondMoments`,
`Cov(ξ_i, ξ_j) = δ_{ij} θ / i + (θ / 2)² Cov(L_i, L_j)` for `1 ≤ i ≤ n - 1`, where
`L_i = sfsLength n i τ T` and the diagonal term is Fu's expected spectrum
(`SiteFrequencySpectrum.integral_sfs`). Fu's `σ_{ij}` is `Cov(L_i, L_j) / 4`. -/
theorem covariance_count_kingman (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)))
    {i : ℕ} (hi : i ∈ Ico 1 n) (j : ℕ) :
    cov[ξ i, ξ j; μ] = (if i = j then θ / i else 0) +
      (θ / 2) ^ 2 * cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
        fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] := by
  rw [h.covariance_count (sup_le hτ (measurable_pi_iff.2 hT).comap_le),
    half_mul_integral_sfsLength hT hτ hτ_law h_indep h hi]

/-- **Variance of a linear SFS statistic under Kingman's coalescent**:
`Var(∑_{i=1}^{n-1} a_i ξ_i) = θ ∑_i a_i² / i + (θ / 2)² Var(∑_i a_i L_i)`. The second-order
term needs exactly the variance of the same linear combination of the branch lengths
`L_i = sfsLength n i τ T`, i.e. `∑_{i,j} a_i a_j Cov(L_i, L_j)`
(`variance_sum_eq_sum_covariance`). -/
theorem variance_sum_kingman (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)))
    (a : ℕ → ℝ) :
    Var[fun ω => ∑ i ∈ Ico 1 n, a i * ξ i ω; μ] =
      θ * ∑ i ∈ Ico 1 n, a i ^ 2 / i +
        (θ / 2) ^ 2 * Var[fun ω => ∑ i ∈ Ico 1 n, a i * sfsLength n i (τ ω) (fun k => K.T k ω);
          μ] := by
  rw [h.variance_sum (sup_le hτ (measurable_pi_iff.2 hT).comap_le), mul_sum, mul_sum]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [mul_left_comm, half_mul_integral_sfsLength hT hτ hτ_law h_indep h hi]
  ring

/-- **Variance of Watterson's estimator from the SFS** (`n ≥ 2`):
`Var(S / a₁) = θ / a₁ + (θ / (2 a₁))² Var(∑_i L_i)` with `S = ∑_{i=1}^{n-1} ξ_i`. Watterson's
estimator needs, of the branch-length covariances, only `Var(∑_i L_i) = ∑_{i,j} Cov(L_i, L_j)`,
the variance of the total length of the branches subtending `1, …, n - 1` copies. -/
theorem variance_watterson_kingman (hn : 2 ≤ n) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω))) :
    Var[fun ω => (∑ i ∈ Ico 1 n, ξ i ω) / tajimaA1 n; μ] =
      θ / tajimaA1 n + (θ / (2 * tajimaA1 n)) ^ 2 *
        Var[fun ω => ∑ i ∈ Ico 1 n, sfsLength n i (τ ω) (fun k => K.T k ω); μ] := by
  have ha := (tajimaA1_pos hn).ne'
  have hdiv : ∀ X : ℕ → Ω → ℝ, (fun ω => (∑ i ∈ Ico 1 n, X i ω) / tajimaA1 n) =
      fun ω => ∑ i ∈ Ico 1 n, (tajimaA1 n)⁻¹ * X i ω := fun X => by
    funext ω
    rw [div_eq_inv_mul, mul_sum]
  rw [hdiv, variance_sum_kingman hT hτ hτ_law h_indep h, ← hdiv,
    show (fun ω => (∑ i ∈ Ico 1 n, sfsLength n i (τ ω) (fun k => K.T k ω)) / tajimaA1 n) =
      fun ω => (tajimaA1 n)⁻¹ * ∑ i ∈ Ico 1 n, sfsLength n i (τ ω) (fun k => K.T k ω) from
      funext fun ω => div_eq_inv_mul _ _, variance_const_mul]
  have hs : ∑ i ∈ Ico 1 n, (tajimaA1 n)⁻¹ ^ 2 / (i : ℝ) = (tajimaA1 n)⁻¹ ^ 2 * tajimaA1 n := by
    rw [tajimaA1, mul_sum]
    rfl
  rw [hs]
  field_simp

/-- **Variance of a weighted SFS estimator** (Achaz 2009): for `θ_ω = ∑_i ω_i i ξ_i`,
`Var θ_ω = θ ∑_i ω_i² i + (θ / 2)² Var(∑_i ω_i i L_i)`; the branch-length term is
`∑_{i,j} ω_i ω_j i j Cov(L_i, L_j)` (Fu's `σ_{ij} = Cov(L_i, L_j) / 4`). -/
theorem variance_thetaWeighted_kingman (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)))
    (w : ℕ → ℝ) :
    Var[thetaWeighted n w ξ; μ] =
      θ * ∑ i ∈ Ico 1 n, w i ^ 2 * i + (θ / 2) ^ 2 *
        Var[thetaWeighted n w (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)); μ] := by
  have := variance_sum_kingman hT hτ hτ_law h_indep h (fun i => w i * i)
  unfold thetaWeighted
  rw [this]
  congr 2
  refine sum_congr rfl fun i hi => ?_
  have : (i : ℝ) ≠ 0 := by have := (mem_Ico.1 hi).1; positivity
  field_simp

/-- **Variance of Tajima's `θ_π` from the SFS** (Tajima 1983, `n ≥ 2`):
`Var θ_π = b₁ θ + (θ / 2)² Var(∑_i i (n - i) L_i / C(n, 2))`. The branch-length term needs the
covariances `Cov(L_i, L_j)` weighted by `i (n - i) j (n - j) / C(n, 2)²`. -/
theorem variance_thetaPi_kingman (hn : 2 ≤ n) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω))) :
    Var[thetaPi n ξ; μ] = θ * tajimaB1 n + (θ / 2) ^ 2 *
      Var[thetaPi n (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)); μ] := by
  unfold thetaPi
  rw [variance_thetaWeighted_kingman hT hτ hτ_law h_indep h, sum_piWeight_sq_mul hn]

/-- Tajima's `D` numerator `θ_π - S / a₁` written on the SFS. -/
private lemma tajimaNum_eq (X : ℕ → Ω → ℝ) :
    (fun ω => thetaPi n X ω - (∑ i ∈ Ico 1 n, X i ω) / tajimaA1 n) =
      fun ω => ∑ i ∈ Ico 1 n, tajimaNumWeight n i * X i ω := by
  funext ω
  unfold thetaPi thetaWeighted tajimaNumWeight
  rw [div_eq_inv_mul, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- **Variance of Tajima's `D` numerator from the SFS** (Tajima 1989, `n ≥ 2`):
`Var(θ_π - S / a₁) = c₁ θ + (θ / 2)² Var(∑_i w_i L_i)` with
`w_i = i (n - i) / C(n, 2) - 1 / a₁` (`tajimaNumWeight`). The `θ`-linear coefficient is
Tajima's `c₁` (`sum_tajimaNumWeight_sq_div`); the `θ²` coefficient needs exactly the
covariances `Cov(L_i, L_j)` weighted by `w_i w_j` (`variance_sum_eq_sum_covariance`), i.e. the
combination that Tajima's `c₂` evaluates. -/
theorem variance_tajimaNumerator_kingman (hn : 2 ≤ n) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω))) :
    Var[fun ω => thetaPi n ξ ω - (∑ i ∈ Ico 1 n, ξ i ω) / tajimaA1 n; μ] =
      θ * tajimaC1 n + (θ / 2) ^ 2 *
        Var[fun ω => ∑ i ∈ Ico 1 n, tajimaNumWeight n i *
          sfsLength n i (τ ω) (fun k => K.T k ω); μ] := by
  rw [tajimaNum_eq, variance_sum_kingman hT hτ hτ_law h_indep h,
    sum_tajimaNumWeight_sq_div hn]

end Kingman

end MathlibExt.Biology.PopulationGenetics.Coalescent.SFSCovariance
