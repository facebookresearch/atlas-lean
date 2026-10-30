/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Kingman
public import Mathlib.Probability.CondVar
import Mathlib.Data.Nat.Choose.Cast

/-!
# Tajima's D: moments of the segregating sites and pairwise differences

For a sample of `n` genes under Kingman's coalescent (time in units of `2N` generations) with
infinite-sites mutation at scaled rate `θ = 4Nu` (rate `θ / 2` per lineage):

* the total branch length `L = ∑_{k=2}^n k T_k` has variance
  `Var L = ∑_{k=2}^n k² Var T_k = 4 ∑_{j=1}^{n-1} 1/j²`;
* if the number of segregating sites `S` is Poisson with mean `θ L / 2` given the genealogy
  (stated through its conditional mean and conditional variance), then
  `Var S = θ a₁ + θ² a₂` with `a₁ = ∑_{i=1}^{n-1} 1/i`, `a₂ = ∑_{i=1}^{n-1} 1/i²`
 ;
* if, for each pair of sampled genes, the number of differences has conditional mean
  `θ τ` given the pair's coalescence time `τ ~ Exp(1)`, the mean number of pairwise
  differences `π` has mean `θ`, so Tajima's numerator `π - S / a₁` has mean zero;
* with Tajima's constants `c₁, c₂` (so that `Var(π - S/a₁) = c₁ θ + c₂ θ²`, Tajima 1989) and
  `e₁ = c₁ / a₁`, `e₂ = c₂ / (a₁² + a₂)`, the statistic `e₁ S + e₂ S (S - 1)` is an unbiased
  estimator of `c₁ θ + c₂ θ²`, the variance in the denominator of Tajima's `D`.

We do not prove the variance identity `Var(π - S/a₁) = c₁ θ + c₂ θ²` itself (it needs the
joint law of the pairwise coalescence times); only the moment identities above. The mutation
model enters only through conditional-moment hypotheses (as for Watterson's estimator in
`Coalescent/Kingman.lean`), and the pairwise coalescence times only through their marginal law
`Exp(1)`. The identities hold for every real `θ` (biologically `θ > 0`). Tajima's constants are
meaningful for `n ≥ 2`; for `n ≤ 1` the definitions return Lean's junk values for division by
zero.

## Main results

* `tajimaA1`, `tajimaA2`, `tajimaB1`, `tajimaB2`, `tajimaC1`, `tajimaC2`, `tajimaE1`,
  `tajimaE2`: Tajima's constants (Tajima 1989).
* `KingmanTimes.variance_totalLength`: `Var L = 4 a₂`.
* `KingmanTimes.variance_segSites`: `Var S = θ a₁ + θ² a₂`.
* `integral_meanPairDiff`: `E π = θ`.
* `KingmanTimes.integral_tajimaNumerator`: `E[π - S / a₁] = 0`.
* `KingmanTimes.integral_tajimaVarEstimator`: `E[e₁ S + e₂ S (S - 1)] = c₁ θ + c₂ θ²`.

## References

* F. Tajima, *Evolutionary relationship of DNA sequences in finite populations*, Genetics 105
  (1983), 437–460.
* F. Tajima, *Statistical method for testing the neutral mutation hypothesis by DNA
  polymorphism*, Genetics 123 (1989), 585–595.
* G. A. Watterson, *On the number of segregating sites in genetical models without
  recombination*, Theor. Popul. Biol. 7 (1975), 256–276.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

/-! ### Tajima's constants -/

/-- `a₁ = ∑_{i=1}^{n-1} 1/i` (Tajima 1989). -/
def tajimaA1 (n : ℕ) : ℝ := ∑ i ∈ Ico 1 n, (i : ℝ)⁻¹

/-- `a₂ = ∑_{i=1}^{n-1} 1/i²` (Tajima 1989). -/
def tajimaA2 (n : ℕ) : ℝ := ∑ i ∈ Ico 1 n, ((i : ℝ) ^ 2)⁻¹

/-- `b₁ = (n + 1) / (3 (n - 1))` (Tajima 1989), for `n ≥ 2`. -/
def tajimaB1 (n : ℕ) : ℝ := ((n : ℝ) + 1) / (3 * ((n : ℝ) - 1))

/-- `b₂ = 2 (n² + n + 3) / (9 n (n - 1))` (Tajima 1989), for `n ≥ 2`. -/
def tajimaB2 (n : ℕ) : ℝ := 2 * ((n : ℝ) ^ 2 + n + 3) / (9 * n * ((n : ℝ) - 1))

/-- `c₁ = b₁ - 1/a₁` (Tajima 1989), for `n ≥ 2`. -/
def tajimaC1 (n : ℕ) : ℝ := tajimaB1 n - 1 / tajimaA1 n

/-- `c₂ = b₂ - (n + 2)/(a₁ n) + a₂/a₁²` (Tajima 1989), for `n ≥ 2`. -/
def tajimaC2 (n : ℕ) : ℝ :=
  tajimaB2 n - ((n : ℝ) + 2) / (tajimaA1 n * n) + tajimaA2 n / tajimaA1 n ^ 2

/-- `e₁ = c₁ / a₁` (Tajima 1989), for `n ≥ 2`. -/
def tajimaE1 (n : ℕ) : ℝ := tajimaC1 n / tajimaA1 n

/-- `e₂ = c₂ / (a₁² + a₂)` (Tajima 1989), for `n ≥ 2`. -/
def tajimaE2 (n : ℕ) : ℝ := tajimaC2 n / (tajimaA1 n ^ 2 + tajimaA2 n)

/-- `a₁` is the harmonic number `H_{n-1}`. -/
theorem tajimaA1_eq_harmonic (n : ℕ) : tajimaA1 n = (harmonic (n - 1) : ℝ) := by
  induction n with
  | zero => simp [tajimaA1]
  | succ n ih =>
    cases n with
    | zero => simp [tajimaA1]
    | succ n =>
      have hstep : tajimaA1 (n + 1 + 1) = tajimaA1 (n + 1) + ((n + 1 : ℕ) : ℝ)⁻¹ :=
        sum_Ico_succ_top (by omega) _
      rw [hstep, ih]
      simp only [Nat.add_sub_cancel, harmonic_succ, Rat.cast_add, Rat.cast_inv,
        Rat.cast_natCast]

private theorem branch_variance_term {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ) ^ 2 * (((k.choose 2 : ℕ) : ℝ)⁻¹) ^ 2 =
      4 * ((((k - 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
  rw [Nat.cast_choose_two, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk1 : (k : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  field_simp
  norm_num

private theorem branch_variance_sum (n : ℕ) :
    (∑ k ∈ Icc 2 n, (k : ℝ) ^ 2 * (((k.choose 2 : ℕ) : ℝ)⁻¹) ^ 2) =
      4 * tajimaA2 n := by
  induction n with
  | zero => simp [tajimaA2]
  | succ n ih =>
    by_cases hn : 1 ≤ n
    · have hstep : tajimaA2 (n + 1) = tajimaA2 n + ((n : ℝ) ^ 2)⁻¹ :=
        sum_Ico_succ_top hn _
      rw [sum_Icc_succ_top (by omega), branch_variance_term (by omega), ih, hstep]
      simp only [Nat.add_sub_cancel]
      ring
    · have : n = 0 := by omega
      subst n
      simp [tajimaA2]

namespace KingmanTimes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : ℕ} (K : KingmanTimes μ n)

/-- Each holding time is square integrable. -/
private theorem memLp_T {k : ℕ} (hk : k ∈ Icc 2 n) : MemLp (K.T k) 2 μ :=
  (K.hasLaw k hk).memLp_comp (f := id)
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (by simpa using integrable_pow_expMeasure (choose_two_pos hk) 2))

/-- `Var[T k] = ((k.choose 2)⁻¹)²`. -/
private theorem variance_T {k : ℕ} (hk : k ∈ Icc 2 n) :
    Var[K.T k; μ] = (((k.choose 2 : ℕ) : ℝ)⁻¹) ^ 2 :=
  (K.hasLaw k hk).variance_eq_of_expMeasure (choose_two_pos hk)

/-- **Variance of the total branch length** (Watterson 1975):
`Var L = ∑_{k=2}^n k² Var T_k = 4 ∑_{j=1}^{n-1} 1/j²` (uses independence of the holding
times). -/
theorem variance_totalLength : Var[K.totalLength; μ] = 4 * tajimaA2 n := by
  classical
  let X : Icc 2 n → Ω → ℝ := fun k ω => (k : ℝ) * K.T k ω
  have hmem : ∀ i ∈ (univ : Finset (Icc 2 n)), MemLp (X i) 2 μ :=
    fun i _ => (K.memLp_T i.property).const_mul _
  have hpair : Set.Pairwise (↑(univ : Finset (Icc 2 n)))
      (fun i j => IndepFun (X i) (X j) μ) := by
    intro i _ j _ hij
    exact (K.indep.indepFun hij).comp (measurable_const.mul measurable_id)
      (measurable_const.mul measurable_id)
  have hsum : K.totalLength = ∑ i : Icc 2 n, X i := by
    ext ω
    simpa only [totalLength, Finset.sum_apply, X] using
      (sum_coe_sort (Icc 2 n) (fun k => (k : ℝ) * K.T k ω)).symm
  rw [hsum, IndepFun.variance_sum hmem hpair]
  change (∑ i : Icc 2 n, Var[fun ω => (i : ℝ) * K.T i ω; μ]) = _
  simp_rw [variance_const_mul]
  rw [sum_coe_sort (Icc 2 n) (fun k => (k : ℝ) ^ 2 * Var[K.T k; μ])]
  calc
    (∑ k ∈ Icc 2 n, (k : ℝ) ^ 2 * Var[K.T k; μ]) =
        ∑ k ∈ Icc 2 n, (k : ℝ) ^ 2 * (((k.choose 2 : ℕ) : ℝ)⁻¹) ^ 2 := by
      apply sum_congr rfl
      intro k hk
      rw [K.variance_T hk]
    _ = 4 * tajimaA2 n := branch_variance_sum n

/-- **Variance of the number of segregating sites** (Watterson 1975;
Tajima 1989): if, given the genealogy σ-algebra `m`, the number `S` of
segregating sites has conditional mean and conditional variance `(θ/2) L` (as for a Poisson
count with mean `θ L / 2`), then `Var S = θ a₁ + θ² a₂`. -/
theorem variance_segSites [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {S : Ω → ℝ} {θ : ℝ} (hS2 : MemLp S 2 μ)
    (hmean : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω)
    (hvar : Var[S; μ | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω) :
    Var[S; μ] = θ * tajimaA1 n + θ ^ 2 * tajimaA2 n := by
  rw [← integral_condVar_add_variance_condExp hm hS2,
    integral_congr_ae hvar, variance_congr hmean, integral_const_mul, variance_const_mul,
    K.integral_totalLength, K.variance_totalLength, tajimaA1_eq_harmonic]
  ring

end KingmanTimes

/-! ### Pairwise differences and Tajima's numerator -/

section Pairwise

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : ℕ}

/-- The pairs of genes in a sample of size `n`. -/
abbrev samplePairs (n : ℕ) : Finset (Finset (Fin n)) := (univ : Finset (Fin n)).powersetCard 2

/-- The mean number of pairwise differences `π = C(n, 2)⁻¹ ∑_{i<j} D_{ij}` (Tajima 1983), where
`D s` is the number of sites at which the two sequences of the pair `s` differ. -/
def meanPairDiff (n : ℕ) (D : Finset (Fin n) → Ω → ℝ) : Ω → ℝ :=
  fun ω => ((n.choose 2 : ℕ) : ℝ)⁻¹ * ∑ s ∈ samplePairs n, D s ω

/-- **Expected pairwise differences** (Tajima 1983): if, for each pair `s` of sampled genes,
the coalescence time `τ s` of the pair is exponential with rate `1` and the number `D s` of
differences has conditional mean `θ τ s` given the genealogy σ-algebra `m` (mutations at rate
`θ / 2` on each of the two branches of length `τ s`), then `E π = θ`. -/
theorem integral_meanPairDiff {m : MeasurableSpace Ω} (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {D τ : Finset (Fin n) → Ω → ℝ} {θ : ℝ} (hn : 2 ≤ n)
    (hτ : ∀ s ∈ samplePairs n, HasLaw (τ s) (expMeasure 1) μ)
    (hDint : ∀ s ∈ samplePairs n, Integrable (D s) μ)
    (hD : ∀ s ∈ samplePairs n, μ[D s | m] =ᵐ[μ] fun ω => θ * τ s ω) :
    μ[meanPairDiff n D] = θ := by
  have hpair : ∀ s ∈ samplePairs n, μ[D s] = θ := fun s hs => by
    rw [← integral_condExp hm, integral_congr_ae (hD s hs), integral_const_mul,
      (hτ s hs).integral_eq_inv_of_expMeasure one_pos, inv_one, mul_one]
  have hc : ((n.choose 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hn).ne'
  unfold meanPairDiff
  rw [integral_const_mul, integral_finsetSum _ hDint, sum_congr rfl hpair, sum_const,
    card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end Pairwise

namespace KingmanTimes

/-- **Tajima's numerator has mean zero** (Tajima 1989): under the hypotheses of
`integral_meanPairDiff` and Watterson's (`E[S | m] = (θ/2) L`),
`E[π - S / a₁] = 0` for a sample of size `n ≥ 2`. -/
theorem integral_tajimaNumerator {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {n : ℕ} (K : KingmanTimes μ n) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)] {S : Ω → ℝ} {D τ : Finset (Fin n) → Ω → ℝ} {θ : ℝ} (hn : 2 ≤ n)
    (hSint : Integrable S μ) (hS : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω)
    (hτ : ∀ s ∈ samplePairs n, HasLaw (τ s) (expMeasure 1) μ)
    (hDint : ∀ s ∈ samplePairs n, Integrable (D s) μ)
    (hD : ∀ s ∈ samplePairs n, μ[D s | m] =ᵐ[μ] fun ω => θ * τ s ω) :
    μ[fun ω => meanPairDiff n D ω - S ω / tajimaA1 n] = 0 := by
  have hπint : Integrable (meanPairDiff n D) μ := by
    have h := (integrable_finsetSum (samplePairs n) hDint).const_mul
      (((n.choose 2 : ℕ) : ℝ)⁻¹)
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp [meanPairDiff]
  rw [integral_sub hπint (hSint.div_const _), integral_meanPairDiff hm hn hτ hDint hD,
    tajimaA1_eq_harmonic, K.watterson_unbiased hm hSint hS hn, sub_self]

/-- **Unbiased estimator of Tajima's variance term** (Tajima 1989): with `S` as in
`variance_segSites`, `E[e₁ S + e₂ S (S - 1)] = c₁ θ + c₂ θ²` for `n ≥ 2`. (By Tajima's
analysis `c₁ θ + c₂ θ²` is `Var(π - S / a₁)`; that identity is not proved here.) -/
theorem integral_tajimaVarEstimator {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {n : ℕ} (K : KingmanTimes μ n) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {S : Ω → ℝ} {θ : ℝ} (hn : 2 ≤ n) (hS2 : MemLp S 2 μ)
    (hmean : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω)
    (hvar : Var[S; μ | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω) :
    μ[fun ω => tajimaE1 n * S ω + tajimaE2 n * (S ω * (S ω - 1))] =
      tajimaC1 n * θ + tajimaC2 n * θ ^ 2 := by
  have hSint : Integrable S μ := hS2.integrable one_le_two
  have hS2int : Integrable (fun ω => S ω ^ 2) μ := hS2.integrable_sq
  have hES : μ[S] = θ * tajimaA1 n := by
    rw [K.integral_segSites hm hSint hmean, tajimaA1_eq_harmonic]
  have hES2 : μ[fun ω => S ω ^ 2] = θ * tajimaA1 n + θ ^ 2 * tajimaA2 n + (θ * tajimaA1 n) ^ 2 := by
    have h := variance_eq_sub hS2
    rw [K.variance_segSites hm hS2 hmean hvar, hES] at h
    simp only [Pi.pow_apply] at h
    linarith
  have ha1 : 0 < tajimaA1 n := by
    rw [tajimaA1_eq_harmonic]
    exact_mod_cast harmonic_pos (by omega)
  have ha2 : 0 ≤ tajimaA2 n := sum_nonneg fun i _ => by positivity
  have hsq : (fun ω => S ω * (S ω - 1)) = fun ω => S ω ^ 2 - S ω := by
    funext ω
    ring
  rw [integral_add (hSint.const_mul _), integral_const_mul, integral_const_mul, hsq,
    integral_sub hS2int hSint, hES2, hES]
  · unfold tajimaE1 tajimaE2
    field_simp
    ring
  · refine ((hS2int.sub hSint).const_mul (tajimaE2 n)).congr (ae_of_all _ fun ω => ?_)
    simp only [Pi.sub_apply]
    ring

end KingmanTimes

end MathlibExt.Biology.PopulationGenetics.Coalescent
