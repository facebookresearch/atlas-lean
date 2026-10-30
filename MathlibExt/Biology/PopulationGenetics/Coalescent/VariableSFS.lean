/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
public import MathlibExt.Biology.PopulationGenetics.Coalescent.Tajima
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import MathlibExt.Analysis.SpecialFunctions.ExpSumZeros
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Probability.Independence.Integration

/-!
# The site frequency spectrum under a variable population size, and what it identifies

Three groups of results about the expected unfolded site frequency spectrum (SFS)
`E ξ_i`, `1 ≤ i ≤ n - 1`, of a sample of `n` gene copies (time in units of `2N₀` generations,
`θ = 4N₀u`, mutations at rate `θ / 2` per lineage).

**Variable population size.** Under a coalescent whose holding times `T k` (`k = n, …, 2`
lineages) are independent of the random-joining topology, but otherwise arbitrary (for
example the time-changed Kingman coalescent of a population of variable size),
`E ξ_i = (θ / 2) ∑_{k=2}^{n} k C(n-i-1, k-2) / C(n-1, k-1) · E T_k`
(Griffiths & Tavaré 1998; Polanski & Kimmel 2003). The kernel is triangular with a nonzero
diagonal, so the expected SFS determines `(E T_2, …, E T_n)` (an elementary observation
recorded here, not attributed to a source).

**Weighted estimators of `θ`.** Under the constant-size coalescent (`E ξ_i = θ / i`), every
`θ_ω = ∑_i ω_i i ξ_i` with `∑_i ω_i = 1` is unbiased for `θ` (Achaz 2009). Hence the
numerators of Fay & Wu's `H` and of Fu & Li's `D` and `F` have mean zero.

**Identifiability.** For a population-size function `η` (relative to `N₀`), the expected time
to the first coalescence among `m` lineages is
`c_m = ∫_0^∞ exp(-C(m,2) R(s)) ds` with `R(s) = ∫_0^s 1/η`. For a piecewise-constant history
with `K` pieces, `C(m,2) c_m` is an exponential sum in `C(m,2)` with at most `K` terms, and an
exponential sum with `r` terms vanishing at `r` distinct points is zero (the matrix
`(exp(-a_p u_q))` has full column rank). Hence `c_2, …, c_n` determine a history with at most
`K` pieces when `n ≥ 2K` (Bhaskar & Song 2014, Corollary 7). Bhaskar & Song show that the
expected SFS of a sample of size `n` and `(c_2, …, c_n)` determine each other; that reduction
(which needs the time-changed coalescent and subsampling) is not formalized here, so the
identifiability theorem is stated for `(c_2, …, c_n)`. Tightness of `n ≥ 2K` is proved for
`K = 2` by an explicit pair; tightness for general `K` and the Myers–Fefferman–Patterson
non-identifiability of general histories are recorded in
`WantedExt/Biology/PopulationGenetics/Coalescent/VariableSFSWanted.lean`.

## Main results

* `integral_sfs_of_indep`: the variable-size expected SFS `E ξ_i = variableSFS θ n (E T) i`.
* `variableSFS_inv_choose_two`: with `E T_k = 1 / C(k,2)` it reduces to Fu's `θ / i`.
* `sfsKernel_eq_zero_of_lt`, `sfsKernel_diag_pos`, `eq_of_variableSFS_eq`: triangularity of
  the kernel and the inversion corollary.
* `integral_thetaWeighted`: `E θ_ω = θ` when `E ξ_i = θ / i` and `∑ ω_i = 1`;
  `integral_fayWuH`, `integral_fuLiDNumerator`, `integral_fuLiFNumerator`: mean zero;
  `integral_thetaWeighted_kingman`: the same under Kingman's coalescent.
* `choose_two_mul_firstCoalMean`: the closed form of `C(m,2) c_m` for a piecewise-constant
  history.
* `sizeFn_eq_of_firstCoalMean_eq`: **Bhaskar–Song identifiability** — two piecewise-constant
  histories with `K` pieces and equal `c_m` for `2 ≤ m ≤ n`, `n ≥ 2K`, have the same size at
  every time `s ≥ 0`.
* `exists_ne_firstCoalMean_eq_two`: the bound is tight for `K = 2` (an explicit pair of
  two-piece histories with equal `c_2`, `c_3`).

## References

* R. C. Griffiths and S. Tavaré, *The age of a mutation in a general coalescent tree*,
  Stoch. Models 14 (1998), 273–295.
* A. Polanski and M. Kimmel, *New explicit expressions for relative frequencies of
  single-nucleotide polymorphisms with application to statistical inference on population
  growth*, Genetics 165 (2003), 427–436.
* G. Achaz, *Frequency spectrum neutrality tests: one for all and all for one*, Genetics 183
  (2009), 249–258.
* J. C. Fay and C.-I. Wu, *Hitchhiking under positive Darwinian selection*, Genetics 155
  (2000), 1405–1413.
* Y.-X. Fu and W.-H. Li, *Statistical tests of neutrality of mutations*, Genetics 133 (1993),
  693–709.
* A. Bhaskar and Y. S. Song, *Descartes' rule of signs and the identifiability of population
  demographic models from genomic variation data*, Ann. Statist. 42 (2014), 2469–2493.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFS

open MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum

/-! ### The variable-size expected SFS -/

/-- The **Griffiths–Tavaré kernel** `k C(n-i-1, k-2) / C(n-1, k-1)`: the expected number of
branches subtending exactly `i` of the `n` sample copies while `k` lineages remain
(`SiteFrequencySpectrum.joinStep_iterate_count`). Meaningful for `1 ≤ i < n`, `2 ≤ k ≤ n`;
outside that range the natural-number subtractions give junk values. -/
def sfsKernel (n i k : ℕ) : ℝ :=
  k * ((n - i - 1).choose (k - 2) : ℝ) / ((n - 1).choose (k - 1) : ℝ)

/-- The expected SFS entry `(θ / 2) ∑_{k=2}^{n} sfsKernel n i k · t k` of a sample of size
`n` whose mean holding times are `t k = E T_k` (Griffiths & Tavaré 1998, Polanski & Kimmel
2003). -/
def variableSFS (θ : ℝ) (n : ℕ) (t : ℕ → ℝ) (i : ℕ) : ℝ :=
  θ / 2 * ∑ k ∈ Icc 2 n, sfsKernel n i k * t k

section Integral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A random block-size history with the random-joining law takes values a.s. in a finite set,
so every statistic of it is integrable with the expectation given by the law. -/
private lemma integral_comp_randomJoining {μ : Measure Ω} [IsProbabilityMeasure μ] {m : ℕ}
    {b : List ℕ} {τ : Ω → List (List ℕ)} (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining m b ps) {F : Finset (List (List ℕ))}
    (hF : ∀ ps ∉ F, randomJoining m b ps = 0) (g : List (List ℕ) → ℝ) :
    Integrable (fun ω => g (τ ω)) μ ∧
      μ[fun ω => g (τ ω)] = ∑ ps ∈ F, randomJoining m b ps * g ps := by
  have hmeas : ∀ ps, MeasurableSet (τ ⁻¹' {ps}) := fun ps =>
    hτ _ (MeasurableSpace.measurableSet_comap.2 ⟨{ps}, trivial, rfl⟩)
  have hae : ∀ᵐ ω ∂μ, τ ω ∈ F := by
    rw [ae_iff]
    have : {ω | ¬ τ ω ∈ F} = ⋃ ps : {ps // ps ∉ F}, τ ⁻¹' {ps.1} := by
      ext ω; simp
    rw [this]
    refine measure_iUnion_null fun ps => ?_
    rw [← measureReal_eq_zero_iff, hτ_law, hF _ ps.2]
  have heq : (fun ω => g (τ ω)) =ᵐ[μ]
      fun ω => ∑ ps ∈ F, (τ ⁻¹' {ps}).indicator (fun _ => g ps) ω := by
    filter_upwards [hae] with ω hω
    rw [Finset.sum_eq_single_of_mem (τ ω) hω]
    · simp
    · intro ps _ hne
      simp [Set.indicator, Ne.symm hne]
  have hint : ∀ ps ∈ F, Integrable ((τ ⁻¹' {ps}).indicator (fun _ => g ps)) μ :=
    fun ps _ => (integrable_const _).indicator (hmeas ps)
  refine ⟨(integrable_finsetSum _ hint).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun ps _ => ?_
  rw [integral_indicator_const _ (hmeas ps), hτ_law, smul_eq_mul]

/-- **Expected SFS under a variable population size** (Griffiths & Tavaré 1998; Polanski &
Kimmel 2003). Let the genealogy of a sample of `n` copies consist of holding times `T k`
(integrable for `2 ≤ k ≤ n`, otherwise arbitrary) and an independent block-size history `τ`
with the random-joining law. If, given the genealogy, the count `ξ i` is integrable with
conditional mean `(θ / 2) L_i`, then `E ξ_i = (θ / 2) ∑_k k C(n-i-1,k-2)/C(n-1,k-1) E T_k`
for `1 ≤ i ≤ n - 1`. Independence of the holding times and the topology holds for the
time-changed Kingman coalescent of any deterministic population-size history (a standard
property of that model, not proved here; it is a hypothesis of this theorem). -/
theorem integral_sfs_of_indep {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    {T : ℕ → Ω → ℝ} (hT : ∀ k, Measurable (T k)) (hT_int : ∀ k ∈ Icc 2 n, Integrable (T k) μ)
    {τ : Ω → List (List ℕ)} (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) =
      randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => T k ω) MeasurableSpace.pi) μ)
    {θ : ℝ} {ξ : ℕ → Ω → ℝ} (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => T k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => T k ω))
    {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    μ[ξ i] = variableSFS θ n (fun k => μ[T k]) i := by
  have hmT : MeasurableSpace.comap (fun ω k => T k ω) MeasurableSpace.pi ≤ mΩ :=
    (measurable_pi_iff.2 hT).comap_le
  have hm := sup_le hτ hmT
  obtain ⟨F, hF0, hF⟩ := exists_finset_randomJoining (n - 1) (List.replicate n 1)
  have hL : μ[fun ω => sfsLength n i (τ ω) (fun k => T k ω)] =
      ∑ k ∈ Icc 2 n, sfsKernel n i k * μ[T k] := by
    have hterm : ∀ k ∈ Icc 2 n,
        Integrable (fun ω => (((τ ω).getD (n - k) []).count i : ℝ) * T k ω) μ ∧
        μ[fun ω => (((τ ω).getD (n - k) []).count i : ℝ) * T k ω] =
          sfsKernel n i k * μ[T k] := by
      intro k hk
      have hk2 := (mem_Icc.1 hk)
      set X : Ω → ℝ := fun ω => (((τ ω).getD (n - k) []).count i : ℝ)
      obtain ⟨hXi, hXe⟩ := integral_comp_randomJoining hτ hτ_law hF0
        (fun ps => ((ps.getD (n - k) []).count i : ℝ))
      have hind : IndepFun X (T k) μ := by
        rw [IndepFun_iff_Indep]
        refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h_indep ?_) ?_
        · rw [show X = (fun ps : List (List ℕ) => ((ps.getD (n - k) []).count i : ℝ)) ∘ τ
            from rfl, ← MeasurableSpace.comap_comp]
          exact MeasurableSpace.comap_mono le_top
        · rw [show T k = (fun f : ℕ → ℝ => f k) ∘ (fun ω k => T k ω) from rfl,
            ← MeasurableSpace.comap_comp]
          exact MeasurableSpace.comap_mono (measurable_pi_apply k).comap_le
      refine ⟨hind.integrable_mul hXi (hT_int k hk), ?_⟩
      change μ[X * T k] = _
      rw [hind.integral_mul_eq_mul_integral hXi.aestronglyMeasurable
        (hT_int k hk).aestronglyMeasurable, hXe,
        hF (n - k) (by omega) (fun b => (b.count i : ℝ)),
        joinStep_iterate_count hk2.1 hk2.2 hi hin, sfsKernel]
    unfold sfsLength
    rw [integral_finsetSum _ fun k hk => (hterm k hk).1,
      Finset.sum_congr rfl fun k hk => (hterm k hk).2]
  have h := setIntegral_condExp hm (hξ_int i)
    (@MeasurableSet.univ Ω (MeasurableSpace.comap τ ⊤ ⊔
      MeasurableSpace.comap (fun ω k => T k ω) MeasurableSpace.pi))
  simp only [Measure.restrict_univ] at h
  rw [← h, integral_congr_ae (hξ i), integral_const_mul, hL, variableSFS]

end Integral

/-- With the constant-size means `E T_k = 1 / C(k,2)`, the variable-size SFS is Fu's
`θ / i`. -/
theorem variableSFS_inv_choose_two (θ : ℝ) {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    variableSFS θ n (fun k => ((k.choose 2 : ℕ) : ℝ)⁻¹) i = θ / i := by
  rw [variableSFS]
  simp only [sfsKernel]
  rw [sum_blockCount_mul_inv_choose_two hi hin]
  have : (i : ℝ) ≠ 0 := by positivity
  field_simp

/-! ### Inversion: the expected SFS determines the mean holding times -/

/-- The kernel row `i` vanishes beyond `k = n - i + 1`: a branch subtending `i` copies cannot
exist while more than `n - i + 1` lineages remain. -/
theorem sfsKernel_eq_zero_of_lt {n i k : ℕ} (hin : i < n) (hk : n - i + 1 < k) :
    sfsKernel n i k = 0 := by
  rw [sfsKernel, Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- The kernel entry at `k = n - i + 1` is `(n - i + 1) / C(n-1, i-1) > 0`. -/
theorem sfsKernel_diag_pos {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    0 < sfsKernel n i (n - i + 1) := by
  rw [sfsKernel, show n - i + 1 - 2 = n - i - 1 by omega, Nat.choose_self]
  have : (0 : ℝ) < ((n - 1).choose (n - i + 1 - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  positivity

/-- **The expected SFS determines the mean holding times.** If two vectors of mean holding
times give the same expected SFS for some `θ ≠ 0`, they agree at every `k = 2, …, n`. This is
a direct consequence of `sfsKernel_eq_zero_of_lt` and `sfsKernel_diag_pos` (the kernel is
triangular with nonzero diagonal); it is recorded here as an observation, not as a cited
theorem. -/
theorem eq_of_variableSFS_eq {θ : ℝ} (hθ : θ ≠ 0) {n : ℕ} {t t' : ℕ → ℝ}
    (h : ∀ i ∈ Ico 1 n, variableSFS θ n t i = variableSFS θ n t' i) :
    ∀ k ∈ Icc 2 n, t k = t' k := by
  have hθ2 : θ / 2 ≠ 0 := div_ne_zero hθ two_ne_zero
  have h0 : ∀ i ∈ Ico 1 n, ∑ k ∈ Icc 2 n, sfsKernel n i k * (t k - t' k) = 0 := by
    intro i hi
    have := mul_left_cancel₀ hθ2 (h i hi)
    simp only [mul_sub, sum_sub_distrib, this, sub_self]
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  obtain ⟨hk2, hkn⟩ := mem_Icc.1 hk
  have hrow := h0 (n - k + 1) (mem_Ico.2 ⟨by omega, by omega⟩)
  rw [sum_eq_single_of_mem k hk] at hrow
  · have hpos := sfsKernel_diag_pos (n := n) (i := n - k + 1) (by omega) (by omega)
    rw [show n - (n - k + 1) + 1 = k by omega] at hpos
    have := (mul_eq_zero.1 hrow).resolve_left hpos.ne'
    linarith
  · intro k' hk' hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [ih k' hlt hk', sub_self, mul_zero]
    · rw [sfsKernel_eq_zero_of_lt (by omega) (by omega), zero_mul]

/-! ### Weighted estimators of `θ` and neutrality-test numerators -/

section Estimators

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Achaz's weighted estimator `θ_ω = ∑_{i=1}^{n-1} ω_i i ξ_i` (Achaz 2009, with the
weights already normalized). -/
def thetaWeighted (n : ℕ) (w : ℕ → ℝ) (ξ : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Ico 1 n, w i * i * ξ i ω

/-- Tajima's `θ_π` in its SFS form `∑_i i (n - i) ξ_i / C(n,2)` (weights `(n - i) / C(n,2)`). -/
def thetaPi (n : ℕ) (ξ : ℕ → Ω → ℝ) : Ω → ℝ :=
  thetaWeighted n (fun i => ((n : ℝ) - i) / (n.choose 2 : ℝ)) ξ

/-- Fay & Wu's `θ_H = ∑_i i² ξ_i / C(n,2)` (weights `i / C(n,2)`). -/
def thetaH (n : ℕ) (ξ : ℕ → Ω → ℝ) : Ω → ℝ :=
  thetaWeighted n (fun i => (i : ℝ) / (n.choose 2 : ℝ)) ξ

/-- Fay & Wu's `H = θ_π - θ_H` (Fay & Wu 2000). -/
def fayWuH (n : ℕ) (ξ : ℕ → Ω → ℝ) : Ω → ℝ := fun ω => thetaPi n ξ ω - thetaH n ξ ω

/-- The numerator `S - a₁ ξ₁` of Fu & Li's `D` with an outgroup, where `S = ∑_i ξ_i` and the
external-branch mutations are the derived singletons `ξ₁` (Fu & Li 1993). -/
def fuLiDNumerator (n : ℕ) (ξ : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Ico 1 n, ξ i ω - tajimaA1 n * ξ 1 ω

/-- The numerator `θ_π - ξ₁` of Fu & Li's `F` with an outgroup (Fu & Li 1993), with `θ_π` in
its SFS form. -/
def fuLiFNumerator (n : ℕ) (ξ : ℕ → Ω → ℝ) : Ω → ℝ := fun ω => thetaPi n ξ ω - ξ 1 ω

variable {μ : Measure Ω} {n : ℕ} {θ : ℝ} {ξ : ℕ → Ω → ℝ}

private lemma sum_Ico_one_cast (n : ℕ) : ∑ i ∈ Ico 1 n, (i : ℝ) = ((n.choose 2 : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [sum_Ico_succ_top hn, ih, show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ' n 1,
      Nat.choose_one_right]
    push_cast
    ring

private lemma choose_two_ne_zero (hn : 2 ≤ n) : ((n.choose 2 : ℕ) : ℝ) ≠ 0 := by
  exact_mod_cast (Nat.choose_pos hn).ne'

private lemma sum_weight_pi (hn : 2 ≤ n) :
    ∑ i ∈ Ico 1 n, ((n : ℝ) - i) / (n.choose 2 : ℝ) = 1 := by
  rw [← sum_div, sum_sub_distrib, sum_Ico_one_cast, sum_const, Nat.card_Ico, nsmul_eq_mul,
    div_eq_one_iff_eq (choose_two_ne_zero hn), Nat.cast_choose_two, Nat.cast_sub (by omega)]
  push_cast
  ring

private lemma sum_weight_H (hn : 2 ≤ n) :
    ∑ i ∈ Ico 1 n, (i : ℝ) / (n.choose 2 : ℝ) = 1 := by
  rw [← sum_div, sum_Ico_one_cast, div_self (choose_two_ne_zero hn)]

private lemma integrable_thetaWeighted (hξ_int : ∀ i, Integrable (ξ i) μ) (w : ℕ → ℝ) :
    Integrable (thetaWeighted n w ξ) μ :=
  integrable_finsetSum _ fun i _ => (hξ_int i).const_mul _

/-- **Achaz's unbiasedness** (Achaz 2009): if `E ξ_i = θ / i` for `1 ≤ i ≤ n - 1` (the
constant-size spectrum, `SiteFrequencySpectrum.integral_sfs`), every weighted estimator with
`∑_i ω_i = 1` has mean `θ`. -/
theorem integral_thetaWeighted (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i ∈ Ico 1 n, μ[ξ i] = θ / i) {w : ℕ → ℝ} (hw : ∑ i ∈ Ico 1 n, w i = 1) :
    μ[thetaWeighted n w ξ] = θ := by
  unfold thetaWeighted
  rw [integral_finsetSum _ fun i _ => (hξ_int i).const_mul _]
  have h : ∀ i ∈ Ico 1 n, μ[fun ω => w i * i * ξ i ω] = θ * w i := by
    intro i hi
    rw [integral_const_mul, hξ i hi]
    have : (i : ℝ) ≠ 0 := by have := (mem_Ico.1 hi).1; positivity
    field_simp
  rw [sum_congr rfl h, ← mul_sum, hw, mul_one]

/-- Fay & Wu's `H` has mean zero under the constant-size spectrum (`n ≥ 2`). -/
theorem integral_fayWuH (hn : 2 ≤ n) (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i ∈ Ico 1 n, μ[ξ i] = θ / i) : μ[fayWuH n ξ] = 0 := by
  unfold fayWuH thetaPi thetaH
  rw [integral_sub (integrable_thetaWeighted hξ_int _) (integrable_thetaWeighted hξ_int _),
    integral_thetaWeighted hξ_int hξ (sum_weight_pi hn),
    integral_thetaWeighted hξ_int hξ (sum_weight_H hn), sub_self]

/-- The numerator of Fu & Li's `D` has mean zero under the constant-size spectrum
(`n ≥ 2`). -/
theorem integral_fuLiDNumerator (hn : 2 ≤ n) (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i ∈ Ico 1 n, μ[ξ i] = θ / i) : μ[fuLiDNumerator n ξ] = 0 := by
  unfold fuLiDNumerator
  rw [integral_sub (integrable_finsetSum _ fun i _ => hξ_int i) ((hξ_int 1).const_mul _),
    integral_finsetSum _ fun i _ => hξ_int i, integral_const_mul,
    sum_congr rfl hξ, hξ 1 (mem_Ico.2 ⟨le_rfl, by omega⟩), tajimaA1]
  simp only [div_eq_mul_inv, ← mul_sum]
  push_cast
  ring

/-- The numerator of Fu & Li's `F` has mean zero under the constant-size spectrum
(`n ≥ 2`). -/
theorem integral_fuLiFNumerator (hn : 2 ≤ n) (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i ∈ Ico 1 n, μ[ξ i] = θ / i) : μ[fuLiFNumerator n ξ] = 0 := by
  unfold fuLiFNumerator thetaPi
  rw [integral_sub (integrable_thetaWeighted hξ_int _) (hξ_int 1),
    integral_thetaWeighted hξ_int hξ (sum_weight_pi hn), hξ 1 (mem_Ico.2 ⟨le_rfl, by omega⟩)]
  simp

/-- Achaz's unbiasedness under Kingman's coalescent, with the hypotheses of
`SiteFrequencySpectrum.integral_sfs`. -/
theorem integral_thetaWeighted_kingman [IsProbabilityMeasure μ]
    (K : KingmanTimes μ n) (hT : ∀ k, Measurable (K.T k))
    {τ : Ω → List (List ℕ)} (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) =
      randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => K.T k ω))
    {w : ℕ → ℝ} (hw : ∑ i ∈ Ico 1 n, w i = 1) :
    μ[thetaWeighted n w ξ] = θ :=
  integral_thetaWeighted hξ_int (fun _ hi => integral_sfs K hT hτ hτ_law h_indep hξ_int hξ
    (mem_Ico.1 hi).1 (mem_Ico.1 hi).2) hw

end Estimators

/-! ### Piecewise-constant histories and their first-coalescence times -/

/-- The cumulative coalescence intensity `R(s) = ∫_0^s 1/η` of a relative population-size
function `η` (pairs coalesce at rate `1/η(s)` at time `s` before the present). Meaningful for
positive `η` with `1/η` locally integrable. -/
def cumRate (η : ℝ → ℝ) (s : ℝ) : ℝ := ∫ r in (0 : ℝ)..s, (η r)⁻¹

/-- The expected time to the first coalescence among `m` lineages,
`c_m = ∫_0^∞ exp(-C(m,2) R(s)) ds`, in a population of relative size `η`
(Bhaskar & Song's `E[T_{m,m}]`). When the integrand is not integrable (for example `η ≡ 0`),
this is Lean's junk value `0`; for piecewise-constant histories it is integrable
(`choose_two_mul_firstCoalMean`). -/
def firstCoalMean (η : ℝ → ℝ) (m : ℕ) : ℝ :=
  ∫ s in Set.Ioi 0, Real.exp (-((m.choose 2 : ℕ) : ℝ) * cumRate η s)

/-- A **piecewise-constant population-size history with `K` pieces**: piece `j < K` starts at
time `start j` (backward from the present, `start 0 = 0`, strictly increasing) and has
relative size `size j > 0`; the last piece extends to infinity. Adjacent pieces may have equal
sizes, so this also covers histories with fewer than `K` distinct pieces. Values at indices
`j ≥ K` are unused. The case `K = 0` is degenerate (its size function is `0`); the theorems
about `c_m` assume `0 < K` where it matters. -/
structure PiecewiseHistory (K : ℕ) where
  /-- The relative size on piece `j`. -/
  size : ℕ → ℝ
  /-- The start time of piece `j`. -/
  start : ℕ → ℝ
  /-- Every piece has a positive size. -/
  size_pos : ∀ j < K, 0 < size j
  /-- The first piece starts at the present. -/
  start_zero : start 0 = 0
  /-- The pieces start at strictly increasing times. -/
  start_lt : ∀ j, j + 1 < K → start j < start (j + 1)

namespace PiecewiseHistory

variable {K : ℕ}

/-- The population-size function of a piecewise-constant history: at time `s ≥ 0` it is the
size of the piece `j` with `start j ≤ s < start (j + 1)` (the last piece has no end). Equal to
`0` for `s < 0` (junk; only `s ≥ 0` is meaningful). -/
def sizeFn (h : PiecewiseHistory K) (s : ℝ) : ℝ :=
  ∑ j ∈ range K, if h.start j ≤ s ∧ (j + 1 < K → s < h.start (j + 1)) then h.size j else 0

/-- The start times are monotone on the pieces. -/
theorem start_mono (h : PiecewiseHistory K) {i j : ℕ} (hij : i ≤ j) (hj : j < K) :
    h.start i ≤ h.start j := by
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · exact (ih (by omega) (by omega)).trans (h.start_lt j hj).le
    · rw [show i = j + 1 by omega]

/-- Every piece starts at a nonnegative time. -/
theorem start_nonneg (h : PiecewiseHistory K) {j : ℕ} (hj : j < K) : 0 ≤ h.start j := by
  rw [← h.start_zero]; exact h.start_mono (Nat.zero_le _) hj

/-- On piece `j` the size function equals `size j`. -/
theorem sizeFn_eq (h : PiecewiseHistory K) {j : ℕ} {s : ℝ} (hj : j < K) (hs : h.start j ≤ s)
    (hs' : j + 1 < K → s < h.start (j + 1)) : h.sizeFn s = h.size j := by
  unfold sizeFn
  rw [sum_eq_single_of_mem j (mem_range.2 hj)]
  · split_ifs with hc
    · rfl
    · exact absurd ⟨hs, hs'⟩ hc
  · intro i hi hne
    split_ifs with hc
    swap; · rfl
    exfalso
    obtain ⟨h1, h2⟩ := hc
    have hi' := mem_range.1 hi
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := h2 (by omega)
      have := h.start_mono (show i + 1 ≤ j by omega) hj
      linarith
    · have := hs' (by omega)
      have := h.start_mono (show j + 1 ≤ i by omega) hi'
      linarith

/-- The integral of `1 / sizeFn` over the beginning of piece `j`. -/
private lemma piece_integral (h : PiecewiseHistory K) {j : ℕ} (hj : j < K) {s : ℝ}
    (hs : h.start j ≤ s) (hs' : j + 1 < K → s ≤ h.start (j + 1)) :
    IntervalIntegrable (fun r => (h.sizeFn r)⁻¹) volume (h.start j) s ∧
      ∫ r in h.start j..s, (h.sizeFn r)⁻¹ = (s - h.start j) / h.size j := by
  have heq : Set.EqOn (fun _ => (h.size j)⁻¹) (fun r => (h.sizeFn r)⁻¹)
      (Set.uIoo (h.start j) s) := by
    intro r hr
    rw [Set.uIoo_of_le hs] at hr
    simp only
    rw [h.sizeFn_eq hj hr.1.le fun hk => hr.2.trans_le (hs' hk)]
  refine ⟨intervalIntegrable_const.congr_uIoo heq, ?_⟩
  rw [← intervalIntegral.integral_congr_uIoo heq, intervalIntegral.integral_const, smul_eq_mul,
    div_eq_mul_inv]

/-- On piece `j` (including its right end), `1 / sizeFn` is integrable on `[0, s]` and the
cumulative rate is affine: `R(s) = R(start j) + (s - start j) / size j`. -/
theorem cumRate_piece (h : PiecewiseHistory K) :
    ∀ j < K, ∀ s, h.start j ≤ s → (j + 1 < K → s ≤ h.start (j + 1)) →
      IntervalIntegrable (fun r => (h.sizeFn r)⁻¹) volume 0 s ∧
      cumRate h.sizeFn s = cumRate h.sizeFn (h.start j) + (s - h.start j) / h.size j := by
  intro j
  induction j with
  | zero =>
    intro hK s hs hs'
    obtain ⟨hi, he⟩ := h.piece_integral hK hs hs'
    rw [h.start_zero] at hi he ⊢
    refine ⟨hi, ?_⟩
    simp only [cumRate, intervalIntegral.integral_same, zero_add]
    exact he
  | succ j ih =>
    intro hK s hs hs'
    obtain ⟨hi0, -⟩ := ih (by omega) (h.start (j + 1)) (h.start_lt j hK).le (fun _ => le_rfl)
    obtain ⟨hi, he⟩ := h.piece_integral hK hs hs'
    refine ⟨hi0.trans hi, ?_⟩
    simp only [cumRate]
    rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi, he]

private lemma hasDerivAt_piece {a U t η : ℝ} (ha : a ≠ 0) (hη : η ≠ 0) (s : ℝ) :
    HasDerivAt (fun s => -(η / a) * Real.exp (-a * (U + (s - t) / η)))
      (Real.exp (-a * (U + (s - t) / η))) s := by
  have h1 : HasDerivAt (fun s => -a * (U + (s - t) / η)) (-a * (1 / η)) s := by
    have := (((hasDerivAt_id s).sub_const t).div_const η).const_add U
    simpa using this.const_mul (-a)
  convert (h1.exp).const_mul (-(η / a)) using 1
  field_simp

private lemma sum_by_parts (η e : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ range N, η j * (e j - e (j + 1)) + η N * e N =
      η 0 * e 0 + ∑ j ∈ Ico 1 (N + 1), (η j - η (j - 1)) * e j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_Ico_succ_top (by omega), Nat.add_sub_cancel]
    linear_combination ih

/-- **Closed form of the first-coalescence times.** For a history with `K ≥ 1` pieces and
`m ≥ 2`, writing `a = C(m,2)` and `R = cumRate h.sizeFn`,
`a c_m = size 0 + ∑_{j=1}^{K-1} (size j - size (j-1)) exp(-a R(start j))`. In particular the
integral defining `c_m` converges. -/
theorem choose_two_mul_firstCoalMean (h : PiecewiseHistory K) (hK : 0 < K) {m : ℕ}
    (hm : 2 ≤ m) :
    ((m.choose 2 : ℕ) : ℝ) * firstCoalMean h.sizeFn m =
      h.size 0 + ∑ j ∈ Ico 1 K, (h.size j - h.size (j - 1)) *
        Real.exp (-((m.choose 2 : ℕ) : ℝ) * cumRate h.sizeFn (h.start j)) := by
  set a : ℝ := ((m.choose 2 : ℕ) : ℝ)
  have ha : 0 < a := Nat.cast_pos.2 (Nat.choose_pos hm)
  set U : ℕ → ℝ := fun j => cumRate h.sizeFn (h.start j)
  set f : ℝ → ℝ := fun s => Real.exp (-a * cumRate h.sizeFn s)
  -- interior pieces
  have hpiece : ∀ j, j + 1 < K → IntervalIntegrable f volume (h.start j) (h.start (j + 1)) ∧
      ∫ s in h.start j..h.start (j + 1), f s =
        h.size j / a * (Real.exp (-a * U j) - Real.exp (-a * U (j + 1))) := by
    intro j hj
    have hη := h.size_pos j (by omega)
    have hle := (h.start_lt j hj).le
    have heq : Set.EqOn f (fun s => Real.exp (-a * (U j + (s - h.start j) / h.size j)))
        (Set.uIcc (h.start j) (h.start (j + 1))) := by
      intro s hs
      rw [Set.uIcc_of_le hle] at hs
      simp only [f, U]
      rw [(h.cumRate_piece j (by omega) s hs.1 fun _ => hs.2).2]
    have hcont : Continuous fun s => Real.exp (-a * (U j + (s - h.start j) / h.size j)) := by
      fun_prop
    refine ⟨(hcont.intervalIntegrable _ _).congr_uIoo
      (fun s hs => (heq (Set.uIoo_subset_uIcc_self hs)).symm), ?_⟩
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_piece ha.ne' hη.ne' s) (hcont.intervalIntegrable _ _)]
    have hU : U (j + 1) = U j + (h.start (j + 1) - h.start j) / h.size j :=
      (h.cumRate_piece j (by omega) _ hle fun _ => le_rfl).2
    rw [hU]
    simp only [sub_self, zero_div, add_zero]
    ring
  -- the last piece
  set T := h.start (K - 1)
  have hT0 : 0 ≤ T := h.start_nonneg (by omega)
  have hlast : IntegrableOn f (Set.Ioi T) ∧
      ∫ s in Set.Ioi T, f s = h.size (K - 1) / a * Real.exp (-a * U (K - 1)) := by
    have hη := h.size_pos (K - 1) (by omega)
    have heq : Set.EqOn f (fun s => Real.exp (-a * (U (K - 1) + (s - T) / h.size (K - 1))))
        (Set.Ici T) := by
      intro s hs
      simp only [f, U]
      rw [(h.cumRate_piece (K - 1) (by omega) s hs fun hk => by omega).2]
    have hform : (fun s => Real.exp (-a * (U (K - 1) + (s - T) / h.size (K - 1)))) =
        fun s => Real.exp (-a * U (K - 1) + a * T / h.size (K - 1)) *
          Real.exp (-(a / h.size (K - 1)) * s) := by
      funext s
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have hint : IntegrableOn
        (fun s => Real.exp (-a * (U (K - 1) + (s - T) / h.size (K - 1)))) (Set.Ioi T) := by
      rw [hform]
      exact (exp_neg_integrableOn_Ioi T (div_pos ha hη)).const_mul _
    refine ⟨hint.congr_fun (fun s hs => (heq (Set.mem_Ici_of_Ioi hs)).symm) measurableSet_Ioi,
      ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => heq (Set.mem_Ici_of_Ioi hs)),
      integral_Ioi_of_hasDerivAt_of_tendsto' (fun s _ => hasDerivAt_piece ha.ne' hη.ne' s) hint
      (m := 0)]
    · simp only [sub_self, zero_div, add_zero]
      ring
    · rw [show (0 : ℝ) = -(h.size (K - 1) / a) * 0 by ring]
      refine Filter.Tendsto.const_mul _ (Real.tendsto_exp_atBot.comp ?_)
      rw [show (fun s => -a * (U (K - 1) + (s - T) / h.size (K - 1))) =
          fun s => -(a / h.size (K - 1)) * s + (-a * U (K - 1) + a * T / h.size (K - 1)) by
        funext s; field_simp; ring]
      exact Filter.tendsto_atBot_add_const_right _ _
        (Filter.tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos (div_pos ha hη)))
  -- assemble
  have hadj : ∀ k < K - 1, IntervalIntegrable f volume (h.start k) (h.start (k + 1)) :=
    fun k hk => (hpiece k (by omega)).1
  have hIoc : IntegrableOn f (Set.Ioc 0 T) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hT0, ← h.start_zero]
    exact IntervalIntegrable.trans_iterate hadj
  have hsplit : firstCoalMean h.sizeFn m =
      (∑ j ∈ range (K - 1), ∫ s in h.start j..h.start (j + 1), f s) +
        ∫ s in Set.Ioi T, f s := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hadj, h.start_zero,
      intervalIntegral.integral_of_le hT0, ← setIntegral_union Set.Ioc_disjoint_Ioi_same
      measurableSet_Ioi hIoc hlast.1, Set.Ioc_union_Ioi_eq_Ioi hT0]
    rfl
  rw [hsplit, sum_congr rfl fun j hj => (hpiece j (by simp at hj; omega)).2, hlast.2]
  have hU0 : U 0 = 0 := by simp [U, h.start_zero, cumRate]
  have key := sum_by_parts h.size (fun j => Real.exp (-a * U j)) (K - 1)
  rw [Nat.sub_add_cancel hK] at key
  simp only [hU0, mul_zero, Real.exp_zero, mul_one] at key
  rw [mul_add, mul_sum]
  rw [← key]
  congr 1
  · refine sum_congr rfl fun j _ => ?_
    field_simp
  · field_simp

/-- Every time `s ≥ 0` lies in some piece. -/
theorem exists_piece (h : PiecewiseHistory K) (hK : 0 < K) {s : ℝ} (hs : 0 ≤ s) :
    ∃ j < K, h.start j ≤ s ∧ (j + 1 < K → s < h.start (j + 1)) := by
  set F := (range K).filter fun i => h.start i ≤ s
  have hF : F.Nonempty := ⟨0, mem_filter.2 ⟨mem_range.2 hK, by rw [h.start_zero]; exact hs⟩⟩
  set j := F.max' hF
  have hjF := mem_filter.1 (F.max'_mem hF)
  refine ⟨j, mem_range.1 hjF.1, hjF.2, fun hk => ?_⟩
  by_contra hc
  have := F.le_max' (j + 1) (mem_filter.2 ⟨mem_range.2 hk, not_lt.1 hc⟩)
  omega

/-- The size function is positive on `[0, ∞)`. -/
theorem sizeFn_pos (h : PiecewiseHistory K) (hK : 0 < K) {s : ℝ} (hs : 0 ≤ s) :
    0 < h.sizeFn s := by
  obtain ⟨j, hj, h1, h2⟩ := h.exists_piece hK hs
  rw [h.sizeFn_eq hj h1 h2]
  exact h.size_pos j hj

/-- The coalescent-time breakpoints `R(start j)` are strictly increasing. -/
theorem cumRate_start_lt (h : PiecewiseHistory K) {j : ℕ} (hj : j + 1 < K) :
    cumRate h.sizeFn (h.start j) < cumRate h.sizeFn (h.start (j + 1)) := by
  rw [(h.cumRate_piece j (by omega) _ (h.start_lt j hj).le fun _ => le_rfl).2]
  have := h.size_pos j (by omega)
  have := sub_pos.2 (h.start_lt j hj)
  linarith [div_pos ‹0 < h.start (j + 1) - h.start j› ‹0 < h.size j›]

/-- The dual history in coalescent time: piece `j` starts at `R(start j)` and has size
`1 / size j`. -/
def dual (h : PiecewiseHistory K) : PiecewiseHistory K where
  size j := (h.size j)⁻¹
  start j := cumRate h.sizeFn (h.start j)
  size_pos j hj := inv_pos.2 (h.size_pos j hj)
  start_zero := by simp [h.start_zero, cumRate]
  start_lt j hj := h.cumRate_start_lt hj

/-- Time `s` in piece `j` maps to coalescent time `R(s)` in piece `j` of the dual. -/
private lemma cumRate_mem_piece (h : PiecewiseHistory K) {j : ℕ} (hj : j < K) {s : ℝ}
    (h1 : h.start j ≤ s) (h2 : j + 1 < K → s < h.start (j + 1)) :
    h.dual.start j ≤ cumRate h.sizeFn s ∧
      (j + 1 < K → cumRate h.sizeFn s < h.dual.start (j + 1)) := by
  have hη := h.size_pos j hj
  rw [(h.cumRate_piece j hj s h1 fun hk => (h2 hk).le).2]
  refine ⟨?_, fun hk => ?_⟩
  · simp only [dual]
    linarith [div_nonneg (sub_nonneg.2 h1) hη.le]
  · simp only [dual]
    rw [(h.cumRate_piece j hj _ (h.start_lt j hk).le fun _ => le_rfl).2]
    have := div_lt_div_of_pos_right (sub_lt_sub_right (h2 hk) (h.start j)) hη
    linarith

/-- The size at time `s` is the inverse of the dual history's size at coalescent time
`R(s)`. -/
theorem sizeFn_eq_inv_dual (h : PiecewiseHistory K) (hK : 0 < K) {s : ℝ} (hs : 0 ≤ s) :
    h.sizeFn s = (h.dual.sizeFn (cumRate h.sizeFn s))⁻¹ := by
  obtain ⟨j, hj, h1, h2⟩ := h.exists_piece hK hs
  obtain ⟨d1, d2⟩ := h.cumRate_mem_piece hj h1 h2
  rw [h.sizeFn_eq hj h1 h2, h.dual.sizeFn_eq hj d1 d2]
  simp [dual]

/-- The dual cumulative rate inverts the cumulative rate. -/
theorem cumRate_dual_cumRate (h : PiecewiseHistory K) (hK : 0 < K) {s : ℝ} (hs : 0 ≤ s) :
    cumRate h.dual.sizeFn (cumRate h.sizeFn s) = s := by
  have key : ∀ j < K, ∀ s, h.start j ≤ s → (j + 1 < K → s ≤ h.start (j + 1)) →
      cumRate h.dual.sizeFn (cumRate h.sizeFn s) = s := by
    intro j
    induction j with
    | zero =>
      intro hK0 s h1 h2
      have hη := h.size_pos 0 hK0
      have e1 := (h.cumRate_piece 0 hK0 s h1 h2).2
      rw [h.start_zero] at e1 h1
      have hc0 : cumRate h.sizeFn 0 = 0 := by simp [cumRate]
      rw [hc0, zero_add] at e1
      have e2 := (h.dual.cumRate_piece 0 hK0 (cumRate h.sizeFn s) (by
        simp only [dual, h.start_zero, hc0]; rw [e1]; positivity) (fun hk => by
          simp only [dual]; rw [e1, (h.cumRate_piece 0 hK0 _ (h.start_lt 0 hk).le
            fun _ => le_rfl).2, h.start_zero, hc0]
          have := h2 hk
          linarith [div_le_div_of_nonneg_right (sub_le_sub_right this 0) hη.le])).2
      rw [e2]
      simp only [dual, h.start_zero, hc0, e1]
      simp [cumRate]
      field_simp
    | succ j ih =>
      intro hj s h1 h2
      have hη := h.size_pos (j + 1) hj
      have hprev := ih (by omega) (h.start (j + 1)) (h.start_lt j hj).le (fun _ => le_rfl)
      have e1 := (h.cumRate_piece (j + 1) hj s h1 h2).2
      have hd1 : h.dual.start (j + 1) ≤ cumRate h.sizeFn s := by
        simp only [dual]; rw [e1]; linarith [div_nonneg (sub_nonneg.2 h1) hη.le]
      have hd2 : j + 1 + 1 < K → cumRate h.sizeFn s ≤ h.dual.start (j + 1 + 1) := by
        intro hk
        simp only [dual]
        rw [e1, (h.cumRate_piece (j + 1) hj _ (h.start_lt (j + 1) hk).le fun _ => le_rfl).2]
        linarith [div_le_div_of_nonneg_right (sub_le_sub_right (h2 hk) (h.start (j + 1))) hη.le]
      rw [(h.dual.cumRate_piece (j + 1) hj _ hd1 hd2).2]
      simp only [dual] at hprev ⊢
      rw [hprev, e1]
      field_simp
      ring
  obtain ⟨j, hj, h1, h2⟩ := h.exists_piece hK hs
  exact key j hj s h1 fun hk => (h2 hk).le

/-- The cumulative rate is strictly increasing on `[0, ∞)`. -/
theorem cumRate_strictMonoOn (h : PiecewiseHistory K) (hK : 0 < K) :
    StrictMonoOn (cumRate h.sizeFn) (Set.Ici 0) := by
  have hint : ∀ s, 0 ≤ s → IntervalIntegrable (fun r => (h.sizeFn r)⁻¹) volume 0 s := by
    intro s hs
    obtain ⟨j, hj, h1, h2⟩ := h.exists_piece hK hs
    exact (h.cumRate_piece j hj s h1 fun hk => (h2 hk).le).1
  intro x hx y hy hxy
  have hsub := intervalIntegral.integral_interval_sub_left (hint y hy) (hint x hx)
  have hpos : 0 < ∫ r in x..y, (h.sizeFn r)⁻¹ :=
    intervalIntegral.intervalIntegral_pos_of_pos_on ((hint x hx).symm.trans (hint y hy))
      (fun r hr => inv_pos.2 (h.sizeFn_pos hK ((Set.mem_Ici.1 hx).trans hr.1.le))) hxy
  simp only [cumRate] at hsub ⊢
  linarith

/-- The coefficient of the rate `u` in the exponential-sum form of `C(m,2) c_m`. -/
private def coef (h : PiecewiseHistory K) (u : ℝ) : ℝ :=
  (if u = 0 then h.size 0 else 0) +
    ∑ j ∈ Ico 1 K, if h.dual.start j = u then h.size j - h.size (j - 1) else 0

private lemma sum_coef_mul_exp (h : PiecewiseHistory K) {S : Finset ℝ} (h0 : (0 : ℝ) ∈ S)
    (hS : ∀ j ∈ Ico 1 K, h.dual.start j ∈ S) (a : ℝ) :
    ∑ u ∈ S, coef h u * Real.exp (-(a * u)) =
      h.size 0 + ∑ j ∈ Ico 1 K, (h.size j - h.size (j - 1)) *
        Real.exp (-a * cumRate h.sizeFn (h.start j)) := by
  simp only [coef, add_mul, sum_add_distrib, ite_mul, zero_mul, sum_mul]
  rw [sum_ite_eq' S 0, ite_eq_left h0, sum_comm]
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [sum_ite_eq S (h.dual.start j), ite_eq_left (hS j hj), neg_mul]
  rfl

private lemma telescope (η : ℕ → ℝ) (J : ℕ) :
    η 0 + ∑ j ∈ Ico 1 (J + 1), (η j - η (j - 1)) = η J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_Ico_succ_top (by omega), ← add_assoc, ih, Nat.add_sub_cancel]
    ring

private lemma sum_coef_le (h : PiecewiseHistory K) (hK : 0 < K) {S : Finset ℝ}
    (h0 : (0 : ℝ) ∈ S) (hS : ∀ j ∈ Ico 1 K, h.dual.start j ∈ S) {u : ℝ} (hu : 0 ≤ u) :
    ∑ v ∈ S.filter (· ≤ u), coef h v = (h.dual.sizeFn u)⁻¹ := by
  obtain ⟨J, hJ, h1, h2⟩ := h.dual.exists_piece hK hu
  rw [h.dual.sizeFn_eq hJ h1 h2]
  simp only [dual, inv_inv]
  simp only [coef, sum_add_distrib]
  rw [sum_ite_eq' _ 0, ite_eq_left (mem_filter.2 ⟨h0, hu⟩), sum_comm]
  have hfilt : ∀ j ∈ Ico 1 K, (∑ v ∈ S.filter (· ≤ u),
      if h.dual.start j = v then h.size j - h.size (j - 1) else 0) =
      if j ≤ J then h.size j - h.size (j - 1) else 0 := by
    intro j hj
    rw [sum_ite_eq]
    have hjK := (mem_Ico.1 hj).2
    by_cases hjJ : j ≤ J
    · rw [ite_eq_left (mem_filter.2 ⟨hS j hj,
        show h.dual.start j ≤ u from (h.dual.start_mono hjJ hJ).trans h1⟩), ite_eq_left hjJ]
    · rw [ite_eq_right, ite_eq_right hjJ]
      intro hm
      have hu' := (mem_filter.1 hm).2
      have := h2 (by omega)
      have := h.dual.start_mono (show J + 1 ≤ j by omega) hjK
      linarith
  rw [sum_congr rfl hfilt, ← sum_filter]
  have : (Ico 1 K).filter (· ≤ J) = Ico 1 (J + 1) := by
    ext j; simp only [mem_filter, mem_Ico]; omega
  rw [this, telescope]

private lemma card_image_choose_two (n : ℕ) :
    ((Icc 2 n).image fun m => ((m.choose 2 : ℕ) : ℝ)).card = n - 1 := by
  rw [card_image_of_injOn, Nat.card_Icc]
  · omega
  intro x hx y hy hxy
  simp only [coe_Icc, Set.mem_Icc] at hx hy
  simp only [Nat.cast_choose_two] at hxy
  have hx' : (2 : ℝ) ≤ x := by exact_mod_cast hx.1
  have hy' : (2 : ℝ) ≤ y := by exact_mod_cast hy.1
  have : ((x : ℝ) - y) * (x + y - 1) = 0 := by linear_combination 2 * hxy
  rcases mul_eq_zero.1 this with h | h
  · exact_mod_cast sub_eq_zero.1 h
  · linarith

/-- **Bhaskar–Song identifiability** (Bhaskar & Song 2014, Corollary 7, "determined" half,
stated for the first-coalescence times): two piecewise-constant histories with `K` pieces whose
expected first-coalescence times `c_m` agree for `2 ≤ m ≤ n`, with `n ≥ 2K`, have the same
population size at every time `s ≥ 0`. The proof writes `C(m,2) c_m` as an exponential sum in
`C(m,2)` over at most `2K - 1` rates (`choose_two_mul_firstCoalMean`), identifies the
coefficients with `Real.eq_zero_of_sum_mul_exp_eq_zero`, recovers the size as a function of
coalescent time (the `dual` history) and inverts `R` (`cumRate_dual_cumRate`). -/
theorem sizeFn_eq_of_firstCoalMean_eq {n : ℕ} (h h' : PiecewiseHistory K) (hn : 2 * K ≤ n)
    (hc : ∀ m ∈ Icc 2 n, firstCoalMean h.sizeFn m = firstCoalMean h'.sizeFn m) :
    ∀ s, 0 ≤ s → h.sizeFn s = h'.sizeFn s := by
  intro s hs
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [sizeFn]
  set S : Finset ℝ := insert 0 ((Ico 1 K).image h.dual.start ∪ (Ico 1 K).image h'.dual.start)
  have h0 : (0 : ℝ) ∈ S := mem_insert_self _ _
  have hS : ∀ j ∈ Ico 1 K, h.dual.start j ∈ S := fun j hj =>
    mem_insert_of_mem (mem_union_left _ (mem_image_of_mem _ hj))
  have hS' : ∀ j ∈ Ico 1 K, h'.dual.start j ∈ S := fun j hj =>
    mem_insert_of_mem (mem_union_right _ (mem_image_of_mem _ hj))
  have hcardS : S.card ≤ 2 * K - 1 := by
    refine (card_insert_le _ _).trans ?_
    have := card_union_le ((Ico 1 K).image h.dual.start) ((Ico 1 K).image h'.dual.start)
    have h1 := card_image_le (s := Ico 1 K) (f := h.dual.start)
    have h2 := card_image_le (s := Ico 1 K) (f := h'.dual.start)
    rw [Nat.card_Ico] at h1 h2
    omega
  -- the coefficients agree
  have hcoef : ∀ u ∈ S, coef h u - coef h' u = 0 := by
    refine Real.eq_zero_of_sum_mul_exp_eq_zero
      (P := (Icc 2 n).image fun m => ((m.choose 2 : ℕ) : ℝ))
      (by rw [card_image_choose_two]; omega) _ fun a ha => ?_
    obtain ⟨m, hm, rfl⟩ := mem_image.1 ha
    simp only [sub_mul, sum_sub_distrib]
    rw [sum_coef_mul_exp h h0 hS, sum_coef_mul_exp h' h0 hS',
      ← h.choose_two_mul_firstCoalMean hK (mem_Icc.1 hm).1,
      ← h'.choose_two_mul_firstCoalMean hK (mem_Icc.1 hm).1, hc m hm, sub_self]
  -- the dual (coalescent-time) histories agree
  have hdual : ∀ u, 0 ≤ u → h.dual.sizeFn u = h'.dual.sizeFn u := by
    intro u hu
    rw [← inv_inj, ← sum_coef_le h hK h0 hS hu, ← sum_coef_le h' hK h0 hS' hu]
    exact sum_congr rfl fun v hv => sub_eq_zero.1 (hcoef v (mem_filter.1 hv).1)
  have hcum : ∀ u, 0 ≤ u → cumRate h.dual.sizeFn u = cumRate h'.dual.sizeFn u := by
    intro u hu
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hu] at hr
    simp only [hdual r hr.1]
  -- hence the cumulative rates agree
  have hR : ∀ g : PiecewiseHistory K, 0 ≤ cumRate g.sizeFn s := fun g => by
    obtain ⟨j, hj, h1, h2⟩ := g.exists_piece hK hs
    exact (g.dual.start_nonneg hj).trans (g.cumRate_mem_piece hj h1 h2).1
  have hRR : cumRate h.sizeFn s = cumRate h'.sizeFn s := by
    have e1 := h.cumRate_dual_cumRate hK hs
    have e2 := h'.cumRate_dual_cumRate hK hs
    rw [← hcum _ (hR h')] at e2
    rcases lt_trichotomy (cumRate h.sizeFn s) (cumRate h'.sizeFn s) with hlt | heq | hgt
    · have := h.dual.cumRate_strictMonoOn hK (hR h) (hR h') hlt
      linarith
    · exact heq
    · have := h.dual.cumRate_strictMonoOn hK (hR h') (hR h) hgt
      linarith
  rw [h.sizeFn_eq_inv_dual hK hs, h'.sizeFn_eq_inv_dual hK hs, hRR, hdual _ (hR h')]

/-- A two-piece history: size `1` on `[0, log 2)`, then size `3` (first half of the tightness
example). -/
def tightA : PiecewiseHistory 2 where
  size j := if j = 0 then 1 else 3
  start j := if j = 0 then 0 else Real.log 2
  size_pos j _ := by split_ifs <;> norm_num
  start_zero := by simp
  start_lt j hj := by
    obtain rfl : j = 0 := by omega
    simpa using Real.log_pos one_lt_two

/-- A two-piece history: size `37/32` on `[0, (37/32) log 3)`, then size `59/16` (second half
of the tightness example). -/
def tightB : PiecewiseHistory 2 where
  size j := if j = 0 then 37 / 32 else 59 / 16
  start j := if j = 0 then 0 else 37 / 32 * Real.log 3
  size_pos j _ := by split_ifs <;> norm_num
  start_zero := by simp
  start_lt j hj := by
    obtain rfl : j = 0 := by omega
    have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]
    positivity

/-- The first coalescent-time breakpoint of a two-piece history. -/
private lemma cumRate_start_one (h : PiecewiseHistory 2) :
    cumRate h.sizeFn (h.start 1) = h.start 1 / h.size 0 := by
  rw [(h.cumRate_piece 0 (by norm_num) _ (h.start_lt 0 (by norm_num)).le fun _ => le_rfl).2]
  simp [h.start_zero, cumRate]

/-- The closed form of `C(m,2) c_m` for a two-piece history. -/
private lemma two_piece (h : PiecewiseHistory 2) {m : ℕ} (hm : 2 ≤ m) :
    ((m.choose 2 : ℕ) : ℝ) * firstCoalMean h.sizeFn m =
      h.size 0 + (h.size 1 - h.size 0) *
        Real.exp (-((m.choose 2 : ℕ) : ℝ) * (h.start 1 / h.size 0)) := by
  rw [h.choose_two_mul_firstCoalMean (by norm_num) hm,
    show (Ico 1 2 : Finset ℕ) = {1} by decide, sum_singleton, cumRate_start_one]

/-- **Tightness of `n ≥ 2K` for `K = 2`**: two different two-piece histories with the same
`c_2` and `c_3`, so `c_2, …, c_{2K-1}` do not determine a two-piece history. This is an
explicit instance (constructed here) of the tightness statement of Bhaskar & Song (2014),
Corollary 7; with `a c_m = η₀ + (η₁ - η₀) x^a`, `a = C(m,2)`, both histories give
`a c_m = 2` at `a = 1` and `5/4` at `a = 3` (`x = 1/2` and `x = 1/3`). The general `K` is
`VariableSFSWanted.exists_ne_firstCoalMean_eq_of_lt`. -/
theorem exists_ne_firstCoalMean_eq_two :
    ∃ h h' : PiecewiseHistory 2, (∃ s, 0 ≤ s ∧ h.sizeFn s ≠ h'.sizeFn s) ∧
      ∀ m ∈ Icc 2 3, firstCoalMean h.sizeFn m = firstCoalMean h'.sizeFn m := by
  refine ⟨tightA, tightB, ⟨0, le_rfl, ?_⟩, fun m hm => ?_⟩
  · rw [tightA.sizeFn_eq (j := 0) (by norm_num) tightA.start_zero.le (fun hk => by
      simpa only [tightA.start_zero] using tightA.start_lt 0 hk),
      tightB.sizeFn_eq (j := 0) (by norm_num) tightB.start_zero.le (fun hk => by
      simpa only [tightB.start_zero] using tightB.start_lt 0 hk)]
    simp [tightA, tightB]
    norm_num
  · have hm2 := (mem_Icc.1 hm).1
    have ha : ((m.choose 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hm2).ne'
    refine mul_left_cancel₀ ha ?_
    rw [two_piece _ hm2, two_piece _ hm2]
    simp only [tightA, tightB, ↓reduceIte, one_ne_zero, div_one]
    have e2 : ∀ k : ℕ, Real.exp (-(k : ℝ) * Real.log 2) = ((2 : ℝ) ^ k)⁻¹ := fun k => by
      rw [neg_mul, Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity)]
    have e3 : ∀ k : ℕ, Real.exp (-(k : ℝ) * (37 / 32 * Real.log 3 / (37 / 32))) =
        ((3 : ℝ) ^ k)⁻¹ := fun k => by
      rw [show 37 / 32 * Real.log 3 / (37 / 32) = Real.log 3 by ring, neg_mul, Real.exp_neg,
        ← Real.log_pow, Real.exp_log (by positivity)]
    rw [e2, e3]
    have hm3 := (mem_Icc.1 hm).2
    obtain rfl | rfl : m = 2 ∨ m = 3 := by omega
    · norm_num
    · norm_num [Nat.choose]

end PiecewiseHistory

end MathlibExt.Biology.PopulationGenetics.Coalescent.VariableSFS
