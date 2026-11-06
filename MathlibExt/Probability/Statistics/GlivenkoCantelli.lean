/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.CDF
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Filter Function
open scoped Topology

namespace MathlibExt.Probability.Statistics.GlivenkoCantelliWanted
/-!
# Glivenko–Cantelli theorem

The uniform SLLN: empirical CDFs converge uniformly a.s. to the
theoretical CDF.
-/

/-- **Empirical count.** Let $X_0, X_1, X_2, \dots$ be real-valued functions on a set $\Omega$.
For a natural number $n$, a point $\omega \in \Omega$ and a real number $x$, the empirical count is
the number of indices $i \in \{0, 1, \dots, n\}$ with $X_i(\omega) \le x$. Divided by $n + 1$, it
is the value at $x$ of the empirical distribution function of $X_0(\omega), \dots, X_n(\omega)$. -/
noncomputable def empiricalCount {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) : ℕ :=
  by classical
    exact (Finset.filter (fun i => X i ω ≤ x) (Finset.range (n + 1))).card

/-- The (right-continuous) theoretical CDF of `X 0`, as a plain real function. -/
private noncomputable def theoreticalCDF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X0 : Ω → ℝ)
    (x : ℝ) : ℝ := (P (X0 ⁻¹' Set.Iic x)).toReal

/-- Quantile grid points used in the uniformization step. -/
private noncomputable def theoreticalQuantile {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X0 : Ω → ℝ)
    (m k : ℕ) : ℝ := sInf {y | (k : ℝ) / (m : ℝ) ≤ theoreticalCDF P X0 y}

/-- Empirical CDF value `#{i ≤ n : X i ω ≤ x}/(n+1)`. -/
private noncomputable def eCDF {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  (empiricalCount X n ω x : ℝ) / ((n + 1 : ℕ) : ℝ)

/-- Left-continuous empirical CDF value `#{i ≤ n : X i ω < x}/(n+1)`. -/
private noncomputable def eCDFlt {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  (((Finset.range (n + 1)).filter (fun i => X i ω < x)).card : ℝ) / ((n + 1 : ℕ) : ℝ)

private lemma empiricalCount_eq {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) :
    empiricalCount X n ω x = ((Finset.range (n + 1)).filter (fun i => X i ω ≤ x)).card := rfl

/-- SLLN for a bounded measurable transform `g` of an i.i.d. sequence. -/
private theorem slln_bounded
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ n, Measurable (X n))
    (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (g : ℝ → ℝ) (hg : Measurable g) (hgb : ∀ t, ‖g t‖ ≤ 1) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, g (X i ω)) / n) atTop
      (𝓝 (∫ ω, g (X 0 ω) ∂P)) := by
  set Y : ℕ → Ω → ℝ := fun i ω => g (X i ω) with hY
  have hY0int : Integrable (Y 0) P := by
    apply (integrable_const (1 : ℝ)).mono' (hg.comp (hMeas 0)).aestronglyMeasurable
    filter_upwards with ω
    simpa using hgb (X 0 ω)
  have hpair : Pairwise ((· ⟂ᵢ[P] ·) on Y) := fun i j hij => (hIndep.indepFun hij).comp hg hg
  have hyident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i => (hIdent i).comp hg
  have := strong_law_ae_real Y hY0int hpair hyident
  simpa [hY] using this

open Classical in
/-- Empirical fraction of the first `n` samples landing in a measurable set `s`
converges a.s. to `(P (X 0 ⁻¹' s)).toReal`. -/
private theorem tendsto_empirical_frac
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ n, Measurable (X n))
    (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
    (s : Set ℝ) (hs : MeasurableSet s) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (((Finset.range n).filter (fun i => X i ω ∈ s)).card : ℝ) / n) atTop
      (𝓝 (P (X 0 ⁻¹' s)).toReal) := by
  have hgmeas : Measurable (s.indicator (1 : ℝ → ℝ)) := (measurable_const).indicator hs
  have hgb : ∀ t, ‖s.indicator (1 : ℝ → ℝ) t‖ ≤ 1 := by
    intro t
    by_cases ht : t ∈ s <;> simp [ht]
  have hmean : (∫ ω, s.indicator (1 : ℝ → ℝ) (X 0 ω) ∂P) = (P (X 0 ⁻¹' s)).toReal := by
    have hcomp : (fun ω => s.indicator (1 : ℝ → ℝ) (X 0 ω))
        = (X 0 ⁻¹' s).indicator 1 := by
      funext ω
      simp [Set.indicator_apply, Set.mem_preimage]
    rw [hcomp, integral_indicator_one (hMeas 0 hs), measureReal_def]
  have H := slln_bounded X hMeas hIndep hIdent (s.indicator 1) hgmeas hgb
  rw [hmean] at H
  filter_upwards [H] with ω hω
  refine hω.congr (fun n => ?_)
  congr 1
  have hcast : ∀ i, s.indicator (1 : ℝ → ℝ) (X i ω) = if X i ω ∈ s then (1:ℝ) else 0 := by
    intro i; simp [Set.indicator_apply]
  simp_rw [hcast]
  rw [Finset.sum_boole]

/-- Deterministic uniformization step. -/
private theorem unif_bound
    (G Gl φ ψ : ℝ → ℝ) (q : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 ≤ δ)
    (hG0 : ∀ x, 0 ≤ G x) (hG1 : ∀ x, G x ≤ 1) (hGmono : Monotone G)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (hφmono : Monotone φ)
    (hψφ : ∀ x y, x < y → φ x ≤ ψ y)
    (hGGL : ∀ x y, x < y → G x ≤ Gl y)
    (hqG : ∀ k, 1 ≤ k → k ≤ m - 1 → (k : ℝ) / m ≤ G (q k))
    (hqGL : ∀ k, 1 ≤ k → k ≤ m - 1 → Gl (q k) ≤ (k : ℝ) / m)
    (hdev2 : ∀ k, 1 ≤ k → k ≤ m - 1 → ψ (q k) ≤ Gl (q k) + δ)
    (hdev1 : ∀ k, 1 ≤ k → k ≤ m - 1 → G (q k) - δ ≤ φ (q k)) :
    ∀ x, |φ x - G x| ≤ 1 / m + δ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  intro x
  rw [abs_le]
  constructor
  · rw [neg_le, neg_sub]
    classical
    set L := (Finset.Icc 1 (m - 1)).filter (fun k => q k ≤ x) with hL
    by_cases hLe : L.Nonempty
    · set k1 := L.max' hLe with hk1
      have hk1mem : k1 ∈ L := L.max'_mem hLe
      have hk1L : q k1 ≤ x := (Finset.mem_filter.mp hk1mem).2
      have hk1I : k1 ∈ Finset.Icc 1 (m - 1) := (Finset.mem_filter.mp hk1mem).1
      have h1k1 : 1 ≤ k1 := (Finset.mem_Icc.mp hk1I).1
      have hk1m : k1 ≤ m - 1 := (Finset.mem_Icc.mp hk1I).2
      have hφge : (k1 : ℝ) / m - δ ≤ φ x := by
        have h1 : G (q k1) - δ ≤ φ (q k1) := hdev1 k1 h1k1 hk1m
        have h2 : (k1 : ℝ)/m ≤ G (q k1) := hqG k1 h1k1 hk1m
        have h3 : φ (q k1) ≤ φ x := hφmono hk1L
        linarith
      by_cases hk1top : k1 = m - 1
      · have hb : G x ≤ 1 := hG1 x
        have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm]; norm_num
        rw [hk1top, hcast] at hφge
        have hh : ((m : ℝ) - 1)/m = 1 - 1/m := by
          rw [sub_div, div_self (ne_of_gt hmR)]
        rw [hh] at hφge
        linarith
      · have hk1' : k1 + 1 ≤ m - 1 := by omega
        have hmemI : k1 + 1 ∈ Finset.Icc 1 (m - 1) := Finset.mem_Icc.mpr ⟨by omega, hk1'⟩
        have hnotL : k1 + 1 ∉ L := fun hc => by
          have := L.le_max' _ hc; omega
        have hlt : x < q (k1 + 1) := by
          by_contra hc
          push Not at hc
          exact hnotL (Finset.mem_filter.mpr ⟨hmemI, hc⟩)
        have hGx : G x ≤ Gl (q (k1 + 1)) := hGGL x (q (k1+1)) hlt
        have hGL : Gl (q (k1+1)) ≤ ((k1:ℝ)+1)/m := by
          have := hqGL (k1+1) (by omega) hk1'
          rw [Nat.cast_add, Nat.cast_one] at this
          exact this
        have hstep : ((k1:ℝ)+1)/m - (k1:ℝ)/m = 1/m := by
          rw [div_sub_div_same]; ring_nf
        linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hLe
      by_cases hm1 : m = 1
      · have : (1:ℝ)/m = 1 := by rw [hm1]; norm_num
        have hφ := hφ0 x; have hG := hG1 x
        linarith
      · have hm2 : 2 ≤ m := by omega
        have hmemI : 1 ∈ Finset.Icc 1 (m-1) := Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩
        have hnotL : (1:ℕ) ∉ L := by rw [hLe]; exact Finset.notMem_empty 1
        have hlt : x < q 1 := by
          by_contra hc; push Not at hc
          exact hnotL (Finset.mem_filter.mpr ⟨hmemI, hc⟩)
        have hGx : G x ≤ Gl (q 1) := hGGL x (q 1) hlt
        have hGL : Gl (q 1) ≤ (1:ℝ)/m := by
          have := hqGL 1 (le_refl 1) (by omega); rw [Nat.cast_one] at this; exact this
        have := hφ0 x
        linarith
  · classical
    set K := (Finset.Icc 1 (m - 1)).filter (fun k => x < q k) with hK
    by_cases hKe : K.Nonempty
    · set k0 := K.min' hKe with hk0
      have hk0mem : k0 ∈ K := K.min'_mem hKe
      have hk0K : x < q k0 := (Finset.mem_filter.mp hk0mem).2
      have hk0I : k0 ∈ Finset.Icc 1 (m - 1) := (Finset.mem_filter.mp hk0mem).1
      have h1k0 : 1 ≤ k0 := (Finset.mem_Icc.mp hk0I).1
      have hk0m : k0 ≤ m - 1 := (Finset.mem_Icc.mp hk0I).2
      have hφle : φ x ≤ (k0 : ℝ)/m + δ := by
        have h1 : φ x ≤ ψ (q k0) := hψφ x (q k0) hk0K
        have h2 : ψ (q k0) ≤ Gl (q k0) + δ := hdev2 k0 h1k0 hk0m
        have h3 : Gl (q k0) ≤ (k0:ℝ)/m := hqGL k0 h1k0 hk0m
        linarith
      by_cases hk0bot : k0 = 1
      · have := hG0 x
        rw [hk0bot] at hφle
        simp only [Nat.cast_one] at hφle
        linarith
      · have h2k0 : 2 ≤ k0 := by omega
        have hk0'I : k0 - 1 ∈ Finset.Icc 1 (m - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hnotK : k0 - 1 ∉ K := fun hc => by
          have := K.min'_le _ hc; omega
        have hle : q (k0 - 1) ≤ x := by
          by_contra hc; push Not at hc
          exact hnotK (Finset.mem_filter.mpr ⟨hk0'I, hc⟩)
        have hGge : ((k0:ℝ) - 1)/m ≤ G x := by
          have h1 := hqG (k0-1) (by omega) (by omega)
          have hcast : ((k0 - 1 : ℕ) : ℝ) = (k0 : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega)]; norm_num
          rw [hcast] at h1
          have h2 : G (q (k0-1)) ≤ G x := hGmono hle
          linarith
        have hstep : (k0:ℝ)/m - ((k0:ℝ)-1)/m = 1/m := by
          rw [div_sub_div_same]; ring_nf
        linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hKe
      have hGxge : ((m:ℝ) - 1)/m ≤ G x := by
        by_cases hm1 : m = 1
        · rw [hm1]; simpa using hG0 x
        · have hm2 : 2 ≤ m := by omega
          have hmemI : m - 1 ∈ Finset.Icc 1 (m-1) := Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩
          have hnotK : m - 1 ∉ K := by rw [hKe]; exact Finset.notMem_empty _
          have hle : q (m-1) ≤ x := by
            by_contra hc; push Not at hc
            exact hnotK (Finset.mem_filter.mpr ⟨hmemI, hc⟩)
          have h1 := hqG (m-1) (by omega) (le_refl _)
          have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega)]; norm_num
          rw [hcast] at h1
          have h2 : G (q (m-1)) ≤ G x := hGmono hle
          linarith
      have hmm : ((m:ℝ)-1)/m = 1 - 1/m := by
        rw [sub_div, div_self (ne_of_gt hmR)]
      have := hφ1 x
      linarith

/-- Quantile properties of a CDF-like function `G`. -/
private theorem quantile_props (G : ℝ → ℝ) (hmono : Monotone G)
    (hrc : ∀ x, ContinuousWithinAt G (Ici x) x)
    (htop : Tendsto G atTop (𝓝 1)) (hbot : Tendsto G atBot (𝓝 0))
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    c ≤ G (sInf {y | c ≤ G y}) ∧ Function.leftLim G (sInf {y | c ≤ G y}) ≤ c := by
  set s : Set ℝ := {y | c ≤ G y} with hs
  have hne : s.Nonempty := by
    have : ∀ᶠ y in atTop, c < G y := htop.eventually (eventually_gt_nhds hc1)
    obtain ⟨y, hy⟩ := this.exists
    exact ⟨y, hy.le⟩
  have hbdd : BddBelow s := by
    have : ∀ᶠ y in atBot, G y < c := hbot.eventually (eventually_lt_nhds hc0)
    rw [eventually_atBot] at this
    obtain ⟨z, hz⟩ := this
    refine ⟨z, fun w hw => ?_⟩
    by_contra hlt
    push Not at hlt
    exact absurd (hz w hlt.le) (not_lt.mpr hw)
  set xc := sInf s with hxc
  have hpos : ∀ y, xc < y → c ≤ G y := by
    intro y hy
    obtain ⟨w, hw, hwy⟩ := exists_lt_of_csInf_lt hne hy
    exact le_trans hw (hmono hwy.le)
  have h1 : c ≤ G xc := by
    have htend : Tendsto G (𝓝[>] xc) (𝓝 (G xc)) :=
      (hrc xc).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    exact ge_of_tendsto htend (Filter.eventually_of_mem self_mem_nhdsWithin
      (fun y hy => hpos y hy))
  have hneg : ∀ y, y < xc → G y < c := by
    intro y hy
    by_contra hle
    push Not at hle
    have : xc ≤ y := csInf_le hbdd hle
    exact absurd hy (not_lt.mpr this)
  have h2 : Function.leftLim G xc ≤ c := by
    have htend : Tendsto G (𝓝[<] xc) (𝓝 (Function.leftLim G xc)) := hmono.tendsto_leftLim xc
    exact le_of_tendsto htend (Filter.eventually_of_mem self_mem_nhdsWithin
      (fun y hy => (hneg y hy).le))
  exact ⟨h1, h2⟩

private lemma eCDF_nonneg {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) :
    0 ≤ eCDF X n ω x := by
  unfold eCDF; positivity

private lemma eCDF_le_one {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) :
    eCDF X n ω x ≤ 1 := by
  unfold eCDF
  rw [empiricalCount_eq]
  rw [div_le_one (by positivity)]
  have : ((Finset.range (n+1)).filter (fun i => X i ω ≤ x)).card ≤ n + 1 := by
    calc ((Finset.range (n+1)).filter (fun i => X i ω ≤ x)).card
        ≤ (Finset.range (n+1)).card := Finset.card_filter_le _ _
      _ = n + 1 := Finset.card_range _
  exact_mod_cast this

private lemma eCDF_mono {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Monotone (fun x => eCDF X n ω x) := by
  intro x y hxy
  simp only [eCDF]
  rw [empiricalCount_eq, empiricalCount_eq]
  gcongr

private lemma eCDF_le_eCDFlt {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) {x y : ℝ} (hxy : x < y) :
    eCDF X n ω x ≤ eCDFlt X n ω y := by
  simp only [eCDF, eCDFlt]
  rw [empiricalCount_eq]
  gcongr

/--
**Glivenko–Cantelli theorem.** Let $P$ be a probability measure on a measurable space $\Omega$,
and let $X_0, X_1, X_2, \dots$ be measurable real-valued functions on $\Omega$ that are mutually
independent under $P$ and each have the same distribution as $X_0$. Write $F(x) = P(X_0 \le x)$
for the distribution function of $X_0$, and $C_n(\omega, x)$ for the empirical count, the number
of indices $i \in \{0, 1, \dots, n\}$ with $X_i(\omega) \le x$. Then for $P$-almost every
$\omega \in \Omega$: for every $\varepsilon > 0$ there is a natural number $N$ such that for all
$n \ge N$ and all real $x$,
$$\left| \frac{C_n(\omega, x)}{n + 1} - F(x) \right| < \varepsilon.$$
That is, almost surely the empirical distribution function of $X_0, \dots, X_n$ converges to $F$
uniformly on $\mathbb{R}$.

Proves `Wanted` entry `glivenko_cantelli`.

Source: V. Glivenko, Sulla determinazione empirica delle leggi di probabilita, Giorn.
Ist. Ital. Attuari 4 (1933) 92–99; F. Cantelli 1933; textbook in Durrett, Probability Theory and
Examples, 5th ed., Probability and Measure
-/
theorem glivenko_cantelli
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (X n))
    (hIndep : iIndepFun X P)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ,
      |((empiricalCount X n ω x : ℝ) / ((n + 1 : ℕ) : ℝ) - (P (X 0 ⁻¹' Set.Iic x)).toReal)| <
          ε := by
  classical
  have hμ0prob : IsProbabilityMeasure (P.map (X 0)) := inferInstance
  set μ0 := P.map (X 0) with hμ0def
  have hGfun : theoreticalCDF P (X 0) = (cdf μ0 : ℝ → ℝ) := by
    funext x
    simp only [theoreticalCDF]
    rw [cdf_eq_real μ0 x, measureReal_def, hμ0def,
        Measure.map_apply (hMeas 0) measurableSet_Iic]
  have hGmono : Monotone (theoreticalCDF P (X 0)) := by rw [hGfun]; exact (cdf μ0).mono
  have hrc : ∀ x, ContinuousWithinAt (theoreticalCDF P (X 0)) (Ici x) x := by
    rw [hGfun]; exact fun x => (cdf μ0).right_continuous x
  have htop : Tendsto (theoreticalCDF P (X 0)) atTop (𝓝 1) := by
    rw [hGfun]; exact tendsto_cdf_atTop μ0
  have hbot : Tendsto (theoreticalCDF P (X 0)) atBot (𝓝 0) := by
    rw [hGfun]; exact tendsto_cdf_atBot μ0
  have hGnonneg : ∀ x, 0 ≤ theoreticalCDF P (X 0) x := by
    rw [hGfun]; exact fun x => cdf_nonneg μ0 x
  have hGle1 : ∀ x, theoreticalCDF P (X 0) x ≤ 1 := by
    rw [hGfun]; exact fun x => cdf_le_one μ0 x
  have hFminusEq : ∀ a, (P (X 0 ⁻¹' Set.Iio a)).toReal
      = Function.leftLim (theoreticalCDF P (X 0)) a := by
    intro a
    have hnn : (0:ℝ) ≤ Function.leftLim (⇑(cdf μ0)) a :=
      le_trans (cdf_nonneg μ0 (a-1)) ((cdf μ0).mono.le_leftLim (show a - 1 < a by linarith))
    have h1 : P (X 0 ⁻¹' Set.Iio a) = μ0 (Set.Iio a) := by
      rw [hμ0def, Measure.map_apply (hMeas 0) measurableSet_Iio]
    have hleq : Function.leftLim (theoreticalCDF P (X 0)) a = Function.leftLim (⇑(cdf μ0)) a := by
      rw [hGfun]
    rw [h1, ← measure_cdf μ0, StieltjesFunction.measure_Iio _ (tendsto_cdf_atBot μ0) a, sub_zero,
        ENNReal.toReal_ofReal hnn, hleq]
  have hae : ∀ᵐ ω ∂P, ∀ (m k : ℕ),
      Tendsto (fun n => eCDF X n ω (theoreticalQuantile P (X 0) m k)) atTop
        (𝓝 (theoreticalCDF P (X 0) (theoreticalQuantile P (X 0) m k))) ∧
      Tendsto (fun n => eCDFlt X n ω (theoreticalQuantile P (X 0) m k)) atTop
        (𝓝 (Function.leftLim (theoreticalCDF P (X 0)) (theoreticalQuantile P (X 0) m k))) := by
    refine ae_all_iff.mpr (fun m => ae_all_iff.mpr (fun k => ?_))
    have hIic := tendsto_empirical_frac X hMeas hIndep hIdent
      (Set.Iic (theoreticalQuantile P (X 0) m k)) measurableSet_Iic
    have hIio := tendsto_empirical_frac X hMeas hIndep hIdent
      (Set.Iio (theoreticalQuantile P (X 0) m k)) measurableSet_Iio
    filter_upwards [hIic, hIio] with ω h1 h2
    refine ⟨?_, ?_⟩
    · have h1' := h1.comp (tendsto_add_atTop_nat 1)
      have hlim : (P (X 0 ⁻¹' Set.Iic (theoreticalQuantile P (X 0) m k))).toReal
          = theoreticalCDF P (X 0) (theoreticalQuantile P (X 0) m k) := rfl
      rw [← hlim]
      exact Tendsto.congr (fun n => rfl) h1'
    · have h2' := h2.comp (tendsto_add_atTop_nat 1)
      rw [← hFminusEq (theoreticalQuantile P (X 0) m k)]
      exact Tendsto.congr (fun n => rfl) h2'
  filter_upwards [hae] with ω hω
  intro ε hε
  obtain ⟨m, hm1, hmε⟩ : ∃ m : ℕ, 1 ≤ m ∧ (1:ℝ)/(m:ℝ) < ε/2 := by
    obtain ⟨m0, hm0⟩ := exists_nat_gt (2/ε)
    refine ⟨m0 + 1, by omega, ?_⟩
    have hmpos : (0:ℝ) < ((m0+1:ℕ):ℝ) := by positivity
    rw [div_lt_iff₀ hmpos]
    have h2 : 2 < (m0:ℝ) * ε := (div_lt_iff₀ hε).mp hm0
    push_cast
    nlinarith [h2, hε]
  set η := ε/2 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  have hev : ∀ᶠ n in atTop, ∀ k ∈ Finset.Icc 1 (m-1),
      |eCDF X n ω (theoreticalQuantile P (X 0) m k)
        - theoreticalCDF P (X 0) (theoreticalQuantile P (X 0) m k)| ≤ η ∧
      |eCDFlt X n ω (theoreticalQuantile P (X 0) m k)
        - Function.leftLim (theoreticalCDF P (X 0)) (theoreticalQuantile P (X 0) m k)| ≤ η := by
    rw [eventually_all_finset]
    intro k _
    obtain ⟨ht1, ht2⟩ := hω m k
    have e1 := ht1.eventually (Metric.closedBall_mem_nhds _ hηpos)
    have e2 := ht2.eventually (Metric.closedBall_mem_nhds _ hηpos)
    filter_upwards [e1, e2] with n hn1 hn2
    rw [Real.dist_eq] at hn1 hn2
    exact ⟨hn1, hn2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn x => ?_⟩
  have hqG : ∀ k, 1 ≤ k → k ≤ m - 1 →
      (k:ℝ)/(m:ℝ) ≤ theoreticalCDF P (X 0) (theoreticalQuantile P (X 0) m k) := by
    intro k hk1 hk2
    have hkpos : 0 < k := hk1
    have hmpos : 0 < m := hm1
    have hc0 : 0 < (k:ℝ)/(m:ℝ) := div_pos (by exact_mod_cast hkpos) (by exact_mod_cast hmpos)
    have hkm : k < m := by omega
    have hc1 : (k:ℝ)/(m:ℝ) < 1 := by
      rw [div_lt_one (by exact_mod_cast hmpos)]; exact_mod_cast hkm
    exact (quantile_props (theoreticalCDF P (X 0)) hGmono hrc htop hbot _ hc0 hc1).1
  have hqGL : ∀ k, 1 ≤ k → k ≤ m - 1 →
      Function.leftLim (theoreticalCDF P (X 0)) (theoreticalQuantile P (X 0) m k)
        ≤ (k:ℝ)/(m:ℝ) := by
    intro k hk1 hk2
    have hkpos : 0 < k := hk1
    have hmpos : 0 < m := hm1
    have hc0 : 0 < (k:ℝ)/(m:ℝ) := div_pos (by exact_mod_cast hkpos) (by exact_mod_cast hmpos)
    have hkm : k < m := by omega
    have hc1 : (k:ℝ)/(m:ℝ) < 1 := by
      rw [div_lt_one (by exact_mod_cast hmpos)]; exact_mod_cast hkm
    exact (quantile_props (theoreticalCDF P (X 0)) hGmono hrc htop hbot _ hc0 hc1).2
  have hdev1 : ∀ k, 1 ≤ k → k ≤ m - 1 →
      theoreticalCDF P (X 0) (theoreticalQuantile P (X 0) m k) - η
        ≤ eCDF X n ω (theoreticalQuantile P (X 0) m k) := by
    intro k hk1 hk2
    have hh := (hN n hn k (Finset.mem_Icc.mpr ⟨hk1, hk2⟩)).1
    rw [abs_le] at hh
    linarith [hh.1]
  have hdev2 : ∀ k, 1 ≤ k → k ≤ m - 1 →
      eCDFlt X n ω (theoreticalQuantile P (X 0) m k)
        ≤ Function.leftLim (theoreticalCDF P (X 0)) (theoreticalQuantile P (X 0) m k) + η := by
    intro k hk1 hk2
    have hh := (hN n hn k (Finset.mem_Icc.mpr ⟨hk1, hk2⟩)).2
    rw [abs_le] at hh
    linarith [hh.2]
  have hbound := unif_bound (theoreticalCDF P (X 0)) (Function.leftLim (theoreticalCDF P (X 0)))
    (fun x => eCDF X n ω x) (fun x => eCDFlt X n ω x) (theoreticalQuantile P (X 0) m) m hm1 η
    (le_of_lt hηpos) hGnonneg hGle1 hGmono
    (fun x => eCDF_nonneg X n ω x) (fun x => eCDF_le_one X n ω x) (eCDF_mono X n ω)
    (fun x y hxy => eCDF_le_eCDFlt X n ω hxy)
    (fun x y hxy => hGmono.le_leftLim hxy)
    hqG hqGL hdev2 hdev1 x
  refine lt_of_le_of_lt hbound ?_
  rw [hη]; linarith [hmε]

end MathlibExt.Probability.Statistics.GlivenkoCantelliWanted
