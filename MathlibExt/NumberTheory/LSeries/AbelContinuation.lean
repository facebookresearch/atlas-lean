/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.MellinTransform
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.LSeries.SumCoeff

@[expose] public section

/-!
# Abel continuation of Dirichlet series under partial-sum bounds

For `f : ℕ → ℂ`, let `A(n) = ∑ k ∈ Finset.Icc 1 n, f k` be the one-based
partial sums. Under a genuine `IsBigO atTop` bound `A(n) = O(n ^ σ)` for an
arbitrary real `σ`, the Abel integral

  `F_f(s) = s * ∫ x in Set.Ioi (1 : ℝ), A(⌊x⌋₊) * x ^ (-s - 1) dx`

(using exact Mathlib conventions, as in `LSeries_eq_mul_integral`) converges
for `σ < s.re`, is complex differentiable there, hence analytic on the
half-plane. The ordered Dirichlet partial sums
`∑ n ∈ Finset.Icc 1 N, LSeries.term f s n` converge to `F_f(s)` under the
same hypotheses alone (no summability): this is genuine conditional
convergence, proved by Abel summation. Only the agreement
`F_f(s) = LSeries f s` needs `LSeriesSummable f s` (and `0 ≤ σ`, which the
public `LSeries_eq_mul_integral` API requires). We prove nothing about
`LSeries f` itself where it is nonsummable: its `tsum`-based definition
collapses to `0` there.

## Main definitions

* `abelPartialSum f n`: the one-based partial sums `∑ k ∈ Finset.Icc 1 n, f k`.
* `abelSummatory f`: the step function `t ↦ abelPartialSum f ⌊t⌋₊` on `ℝ`.
* `abelContinuation f s`: the Abel continuation `F_f(s)` above.

## Main results

* `differentiableAt_abelContinuation`: pointwise complex differentiability on
  `σ < s.re` for arbitrary real `σ`, via the Mellin transform identity
  `F_f(s) = s * mellin (abelSummatory f) (-s)` and
  `mellin_differentiableAt_of_isBigO_rpow`.
* `analyticOn_abelContinuation`: set-level analyticity on the half-plane,
  for arbitrary real `σ`.
* `tendsto_abelContinuation_Icc`: convergence of ordered Dirichlet partial
  sums to `F_f(s)` from the growth hypothesis and `σ < s.re` alone, via
  public `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`.
* `abelContinuation_eq_LSeries`: agreement with `LSeries f s` under
  `LSeriesSummable f s` (requires `0 ≤ σ`, inherited from Mathlib's
  `LSeries_eq_mul_integral`).
-/

open Filter Asymptotics MeasureTheory Topology Set Complex

noncomputable section

/-- One-based partial sums of `f`. -/
def abelPartialSum (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 n, f k

/-- The summatory step function `t ↦ A(⌊t⌋₊)` on `ℝ`. -/
def abelSummatory (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  abelPartialSum f ⌊t⌋₊

/-- The Abel continuation `F_f(s) = s * ∫ x in Ioi 1, A(⌊x⌋) * x^(-s-1)`,
in the exact conventions of `LSeries_eq_mul_integral`. -/
def abelContinuation (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  s * ∫ t : ℝ in Set.Ioi (1 : ℝ), abelSummatory f t * (t : ℂ) ^ (-(s + 1))

/-- The summatory function vanishes below `1`. -/
theorem abelSummatory_eq_zero_of_lt_one (f : ℕ → ℂ) {t : ℝ} (ht : t < 1) :
    abelSummatory f t = 0 := by
  have hfloor : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht
  simp [abelSummatory, abelPartialSum, hfloor]

/-- The summatory function is locally integrable on `Ioi 0`. -/
theorem locallyIntegrableOn_abelSummatory (f : ℕ → ℂ) :
    LocallyIntegrableOn (abelSummatory f) (Set.Ioi (0 : ℝ)) := by
  have h : LocallyIntegrableOn (fun t : ℝ => (1 : ℂ) * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k)
      (Set.Ici (0 : ℝ)) :=
    locallyIntegrableOn_mul_sum_Icc f le_rfl (locallyIntegrableOn_const 1)
  refine LocallyIntegrableOn.congr ?_ (h.mono_set Set.Ioi_subset_Ici_self)
  filter_upwards with t
  simp [abelSummatory, abelPartialSum]

/-- Under `A(n) = O(n ^ σ)` for arbitrary real `σ`, the summatory function
is `O(t ^ σ)` at infinity. The floor comparison goes through
`Asymptotics.isEquivalent_nat_floor.rpow` applied to the symmetric
equivalence, so the nonnegativity hypothesis falls on real casts of
naturals (always true) rather than on `σ`. -/
theorem isBigO_abelSummatory_atTop (f : ℕ → ℂ) {σ : ℝ}
    (hO : (fun n => abelPartialSum f n) =O[atTop]
      fun n => ((n : ℝ) ^ σ : ℝ)) :
    (abelSummatory f) =O[atTop] fun t : ℝ => (t ^ σ : ℝ) := by
  have h1 : ((fun n => abelPartialSum f n) ∘ fun t : ℝ => ⌊t⌋₊) =O[atTop]
      ((fun n : ℕ => ((n : ℝ) ^ σ : ℝ)) ∘ fun t : ℝ => ⌊t⌋₊) :=
    hO.comp_tendsto tendsto_nat_floor_atTop
  have h2 : (fun t : ℝ => (((⌊t⌋₊ : ℕ) : ℝ) ^ σ : ℝ)) =O[atTop]
      fun t => (t ^ σ : ℝ) :=
    ((Asymptotics.isEquivalent_nat_floor (R := ℝ)).symm.rpow (r := σ)
      (Pi.le_def.mpr fun _ => Nat.cast_nonneg _)).symm.isBigO
  exact h1.trans h2

/-- The summatory function is eventually zero near `0`, hence `O` of anything. -/
theorem isBigO_abelSummatory_nhdsGT_zero (f : ℕ → ℂ) (b : ℝ) :
    (abelSummatory f) =O[𝓝[>] (0 : ℝ)] fun t : ℝ => (t ^ (-b) : ℝ) := by
  refine Filter.EventuallyEq.trans_isBigO ?_ (Asymptotics.isBigO_zero _ _)
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
  simp [abelSummatory_eq_zero_of_lt_one f ht.2]

/-- The Abel integral equals `s` times the Mellin transform at `-s`.
This is the bridge that transfers Mellin holomorphy to the continuation. -/
theorem abelContinuation_eq_mul_mellin (f : ℕ → ℂ) {σ : ℝ} {s : ℂ}
    (hs : σ < s.re)
    (hO : (fun n => abelPartialSum f n) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
    abelContinuation f s = s * mellin (abelSummatory f) (-s) := by
  have hf_top : abelSummatory f =O[atTop] fun t : ℝ => (t ^ (- -σ) : ℝ) := by
    simpa using isBigO_abelSummatory_atTop f hO
  have hs_top : (-s).re < -σ := by
    rw [Complex.neg_re, neg_lt_neg_iff]
    exact hs
  have hf_bot :
      abelSummatory f =O[𝓝[>] (0 : ℝ)] fun t : ℝ => (t ^ (-((-s).re - 1)) : ℝ) :=
    isBigO_abelSummatory_nhdsGT_zero f _
  have hs_bot : (-s).re - 1 < (-s).re := sub_lt_self _ one_pos
  have hconv : MellinConvergent (abelSummatory f) (-s) :=
    mellinConvergent_of_isBigO_rpow (locallyIntegrableOn_abelSummatory f)
      hf_top hs_top hf_bot hs_bot
  have hInt : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (-s - 1) • abelSummatory f t) (Set.Ioi (0 : ℝ)) :=
    hconv
  rw [abelContinuation, mellin,
    (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hInt.mono_set Set.Ioc_subset_Ioi_self)
      (hInt.mono_set (Set.Ioi_subset_Ioi zero_le_one))]
  have hzero : (∫ t : ℝ in Set.Ioc 0 1,
      (t : ℂ) ^ (-s - 1) • abelSummatory f t) = 0 := by
    refine setIntegral_eq_zero_of_ae_eq_zero ?_
    have hnull : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by
      rw [ae_iff]
      simp
    filter_upwards [hnull] with t ht1 htIoc
    have hlt : t < 1 := lt_of_le_of_ne htIoc.2 ht1
    rw [abelSummatory_eq_zero_of_lt_one f hlt, smul_zero]
  rw [hzero, zero_add]
  refine congrArg (s * ·) (setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_)
  rw [smul_eq_mul, mul_comm, show (-s - 1 : ℂ) = (-(s + 1)) by ring]

/-- Pointwise complex differentiability of the Abel continuation on `σ < s.re`
for arbitrary real `σ`. The Mellin transform provides holomorphy at `-s`;
precompose with negation and multiply by `s`. -/
theorem differentiableAt_abelContinuation (f : ℕ → ℂ) {σ : ℝ}
    {s : ℂ} (hs : σ < s.re)
    (hO : (fun n => abelPartialSum f n) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
    DifferentiableAt ℂ (abelContinuation f) s := by
  have hf_top : abelSummatory f =O[atTop] fun t : ℝ => (t ^ (- -σ) : ℝ) := by
    simpa using isBigO_abelSummatory_atTop f hO
  have hs_top : (-s).re < -σ := by
    rw [Complex.neg_re, neg_lt_neg_iff]
    exact hs
  have hf_bot :
      abelSummatory f =O[𝓝[>] (0 : ℝ)] fun t : ℝ => (t ^ (-((-s).re - 1)) : ℝ) :=
    isBigO_abelSummatory_nhdsGT_zero f _
  have hs_bot : (-s).re - 1 < (-s).re := sub_lt_self _ one_pos
  have hdiff : DifferentiableAt ℂ (mellin (abelSummatory f)) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (locallyIntegrableOn_abelSummatory f)
      hf_top hs_top hf_bot hs_bot
  have hcomp : DifferentiableAt ℂ (fun s => mellin (abelSummatory f) (-s)) s :=
    hdiff.comp s (by fun_prop)
  have hmul : DifferentiableAt ℂ (fun s => s * mellin (abelSummatory f) (-s)) s :=
    differentiableAt_id.mul hcomp
  have hev : (fun s => s * mellin (abelSummatory f) (-s)) =ᶠ[𝓝 s]
      abelContinuation f := by
    have hopen : IsOpen {s : ℂ | σ < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with s' hs'
    exact (abelContinuation_eq_mul_mellin f hs' hO).symm
  exact hmul.congr_of_eventuallyEq hev.symm

/-- The Abel continuation is analytic on the half-plane `σ < s.re`,
for arbitrary real `σ`. -/
theorem analyticOn_abelContinuation (f : ℕ → ℂ) {σ : ℝ}
    (hO : (fun n => abelPartialSum f n) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
    AnalyticOn ℂ (abelContinuation f) {s | σ < s.re} := by
  rw [Complex.analyticOn_iff_differentiableOn
    (isOpen_lt continuous_const Complex.continuous_re)]
  intro s hs
  exact (differentiableAt_abelContinuation f hs hO).differentiableWithinAt

/-- Agreement with `LSeries f s` at summable points. The hypothesis `0 ≤ σ`
is required only here, because the public `LSeries_eq_mul_integral` API
requires it; no claim is made about `LSeries f` itself where it is
nonsummable (there it is `0` by definition). -/
theorem abelContinuation_eq_LSeries (f : ℕ → ℂ) {σ : ℝ} (hσ : 0 ≤ σ) {s : ℂ}
    (hs : σ < s.re) (hS : LSeriesSummable f s)
    (hO : (fun n => abelPartialSum f n) =O[atTop] fun n => ((n : ℝ) ^ σ : ℝ)) :
    abelContinuation f s = LSeries f s := by
  simp only [abelContinuation, abelSummatory, abelPartialSum]
  exact (LSeries_eq_mul_integral f hσ hs hS hO).symm

/-- Ordered Dirichlet partial sums converge to the Abel continuation under
the growth hypothesis and `σ < s.re` alone, for arbitrary real `σ`: no
summability is assumed. The proof applies public Abel summation
(`tendsto_sum_mul_atTop_nhds_one_sub_integral₀`) to the zero-padded
coefficients `c n = if n = 0 then 0 else f n`, whose partial sums agree
with `abelPartialSum f`, with weight `x ↦ (x : ℂ) ^ (-s)`. -/
theorem tendsto_abelContinuation_Icc (f : ℕ → ℂ) {σ : ℝ} {s : ℂ}
    (hs : σ < s.re)
    (hO : (fun n => abelPartialSum f n) =O[atTop]
      fun n => ((n : ℝ) ^ σ : ℝ)) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, LSeries.term f s n) atTop
      (𝓝 (abelContinuation f s)) := by
  set c : ℕ → ℂ := fun n => if n = 0 then 0 else f n with hc_def
  have hc0 : c 0 = 0 := by simp [hc_def]
  have hc_eq : ∀ k : ℕ, k ≠ 0 → c k = f k := by
    intro k hk
    simp [hc_def, hk]
  have hsum_eq : ∀ n : ℕ, ∑ k ∈ Finset.Icc 0 n, c k = abelPartialSum f n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hc0, abelPartialSum]
    · conv_lhs => rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le n)]
      rw [Finset.sum_insert (by simp), hc0, zero_add]
      exact Finset.sum_congr rfl fun k hk => hc_eq k
        (zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1).ne'
  have hO' : (fun n => ∑ k ∈ Finset.Icc 0 n, c k) =O[atTop]
      fun n => ((n : ℝ) ^ σ : ℝ) := by
    simpa only [hsum_eq] using hO
  have hfloor : (fun t : ℝ => (((⌊t⌋₊ : ℕ) : ℝ) ^ σ : ℝ)) =O[atTop]
      fun t => (t ^ σ : ℝ) :=
    ((Asymptotics.isEquivalent_nat_floor (R := ℝ)).symm.rpow (r := σ)
      (Pi.le_def.mpr fun _ => Nat.cast_nonneg _)).symm.isBigO
  have hf_diff : ∀ t ∈ Set.Ici (1 : ℝ),
      DifferentiableAt ℝ (fun x : ℝ => (x : ℂ) ^ (-s)) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans_le ht)
    by_cases hs0 : s = 0
    · subst hs0
      have hfun : (fun x : ℝ => (x : ℂ) ^ (-(0 : ℂ))) = fun _ => 1 := by
        simp [neg_zero]
      rw [hfun]
      exact differentiableAt_const 1
    · exact differentiableAt_id.ofReal_cpow_const ht0 (neg_ne_zero.mpr hs0)
  have hf_int : LocallyIntegrableOn
      (deriv fun x : ℝ => (x : ℂ) ^ (-s)) (Set.Ici 1) := by
    by_cases hs0 : s = 0
    · subst hs0
      have hfun : (fun x : ℝ => (x : ℂ) ^ (-(0 : ℂ))) = fun _ => 1 := by
        simp [neg_zero]
      have hderiv : deriv (fun x : ℝ => (x : ℂ) ^ (-(0 : ℂ))) = fun _ => 0 := by
        rw [hfun, deriv_const']
      rw [hderiv]
      exact locallyIntegrableOn_zero
    · have hRHS : ContinuousOn (fun x : ℝ => -s * (x : ℂ) ^ (-s - 1))
          (Set.Ici 1) := by
        refine ContinuousOn.mul continuousOn_const fun x hx => ?_
        exact (Complex.continuousAt_ofReal_cpow_const _ _
          (Or.inr (ne_of_gt (zero_lt_one.trans_le hx)))).continuousWithinAt
      have heq : Set.EqOn (deriv fun x : ℝ => (x : ℂ) ^ (-s))
          (fun x : ℝ => -s * (x : ℂ) ^ (-s - 1)) (Set.Ici 1) := by
        intro x hx
        exact Complex.deriv_ofReal_cpow_const
          (ne_of_gt (zero_lt_one.trans_le hx)) (neg_ne_zero.mpr hs0)
      exact (hRHS.congr heq).locallyIntegrableOn measurableSet_Ici
  have hlim : Tendsto
      (fun n : ℕ => ((n : ℝ) : ℂ) ^ (-s) * ∑ k ∈ Finset.Icc 0 n, c k)
      atTop (𝓝 0) := by
    have hlim0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(s.re - σ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    refine (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-s.re) _ _
      ?_ hO' ?_).trans_tendsto hlim0
    · exact isBigO_norm_left.mp
        (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop
    · linarith
  have hexp : (-(s + 1)).re + σ < -1 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    linarith
  have hg_dom : (fun t : ℝ => deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop]
      fun t => (t : ℝ) ^ ((-(s + 1)).re + σ) := by
    refine IsBigO.mul_atTop_rpow_of_isBigO_rpow (-(s + 1)).re σ _
      ?_ ?_ le_rfl
    · simpa [-neg_add_rev, neg_add'] using!
        isBigO_deriv_ofReal_cpow_const_atTop _
    · exact (hO'.comp_tendsto tendsto_nat_floor_atTop).trans hfloor
  have habel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (c := c)
    (f := fun x : ℝ => (x : ℂ) ^ (-s)) (l := 0) hc0 hf_diff hf_int hlim
    hg_dom (integrableAtFilter_rpow_atTop_iff.mpr hexp)
  have hterm : ∀ N : ℕ, (∑ k ∈ Finset.Icc 0 N, ((k : ℝ) : ℂ) ^ (-s) * c k) =
      ∑ n ∈ Finset.Icc 1 N, LSeries.term f s n := by
    intro N
    rcases eq_or_ne N 0 with rfl | hN
    · rw [Finset.Icc_self, Finset.sum_singleton, hc0, mul_zero,
        show Finset.Icc 1 0 = (∅ : Finset ℕ) by simp, Finset.sum_empty]
    · rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N),
        Finset.sum_insert (by simp), hc0, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk0 : k ≠ 0 :=
        (zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1).ne'
      rw [hc_eq k hk0, LSeries.term_of_ne_zero hk0]
      simp only [div_eq_mul_inv, Complex.ofReal_natCast, Complex.cpow_neg]
      exact mul_comm _ _
  have hderiv_eq : ∀ t ∈ Set.Ioi (1 : ℝ),
      deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
      -(s * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) * (t : ℂ) ^ (-(s + 1)))) := by
    intro t ht
    by_cases hs0 : s = 0
    · subst hs0
      have hfun : (fun x : ℝ => (x : ℂ) ^ (-(0 : ℂ))) = fun _ => 1 := by
        simp [neg_zero]
      rw [hfun]
      simp
    · rw [Complex.deriv_ofReal_cpow_const (ne_of_gt (zero_lt_one.trans ht))
        (neg_ne_zero.mpr hs0), show (-s - 1 : ℂ) = (-(s + 1)) by ring]
      ring
  have hcongr : ∀ t ∈ Set.Ioi (1 : ℝ),
      -(deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t *
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      s * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) * (t : ℂ) ^ (-(s + 1))) := by
    intro t ht
    rw [hderiv_eq t ht, neg_neg]
  have hint : (0 : ℂ) - ∫ t : ℝ in Set.Ioi 1,
      deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
      abelContinuation f s := by
    rw [zero_sub, ← integral_neg,
      setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
      abelContinuation]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    congr 1
    exact hsum_eq _
  rw [← hint]
  exact habel.congr fun N => hterm N
