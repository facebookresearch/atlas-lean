/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry10ZetaSide
import Mathlib.Analysis.Meromorphic.Complex
import MathlibExt.NumberTheory.LSeries.RiemannZeta

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 10

Bernoulli-Gamma-sine expression equals (1-nʳ⁺¹)ζ(-r) meromorphically.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry10Zeta4

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7BernoulliStar (z : ℂ) : ℂ :=
  2 * Complex.Gamma (z + 1) * riemannZeta z /
    Complex.cpow (2 * (Real.pi : ℂ)) z

def chapter7Entry10BernoulliSide (n : ℕ) (r : ℂ) : ℂ :=
  (Complex.cpow (n : ℂ) (r + 1) - 1) *
    Complex.sin ((Real.pi : ℂ) * r / 2) * chapter7BernoulliStar (r + 1) /
      (r + 1)

private theorem diff_ncpow_aux (n : ℕ) (hn : 0 < n) :
    Differentiable ℂ (fun r : ℂ => Complex.cpow (n : ℂ) (r + 1)) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h1 : Differentiable ℂ (fun r : ℂ => r + 1) := differentiable_id.add_const 1
  exact Differentiable.const_cpow h1 (Or.inl hn0)

private theorem mero_ncpow_aux (n : ℕ) (hn : 0 < n) :
    MeromorphicOn (fun r : ℂ => Complex.cpow (n : ℂ) (r + 1)) Set.univ := by
  have hdiff := diff_ncpow_aux n hn
  have hanal : AnalyticOnNhd ℂ (fun r : ℂ => Complex.cpow (n : ℂ) (r + 1)) Set.univ :=
    fun x _ => hdiff.analyticAt x
  exact AnalyticOnNhd.meromorphicOn hanal

private theorem diff_sin_piece_aux :
    Differentiable ℂ (fun r : ℂ => Complex.sin ((Real.pi : ℂ) * r / 2)) := by
  have hlin : Differentiable ℂ (fun r : ℂ => (Real.pi : ℂ) * r / 2) := by
    exact (differentiable_const ((Real.pi : ℂ))).mul differentiable_id |>.div_const 2
  exact Complex.differentiable_sin.comp hlin

private theorem diff_add1_aux : Differentiable ℂ (fun r : ℂ => r + 1) :=
  differentiable_id.add_const 1

private theorem diff_twopi_pow_aux :
    Differentiable ℂ (fun r : ℂ => Complex.cpow (2 * (Real.pi : ℂ)) (r + 1)) := by
  have hbase : (2 * (Real.pi : ℂ) : ℂ) ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [hpi]
  exact Differentiable.const_cpow diff_add1_aux (Or.inl hbase)

private theorem mero_bstar_comp_aux :
    MeromorphicOn (fun r : ℂ => chapter7BernoulliStar (r + 1)) Set.univ := by
  unfold chapter7BernoulliStar
  have hadd1 : AnalyticOnNhd ℂ (fun r : ℂ => r + 1) Set.univ :=
    fun x _ => diff_add1_aux.analyticAt x
  have hGamma : MeromorphicOn (fun r : ℂ => Complex.Gamma ((r + 1) + 1)) Set.univ := by
    have hinner_diff : Differentiable ℂ (fun r : ℂ => (r + 1) + 1) :=
      diff_add1_aux.add_const 1
    have hinner : AnalyticOnNhd ℂ (fun r : ℂ => (r + 1) + 1) Set.univ :=
      fun x _ => hinner_diff.analyticAt x
    exact MeromorphicOn.Gamma.comp_analyticOnNhd hinner (Set.mapsTo_univ _ _)
  have hzeta : MeromorphicOn (fun r : ℂ => riemannZeta (r + 1)) Set.univ :=
    meromorphicOn_riemannZeta.comp_analyticOnNhd hadd1 (Set.mapsTo_univ _ _)
  have hpow : MeromorphicOn (fun r : ℂ => Complex.cpow (2 * (Real.pi : ℂ)) (r + 1)) Set.univ := by
    have hanal : AnalyticOnNhd ℂ (fun r : ℂ => Complex.cpow (2 * (Real.pi : ℂ)) (r + 1)) Set.univ :=
      fun x _ => diff_twopi_pow_aux.analyticAt x
    exact AnalyticOnNhd.meromorphicOn hanal
  have hconst : MeromorphicOn (fun _ : ℂ => (2 : ℂ)) Set.univ :=
    analyticOnNhd_const.meromorphicOn
  have hnum : MeromorphicOn
      (fun r : ℂ => 2 * Complex.Gamma ((r + 1) + 1) * riemannZeta (r + 1)) Set.univ :=
    (hconst.mul hGamma).mul hzeta
  exact hnum.div hpow

private theorem mero_bernoulli_side_aux (n : ℕ) (hn : 0 < n) :
    MeromorphicOn (chapter7Entry10BernoulliSide n) Set.univ := by
  unfold chapter7Entry10BernoulliSide
  have hpow := mero_ncpow_aux n hn
  have hsub : MeromorphicOn (fun r : ℂ => Complex.cpow (n : ℂ) (r + 1) - 1) Set.univ :=
    hpow.sub analyticOnNhd_const.meromorphicOn
  have hsin : MeromorphicOn (fun r : ℂ => Complex.sin ((Real.pi : ℂ) * r / 2)) Set.univ :=
    AnalyticOnNhd.meromorphicOn (fun x _ => diff_sin_piece_aux.analyticAt x)
  have hB := mero_bstar_comp_aux
  have hden : MeromorphicOn (fun r : ℂ => (r + 1 : ℂ)) Set.univ :=
    AnalyticOnNhd.meromorphicOn (fun x _ => diff_add1_aux.analyticAt x)
  exact ((hsub.mul hsin).mul hB).div hden

private theorem pointwise_eq_aux (n : ℕ) (_hn : 0 < n) (r : ℂ) (hr0 : r ≠ 0)
    (hr : ∀ k : ℕ, r ≠ -1 - (k : ℂ)) :
    chapter7Entry10ZetaSide n r = chapter7Entry10BernoulliSide n r := by
  unfold chapter7Entry10ZetaSide chapter7Entry10BernoulliSide chapter7BernoulliStar
  have hs1 : r + 1 ≠ 1 := by
    intro h
    apply hr0
    have : r = (r + 1) - 1 := by ring
    rw [h] at this
    simpa using this
  have hsn : ∀ k : ℕ, r + 1 ≠ -(k : ℂ) := by
    intro k hk
    apply hr k
    have : r = (r + 1) - 1 := by ring
    rw [hk] at this
    ring_nf at this ⊢
    exact this
  have hfun := riemannZeta_one_sub (s := r + 1) hsn hs1
  have h1sub : (1 : ℂ) - (r + 1) = -r := by ring
  rw [h1sub] at hfun
  have hcos : Complex.cos ((Real.pi : ℂ) * (r + 1) / 2)
      = -Complex.sin ((Real.pi : ℂ) * r / 2) := by
    have : (Real.pi : ℂ) * (r + 1) / 2
        = (Real.pi : ℂ) * r / 2 + (Real.pi : ℂ) / 2 := by ring
    rw [this, Complex.cos_add]
    have hcos_half : Complex.cos ((Real.pi : ℂ) / 2) = 0 := by
      have h : (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [h, ← Complex.ofReal_cos, Real.cos_pi_div_two]
      simp
    have hsin_half : Complex.sin ((Real.pi : ℂ) / 2) = 1 := by
      have h : (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [h, ← Complex.ofReal_sin, Real.sin_pi_div_two]
      simp
    rw [hcos_half, hsin_half]
    ring
  rw [hcos] at hfun
  have hr1 : r + 1 ≠ 0 := by
    intro h
    apply hr 0
    linear_combination h
  have hGamma : Complex.Gamma ((r + 1) + 1) = (r + 1) * Complex.Gamma (r + 1) :=
    Complex.Gamma_add_one _ hr1
  rw [hGamma]
  rw [hfun]
  have hcpow_eq : ∀ x y : ℂ, Complex.cpow x y = x ^ y := fun x y => rfl
  simp only [hcpow_eq, Complex.cpow_neg]
  field_simp
  ring

private def chapter7BadSet : Set ℂ := {0} ∪ Set.range (fun k : ℕ => (-1 - (k : ℂ)))

private theorem bad_spacing (e₁ e₂ : ℂ) (h1 : e₁ ∈ chapter7BadSet) (h2 : e₂ ∈ chapter7BadSet)
    (hne : e₁ ≠ e₂) : 1 ≤ ‖e₁ - e₂‖ := by
  have hre_le : |(e₁ - e₂).re| ≤ ‖e₁ - e₂‖ := Complex.abs_re_le_norm _
  simp only [chapter7BadSet, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_range] at h1 h2
  rcases h1 with rfl | ⟨k₁, rfl⟩ <;> rcases h2 with rfl | ⟨k₂, rfl⟩
  · exact absurd rfl hne
  · have hrediff : ((0 : ℂ) - (-1 - (k₂ : ℂ))).re = 1 + (k₂ : ℝ) := by
      simp [Complex.natCast_re]
      ring
    rw [hrediff] at hre_le
    have hpos : (0 : ℝ) ≤ (k₂ : ℝ) := Nat.cast_nonneg _
    have habs : |(1 : ℝ) + (k₂ : ℝ)| = 1 + (k₂ : ℝ) := by
      rw [abs_of_nonneg (by linarith)]
    rw [habs] at hre_le
    linarith
  · have hrediff : ((-1 - (k₁ : ℂ)) - (0 : ℂ)).re = -1 - (k₁ : ℝ) := by
      simp [Complex.natCast_re]
    rw [hrediff] at hre_le
    have hpos : (0 : ℝ) ≤ (k₁ : ℝ) := Nat.cast_nonneg _
    have hthis : |-1 - (k₁ : ℝ)| = 1 + (k₁ : ℝ) := by
      rw [abs_of_nonpos (by linarith : (-1 : ℝ) - (k₁ : ℝ) ≤ 0)]
      ring
    rw [hthis] at hre_le
    linarith
  · by_cases hk : k₁ = k₂
    · subst hk
      exact absurd rfl hne
    · have hrediff : ((-1 - (k₁ : ℂ)) - (-1 - (k₂ : ℂ))).re
          = (k₂ : ℝ) - (k₁ : ℝ) := by
        simp [Complex.natCast_re]
      rw [hrediff] at hre_le
      have hne' : (k₁ : ℝ) ≠ (k₂ : ℝ) := by exact_mod_cast hk
      have h1le : (1 : ℝ) ≤ |(k₂ : ℝ) - (k₁ : ℝ)| := by
        have h : (k₁ : ℝ) < (k₂ : ℝ) ∨ (k₂ : ℝ) < (k₁ : ℝ) := lt_or_gt_of_ne hne'
        rcases h with hlt | hgt
        · have hle : (k₁ : ℝ) + 1 ≤ (k₂ : ℝ) := by
            have hnat : k₁ + 1 ≤ k₂ := Nat.succ_le_of_lt (Nat.cast_lt.mp hlt)
            exact_mod_cast hnat
          rw [abs_of_nonneg (by linarith)]
          linarith
        · have hle : (k₂ : ℝ) + 1 ≤ (k₁ : ℝ) := by
            have hnat : k₂ + 1 ≤ k₁ := Nat.succ_le_of_lt (Nat.cast_lt.mp hgt)
            exact_mod_cast hnat
          rw [abs_of_nonpos (by linarith)]
          linarith
      linarith

private theorem bad_unique_near (x e₁ e₂ : ℂ) (h1 : e₁ ∈ chapter7BadSet)
    (h2 : e₂ ∈ chapter7BadSet) (hm1 : ‖e₁ - x‖ < 1 / 2)
    (hm2 : ‖e₂ - x‖ < 1 / 2) : e₁ = e₂ := by
  by_contra hne
  have hsp := bad_spacing e₁ e₂ h1 h2 hne
  have htri : ‖e₁ - e₂‖ < 1 := by
    calc ‖e₁ - e₂‖ = ‖(e₁ - x) + (x - e₂)‖ := by congr 1; abel
    _ ≤ ‖e₁ - x‖ + ‖x - e₂‖ := norm_add_le _ _
    _ < 1 / 2 + 1 / 2 := by
        have h2' : ‖x - e₂‖ = ‖e₂ - x‖ := norm_sub_rev _ _
        linarith [hm1, hm2, h2']
    _ = 1 := by ring
  linarith

private theorem bad_compl_mem_codiscrete : chapter7BadSetᶜ ∈ Filter.codiscrete ℂ := by
  rw [mem_codiscrete]
  simp only [compl_compl]
  intro x
  rw [Filter.disjoint_principal_right]
  rw [mem_nhdsWithin]
  by_cases hex : ∃ e ∈ chapter7BadSet, e ≠ x ∧ ‖e - x‖ < 1 / 2
  · obtain ⟨e₀, he₀mem, he₀ne, he₀close⟩ := hex
    have hpos0 : 0 < ‖e₀ - x‖ := by
      rw [norm_pos_iff]
      intro h
      apply he₀ne
      have : e₀ = x := by linear_combination h
      exact this
    have heps : 0 < min (1 / 2 : ℝ) (‖e₀ - x‖ / 2) :=
      lt_min (by norm_num) (by linarith)
    refine ⟨Metric.ball x (min (1 / 2) (‖e₀ - x‖ / 2)), Metric.isOpen_ball,
      Metric.mem_ball_self heps, ?_⟩
    intro y hy
    have hyball : y ∈ Metric.ball x (min (1 / 2) (‖e₀ - x‖ / 2)) := hy.1
    rw [Metric.mem_ball, dist_eq_norm] at hyball
    change y ∈ chapter7BadSetᶜ
    rw [Set.mem_compl_iff]
    intro hymem
    have hydist' : ‖y - x‖ < 1 / 2 := lt_of_lt_of_le hyball (min_le_left _ _)
    have hye : y = e₀ := bad_unique_near x y e₀ hymem he₀mem hydist' he₀close
    rw [hye] at hyball
    have hle : min (1 / 2 : ℝ) (‖e₀ - x‖ / 2) ≤ ‖e₀ - x‖ / 2 :=
      min_le_right _ _
    linarith
  · refine ⟨Metric.ball x (1 / 2), Metric.isOpen_ball,
      Metric.mem_ball_self (by norm_num), ?_⟩
    intro y hy
    have hyball : y ∈ Metric.ball x (1 / 2) := hy.1
    have hynex : y ∈ ({x}ᶜ : Set ℂ) := hy.2
    rw [Metric.mem_ball, dist_eq_norm] at hyball
    rw [Set.mem_compl_iff] at hynex ⊢
    simp only [Set.mem_singleton_iff] at hynex
    intro hymem
    exact hex ⟨y, hymem, hynex, hyball⟩

private theorem eventual_eq_aux (n : ℕ) (hn : 0 < n) :
    chapter7Entry10ZetaSide n =ᶠ[codiscrete ℂ]
      chapter7Entry10BernoulliSide n := by
  apply Filter.mem_of_superset bad_compl_mem_codiscrete
  intro r hr
  simp only [chapter7BadSet, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_range, Set.mem_compl_iff] at hr
  push Not at hr
  obtain ⟨hr0, hrneg⟩ := hr
  exact pointwise_eq_aux n hn r hr0 (fun k => (hrneg k).symm)

/-- **The Entry 10 zeta factor in Bernoulli form.** Let $n$ be a positive integer, and for
$z \in \mathbb{C}$ put $B^*(z) = 2\,\Gamma(z + 1)\,\zeta(z) / (2\pi)^z$. Then the functions
$Z(r) = (1 - n^{r+1})\,\zeta(-r)$ and
$B(r) = (n^{r+1} - 1) \sin(\pi r / 2)\, B^*(r + 1) / (r + 1)$ are meromorphic on $\mathbb{C}$,
and $Z(r) = B(r)$ for all $r \in \mathbb{C}$ outside a closed discrete subset of $\mathbb{C}$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7, Entry 10.
Proves `Wanted` entry `ramanujan_part1_ch7_entry10_zeta4`.
-/
theorem ramanujan_part1_ch7_entry10_zeta4 (n : ℕ) (hn : 0 < n) :
    MeromorphicOn (chapter7Entry10ZetaSide n) Set.univ ∧
      MeromorphicOn (chapter7Entry10BernoulliSide n) Set.univ ∧
      chapter7Entry10ZetaSide n =ᶠ[codiscrete ℂ]
        chapter7Entry10BernoulliSide n := by
  exact ⟨meromorphicOn_chapter7Entry10ZetaSide n hn, mero_bernoulli_side_aux n hn,
    eventual_eq_aux n hn⟩

end

end Entry10Zeta4

end MathlibExt.Analysis.Ramanujan.Part1Ch7
