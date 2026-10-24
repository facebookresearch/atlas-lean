/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.RealRooted
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Algebra.Polynomial.RuleOfSigns

/-!
# Largest roots and interlacing families

This file develops the univariate root-ordering facts used by the interlacing-family step in the
Marcus--Spielman--Srivastava argument.
-/

@[expose] public section

open scoped ComplexOrder NNReal

namespace Polynomial

private lemma ksMaxRealRoot_sub_lt_of_coeff_sub_lt
    {f g : Polynomial ℂ} (hfmonic : f.Monic) (hgmonic : g.Monic)
    (hfrooted : f.IsRealRooted) (hdegree : 0 < f.natDegree)
    (hdegreeEq : g.natDegree = f.natDegree) {ρ B ε : ℝ} (hρ : 0 < ρ)
    (hrootsBound : ∀ z ∈ f.roots, max ‖z‖ 1 ≤ B)
    (hcoeff : ∀ i : ℕ, ‖g.coeff i - f.coeff i‖ < ρ)
    (hradius :
      ((f.natDegree + 1 : ℝ) * ρ) ^ (f.natDegree : ℝ)⁻¹ * B < ε) :
    f.maxRealRoot - g.maxRealRoot < ε := by
  have hmaxMem : (f.maxRealRoot : ℂ) ∈ f.roots :=
    coe_maxRealRoot_mem_roots hfrooted hdegree
  have hmaxEval : f.eval (f.maxRealRoot : ℂ) = 0 :=
    Polynomial.IsRoot.def.mp ((Polynomial.mem_roots hfmonic.ne_zero).mp hmaxMem)
  obtain ⟨b, hb, hclose⟩ :=
    exists_roots_norm_sub_lt_of_norm_coeff_sub_lt hρ hmaxEval hfmonic hgmonic
      hdegreeEq hcoeff (IsAlgClosed.splits g)
  have hnonneg :
      0 ≤ ((f.natDegree + 1 : ℝ) * ρ) ^ (f.natDegree : ℝ)⁻¹ :=
    Real.rpow_nonneg (by positivity) _
  have hdist : ‖(f.maxRealRoot : ℂ) - b‖ < ε := by
    calc
      ‖(f.maxRealRoot : ℂ) - b‖ <
          ((f.natDegree + 1 : ℝ) * ρ) ^ (f.natDegree : ℝ)⁻¹ *
            max ‖(f.maxRealRoot : ℂ)‖ 1 := hclose
      _ ≤ ((f.natDegree + 1 : ℝ) * ρ) ^ (f.natDegree : ℝ)⁻¹ * B :=
        mul_le_mul_of_nonneg_left (hrootsBound _ hmaxMem) hnonneg
      _ < ε := hradius
  have hre : |f.maxRealRoot - b.re| < ε := by
    apply lt_of_le_of_lt _ hdist
    simpa using Complex.abs_re_le_norm ((f.maxRealRoot : ℂ) - b)
  have hbmax : b.re ≤ g.maxRealRoot := root_re_le_maxRealRoot hb
  linarith [abs_lt.mp hre]

private lemma ksAbs_maxRealRoot_sub_lt_of_coeff_sub_lt
    {f g : Polynomial ℂ} (hfmonic : f.Monic) (hgmonic : g.Monic)
    (hfrooted : f.IsRealRooted) (hgrooted : g.IsRealRooted)
    (hdegree : 0 < f.natDegree) (hdegreeEq : g.natDegree = f.natDegree)
    {ρ B ε : ℝ} (hρ : 0 < ρ)
    (hfrootsBound : ∀ z ∈ f.roots, max ‖z‖ 1 ≤ B)
    (hgrootsBound : ∀ z ∈ g.roots, max ‖z‖ 1 ≤ B)
    (hcoeff : ∀ i : ℕ, ‖g.coeff i - f.coeff i‖ < ρ)
    (hradius :
      ((f.natDegree + 1 : ℝ) * ρ) ^ (f.natDegree : ℝ)⁻¹ * B < ε) :
    |g.maxRealRoot - f.maxRealRoot| < ε := by
  rw [abs_lt]
  constructor
  · have hforward := ksMaxRealRoot_sub_lt_of_coeff_sub_lt hfmonic hgmonic hfrooted
      hdegree hdegreeEq hρ hfrootsBound hcoeff hradius
    linarith
  · exact ksMaxRealRoot_sub_lt_of_coeff_sub_lt hgmonic hfmonic hgrooted
      (hdegreeEq ▸ hdegree) hdegreeEq.symm hρ hgrootsBound
      (fun i ↦ by simpa [norm_sub_rev] using hcoeff i) (by simpa [hdegreeEq] using hradius)

private lemma ksExists_rootRadius_lt {n : ℕ} (hn : 0 < n) {B ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ((n + 1 : ℝ) * ρ) ^ (n : ℝ)⁻¹ * B < ε := by
  let F : ℝ → ℝ := fun ρ ↦ ((n + 1 : ℝ) * ρ) ^ (n : ℝ)⁻¹ * B
  have hexponent : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne')
  have hcont : ContinuousAt F 0 := by
    dsimp only [F]
    exact ((continuousAt_const.mul continuousAt_id).rpow_const (Or.inr (by positivity))).mul
      continuousAt_const
  have hzero : F 0 = 0 := by
    simp [F, Real.zero_rpow hexponent]
  obtain ⟨δ, hδ, hnear⟩ := (Metric.continuousAt_iff.mp hcont) ε hε
  refine ⟨δ / 2, by positivity, ?_⟩
  have hdist : dist (δ / 2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  have := hnear hdist
  rw [hzero, Real.dist_eq, sub_zero] at this
  exact lt_of_le_of_lt (le_abs_self (F (δ / 2))) this

private lemma ksContinuous_maxRealRoot
    {P : ℝ → Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hmonic : ∀ t, (P t).Monic) (hrooted : ∀ t, (P t).IsRealRooted)
    (hdegree : ∀ t, (P t).natDegree = n) {B : ℝ}
    (hrootsBound : ∀ t z, z ∈ (P t).roots → max ‖z‖ 1 ≤ B)
    (hcoeffContinuous : ∀ i : ℕ, Continuous fun t ↦ (P t).coeff i) :
    Continuous fun t ↦ (P t).maxRealRoot := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨ρ, hρ, hradius⟩ := ksExists_rootRadius_lt hn (B := B) hε
  let C : ℝ → ℝ := fun t ↦
    ∑ i ∈ Finset.range (n + 1), ‖(P t).coeff i - (P t₀).coeff i‖
  have hCContinuous : Continuous C := by
    dsimp only [C]
    fun_prop
  obtain ⟨δ, hδ, hnear⟩ :=
    (Metric.continuousAt_iff.mp hCContinuous.continuousAt) ρ hρ
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have hClt : C t < ρ := by
    have h := hnear ht
    exact (abs_lt.mp (by simpa [C, Real.dist_eq] using h)).2
  rw [Real.dist_eq]
  apply ksAbs_maxRealRoot_sub_lt_of_coeff_sub_lt (hmonic t₀) (hmonic t)
    (hrooted t₀) (hrooted t) (hdegree t₀ ▸ hn)
    ((hdegree t).trans (hdegree t₀).symm) hρ (hrootsBound t₀) (hrootsBound t)
  · intro i
    by_cases hi : i < n + 1
    · calc
        ‖(P t).coeff i - (P t₀).coeff i‖ ≤ C t := by
          dsimp only [C]
          exact Finset.single_le_sum
            (f := fun j ↦ ‖(P t).coeff j - (P t₀).coeff j‖)
            (s := Finset.range (n + 1)) (fun j hj ↦ norm_nonneg _)
            (Finset.mem_range.mpr hi)
        _ < ρ := hClt
    · have hni : n < i := by omega
      rw [coeff_eq_zero_of_natDegree_lt (hdegree t ▸ hni),
        coeff_eq_zero_of_natDegree_lt (hdegree t₀ ▸ hni), sub_self, norm_zero]
      exact hρ
  · simpa [hdegree t₀] using hradius

private lemma ksAffine_isMonicOfDegree {p q : Polynomial ℂ} {n : ℕ}
    (hp : p.IsMonicOfDegree n) (hq : q.IsMonicOfDegree n) (t : ℝ) :
    ((1 - (t : ℂ)) • p + (t : ℂ) • q).IsMonicOfDegree n := by
  rw [isMonicOfDegree_iff]
  constructor
  · have hple : ((1 - (t : ℂ)) • p).natDegree ≤ n :=
      (natDegree_smul_le _ _).trans hp.natDegree_eq.le
    have hqle : ((t : ℂ) • q).natDegree ≤ n :=
      (natDegree_smul_le _ _).trans hq.natDegree_eq.le
    exact (natDegree_add_le _ _).trans (max_le hple hqle)
  · have hpcoeff : p.coeff n = 1 := by
      rw [← hp.natDegree_eq]
      exact hp.monic.coeff_natDegree
    have hqcoeff : q.coeff n = 1 := by
      rw [← hq.natDegree_eq]
      exact hq.monic.coeff_natDegree
    rw [coeff_add, coeff_smul, coeff_smul, hpcoeff, hqcoeff]
    simp

private lemma ksAffine_cauchyBound_le {p q : Polynomial ℂ} {n : ℕ}
    (hp : p.IsMonicOfDegree n) (hq : q.IsMonicOfDegree n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((((1 - (t : ℂ)) • p + (t : ℂ) • q).cauchyBound : ℝ) ≤
      (∑ i ∈ Finset.range n, (‖p.coeff i‖ + ‖q.coeff i‖)) + 1) := by
  have hr := ksAffine_isMonicOfDegree hp hq t
  rw [Polynomial.cauchyBound, hr.natDegree_eq, hr.leadingCoeff_eq]
  simp only [nnnorm_one, div_one, NNReal.coe_add, NNReal.coe_one]
  rw [add_le_add_iff_right]
  let S : ℝ≥0 := ∑ i ∈ Finset.range n, (‖p.coeff i‖₊ + ‖q.coeff i‖₊)
  have htNorm : ‖(t : ℂ)‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    simpa [abs_of_nonneg ht.1] using ht.2
  have hOneSubNorm : ‖(1 - (t : ℂ))‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm, NNReal.coe_one]
    rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by norm_num]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    exact sub_le_self 1 ht.1
  have hsup : (Finset.range n).sup
      (fun i ↦ ‖((1 - (t : ℂ)) • p + (t : ℂ) • q).coeff i‖₊) ≤ S := by
    apply Finset.sup_le
    intro i hi
    simp only [coeff_add, coeff_smul]
    calc
      ‖(1 - (t : ℂ)) • p.coeff i + (t : ℂ) • q.coeff i‖₊ ≤
          ‖(1 - (t : ℂ)) • p.coeff i‖₊ + ‖(t : ℂ) • q.coeff i‖₊ :=
        nnnorm_add_le _ _
      _ = ‖(1 - (t : ℂ))‖₊ * ‖p.coeff i‖₊ + ‖(t : ℂ)‖₊ * ‖q.coeff i‖₊ := by
        simp
      _ ≤ ‖p.coeff i‖₊ + ‖q.coeff i‖₊ := by
        apply add_le_add
        · exact mul_le_of_le_one_left (by positivity) hOneSubNorm
        · exact mul_le_of_le_one_left (by positivity) htNorm
      _ ≤ S := by
        dsimp only [S]
        exact Finset.single_le_sum
          (f := fun j ↦ ‖p.coeff j‖₊ + ‖q.coeff j‖₊)
          (s := Finset.range n) (fun j hj ↦ by positivity) hi
  have hsupReal := NNReal.coe_le_coe.mpr hsup
  simpa [S, NNReal.coe_sum] using hsupReal

private lemma ksAffine_roots_bound {p q : Polynomial ℂ} {n : ℕ}
    (hp : p.IsMonicOfDegree n) (hq : q.IsMonicOfDegree n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {z : ℂ}
    (hz : z ∈ ((1 - (t : ℂ)) • p + (t : ℂ) • q).roots) :
    max ‖z‖ 1 ≤ (∑ i ∈ Finset.range n, (‖p.coeff i‖ + ‖q.coeff i‖)) + 1 := by
  let r : Polynomial ℂ := (1 - (t : ℂ)) • p + (t : ℂ) • q
  have hr : r.IsMonicOfDegree n := ksAffine_isMonicOfDegree hp hq t
  have hzroot : r.IsRoot z := (Polynomial.mem_roots hr.monic.ne_zero).mp hz
  have hnormNN := hzroot.norm_lt_cauchyBound hr.monic.ne_zero
  have hnorm : ‖z‖ < (r.cauchyBound : ℝ) := by exact_mod_cast hnormNN
  have hbound : (r.cauchyBound : ℝ) ≤
      (∑ i ∈ Finset.range n, (‖p.coeff i‖ + ‖q.coeff i‖)) + 1 := by
    exact ksAffine_cauchyBound_le hp hq ht
  apply max_le
  · exact (hnorm.trans_le hbound).le
  · have hsum : 0 ≤ ∑ i ∈ Finset.range n, (‖p.coeff i‖ + ‖q.coeff i‖) := by
      exact Finset.sum_nonneg fun i hi ↦ add_nonneg (norm_nonneg _) (norm_nonneg _)
    linarith

private lemma ksMaxRealRoot_lt_of_segment
    {p q : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hp : p.IsMonicOfDegree n) (hq : q.IsMonicOfDegree n)
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (t : ℂ)) • p + (t : ℂ) • q).IsRealRooted)
    {x : ℝ} (hpmax : p.maxRealRoot < x) (hqeval : 0 < (q.eval (x : ℂ)).re) :
    q.maxRealRoot < x := by
  let clip : ℝ → ℝ := fun t ↦ max 0 (min 1 t)
  have hclipContinuous : Continuous clip := by
    dsimp only [clip]
    fun_prop
  have hclipMem : ∀ t, clip t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  let P : ℝ → Polynomial ℂ := fun t ↦
    (1 - (clip t : ℂ)) • p + (clip t : ℂ) • q
  have hPdegree : ∀ t, (P t).natDegree = n := by
    intro t
    exact (ksAffine_isMonicOfDegree hp hq (clip t)).natDegree_eq
  have hPmonic : ∀ t, (P t).Monic := by
    intro t
    exact (ksAffine_isMonicOfDegree hp hq (clip t)).monic
  have hProoted : ∀ t, (P t).IsRealRooted := by
    intro t
    exact hsegment (clip t) (hclipMem t)
  have hPbound : ∀ t z, z ∈ (P t).roots →
      max ‖z‖ 1 ≤ (∑ i ∈ Finset.range n, (‖p.coeff i‖ + ‖q.coeff i‖)) + 1 := by
    intro t z hz
    exact ksAffine_roots_bound hp hq (hclipMem t) hz
  have hPcoeffContinuous : ∀ i : ℕ, Continuous fun t ↦ (P t).coeff i := by
    intro i
    dsimp only [P]
    simp only [coeff_add, coeff_smul]
    fun_prop
  have hmaxContinuous : Continuous fun t ↦ (P t).maxRealRoot :=
    ksContinuous_maxRealRoot hn hPmonic hProoted hPdegree hPbound hPcoeffContinuous
  have hPzero : P 0 = p := by simp [P, clip]
  have hPone : P 1 = q := by simp [P, clip]
  have hprooted : p.IsRealRooted := by
    simpa using hsegment 0 (by simp)
  have hpeval : 0 < (p.eval (x : ℂ)).re :=
    eval_re_pos_of_maxRealRoot_lt hp.monic hprooted hpmax
  by_contra hqmax
  have hxbetween : x ∈ Set.Icc ((P 0).maxRealRoot) ((P 1).maxRealRoot) := by
    rw [hPzero, hPone]
    exact ⟨hpmax.le, le_of_not_gt hqmax⟩
  obtain ⟨t, ht, htroot⟩ :=
    intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hmaxContinuous.continuousOn
      hxbetween
  have hrootMem : (x : ℂ) ∈ (P t).roots := by
    rw [← htroot]
    exact coe_maxRealRoot_mem_roots (hProoted t) (hPdegree t ▸ hn)
  have hevalZero : (P t).eval (x : ℂ) = 0 :=
    Polynomial.IsRoot.def.mp ((Polynomial.mem_roots (hPmonic t).ne_zero).mp hrootMem)
  have hclip := hclipMem t
  have hevalPos : 0 < ((P t).eval (x : ℂ)).re := by
    rw [show P t = (1 - (clip t : ℂ)) • p + (clip t : ℂ) • q by rfl]
    rw [eval_add, eval_smul, eval_smul]
    have hre :
        ((1 - (clip t : ℂ)) • p.eval (x : ℂ) +
          (clip t : ℂ) • q.eval (x : ℂ)).re =
        (1 - clip t) * (p.eval (x : ℂ)).re +
          clip t * (q.eval (x : ℂ)).re := by
      simp [smul_eq_mul, Complex.mul_re, Complex.add_re]
    rw [hre]
    by_cases hzero : clip t = 0
    · simpa [hzero] using hpeval
    by_cases hone : clip t = 1
    · simpa [hone] using hqeval
    exact add_pos (mul_pos (sub_pos.mpr (lt_of_le_of_ne hclip.2 hone)) hpeval)
      (mul_pos (lt_of_le_of_ne hclip.1 (Ne.symm hzero)) hqeval)
  rw [hevalZero] at hevalPos
  exact (lt_irrefl 0 hevalPos)

/-- **Upper interlacing point.** Let $p$ be a complex polynomial and let
$\operatorname{maxroot}(p)$ be the largest real part of an element of the multiset of roots of
$p$, with $\operatorname{maxroot}(p) = 0$ when that multiset is empty (as it is for nonzero
constants and for $p = 0$). A real number $a$ is an upper interlacing point of $p$ if
$a \le \operatorname{maxroot}(p)$ and, after removing one copy of $\operatorname{maxroot}(p)$
from the multiset of roots of $p$ (if it occurs there), every remaining root has real part at
most $a$. -/
public def HasUpperInterlacingPoint (p : Polynomial ℂ) (a : ℝ) : Prop :=
  a ≤ p.maxRealRoot ∧
    ∀ z ∈ p.roots.erase (p.maxRealRoot : ℂ), z.re ≤ a

/-- **Common upper interlacing point.** A family $(P_i)_{i \in I}$ of complex polynomials,
indexed by an arbitrary type $I$, has a common upper interlacing point if some real number $a$
is an upper interlacing point of $P_i$ for every $i \in I$. -/
public def HasCommonUpperInterlacing {ι : Type*} (P : ι → Polynomial ℂ) : Prop :=
  ∃ a : ℝ, ∀ i, (P i).HasUpperInterlacingPoint a

/-- **Nonpositivity between an upper interlacing point and the largest root.** Let $p$ be a
monic complex polynomial of positive degree all of whose roots are real, let
$\operatorname{maxroot}(p)$ be its largest root, and let $a$ be an upper interlacing point
of $p$. Then for every real $x$ with $a \le x \le \operatorname{maxroot}(p)$, the real part
of $p(x)$ is at most $0$. -/
public theorem eval_re_nonpos_of_upperInterlacing
    {p : Polynomial ℂ} (hmonic : p.Monic) (hrooted : p.IsRealRooted)
    {a x : ℝ} (ha : p.HasUpperInterlacingPoint a) (hax : a ≤ x)
    (hx : x ≤ p.maxRealRoot) (hdegree : 0 < p.natDegree) :
    (p.eval (x : ℂ)).re ≤ 0 := by
  have hmaxroot : (p.maxRealRoot : ℂ) ∈ p.roots :=
    coe_maxRealRoot_mem_roots hrooted hdegree
  rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hmonic]
  rw [← Multiset.cons_erase hmaxroot, Multiset.map_cons, Multiset.prod_cons]
  have hfirst : (x : ℂ) - (p.maxRealRoot : ℂ) ≤ 0 := by
    rw [RCLike.nonpos_iff]
    exact ⟨sub_nonpos.mpr hx, by simp⟩
  have hrest :
      0 ≤ ((p.roots.erase (p.maxRealRoot : ℂ)).map (fun z ↦ (x : ℂ) - z)).prod := by
    apply Multiset.prod_nonneg
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hw
    rw [RCLike.nonneg_iff]
    exact ⟨sub_nonneg.mpr ((ha.2 z hz).trans hax),
      by simpa using hrooted z (Multiset.mem_of_le (Multiset.erase_le _ _) hz)⟩
  exact (RCLike.nonpos_iff.mp (mul_nonpos_of_nonpos_of_nonneg hfirst hrest)).1

private lemma ksEval_re_weightedSum {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (P : ι → Polynomial ℂ) (x : ℝ) :
    ((∑ i, (w i : ℂ) • P i).eval (x : ℂ)).re =
      ∑ i, w i * ((P i).eval (x : ℂ)).re := by
  rw [Polynomial.eval_finsetSum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_smul]
  change ((w i : ℂ) * (P i).eval (x : ℂ)).re = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- **Common upper interlacing bounds some member's largest root by a weighted sum's.** Let $I$
be a nonempty finite set and, for each $i \in I$, let $P_i$ be a monic complex polynomial of
positive degree all of whose roots are real, such that the family $(P_i)_{i \in I}$ has a
common upper interlacing point. Let $w_i \ge 0$ be real weights such that
$Q = \sum_{i \in I} w_i P_i$ is monic and all of its roots are real. Then there is $i \in I$
with $\operatorname{maxroot}(P_i) \le \operatorname{maxroot}(Q)$, where
$\operatorname{maxroot}(f)$ denotes the largest root of a real-rooted polynomial $f$. -/
public theorem exists_maxRealRoot_le_weightedSum_of_commonUpperInterlacing
    {ι : Type*} [Fintype ι] [Nonempty ι] (w : ι → ℝ) (P : ι → Polynomial ℂ)
    (hw : ∀ i, 0 ≤ w i) (hmonic : ∀ i, (P i).Monic)
    (hrooted : ∀ i, (P i).IsRealRooted) (hdegree : ∀ i, 0 < (P i).natDegree)
    (hcommon : Polynomial.HasCommonUpperInterlacing P)
    (hsumMonic : (∑ i, (w i : ℂ) • P i).Monic)
    (hsumRooted : (∑ i, (w i : ℂ) • P i).IsRealRooted) :
    ∃ i, (P i).maxRealRoot ≤ (∑ j, (w j : ℂ) • P j).maxRealRoot := by
  classical
  let q : Polynomial ℂ := ∑ i, (w i : ℂ) • P i
  change ∃ i, (P i).maxRealRoot ≤ q.maxRealRoot
  change q.Monic at hsumMonic
  change q.IsRealRooted at hsumRooted
  obtain ⟨a, ha⟩ := hcommon
  have haq : a ≤ q.maxRealRoot := by
    by_contra hnot
    have hqa : (q.eval (a : ℂ)).re ≤ 0 := by
      change ((∑ i, (w i : ℂ) • P i).eval (a : ℂ)).re ≤ 0
      rw [ksEval_re_weightedSum]
      apply Finset.sum_nonpos
      intro i hi
      exact mul_nonpos_of_nonneg_of_nonpos (hw i)
        (eval_re_nonpos_of_upperInterlacing (hmonic i) (hrooted i) (ha i)
          le_rfl (ha i).1 (hdegree i))
    have hqpos : 0 < (q.eval (a : ℂ)).re :=
      eval_re_pos_of_maxRealRoot_lt hsumMonic hsumRooted (lt_of_not_ge hnot)
    linarith
  obtain ⟨i₀, hi₀mem, hi₀min⟩ := Finset.exists_min_image Finset.univ
    (fun i ↦ (P i).maxRealRoot) Finset.univ_nonempty
  refine ⟨i₀, ?_⟩
  by_contra hnot
  have hq_lt_i₀ : q.maxRealRoot < (P i₀).maxRealRoot := lt_of_not_ge hnot
  let y : ℝ := (q.maxRealRoot + (P i₀).maxRealRoot) / 2
  have hq_lt_y : q.maxRealRoot < y := by
    dsimp only [y]
    linarith
  have hy_lt_i₀ : y < (P i₀).maxRealRoot := by
    dsimp only [y]
    linarith
  have ha_lt_y : a < y := lt_of_le_of_lt haq hq_lt_y
  have hqpos : 0 < (q.eval (y : ℂ)).re :=
    eval_re_pos_of_maxRealRoot_lt hsumMonic hsumRooted hq_lt_y
  change 0 < ((∑ i, (w i : ℂ) • P i).eval (y : ℂ)).re at hqpos
  rw [ksEval_re_weightedSum] at hqpos
  have hexists : ∃ i, 0 < w i * ((P i).eval (y : ℂ)).re := by
    by_contra hnone
    push Not at hnone
    have hnonpos : (∑ i, w i * ((P i).eval (y : ℂ)).re) ≤ 0 :=
      Finset.sum_nonpos fun i hi ↦ hnone i
    linarith
  obtain ⟨i, hipos⟩ := hexists
  have hieval : 0 < ((P i).eval (y : ℂ)).re := by
    rcases (mul_pos_iff.mp hipos) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge (hw i) hneg.1).elim
  have himax : (P i).maxRealRoot < y := by
    by_contra hiy
    have hinonpos : ((P i).eval (y : ℂ)).re ≤ 0 :=
      eval_re_nonpos_of_upperInterlacing (hmonic i) (hrooted i) (ha i)
        (le_of_lt ha_lt_y) (le_of_not_gt hiy) (hdegree i)
    linarith
  have hmin := hi₀min i (Finset.mem_univ i)
  linarith

/-- **Some member's largest root is at most that of a weighted sum, via real-rooted segments.**
Let $I$ be a nonempty finite set, let $n \ge 1$, and for each $i \in I$ let $P_i$ be a monic
complex polynomial of degree $n$ and $w_i \ge 0$ a real weight. Suppose that
$Q = \sum_{i \in I} w_i P_i$ is monic of degree $n$ and that, for every $i \in I$ and every
$t \in [0, 1]$, all roots of $(1 - t) Q + t P_i$ are real. Then there is $i \in I$ with
$\operatorname{maxroot}(P_i) \le \operatorname{maxroot}(Q)$, where $\operatorname{maxroot}(f)$
denotes the largest real part of a root of $f$. -/
public theorem exists_maxRealRoot_le_weightedSum_of_segment_realRooted
    {ι : Type*} [Fintype ι] (hne : Nonempty ι) (w : ι → ℝ) (P : ι → Polynomial ℂ)
    {n : ℕ} (hn : 0 < n) (hw : ∀ i, 0 ≤ w i)
    (hfamily : ∀ i, (P i).IsMonicOfDegree n)
    (hsum : (∑ i, (w i : ℂ) • P i).IsMonicOfDegree n)
    (hsegments : ∀ i t, t ∈ Set.Icc (0 : ℝ) 1 →
      ((1 - (t : ℂ)) • (∑ j, (w j : ℂ) • P j) + (t : ℂ) • P i).IsRealRooted) :
    ∃ i, (P i).maxRealRoot ≤ (∑ j, (w j : ℂ) • P j).maxRealRoot := by
  classical
  let Q : Polynomial ℂ := ∑ i, (w i : ℂ) • P i
  change ∃ i, (P i).maxRealRoot ≤ Q.maxRealRoot
  change Q.IsMonicOfDegree n at hsum
  change ∀ i t, t ∈ Set.Icc (0 : ℝ) 1 →
    ((1 - (t : ℂ)) • Q + (t : ℂ) • P i).IsRealRooted at hsegments
  by_contra hnone
  push Not at hnone
  obtain ⟨i₀, hi₀mem, hi₀min⟩ := Finset.exists_min_image Finset.univ
    (fun i ↦ (P i).maxRealRoot) ⟨Classical.choice hne, Finset.mem_univ _⟩
  have hQrooted : Q.IsRealRooted := by
    simpa using hsegments i₀ 0 (by simp)
  have hQltMin : Q.maxRealRoot < (P i₀).maxRealRoot := hnone i₀
  let x : ℝ := (Q.maxRealRoot + (P i₀).maxRealRoot) / 2
  have hQltx : Q.maxRealRoot < x := by
    dsimp only [x]
    linarith
  have hxltMin : x < (P i₀).maxRealRoot := by
    dsimp only [x]
    linarith
  have hQeval : 0 < (Q.eval (x : ℂ)).re :=
    eval_re_pos_of_maxRealRoot_lt hsum.monic hQrooted hQltx
  change 0 < ((∑ i, (w i : ℂ) • P i).eval (x : ℂ)).re at hQeval
  rw [ksEval_re_weightedSum] at hQeval
  have hexists : ∃ i, 0 < w i * ((P i).eval (x : ℂ)).re := by
    by_contra hnonpos
    push Not at hnonpos
    have hsumNonpos : (∑ i, w i * ((P i).eval (x : ℂ)).re) ≤ 0 :=
      Finset.sum_nonpos fun i hi ↦ hnonpos i
    linarith
  obtain ⟨i, hipos⟩ := hexists
  have hieval : 0 < ((P i).eval (x : ℂ)).re := by
    rcases (mul_pos_iff.mp hipos) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge (hw i) hneg.1).elim
  have himaxlt : (P i).maxRealRoot < x :=
    ksMaxRealRoot_lt_of_segment hn hsum (hfamily i) (hsegments i) hQltx hieval
  have hmin := hi₀min i (Finset.mem_univ i)
  linarith

end Polynomial
