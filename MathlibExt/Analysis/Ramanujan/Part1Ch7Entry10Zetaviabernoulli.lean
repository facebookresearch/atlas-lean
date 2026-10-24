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
public import MathlibExt.Analysis.Ramanujan.Part1Ch7PowerDifference
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.LSeries.Dirichlet
import MathlibExt.NumberTheory.LSeries.RiemannZeta

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 10, corollary

For `φ_r(x) = ∑_{j ≥ 0} ((j + 1)ʳ - (j + 1 + x)ʳ)`, `∑_{k=1}^{n-1} φ_r(-k/n) = (n - n⁻ʳ) ζ(-r)`
as meromorphic functions of `r`.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry10Zetaviabernoulli

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section


/-- **Left side of the corollary to Entry 10.** For a function
$\varphi : \mathbb{C} \to \mathbb{C} \to \mathbb{C}$, a natural number $n$ and $r \in \mathbb{C}$,
the left side of the corollary to Entry 10 is $\sum_{k=1}^{n-1} \varphi(r, -k/n)$, the empty sum
$0$ when $n \le 1$. In Berndt's notation, $\varphi(r, x)$ is written $\varphi_r(x)$. -/
def chapter7Entry10CorollaryLeft
    (phi : ℂ → ℂ → ℂ) (n : ℕ) (r : ℂ) : ℂ :=
  ∑ k ∈ Icc 1 (n - 1), phi r (-((k : ℂ) / n))

/-- **Right side of the corollary to Entry 10.** For a natural number $n$ and $r \in \mathbb{C}$,
the right side of the corollary to Entry 10 is $(n - n^{-r})\,\zeta(-r)$, where $n^{-r}$ is the
principal complex power and $\zeta$ is the Riemann zeta function. -/
def chapter7Entry10CorollaryRight (n : ℕ) (r : ℂ) : ℂ :=
  ((n : ℂ) - Complex.cpow (n : ℂ) (-r)) * riemannZeta (-r)


@[simp]
theorem chapter7Entry10CorollaryLeft_one (phi : ℂ → ℂ → ℂ) (r : ℂ) :
    chapter7Entry10CorollaryLeft phi 1 r = 0 := by
  simp [chapter7Entry10CorollaryLeft]

@[simp]
theorem chapter7Entry10CorollaryRight_one (r : ℂ) : chapter7Entry10CorollaryRight 1 r = 0 := by
  simp [chapter7Entry10CorollaryRight]


private lemma adm_aux {n k j : ℕ} (hn : 0 < n) (hkn : k < n)
    (hj : ((j : ℂ) + 1) + (-((k : ℂ) / (n : ℂ))) = 0) : False := by
  have hn0 : ((n : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have h1 : ((j : ℂ) + 1) = (k : ℂ) / (n : ℂ) := by
    have hsub : ((j : ℂ) + 1) - (k : ℂ) / (n : ℂ) = 0 := by
      rw [sub_eq_add_neg]; exact hj
    exact sub_eq_zero.mp hsub
  have h2 : ((j : ℂ) + 1) * (n : ℂ) = (k : ℂ) := by
    rw [h1, div_mul_cancel₀ _ hn0]
  have h3 : ((n * (j + 1) : ℕ) : ℂ) = ((k : ℕ) : ℂ) := by
    push_cast at h2 ⊢
    rw [mul_comm] at h2
    exact h2
  have h4 : n * (j + 1) = k := Nat.cast_injective h3
  have h5 : n ≤ n * (j + 1) := Nat.le_mul_of_pos_right n (Nat.succ_pos j)
  omega

/-- **The points $-k/n$ are admissible.** For natural numbers $n$ and $k$ with
$1 \le k \le n - 1$, the point $x = -k/n$ is admissible, that is, $j + 1 + x \neq 0$ for every
natural number $j$.

These are the points at which the left side of the corollary to Entry 10 evaluates $\varphi$. -/
theorem chapter7Admissible_neg_div {n k : ℕ} (hk : k ∈ Finset.Icc 1 (n - 1)) :
    chapter7Admissible (-((k : ℂ) / (n : ℂ))) := by
  intro j hj
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  have hkn : k < n := by omega
  exact adm_aux (by omega) hkn hj

private lemma one_div_cpow_neg (z : ℂ) (hz : z ≠ 0) (r : ℂ) :
    (1 : ℂ) / Complex.cpow z (-r) = Complex.cpow z r := by
  have hmul : Complex.cpow z r * Complex.cpow z (-r) = 1 := by
    have h := Complex.cpow_add r (-r) hz
    rw [add_neg_cancel] at h
    rw [Complex.cpow_zero] at h
    exact h.symm
  have hne : Complex.cpow z (-r) ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  rw [div_eq_iff hne]
  exact hmul.symm

private lemma hasSum_zeta_shift (r : ℂ) (hr : r.re < -1) :
    HasSum (fun m : ℕ => Complex.cpow ((((m + 1 : ℕ)) : ℂ)) r)
      (riemannZeta (-r)) := by
  have hs : (1 : ℝ) < (-r).re := by
    simp only [Complex.neg_re]
    linarith
  have hL : HasSum (LSeries.term (1 : ℕ → ℂ) (-r)) (riemannZeta (-r)) :=
    LSeriesHasSum_one hs
  have h0 : LSeries.term (1 : ℕ → ℂ) (-r) 0 = 0 := by
    unfold LSeries.term
    simp
  have hshift : HasSum (fun n : ℕ => LSeries.term (1 : ℕ → ℂ) (-r) (n + 1))
      (riemannZeta (-r)) := by
    have h1 : riemannZeta (-r) + ∑ i ∈ Finset.range 1,
          LSeries.term (1 : ℕ → ℂ) (-r) i = riemannZeta (-r) := by
      simp [h0]
    have hf' : HasSum (LSeries.term (1 : ℕ → ℂ) (-r))
        (riemannZeta (-r) + ∑ i ∈ Finset.range 1,
          LSeries.term (1 : ℕ → ℂ) (-r) i) := by
      rw [h1]
      exact hL
    exact (hasSum_nat_add_iff 1).mpr hf'
  have hcongr : (fun n : ℕ => LSeries.term (1 : ℕ → ℂ) (-r) (n + 1))
      = (fun m : ℕ => Complex.cpow ((((m + 1 : ℕ)) : ℂ)) r) := by
    funext n
    have hterm : LSeries.term (1 : ℕ → ℂ) (-r) (n + 1)
        = 1 / ((((n + 1 : ℕ)) : ℂ) ^ (-r)) := by
      unfold LSeries.term
      simp
    rw [hterm]
    have hz : ((((n + 1 : ℕ)) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    exact one_div_cpow_neg _ hz r
  rw [hcongr] at hshift
  exact hshift

private lemma nat_cpow_mul (a b : ℕ) (r : ℂ) :
    Complex.cpow ((((a * b : ℕ)) : ℂ)) r
      = Complex.cpow ((a : ℂ)) r * Complex.cpow ((b : ℂ)) r := by
  have e1 : ((((a * b : ℕ)) : ℂ)) = (((a : ℝ) : ℂ)) * (((b : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_mul]
    push_cast
    ring
  rw [e1]
  have e2 : ((a : ℂ)) = (((a : ℝ) : ℂ)) := by
    push_cast
    ring
  have e3 : ((b : ℂ)) = (((b : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [e2, e3]
  exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) r

private lemma tsum_split_mod (n : ℕ) [NeZero n] (a : ℕ → ℂ) (ha : Summable a) :
    ∑' m, a m = ∑ i : Fin n, ∑' q, a (q * n + (i : ℕ)) := by
  have hsymm_eq : ∀ q (i : Fin n),
      (Nat.divModEquiv n).symm (q, i) = q * n + (i : ℕ) := by
    intro q i
    unfold Nat.divModEquiv
    simp
  have hsum : Summable (fun p : ℕ × Fin n => a ((Nat.divModEquiv n).symm p)) :=
    ((Nat.divModEquiv n).symm.summable_iff).mpr ha
  have h1 : ∑' m, a m
      = ∑' p : ℕ × Fin n, a ((Nat.divModEquiv n).symm p) :=
    ((Nat.divModEquiv n).symm.tsum_eq a).symm
  have hsub : ∀ q : ℕ,
      Summable (fun i : Fin n => a ((Nat.divModEquiv n).symm (q, i))) := by
    intro q
    apply hsum.comp_injective
    intro i1 i2 h
    simpa using h
  have hprod : (∑' p : ℕ × Fin n, a ((Nat.divModEquiv n).symm p))
      = ∑' q, ∑' i : Fin n, a ((Nat.divModEquiv n).symm (q, i)) :=
    hsum.tsum_prod' hsub
  rw [h1, hprod]
  have hfin : ∀ q : ℕ, (∑' i : Fin n, a ((Nat.divModEquiv n).symm (q, i)))
      = ∑ i : Fin n, a ((Nat.divModEquiv n).symm (q, i)) := by
    intro q
    exact tsum_fintype _
  simp_rw [hfin]
  have hq : ∀ i : Fin n,
      Summable (fun q : ℕ => a ((Nat.divModEquiv n).symm (q, i))) := by
    intro i
    apply hsum.comp_injective
    intro q1 q2 h
    simpa using h
  have hHas : HasSum (fun q : ℕ => ∑ i : Fin n, a ((Nat.divModEquiv n).symm (q, i)))
      (∑ i : Fin n, ∑' q, a ((Nat.divModEquiv n).symm (q, i))) := by
    apply hasSum_sum
    intro i _
    exact (hq i).hasSum
  rw [hHas.tsum_eq]
  apply Finset.sum_congr rfl
  intro i _
  apply tsum_congr
  intro q
  rw [hsymm_eq q i]

private lemma fixedJ_eq {n j : ℕ} (hn2 : 2 ≤ n) (r : ℂ) :
    (∑ k ∈ Finset.Icc 1 (n - 1),
      Complex.cpow ((((n * (j + 1) - k : ℕ)) : ℂ)) r)
    = ∑ i ∈ Finset.range (n - 1),
      Complex.cpow ((((n * j + (i + 1) : ℕ)) : ℂ)) r := by
  have hIcc : ∑ k ∈ Finset.Icc 1 (n - 1),
        Complex.cpow ((((n * (j + 1) - k : ℕ)) : ℂ)) r
      = ∑ i ∈ Finset.range (n - 1),
        Complex.cpow ((((n * (j + 1) - (i + 1) : ℕ)) : ℂ)) r := by
    apply Finset.sum_bij (fun k _ => k - 1)
    · intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_range]
      omega
    · intro k1 hk1 k2 hk2 h
      rw [Finset.mem_Icc] at hk1 hk2
      omega
    · intro i hi
      rw [Finset.mem_range] at hi
      refine ⟨i + 1, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · show i + 1 - 1 = i
        omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      have hk1 : 1 ≤ k := hk.1
      have heq : k - 1 + 1 = k := Nat.sub_add_cancel hk1
      rw [heq]
  rw [hIcc]
  have hbase : ∀ i ∈ Finset.range (n - 1),
      (n * (j + 1) - (i + 1)) = (n * j + ((n - 1 - 1 - i) + 1)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : n * (j + 1) = n * j + n := by ring
    rw [h1]
    omega
  have hcpow : ∀ i ∈ Finset.range (n - 1),
      Complex.cpow ((((n * (j + 1) - (i + 1) : ℕ)) : ℂ)) r
      = Complex.cpow ((((n * j + ((n - 1 - 1 - i) + 1) : ℕ)) : ℂ)) r := by
    intro i hi
    rw [hbase i hi]
  rw [Finset.sum_congr rfl hcpow]
  have hreflect : (∑ i ∈ Finset.range (n - 1),
        Complex.cpow ((((n * j + ((n - 1 - 1 - i) + 1) : ℕ)) : ℂ)) r)
      = ∑ i ∈ Finset.range (n - 1),
        Complex.cpow ((((n * j + (i + 1) : ℕ)) : ℂ)) r := by
    have h := Finset.sum_range_reflect
      (fun t => Complex.cpow ((((n * j + (t + 1) : ℕ)) : ℂ)) r) (n - 1)
    simpa using h
  exact hreflect

private lemma cpow_base_div {n j k : ℕ} (hn : 0 < n) (hkn : k < n) (r : ℂ) :
    Complex.cpow ((((j : ℂ) + 1) + (-((k : ℂ) / (n : ℂ))))) r
    = Complex.cpow ((((n * (j + 1) - k : ℕ)) : ℂ)) r / Complex.cpow (((n : ℂ))) r := by
  have hle : k ≤ n * (j + 1) :=
    le_trans (le_of_lt hkn) (Nat.le_mul_of_pos_right n (Nat.succ_pos j))
  have hcast : ((((n * (j + 1) - k : ℕ)) : ℂ))
      = ((n : ℂ) * (((j : ℂ) + 1))) - ((k : ℂ)) := by
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hbase : ((((j : ℂ) + 1) + (-((k : ℂ) / (n : ℂ)))))
      = ((((n * (j + 1) - k : ℕ)) : ℂ)) / ((n : ℂ)) := by
    rw [hcast]
    have hn0 : ((n : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hn
    field_simp
    ring
  rw [hbase]
  have hmR : (0 : ℝ) ≤ ((n * (j + 1) - k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnR : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
  have e1 : ((((n * (j + 1) - k : ℕ)) : ℂ))
      = ((((n * (j + 1) - k : ℕ) : ℝ)) : ℂ) := by
    push_cast
    ring
  have e2 : (((n : ℕ)) : ℂ) = ((((n : ℕ) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [e1, e2]
  exact Complex.div_cpow_ofReal_nonneg hmR hnR r

private lemma card_icc2 (n : ℕ) (hn2 : 2 ≤ n) :
    (Finset.Icc 1 (n - 1)).card = n - 1 := by
  rw [Nat.card_Icc]
  omega

private lemma inner_split2 (n : ℕ) (r : ℂ) (j : ℕ) :
    (∑ k ∈ Finset.Icc 1 (n - 1),
      chapter7PowerDifferenceTerm r (-((k : ℂ) / n)) j)
    = ((Finset.Icc 1 (n - 1)).card : ℂ) * Complex.cpow (((j : ℂ) + 1)) r
      - ∑ k ∈ Finset.Icc 1 (n - 1),
        Complex.cpow ((((j : ℂ) + 1) + (-((k : ℂ) / n)))) r := by
  unfold chapter7PowerDifferenceTerm
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_const, nsmul_eq_mul]

private lemma left_analytic (phi : ℂ → ℂ → ℂ)
    (hphi_entire : ∀ x, chapter7Admissible x →
      Differentiable ℂ (fun r : ℂ => phi r x))
    (n : ℕ) :
    AnalyticOnNhd ℂ (chapter7Entry10CorollaryLeft phi n) Set.univ := by
  have hdiff : Differentiable ℂ (chapter7Entry10CorollaryLeft phi n) := by
    unfold chapter7Entry10CorollaryLeft
    apply Differentiable.fun_sum
    intro k hk
    exact hphi_entire _ (chapter7Admissible_neg_div hk)
  exact hdiff.differentiableOn.analyticOnNhd isOpen_univ

private lemma left_mero (phi : ℂ → ℂ → ℂ)
    (hphi_entire : ∀ x, chapter7Admissible x →
      Differentiable ℂ (fun r : ℂ => phi r x))
    (n : ℕ) :
    MeromorphicOn (chapter7Entry10CorollaryLeft phi n) Set.univ :=
  (left_analytic phi hphi_entire n).meromorphicOn

private lemma right_mero (n : ℕ) (hn : 0 < n) :
    MeromorphicOn (chapter7Entry10CorollaryRight n) Set.univ := by
  unfold chapter7Entry10CorollaryRight
  have hfac : AnalyticOnNhd ℂ
      (fun r : ℂ => ((n : ℂ) - Complex.cpow (n : ℂ) (-r))) Set.univ := by
    have hdiff : Differentiable ℂ
        (fun r : ℂ => ((n : ℂ) - Complex.cpow (n : ℂ) (-r))) := by
      apply Differentiable.sub (differentiable_const _)
      apply Differentiable.cpow (differentiable_const _)
      · exact differentiable_id.neg
      · intro x
        have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have h : (((n : ℝ) : ℂ)) ∈ Complex.slitPlane :=
          Complex.ofReal_mem_slitPlane.mpr hnR
        have heq : ((n : ℂ)) = (((n : ℝ) : ℂ)) := by
          push_cast
          ring
        rw [heq]
        exact h
    exact hdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hneg : AnalyticOnNhd ℂ (fun r : ℂ => -r) Set.univ := by
    have hdiff : Differentiable ℂ (fun r : ℂ => -r) := differentiable_id.neg
    exact hdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hzeta : MeromorphicOn (riemannZeta ∘ (fun r : ℂ => -r)) Set.univ := by
    have hmero : Meromorphic riemannZeta :=
      meromorphicOn_univ.mp meromorphicOn_riemannZeta
    exact hmero.comp_analyticOnNhd hneg
  have hzeta' : MeromorphicOn (fun r : ℂ => riemannZeta (-r)) Set.univ := hzeta
  exact hfac.meromorphicOn.mul hzeta'

private lemma right_analytic_U (n : ℕ) (hn : 0 < n) :
    AnalyticOnNhd ℂ (chapter7Entry10CorollaryRight n) ({(-1 : ℂ)}ᶜ) := by
  unfold chapter7Entry10CorollaryRight
  have hfacU : AnalyticOnNhd ℂ
      (fun r : ℂ => ((n : ℂ) - Complex.cpow (n : ℂ) (-r))) ({(-1 : ℂ)}ᶜ) := by
    have hdiff : Differentiable ℂ
        (fun r : ℂ => ((n : ℂ) - Complex.cpow (n : ℂ) (-r))) := by
      apply Differentiable.sub (differentiable_const _)
      apply Differentiable.cpow (differentiable_const _)
      · exact differentiable_id.neg
      · intro x
        have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have h : (((n : ℝ) : ℂ)) ∈ Complex.slitPlane :=
          Complex.ofReal_mem_slitPlane.mpr hnR
        have heq : ((n : ℂ)) = (((n : ℝ) : ℂ)) := by
          push_cast
          ring
        rw [heq]
        exact h
    have hU : AnalyticOnNhd ℂ
        (fun r : ℂ => ((n : ℂ) - Complex.cpow (n : ℂ) (-r))) Set.univ :=
      hdiff.differentiableOn.analyticOnNhd isOpen_univ
    exact hU.mono (Set.subset_univ _)
  have hnegU : AnalyticOnNhd ℂ (fun r : ℂ => -r) ({(-1 : ℂ)}ᶜ) := by
    have hdiff : Differentiable ℂ (fun r : ℂ => -r) := differentiable_id.neg
    have hU : AnalyticOnNhd ℂ (fun r : ℂ => -r) Set.univ :=
      hdiff.differentiableOn.analyticOnNhd isOpen_univ
    exact hU.mono (Set.subset_univ _)
  have hmaps : Set.MapsTo (fun r : ℂ => -r) ({(-1 : ℂ)}ᶜ) ({(1 : ℂ)}ᶜ) := by
    intro r hr
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hr ⊢
    intro h
    apply hr
    have hneg : - -r = -1 := congrArg Neg.neg h
    simpa using hneg
  have hzetaU : AnalyticOnNhd ℂ (riemannZeta ∘ (fun r : ℂ => -r))
      ({(-1 : ℂ)}ᶜ) :=
    analyticOn_riemannZeta.comp hnegU hmaps
  have hzetaU' : AnalyticOnNhd ℂ (fun r : ℂ => riemannZeta (-r))
      ({(-1 : ℂ)}ᶜ) := hzetaU
  exact hfacU.mul hzetaU'

private lemma agree_of_re_lt (phi : ℂ → ℂ → ℂ)
    (hphi_series : ∀ r x, r.re < 0 → chapter7Admissible x →
      HasSum (chapter7PowerDifferenceTerm r x) (phi r x))
    (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n) (r : ℂ) (hr : r.re < -1) :
    chapter7Entry10CorollaryLeft phi n r
      = chapter7Entry10CorollaryRight n r := by
  have hr0 : r.re < 0 := by linarith
  have _ne : NeZero n := ⟨by omega⟩
  have hS0 := hasSum_zeta_shift r hr
  have hS : HasSum (fun (j : ℕ) => Complex.cpow (((j : ℂ) + 1)) r)
      (riemannZeta (-r)) := by
    apply hS0.congr_fun
    intro j
    congr 1
    push_cast
    ring
  have hLeft : HasSum (fun (j : ℕ) => ∑ k ∈ Finset.Icc 1 (n - 1),
      chapter7PowerDifferenceTerm r (-((k : ℂ) / n)) j)
      (chapter7Entry10CorollaryLeft phi n r) := by
    unfold chapter7Entry10CorollaryLeft
    apply hasSum_sum
    intro k hk
    exact hphi_series r _ hr0 (chapter7Admissible_neg_div hk)
  have hcard : (Finset.Icc 1 (n - 1)).card = n - 1 := card_icc2 n hn2
  have hinner : (fun (j : ℕ) => ∑ k ∈ Finset.Icc 1 (n - 1),
        chapter7PowerDifferenceTerm r (-((k : ℂ) / n)) j)
      = (fun (j : ℕ) => ((((n - 1 : ℕ)) : ℂ)) * Complex.cpow (((j : ℂ) + 1)) r
        - ∑ k ∈ Finset.Icc 1 (n - 1),
          Complex.cpow ((((j : ℂ) + 1) + (-((k : ℂ) / n)))) r) := by
    funext j
    rw [inner_split2 n r j, hcard]
  rw [hinner] at hLeft
  have hFirst : HasSum
      (fun (j : ℕ) => ((((n - 1 : ℕ)) : ℂ)) * Complex.cpow (((j : ℂ) + 1)) r)
      (((((n - 1 : ℕ)) : ℂ)) * riemannZeta (-r)) :=
    hS.mul_left _
  have hB : HasSum (fun (j : ℕ) => ∑ k ∈ Finset.Icc 1 (n - 1),
        Complex.cpow ((((j : ℂ) + 1) + (-((k : ℂ) / n)))) r)
      (((((n - 1 : ℕ)) : ℂ)) * riemannZeta (-r)
        - chapter7Entry10CorollaryLeft phi n r) := by
    have hsub := hFirst.sub hLeft
    apply hsub.congr_fun
    intro j
    ring
  have hnC : ((n : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hmul_nr : Complex.cpow ((n : ℂ)) r * Complex.cpow ((n : ℂ)) (-r) = 1 := by
    have h := Complex.cpow_add r (-r) hnC
    rw [add_neg_cancel] at h
    rw [Complex.cpow_zero] at h
    exact h.symm
  have hnr_ne : Complex.cpow ((n : ℂ)) r ≠ 0 :=
    left_ne_zero_of_mul_eq_one hmul_nr
  have hB_eq : (fun (j : ℕ) => ∑ k ∈ Finset.Icc 1 (n - 1),
        Complex.cpow ((((j : ℂ) + 1) + (-((k : ℂ) / n)))) r)
      = (fun (j : ℕ) => ∑ i ∈ Finset.range (n - 1),
        (Complex.cpow ((((n * j + (i + 1) : ℕ)) : ℂ)) r
          / Complex.cpow ((n : ℂ)) r)) := by
    funext j
    have h1 : ∀ k ∈ Finset.Icc 1 (n - 1),
        Complex.cpow ((((j : ℂ) + 1) + (-((k : ℂ) / n)))) r
        = Complex.cpow ((((n * (j + 1) - k : ℕ)) : ℂ)) r
          / Complex.cpow ((n : ℂ)) r := by
      intro k hk
      have hkn : k < n := by
        have := (Finset.mem_Icc.mp hk).2
        omega
      exact cpow_base_div hn hkn r
    have h2 : (∑ k ∈ Finset.Icc 1 (n - 1),
          Complex.cpow ((((j : ℂ) + 1) + (-((k : ℂ) / n)))) r)
        = (∑ k ∈ Finset.Icc 1 (n - 1),
          Complex.cpow ((((n * (j + 1) - k : ℕ)) : ℂ)) r
            / Complex.cpow ((n : ℂ)) r) :=
      Finset.sum_congr rfl h1
    rw [h2, ← Finset.sum_div, ← Finset.sum_div, fixedJ_eq hn2 r]
  rw [hB_eq] at hB
  have hBmul : HasSum (fun (j : ℕ) => (∑ i ∈ Finset.range (n - 1),
        (Complex.cpow ((((n * j + (i + 1) : ℕ)) : ℂ)) r
          / Complex.cpow ((n : ℂ)) r))
        * Complex.cpow ((n : ℂ)) r)
      ((((((n - 1 : ℕ)) : ℂ)) * riemannZeta (-r)
        - chapter7Entry10CorollaryLeft phi n r)
        * Complex.cpow ((n : ℂ)) r) :=
    hB.mul_right _
  have hRange : HasSum (fun (j : ℕ) => ∑ i ∈ Finset.range (n - 1),
        Complex.cpow ((((n * j + (i + 1) : ℕ)) : ℂ)) r)
      ((((((n - 1 : ℕ)) : ℂ)) * riemannZeta (-r)
        - chapter7Entry10CorollaryLeft phi n r)
        * Complex.cpow ((n : ℂ)) r) := by
    apply hBmul.congr_fun
    intro j
    rw [← Finset.sum_div]
    exact (div_mul_cancel₀ _ hnr_ne).symm
  have hSumm : Summable
      (fun m : ℕ => Complex.cpow ((((m + 1 : ℕ)) : ℂ)) r) :=
    hS0.summable
  have hSplit : (∑' m, Complex.cpow ((((m + 1 : ℕ)) : ℂ)) r)
      = ∑ i : Fin n, ∑' q,
        Complex.cpow ((((q * n + (i : ℕ) + 1 : ℕ)) : ℂ)) r :=
    tsum_split_mod n _ hSumm
  have hFinRange : (∑ i : Fin n, ∑' q,
        Complex.cpow ((((q * n + (i : ℕ) + 1 : ℕ)) : ℂ)) r)
      = ∑ i ∈ Finset.range n, ∑' q,
        Complex.cpow ((((q * n + i + 1 : ℕ)) : ℂ)) r := by
    have h := Fin.sum_univ_eq_sum_range
      (fun t : ℕ => ∑' q,
        Complex.cpow ((((q * n + t + 1 : ℕ)) : ℂ)) r) n
    simpa using h
  have hn1 : 1 ≤ n := by omega
  have hn_eq : n = (n - 1) + 1 := (Nat.sub_add_cancel hn1).symm
  have hRangeSplit : (∑ i ∈ Finset.range n, ∑' q,
        Complex.cpow ((((q * n + i + 1 : ℕ)) : ℂ)) r)
      = (∑ i ∈ Finset.range (n - 1), ∑' q,
        Complex.cpow ((((q * n + i + 1 : ℕ)) : ℂ)) r)
        + ∑' q,
          Complex.cpow ((((q * n + (n - 1) + 1 : ℕ)) : ℂ)) r := by
    nth_rewrite 1 [hn_eq]
    rw [Finset.sum_range_succ]
  have hMult_eq : (∑' q,
        Complex.cpow ((((q * n + (n - 1) + 1 : ℕ)) : ℂ)) r)
      = Complex.cpow ((n : ℂ)) r * riemannZeta (-r) := by
    have hMul : HasSum
        (fun j : ℕ => Complex.cpow ((((n * (j + 1) : ℕ)) : ℂ)) r)
        (Complex.cpow ((n : ℂ)) r * riemannZeta (-r)) := by
      have hcongr : (fun j : ℕ => Complex.cpow ((((n * (j + 1) : ℕ)) : ℂ)) r)
          = (fun j : ℕ => Complex.cpow ((n : ℂ)) r
            * Complex.cpow ((((j + 1 : ℕ)) : ℂ)) r) := by
        funext j
        exact nat_cpow_mul n (j + 1) r
      rw [hcongr]
      exact hS0.mul_left _
    have hcongr2 : (fun q : ℕ =>
          Complex.cpow ((((q * n + (n - 1) + 1 : ℕ)) : ℂ)) r)
        = (fun j : ℕ => Complex.cpow ((((n * (j + 1) : ℕ)) : ℂ)) r) := by
      funext q
      congr 1
      congr 1
      have h1 : q * n + (n - 1) + 1 = n * (q + 1) := by
        have hn1' : n - 1 + 1 = n := Nat.sub_add_cancel hn1
        have : q * n + (n - 1) + 1 = q * n + (n - 1 + 1) := by ring
        rw [this, hn1']
        ring
      exact h1
    rw [hcongr2]
    exact hMul.tsum_eq
  have hEach : ∀ i ∈ Finset.range (n - 1),
      HasSum (fun q : ℕ => Complex.cpow ((((q * n + i + 1 : ℕ)) : ℂ)) r)
        (∑' q, Complex.cpow ((((q * n + i + 1 : ℕ)) : ℂ)) r) := by
    intro i _
    apply Summable.hasSum
    apply hSumm.comp_injective
    intro q1 q2 h
    simp only at h
    have h1 : q1 * n = q2 * n := Nat.add_right_cancel h
    exact Nat.mul_right_cancel (by omega : 0 < n) h1
  have hSumRange : HasSum (fun (q : ℕ) => ∑ i ∈ Finset.range (n - 1),
        Complex.cpow ((((q * n + i + 1 : ℕ)) : ℂ)) r)
      (∑ i ∈ Finset.range (n - 1), ∑' q,
        Complex.cpow ((((q * n + i + 1 : ℕ)) : ℂ)) r) := by
    apply hasSum_sum
    intro i hi
    exact hEach i hi
  have hRangeEq : (∑ i ∈ Finset.range (n - 1), ∑' q,
        Complex.cpow ((((q * n + i + 1 : ℕ)) : ℂ)) r)
      = ((((((n - 1 : ℕ)) : ℂ)) * riemannZeta (-r)
        - chapter7Entry10CorollaryLeft phi n r)
        * Complex.cpow ((n : ℂ)) r) := by
    have hRangeTsum := hRange.tsum_eq
    have hSumTsum := hSumRange.tsum_eq
    have hcongr : (fun (q : ℕ) => ∑ i ∈ Finset.range (n - 1),
          Complex.cpow ((((q * n + i + 1 : ℕ)) : ℂ)) r)
        = (fun (j : ℕ) => ∑ i ∈ Finset.range (n - 1),
          Complex.cpow ((((n * j + (i + 1) : ℕ)) : ℂ)) r) := by
      funext q
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      congr 1
      ring
    rw [hcongr] at hSumTsum
    rw [← hSumTsum]
    exact hRangeTsum
  have hS_eq : (∑' m, Complex.cpow ((((m + 1 : ℕ)) : ℂ)) r)
      = riemannZeta (-r) :=
    hS0.tsum_eq
  have h1 : (∑' m, Complex.cpow ((((m + 1 : ℕ)) : ℂ)) r)
      = ((((((n - 1 : ℕ)) : ℂ)) * riemannZeta (-r)
        - chapter7Entry10CorollaryLeft phi n r)
        * Complex.cpow ((n : ℂ)) r)
        + Complex.cpow ((n : ℂ)) r * riemannZeta (-r) := by
    rw [hSplit, hFinRange, hRangeSplit, hRangeEq, hMult_eq]
  have hSeq : riemannZeta (-r)
      = ((((((n - 1 : ℕ)) : ℂ)) * riemannZeta (-r)
        - chapter7Entry10CorollaryLeft phi n r)
        * Complex.cpow ((n : ℂ)) r)
        + Complex.cpow ((n : ℂ)) r * riemannZeta (-r) :=
    hS_eq.symm.trans h1
  have hneg : Complex.cpow ((n : ℂ)) (-r)
      = 1 / Complex.cpow ((n : ℂ)) r := by
    rw [eq_div_iff hnr_ne, mul_comm]
    exact hmul_nr
  have hcast : ((((n - 1 : ℕ)) : ℂ)) = ((n : ℂ)) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  unfold chapter7Entry10CorollaryRight
  rw [hcast] at hSeq
  rw [hneg]
  field_simp
  linear_combination hSeq

/-- **The corollary to Entry 10 in the half-plane $\operatorname{Re} r < -1$.** Call
$x \in \mathbb{C}$ admissible if $j + 1 + x \neq 0$ for every natural number $j$. Let
$\varphi : \mathbb{C} \to \mathbb{C} \to \mathbb{C}$ be such that, for every $r \in \mathbb{C}$ with
$\operatorname{Re} r < 0$ and every admissible $x$, the series
$\sum_{j \ge 0} \bigl((j + 1)^r - (j + 1 + x)^r\bigr)$ of principal complex powers is
unconditionally summable with sum $\varphi(r, x)$. Then for every natural number $n$ and every
$r \in \mathbb{C}$ with $\operatorname{Re} r < -1$,
$\sum_{k=1}^{n-1} \varphi(r, -k/n) = (n - n^{-r})\,\zeta(-r)$, where $\zeta$ is the Riemann zeta
function. -/
theorem chapter7Entry10CorollaryLeft_eq_right (phi : ℂ → ℂ → ℂ)
    (hphi_series : ∀ r x, r.re < 0 → chapter7Admissible x →
      HasSum (chapter7PowerDifferenceTerm r x) (phi r x))
    (n : ℕ) (r : ℂ) (hr : r.re < -1) :
    chapter7Entry10CorollaryLeft phi n r
      = chapter7Entry10CorollaryRight n r := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hr0 : -r ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.zero_re] at this
      linarith
    simp [chapter7Entry10CorollaryLeft, chapter7Entry10CorollaryRight, Complex.zero_cpow hr0]
  by_cases hn1 : n = 1
  · subst hn1
    unfold chapter7Entry10CorollaryLeft chapter7Entry10CorollaryRight
    simp
  · have hn2 : 2 ≤ n := by omega
    exact agree_of_re_lt phi hphi_series n hn hn2 r hr

/-- **Ramanujan's corollary to Entry 10 of Chapter 7.** Call $x \in \mathbb{C}$ admissible if
$j + 1 + x \neq 0$ for every natural number $j$. Let
$\varphi : \mathbb{C} \to \mathbb{C} \to \mathbb{C}$ be such that, for every admissible $x$, the
function $r \mapsto \varphi(r, x)$ is entire, and, for every $r \in \mathbb{C}$ with
$\operatorname{Re} r < 0$ and every admissible $x$, the series
$\sum_{j \ge 0} \bigl((j + 1)^r - (j + 1 + x)^r\bigr)$ of principal complex powers is
unconditionally summable with sum $\varphi(r, x)$. Then for every positive integer $n$ the
functions $L(r) = \sum_{k=1}^{n-1} \varphi(r, -k/n)$ and $R(r) = (n - n^{-r})\,\zeta(-r)$, where
$\zeta$ is the Riemann zeta function, are meromorphic on $\mathbb{C}$, and the set of
$r \in \mathbb{C}$ with $L(r) \neq R(r)$ has no accumulation point in $\mathbb{C}$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7.
Proves `Wanted` entry `ramanujan_part1_ch7_entry10_zetaviabernoulli`.
-/
theorem ramanujan_part1_ch7_entry10_zetaviabernoulli
    (phi : ℂ → ℂ → ℂ)
    (hphi_entire : ∀ x, chapter7Admissible x →
      Differentiable ℂ (fun r : ℂ => phi r x))
    (hphi_series : ∀ r x, r.re < 0 → chapter7Admissible x →
      HasSum (chapter7PowerDifferenceTerm r x) (phi r x))
    (n : ℕ) (hn : 0 < n) :
    MeromorphicOn (chapter7Entry10CorollaryLeft phi n) Set.univ ∧
      MeromorphicOn (chapter7Entry10CorollaryRight n) Set.univ ∧
      chapter7Entry10CorollaryLeft phi n =ᶠ[codiscrete ℂ]
        chapter7Entry10CorollaryRight n := by
  refine ⟨left_mero phi hphi_entire n, right_mero n hn, ?_⟩
  have hLU : AnalyticOnNhd ℂ (chapter7Entry10CorollaryLeft phi n)
      ({(-1 : ℂ)}ᶜ) :=
    (left_analytic phi hphi_entire n).mono (Set.subset_univ _)
  have hRU := right_analytic_U n hn
  have hConn : IsConnected ({(-1 : ℂ)}ᶜ : Set ℂ) := by
    apply isConnected_compl_singleton_of_one_lt_rank _ (-1)
    have h : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
    have h1 : 1 < Module.finrank ℝ ℂ := by
      rw [h]
      norm_num
    exact Module.one_lt_rank_of_one_lt_finrank h1
  have hPre : IsPreconnected ({(-1 : ℂ)}ᶜ : Set ℂ) := hConn.isPreconnected
  have hmemU : (-2 : ℂ) ∈ ({(-1 : ℂ)}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    norm_num
  have hEqRe : Set.EqOn (chapter7Entry10CorollaryLeft phi n)
      (chapter7Entry10CorollaryRight n) {r : ℂ | r.re < -1} := by
    intro r hr
    exact chapter7Entry10CorollaryLeft_eq_right phi hphi_series n r hr
  have hOpenRe : IsOpen {r : ℂ | r.re < -1} := Complex.isOpen_re_lt (-1)
  have hmemRe : (-2 : ℂ) ∈ {r : ℂ | r.re < -1} := by
    change (-2 : ℂ).re < -1
    norm_num
  have hEv : (chapter7Entry10CorollaryLeft phi n) =ᶠ[nhds (-2 : ℂ)]
      (chapter7Entry10CorollaryRight n) := by
    have hmem_nhds : {r : ℂ | r.re < -1} ∈ nhds (-2 : ℂ) :=
      hOpenRe.mem_nhds hmemRe
    filter_upwards [hmem_nhds] with r hr
    exact hEqRe hr
  have hEqU : Set.EqOn (chapter7Entry10CorollaryLeft phi n)
      (chapter7Entry10CorollaryRight n) ({(-1 : ℂ)}ᶜ) :=
    hLU.eqOn_of_preconnected_of_eventuallyEq hRU hPre hmemU hEv
  have hmem_cod : ({(-1 : ℂ)}ᶜ : Set ℂ) ∈ codiscrete ℂ := by
    have hfin : ({(-1 : ℂ)} : Set ℂ).Finite := Set.finite_singleton _
    have h := hfin.compl_mem_codiscrete
    simpa using h
  filter_upwards [hmem_cod] with r hr
  exact hEqU hr

end

/-- Compatibility alias for the former `Entry10Zetaviabernoulli.chapter7Admissible`.

For new code, use `MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7Admissible` directly. -/
abbrev chapter7Admissible (x : ℂ) : Prop :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7Admissible x

/-- Compatibility alias for the former `Entry10Zetaviabernoulli.chapter7PowerDifferenceTerm`.

For new code, use `MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm`
directly. -/
noncomputable abbrev chapter7PowerDifferenceTerm (r x : ℂ) (j : ℕ) : ℂ :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm r x j

/-- **Zero is admissible.** The point $x = 0$ is admissible: $j + 1 + x \neq 0$ for every natural
number $j$. -/
@[simp]
theorem chapter7Admissible_zero : chapter7Admissible 0 :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7Admissible_zero

/-- **Power-difference terms vanish at exponent zero.** For every $x \in \mathbb{C}$ and every
natural number $j$, the power-difference term $(j + 1)^r - (j + 1 + x)^r$ vanishes at $r = 0$. -/
@[simp]
theorem chapter7PowerDifferenceTerm_zero_left (x : ℂ) (j : ℕ) :
    chapter7PowerDifferenceTerm 0 x j = 0 :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm_zero_left x j

/-- **Power-difference terms vanish at $x = 0$.** For every $r \in \mathbb{C}$ and every natural
number $j$, the power-difference term $(j + 1)^r - (j + 1 + x)^r$ vanishes at $x = 0$. -/
@[simp]
theorem chapter7PowerDifferenceTerm_zero_right (r : ℂ) (j : ℕ) :
    chapter7PowerDifferenceTerm r 0 j = 0 :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm_zero_right r j

end Entry10Zetaviabernoulli

end MathlibExt.Analysis.Ramanujan.Part1Ch7
