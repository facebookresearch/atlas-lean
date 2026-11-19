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
public import MathlibExt.Analysis.Ramanujan.Part1Ch7PowerDifference
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 10

Power-sum distribution relation equals (1-nʳ⁺¹)ζ(-r) meromorphically.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry10Zeta2

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7Entry10DistributionLeft
    (phi : ℂ → ℂ → ℂ) (n : ℕ) (x r : ℂ) : ℂ :=
  phi r x - Complex.cpow (n : ℂ) r *
    ∑ k ∈ range n, phi r ((x - k) / n)

export Entry10Zeta4 (chapter7Entry10ZetaSide)

private lemma ch7_cpow_nat_mul (n : ℕ) (hn : (n : ℂ) ≠ 0) (w r : ℂ) (hr : r ≠ 0) :
    Complex.cpow ((n : ℂ) * w) r = Complex.cpow (n : ℂ) r * Complex.cpow w r := by
  show ((n : ℂ) * w) ^ r = (n : ℂ) ^ r * w ^ r
  by_cases hw : w = 0
  · subst hw
    rw [mul_zero, Complex.zero_cpow hr, mul_zero]
  · have hnw : (n : ℂ) * w ≠ 0 := mul_ne_zero hn hw
    have hlog : Complex.log ((n : ℂ) * w) = Complex.log (n : ℂ) + Complex.log w :=
      Complex.log_mul hn hw (by
        rw [← Complex.ofReal_natCast,
          Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
        simp only [zero_add]
        exact ⟨Complex.neg_pi_lt_arg w, Complex.arg_le_pi w⟩)
    rw [Complex.cpow_def_of_ne_zero hnw, Complex.cpow_def_of_ne_zero hn,
      Complex.cpow_def_of_ne_zero hw, hlog, add_mul, Complex.exp_add]

private lemma ch7_diff_cpow_nat (n : ℕ) (hn : (n : ℂ) ≠ 0) :
    Differentiable ℂ (fun r : ℂ => (n : ℂ) ^ r) :=
  differentiable_id.const_cpow (Or.inl hn)

private lemma ch7_mero_cpow_nat (n : ℕ) (hn : (n : ℂ) ≠ 0) :
    MeromorphicOn (fun r : ℂ => (n : ℂ) ^ r) Set.univ := by
  intro x _
  exact AnalyticAt.meromorphicAt ((ch7_diff_cpow_nat n hn).analyticAt x)

private lemma ch7_mero_distLeft (phi : ℂ → ℂ → ℂ)
    (hphi_meromorphic : ∀ x, MeromorphicOn (fun r : ℂ => phi r x) Set.univ)
    (n : ℕ) (hn : 0 < n) (x : ℂ) :
    MeromorphicOn (chapter7Entry10DistributionLeft phi n x) Set.univ := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hsum : ∀ m : ℕ, MeromorphicOn
      (fun r : ℂ => ∑ k ∈ range m, phi r ((x - k) / n)) Set.univ := by
    intro m
    induction m with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact MeromorphicOn.const _
    | succ m ih =>
      have hstep : (fun r : ℂ => ∑ k ∈ range (m + 1), phi r ((x - k) / n))
          = (fun r : ℂ => ∑ k ∈ range m, phi r ((x - k) / n))
            + (fun r : ℂ => phi r ((x - m) / n)) := by
        funext r
        simp only [Pi.add_apply]
        exact Finset.sum_range_succ _ _
      rw [hstep]
      exact ih.fun_add (hphi_meromorphic _)
  show MeromorphicOn (fun r : ℂ =>
    phi r x - (n : ℂ) ^ r * (∑ k ∈ range n, phi r ((x - k) / n))) Set.univ
  exact (hphi_meromorphic x).fun_sub ((ch7_mero_cpow_nat n hnC).fun_mul (hsum n))

private lemma ch7_zeta_hasSum (r : ℂ) (hr : r.re < -1) :
    HasSum (fun j : ℕ => Complex.cpow (j + 1 : ℂ) r) (riemannZeta (-r)) := by
  have h1 : 1 < (-r).re := by
    rw [Complex.neg_re]
    linarith
  have hEq := zeta_eq_tsum_one_div_nat_add_one_cpow (s := -r) h1
  have hS : Summable (fun j : ℕ => 1 / ((j : ℂ) + 1) ^ (-r)) := by
    have h2 := (HasSum.summable (ArithmeticFunction.LSeriesHasSum_zeta h1)).comp_injective
      Nat.succ_injective
    refine h2.congr (fun j => ?_)
    rw [Function.comp_apply]
    unfold LSeries.term
    simp only []
    simp only [Nat.succ_ne_zero j, ArithmeticFunction.zeta_apply, ite_false,
      Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
  have hV : (∑' (j : ℕ), 1 / ((j : ℂ) + 1) ^ (-r)) = riemannZeta (-r) := hEq.symm
  have hHS : HasSum (fun j : ℕ => 1 / ((j : ℂ) + 1) ^ (-r)) (riemannZeta (-r)) :=
    hV ▸ hS.hasSum
  refine hHS.congr_fun (fun j => ?_)
  show ((j : ℂ) + 1) ^ r = 1 / ((j : ℂ) + 1) ^ (-r)
  rw [one_div, Complex.cpow_neg, inv_inv]

private lemma ch7_shift_hasSum (r : ℂ) (phi : ℂ → ℂ → ℂ)
    (hphi_series : ∀ r x, r.re < 0 → HasSum (chapter7PowerDifferenceTerm r x) (phi r x))
    (hr : r.re < -1) (y : ℂ) :
    HasSum (fun j : ℕ => Complex.cpow ((j + 1 : ℂ) + y) r)
      (riemannZeta (-r) - phi r y) := by
  have hr0 : r.re < 0 := by linarith
  have hsub := (ch7_zeta_hasSum r hr).sub (hphi_series r y hr0)
  refine HasSum.congr_fun hsub (fun j => ?_)
  show Complex.cpow ((j + 1 : ℂ) + y) r =
    Complex.cpow (j + 1 : ℂ) r - chapter7PowerDifferenceTerm r y j
  unfold chapter7PowerDifferenceTerm
  ring

private noncomputable def ch7Reindex (n : ℕ) (hn : 0 < n) : Fin n × ℕ ≃ ℕ where
  toFun p := n * p.2 + (n - 1 - p.1.val)
  invFun m := (⟨n - 1 - m % n, by have h := Nat.mod_lt m hn; omega⟩, m / n)
  left_inv := by
    rintro ⟨k, j⟩
    have hkn : k.val < n := k.isLt
    have ht : n - 1 - k.val < n := by omega
    have hmod : (n * j + (n - 1 - k.val)) % n = n - 1 - k.val := by
      rw [show n * j + (n - 1 - k.val) = (n - 1 - k.val) + n * j from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
    have hdiv : (n * j + (n - 1 - k.val)) / n = j := by
      rw [show n * j + (n - 1 - k.val) = (n - 1 - k.val) + n * j from by ring,
        Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt ht, zero_add]
    refine Prod.ext (Fin.ext ?_) hdiv
    show n - 1 - (n * j + (n - 1 - k.val)) % n = k.val
    rw [hmod]
    omega
  right_inv := by
    intro m
    have ht : m % n < n := Nat.mod_lt m hn
    have hsub : n - 1 - (n - 1 - m % n) = m % n := by omega
    show n * (m / n) + (n - 1 - (n - 1 - m % n)) = m
    rw [hsub]
    exact Nat.div_add_mod m n

private lemma ch7Reindex_apply (n : ℕ) (hn : 0 < n) (k : Fin n) (j : ℕ) :
    ch7Reindex n hn (k, j) = n * j + (n - 1 - k.val) := rfl

private lemma ch7_fiber_eq (n : ℕ) (hn : 0 < n) (x r : ℂ) (hrne : r ≠ 0)
    (hnC : (n : ℂ) ≠ 0) (k : Fin n) (j : ℕ) :
    (n : ℂ) ^ r * Complex.cpow ((j + 1 : ℂ) + ((x - (k : ℕ)) / n)) r
      = Complex.cpow ((ch7Reindex n hn (k, j) + 1 : ℂ) + x) r := by
  have h1 : k.val ≤ n - 1 := by have := k.isLt; omega
  have h2 : 1 ≤ n := by omega
  have hw : (n : ℂ) * (((j + 1 : ℂ)) + ((x - (k : ℕ)) / (n : ℂ)))
      = ((ch7Reindex n hn (k, j) + 1 : ℂ)) + x := by
    rw [ch7Reindex_apply]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_sub h1,
      Nat.cast_sub h2]
    have hdiv : (n : ℂ) * ((((x : ℂ) - (k.val : ℂ))) / (n : ℂ))
        = ((x : ℂ) - (k.val : ℂ)) := by field_simp
    rw [mul_add, hdiv]
    ring
  rw [← hw]
  show Complex.cpow (n : ℂ) r
      * Complex.cpow (((j + 1 : ℂ)) + ((x - (k : ℕ)) / (n : ℂ))) r
    = Complex.cpow ((n : ℂ) * ((((j + 1 : ℂ)) + ((x - (k : ℕ)) / (n : ℂ))))) r
  exact (ch7_cpow_nat_mul n hnC _ r hrne).symm

private lemma ch7_eq_of_re_lt (phi : ℂ → ℂ → ℂ)
    (hphi_series : ∀ r x, r.re < 0 → HasSum (chapter7PowerDifferenceTerm r x) (phi r x))
    (n : ℕ) (hn : 0 < n) (x r : ℂ) (hr : r.re < -1) :
    chapter7Entry10DistributionLeft phi n x r = chapter7Entry10ZetaSide n r := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hr0 : r.re < 0 := by linarith
  have hrne : r ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hr
    linarith
  have hA := ch7_zeta_hasSum r hr
  have hG : HasSum (fun j : ℕ => (n : ℂ) ^ r * Complex.cpow (j + 1 : ℂ) r)
      ((n : ℂ) ^ r * riemannZeta (-r)) := hA.mul_left ((n : ℂ) ^ r)
  have hHk : ∀ k : ℕ, HasSum
      (fun j : ℕ => (n : ℂ) ^ r * Complex.cpow ((j + 1 : ℂ) + ((x - k) / n)) r)
      ((n : ℂ) ^ r * (riemannZeta (-r) - phi r ((x - k) / n))) := fun k =>
    (ch7_shift_hasSum r phi hphi_series hr _).mul_left ((n : ℂ) ^ r)
  have hNPT : ∀ k : ℕ, HasSum
      (fun j : ℕ => (n : ℂ) ^ r * chapter7PowerDifferenceTerm r ((x - k) / n) j)
      ((n : ℂ) ^ r * phi r ((x - k) / n)) := fun k =>
    (hphi_series r _ hr0).mul_left ((n : ℂ) ^ r)
  have hkval : ∀ k : ℕ, (n : ℂ) ^ r * phi r ((x - k) / n)
      = (n : ℂ) ^ r * riemannZeta (-r)
        - ∑' (j : ℕ), ((n : ℂ) ^ r * Complex.cpow ((j + 1 : ℂ) + ((x - k) / n)) r) := by
    intro k
    have hGH : HasSum (fun j : ℕ => (n : ℂ) ^ r * Complex.cpow (j + 1 : ℂ) r
        - (n : ℂ) ^ r * Complex.cpow ((j + 1 : ℂ) + ((x - k) / n)) r)
        ((n : ℂ) ^ r * riemannZeta (-r)
          - (n : ℂ) ^ r * (riemannZeta (-r) - phi r ((x - k) / n))) :=
      hG.sub (hHk k)
    have hcong : HasSum
        (fun j : ℕ => (n : ℂ) ^ r * chapter7PowerDifferenceTerm r ((x - k) / n) j)
        ((n : ℂ) ^ r * riemannZeta (-r)
          - (n : ℂ) ^ r * (riemannZeta (-r) - phi r ((x - k) / n))) := by
      refine HasSum.congr_fun hGH (fun j => ?_)
      show (n : ℂ) ^ r * chapter7PowerDifferenceTerm r ((x - k) / n) j = _
      unfold chapter7PowerDifferenceTerm
      ring
    have huniq := HasSum.unique hcong (hNPT k)
    rw [(hHk k).tsum_eq]
    exact huniq.symm
  have hB : HasSum (fun j : ℕ => Complex.cpow ((j + 1 : ℂ) + x) r)
      (riemannZeta (-r) - phi r x) := ch7_shift_hasSum r phi hphi_series hr x
  have hBsum : Summable (fun m : ℕ => Complex.cpow ((m + 1 : ℂ) + x) r) :=
    hB.summable
  have hBe : Summable (fun p : Fin n × ℕ =>
      Complex.cpow ((ch7Reindex n hn p + 1 : ℂ) + x) r) :=
    hBsum.comp_injective (ch7Reindex n hn).injective
  have hfib : ∀ k : Fin n,
      (∑' (j : ℕ), ((n : ℂ) ^ r * Complex.cpow ((j + 1 : ℂ) + ((x - (k : ℕ)) / n)) r))
        = (∑' (j : ℕ), Complex.cpow ((ch7Reindex n hn (k, j) + 1 : ℂ) + x) r) :=
    fun k => tsum_congr (fun j => ch7_fiber_eq n hn x r hrne hnC k j)
  have hRe : (∑ k ∈ range n,
        ∑' (j : ℕ), ((n : ℂ) ^ r * Complex.cpow ((j + 1 : ℂ) + ((x - k) / n)) r))
      = riemannZeta (-r) - phi r x := by
    calc (∑ k ∈ range n,
            ∑' (j : ℕ), ((n : ℂ) ^ r * Complex.cpow ((j + 1 : ℂ) + ((x - k) / n)) r))
        = ∑ k : Fin n, ∑' (j : ℕ),
            ((n : ℂ) ^ r * Complex.cpow ((j + 1 : ℂ) + ((x - (k : ℕ)) / n)) r) :=
          (Fin.sum_univ_eq_sum_range
            (fun k : ℕ => ∑' (j : ℕ), ((n : ℂ) ^ r * Complex.cpow ((j + 1 : ℂ) + ((x - k) / n)) r)) n).symm
      _ = ∑ k : Fin n, ∑' (j : ℕ),
            Complex.cpow ((ch7Reindex n hn (k, j) + 1 : ℂ) + x) r :=
          Finset.sum_congr rfl (fun k _ => hfib k)
      _ = ∑' (k : Fin n), ∑' (j : ℕ),
            Complex.cpow ((ch7Reindex n hn (k, j) + 1 : ℂ) + x) r :=
          (tsum_fintype _).symm
      _ = ∑' (p : Fin n × ℕ),
            Complex.cpow ((ch7Reindex n hn p + 1 : ℂ) + x) r :=
          (hBe.tsum_prod).symm
      _ = ∑' (m : ℕ), Complex.cpow ((m + 1 : ℂ) + x) r :=
          Equiv.tsum_eq (ch7Reindex n hn)
            (fun m : ℕ => Complex.cpow ((m + 1 : ℂ) + x) r)
      _ = riemannZeta (-r) - phi r x := hB.tsum_eq
  have hNpow : n • ((n : ℂ) ^ r * riemannZeta (-r))
      = (n : ℂ) ^ (r + 1) * riemannZeta (-r) := by
    rw [nsmul_eq_mul]
    have h : (n : ℂ) * (n : ℂ) ^ r = (n : ℂ) ^ (r + 1) := by
      calc (n : ℂ) * (n : ℂ) ^ r
          = (n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ r := by rw [Complex.cpow_one]
        _ = (n : ℂ) ^ (1 + r) := (Complex.cpow_add 1 r hnC).symm
        _ = (n : ℂ) ^ (r + 1) := by rw [add_comm (1 : ℂ) r]
    rw [← mul_assoc, h]
  have hsumval : (∑ k ∈ range n, ((n : ℂ) ^ r * phi r ((x - k) / n)))
      = (n : ℂ) ^ (r + 1) * riemannZeta (-r) - (riemannZeta (-r) - phi r x) := by
    have e1 : (∑ k ∈ range n, ((n : ℂ) ^ r * phi r ((x - k) / n)))
        = ∑ k ∈ range n, ((n : ℂ) ^ r * riemannZeta (-r)
          - ∑' (j : ℕ), ((n : ℂ) ^ r * Complex.cpow ((j + 1 : ℂ) + ((x - k) / n)) r)) :=
      Finset.sum_congr rfl (fun k _ => hkval k)
    rw [e1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, hNpow, hRe]
  show phi r x - (n : ℂ) ^ r * (∑ k ∈ range n, phi r ((x - k) / n))
    = (1 - (n : ℂ) ^ (r + 1)) * riemannZeta (-r)
  rw [Finset.mul_sum (Finset.range n) (fun k => phi r ((x - k) / n)) ((n : ℂ) ^ r),
    hsumval]
  ring

/-- **Ramanujan's distribution relation for the power-difference function.** Let
$\varphi : \mathbb{C} \times \mathbb{C} \to \mathbb{C}$, written $(r, x) \mapsto \varphi_r(x)$, be
such that for every $x \in \mathbb{C}$ the function $r \mapsto \varphi_r(x)$ is meromorphic on
$\mathbb{C}$, and such that for all $r, x \in \mathbb{C}$ with $\operatorname{Re} r < 0$ the
series $\sum_{j \ge 0} \bigl((j + 1)^r - (j + 1 + x)^r\bigr)$ converges absolutely with sum
$\varphi_r(x)$. Let $n$ be a positive integer and $x \in \mathbb{C}$. Then the functions
$L(r) = \varphi_r(x) - n^r \sum_{k=0}^{n-1} \varphi_r\bigl((x - k)/n\bigr)$ and
$Z(r) = (1 - n^{r+1})\,\zeta(-r)$ are meromorphic on $\mathbb{C}$, and $L(r) = Z(r)$ for all
$r \in \mathbb{C}$ outside a closed discrete subset of $\mathbb{C}$.

Complex powers are principal-branch powers: $w^r = \exp(r \log w)$ for $w \ne 0$, and
$0^r = 0$ for $r \ne 0$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7, Entry 10.
Proves `Wanted` entry `ramanujan_part1_ch7_entry10_zeta2`.
-/
theorem ramanujan_part1_ch7_entry10_zeta2
    (phi : ℂ → ℂ → ℂ)
    (hphi_meromorphic : ∀ x, MeromorphicOn (fun r : ℂ => phi r x) Set.univ)
    (hphi_series : ∀ r x, r.re < 0 → HasSum (chapter7PowerDifferenceTerm r x) (phi r x))
    (n : ℕ) (hn : 0 < n) (x : ℂ) :
    MeromorphicOn (chapter7Entry10DistributionLeft phi n x) Set.univ ∧
      MeromorphicOn (chapter7Entry10ZetaSide n) Set.univ ∧
      chapter7Entry10DistributionLeft phi n x =ᶠ[codiscrete ℂ]
        chapter7Entry10ZetaSide n := by
  refine ⟨ch7_mero_distLeft phi hphi_meromorphic n hn x,
    Entry10Zeta4.meromorphicOn_chapter7Entry10ZetaSide n hn, ?_⟩
  have hsub := (ch7_mero_distLeft phi hphi_meromorphic n hn x).sub
    (Entry10Zeta4.meromorphicOn_chapter7Entry10ZetaSide n hn)
  have hvan : ∀ r : ℂ, r.re < -1 →
      (chapter7Entry10DistributionLeft phi n x - chapter7Entry10ZetaSide n) r = 0 := by
    intro r hr
    rw [Pi.sub_apply]
    exact sub_eq_zero.mpr (ch7_eq_of_re_lt phi hphi_series n hn x r hr)
  have hx₀ : ((-2 : ℝ) : ℂ).re < -1 := by
    rw [Complex.ofReal_re]
    norm_num
  have hSmem : Complex.re ⁻¹' Set.Iio (-1 : ℝ) ∈ nhds ((-2 : ℝ) : ℂ) :=
    (isOpen_Iio.preimage Complex.continuous_re).mem_nhds (by
      simp only [Set.mem_preimage, Set.mem_Iio]
      exact hx₀)
  have hord0 : meromorphicOrderAt
      (chapter7Entry10DistributionLeft phi n x - chapter7Entry10ZetaSide n)
      ((-2 : ℝ) : ℂ) = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    refine (Filter.eventually_of_mem hSmem (fun z hz => ?_)).filter_mono
      nhdsWithin_le_nhds
    exact hvan z (by
      simp only [Set.mem_preimage, Set.mem_Iio] at hz
      exact hz)
  have hordAll : ∀ y : ℂ, meromorphicOrderAt
      (chapter7Entry10DistributionLeft phi n x - chapter7Entry10ZetaSide n) y = ⊤ :=
    fun y => hsub.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ _) (Set.mem_univ _) hord0
  rw [eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE]
  intro y
  have hloc := meromorphicOrderAt_eq_top_iff.mp (hordAll y)
  filter_upwards [hloc] with z hz
  rw [Pi.sub_apply] at hz
  exact sub_eq_zero.mp hz

end

/-- Compatibility alias for the former `Entry10Zeta2.chapter7PowerDifferenceTerm`.

For new code, use `MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm`
directly. -/
noncomputable abbrev chapter7PowerDifferenceTerm (r x : ℂ) (j : ℕ) : ℂ :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm r x j

end Entry10Zeta2

end MathlibExt.Analysis.Ramanujan.Part1Ch7
