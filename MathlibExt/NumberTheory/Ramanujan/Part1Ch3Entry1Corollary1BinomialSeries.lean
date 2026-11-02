/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 1, Corollary 1

Binomial-series specialization of the Q-weighted Taylor-shift identity.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry1Corollary1BinomialSeries

private theorem smeval_descPochhammer_eq_prod (r : ℂ) : ∀ n : ℕ,
    (descPochhammer ℤ n).smeval r = ∏ j ∈ Finset.range n, (r - (j : ℂ)) := by
  intro n
  induction n with
  | zero =>
    simp [descPochhammer_zero]
  | succ n ih =>
    rw [descPochhammer_succ_right, Polynomial.smeval_mul ℤ _ _ r, ih]
    have hX : (Polynomial.X : Polynomial ℤ).smeval r = r := by
      rw [Polynomial.smeval_X ℤ r]
      simp
    have hnat : ((n : Polynomial ℤ)).smeval r = (n : ℂ) := by
      rw [Polynomial.smeval_natCast ℤ r n]
      simp
    rw [Polynomial.smeval_sub ℤ _ _ r, hX, hnat]
    rw [Finset.prod_range_succ]

private theorem choose_eq_prod_div (r : ℂ) (n : ℕ) :
    Ring.choose r n = (∏ j ∈ Finset.range n, (r - (j : ℂ))) / (Nat.factorial n : ℂ) := by
  rw [Ring.choose_eq_smul, smeval_descPochhammer_eq_prod]
  simp only [smul_eq_mul]
  rw [div_eq_mul_inv, mul_comm]

private theorem binom_hasSum (r x : ℂ) (hx : ‖x‖ < 1) :
    HasSum (fun m : ℕ => (∏ j ∈ Finset.range m, (r - (j : ℂ))) * x ^ m / (Nat.factorial m : ℂ))
      (Complex.exp (r * Complex.log (1 + x))) := by
  have hball := Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := r)
  have hxmem : x ∈ Metric.eball (0 : ℂ) (1 : ENNReal) := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff]
    have h1 : ‖x‖₊ < (1 : NNReal) := by exact_mod_cast hx
    exact h1
  have hHas := hball.hasSum_sub hxmem
  simp only [sub_zero] at hHas
  have h1x : (1 : ℂ) + x ≠ 0 := by
    intro h
    have hx1 : x = -1 := by linear_combination h
    rw [hx1] at hx
    simp at hx
  have hcpow : ((1 : ℂ) + x) ^ r = Complex.exp (r * Complex.log (1 + x)) := by
    rw [Complex.cpow_def_of_ne_zero h1x, mul_comm]
  rw [hcpow] at hHas
  have hterm : ∀ m : ℕ, (binomialSeries ℂ r m) (fun _ => x) =
      (∏ j ∈ Finset.range m, (r - (j : ℂ))) * x ^ m / (Nat.factorial m : ℂ) := by
    intro m
    rw [binomialSeries_apply, choose_eq_prod_div]
    simp only [smul_eq_mul]
    have hprod : (List.ofFn (fun _ : Fin m => x)).prod = x ^ m := by
      rw [List.ofFn_const, List.prod_replicate]
    rw [hprod]
    ring
  exact hHas.congr_fun (fun m => (hterm m).symm)

/-- Falling factorial splits: `(n)_{k+m} = (n)_k * (n-k)_m`. -/
private theorem fall_add (n : ℂ) (k m : ℕ) :
    (∏ j ∈ Finset.range (k + m), (n - (j : ℂ))) =
      (∏ j ∈ Finset.range k, (n - (j : ℂ))) *
        ∏ j ∈ Finset.range m, ((n - (k : ℂ)) - (j : ℂ)) := by
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  push_cast
  ring

/-- Reindexing: pairs by (sum, the pair itself with proof). -/
private def pairEquiv : ℕ × ℕ ≃ Σ _k : ℕ, {p : ℕ × ℕ // p.1 + p.2 = _k} where
  toFun p := ⟨p.1 + p.2, p, rfl⟩
  invFun q := q.2.1
  left_inv p := by
    obtain ⟨a, b⟩ := p
    rfl
  right_inv q := by
    obtain ⟨k, ⟨p, hp⟩⟩ := q
    cases hp
    rfl

/-- Each fiber is finite. -/
private def fiberEquiv (k : ℕ) : {p : ℕ × ℕ // p.1 + p.2 = k} ≃ Fin (k + 1) where
  toFun q := ⟨q.1.1, by
    have hle : q.1.1 ≤ k := by omega
    exact Nat.lt_succ_of_le hle⟩
  invFun j := ⟨(j.1, k - j.1), by
    have hj : j.1 ≤ k := Nat.le_of_lt_succ j.2
    show (j.1, k - j.1).1 + (j.1, k - j.1).2 = k
    rw [Nat.add_sub_cancel' hj]⟩
  left_inv q := by
    obtain ⟨⟨a, b⟩, hp⟩ := q
    apply Subtype.ext
    show (a, k - a) = (a, b)
    have h : k - a = b := by omega
    rw [h]
  right_inv j := by
    obtain ⟨j, hj⟩ := j
    rfl

/-- **Ramanujan's binomial series transformation without the radius hypothesis.** Let $n$ and $x$
be complex numbers with $|x| < 1$, write $(n)_k = n(n-1)\cdots(n-k+1)$ for the falling factorial
(with $(n)_0 = 1$), and let $Q_0, Q_1, Q_2, \ldots$ be complex numbers such that the double series
$$\sum_{j, m \ge 0} \frac{Q_j\, (n)_{j+m}\, x^{j+m}}{m!}$$
is absolutely summable. Then the series
$$\sum_{k=0}^{\infty} \Bigl(\sum_{j=0}^{k} \frac{Q_j}{(k-j)!}\Bigr) (n)_k\, x^k$$
and
$$\sum_{k=0}^{\infty} Q_k\, (n)_k\, x^k\, (1 + x)^{n-k}$$
converge unconditionally to the same sum, where $(1 + x)^{n-k} = e^{(n-k) \log(1+x)}$ with the
principal branch of the logarithm. -/
theorem ramanujan_part1_ch3_entry1_corollary1_binomial_series_general (n x : ℂ)
    (Q : ℕ → ℂ)
        (hx : ‖x‖ < 1)
                (hsum : Summable (fun p : ℕ × ℕ => Q p.1 *
                    (∏ j ∈ Finset.range (p.1 + p.2), (n - (j : ℂ))) * x ^ (p.1 + p.2) /
                        (Nat.factorial p.2 : ℂ))) :
    ∃ s : ℂ,
        HasSum (fun k : ℕ => (∑ j ∈ Finset.range (k + 1), Q j / (Nat.factorial (k - j) : ℂ)) *
            (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k) s ∧
            HasSum (fun k : ℕ => Q k * (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k *
                Complex.exp ((n - (k : ℂ)) * Complex.log (1 + x))) s := by
  classical
  set F : ℕ × ℕ → ℂ := fun p => Q p.1 *
      (∏ j ∈ Finset.range (p.1 + p.2), (n - (j : ℂ))) * x ^ (p.1 + p.2) /
          (Nat.factorial p.2 : ℂ) with hF
  have hsumF : Summable F := hsum
  refine ⟨∑' p, F p, ?_, ?_⟩
  · -- First series: antidiagonal grouping.
    have hsum_eq : ∀ k : ℕ, (∑ j : Fin (k + 1), F (j.1, k - j.1)) =
        (∑ j ∈ Finset.range (k + 1), Q j / (Nat.factorial (k - j) : ℂ)) *
          (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k := by
      intro k
      have hrr : (∑ j : Fin (k + 1), F (j.1, k - j.1)) =
          ∑ j ∈ Finset.range (k + 1), F (j, k - j) :=
        Fin.sum_univ_eq_sum_range (fun a : ℕ => F (a, k - a)) (k + 1)
      rw [hrr, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have hle : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hjm : j + (k - j) = k := Nat.add_sub_cancel' hle
      have hfac : ((Nat.factorial (k - j) : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero _
      simp only [hF]
      rw [hjm]
      field_simp
    have hfib : ∀ k : ℕ, HasSum
        (fun c : {p : ℕ × ℕ // p.1 + p.2 = k} => F (c.1 : ℕ × ℕ))
        ((∑ j ∈ Finset.range (k + 1), Q j / (Nat.factorial (k - j) : ℂ)) *
          (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k) := by
      intro k
      have hft : Fintype {p : ℕ × ℕ // p.1 + p.2 = k} :=
        Fintype.ofEquiv (Fin (k + 1)) (fiberEquiv k).symm
      have hfin : HasSum (fun c : {p : ℕ × ℕ // p.1 + p.2 = k} => F (c.1 : ℕ × ℕ))
          (∑ c : {p : ℕ × ℕ // p.1 + p.2 = k}, F (c.1 : ℕ × ℕ)) :=
        hasSum_fintype _
      have hsub : (∑ c : {p : ℕ × ℕ // p.1 + p.2 = k}, F (c.1 : ℕ × ℕ)) =
          ∑ j : Fin (k + 1), F (j.1, k - j.1) := by
        apply Fintype.sum_equiv (fiberEquiv k)
          (fun c : {p : ℕ × ℕ // p.1 + p.2 = k} => F (c.1 : ℕ × ℕ))
          (fun j : Fin (k + 1) => F (j.1, k - j.1))
        intro c
        obtain ⟨⟨a, b⟩, hp⟩ := c
        show F (a, b) = F (a, k - a)
        have h : k - a = b := by omega
        rw [h]
      rw [hsub, hsum_eq k] at hfin
      exact hfin
    have hbase := (Equiv.hasSum_iff pairEquiv.symm).mpr hsumF.hasSum
    have hcomp : HasSum (fun q : Σ _k : ℕ, {p : ℕ × ℕ // p.1 + p.2 = _k} => F (q.2.1 : ℕ × ℕ))
        (∑' p, F p) := by
      refine hbase.congr_fun (fun q => ?_)
      rfl
    exact hcomp.sigma (fun k => hfib k)
  · -- Second series: iterate over first component, binomial in second.
    have hfib : ∀ k : ℕ, HasSum (fun m : ℕ => F (k, m))
        (Q k * (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k *
          Complex.exp ((n - (k : ℂ)) * Complex.log (1 + x))) := by
      intro k
      have h := binom_hasSum (n - (k : ℂ)) x hx
      have hmul : HasSum
          (fun m : ℕ => (∏ j ∈ Finset.range m, ((n - (k : ℂ)) - (j : ℂ))) * x ^ m /
            (Nat.factorial m : ℂ) * (Q k * (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k))
          (Complex.exp ((n - (k : ℂ)) * Complex.log (1 + x)) *
            (Q k * (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k)) :=
        h.mul_right _
      have heq1 : ∀ m : ℕ, F (k, m) =
          (∏ j ∈ Finset.range m, ((n - (k : ℂ)) - (j : ℂ))) * x ^ m /
            (Nat.factorial m : ℂ) * (Q k * (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k) := by
        intro m
        simp only [hF]
        rw [fall_add, pow_add]
        have hfac : ((Nat.factorial m : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero _
        field_simp
      have heq2 : Complex.exp ((n - (k : ℂ)) * Complex.log (1 + x)) *
          (Q k * (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k) =
          Q k * (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k *
            Complex.exp ((n - (k : ℂ)) * Complex.log (1 + x)) := by
        ring
      rw [heq2] at hmul
      exact hmul.congr_fun heq1
    exact hsumF.hasSum.prod_fiberwise hfib

set_option linter.unusedVariables false in
/-- **Ramanujan's binomial series transformation (Chapter 3, Entry 1, Corollary 1).** Let $n$ and
$x$ be complex numbers with $|x| < 1$, write $(n)_k = n(n-1)\cdots(n-k+1)$ for the falling
factorial (with $(n)_0 = 1$), and let $Q_0, Q_1, Q_2, \ldots$ be complex numbers such that, for
some $R > 0$, the power series $\sum_k Q_k z^k$ converges absolutely for every complex $z$ with
$|z| < R$. Suppose that the double series
$$\sum_{j, m \ge 0} \frac{Q_j\, (n)_{j+m}\, x^{j+m}}{m!}$$
is absolutely summable. Then the series
$$\sum_{k=0}^{\infty} \Bigl(\sum_{j=0}^{k} \frac{Q_j}{(k-j)!}\Bigr) (n)_k\, x^k$$
and
$$\sum_{k=0}^{\infty} Q_k\, (n)_k\, x^k\, (1 + x)^{n-k}$$
converge unconditionally to the same sum, where $(1 + x)^{n-k} = e^{(n-k) \log(1+x)}$ with the
principal branch of the logarithm.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 1, Corollary 1, printed p.
    45 / PDF p. 55.
Proves `Wanted` entry `ramanujan_part1_ch3_entry1_corollary1_binomial_series`.
-/
theorem ramanujan_part1_ch3_entry1_corollary1_binomial_series (n x : ℂ)
    (Q : ℕ → ℂ)
        (hx : ‖x‖ < 1)
            (hQ : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, ‖z‖ < R → Summable (fun k : ℕ => Q k * z ^ k))
                (hsum : Summable (fun p : ℕ × ℕ => Q p.1 *
                    (∏ j ∈ Finset.range (p.1 + p.2), (n - (j : ℂ))) * x ^ (p.1 + p.2) /
                        (Nat.factorial p.2 : ℂ))) :
    ∃ s : ℂ,
        HasSum (fun k : ℕ => (∑ j ∈ Finset.range (k + 1), Q j / (Nat.factorial (k - j) : ℂ)) *
            (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k) s ∧
            HasSum (fun k : ℕ => Q k * (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k *
                Complex.exp ((n - (k : ℂ)) * Complex.log (1 + x))) s :=
  by apply ramanujan_part1_ch3_entry1_corollary1_binomial_series_general <;> assumption

end Entry1Corollary1BinomialSeries

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
