/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Analytic core of Poisson convergence

If `p_{n,1}, …, p_{n,k(n)}` are nonnegative numbers with
`∑_i p_{n,i} → λ` and `max_i p_{n,i} → 0`, then for every fixed `j`,
the Poisson-binomial mass
`∑_{|A| = j} ∏_{i ∈ A} p_{n,i} · ∏_{i ∉ A} (1 - p_{n,i})`
converges to the Poisson mass `λ ^ j e ^ (-λ) / j !`.

## Source

This formalizes `elem_symm_poly_tendsto_poisson` in
`v1/Atlas/TheoryOfProbability/code/PoissonConvergence.lean`, the
analytic core of the target "Theorem (Poisson convergence)"
(Lecture 17) in `v1/Atlas/TheoryOfProbability/targets.yaml`. That
target is proved in v1 by combining this lemma with the
fully proved `bernoulli_sum_pmf` in the same file; the pmf lemma
itself is ported in an earlier batch
(`ProbabilityTheory.bernoulli_sum_pmf`), so it is not reproved here,
and the full Poisson convergence theorem (pmf convergence for sums of
independent Bernoulli variables) follows from the two pieces.

## Correction to the v1 statement (please read)

The v1 statement is **false as written**: it does not assume the
`p_{n,i}` are nonnegative, but its hypotheses
(`max_i p_{n,i} → 0` in the one-sided sense `p_{n,i} < ε` eventually,
and `∑_i p_{n,i} → λ ≥ 0`) do not force nonnegativity.
Counterexample: take `k(n) = 2 n ^ 2` and, for `n ≥ 1`,
`p_{n,i} = 1 / n` for the first `n ^ 2` indices and
`p_{n,i} = -1 / n` for the remaining `n ^ 2` indices. Then
`∑_i p_{n,i} = 0 → λ = 0` and `p_{n,i} ≤ 1 / n < ε` eventually,
so the v1 hypotheses hold with `λ = 0`. But for `j = 1` and `n ≥ 2` the
Poisson-binomial mass is
`∏_i (1 - p_{n,i}) · ∑_i p_{n,i} / (1 - p_{n,i})
  = (1 - 1 / n ^ 2) ^ (n ^ 2) · 2 n ^ 2 / (n ^ 2 - 1) → 2 / e ≠ 0`,
while the Poisson mass at `λ = 0`, `j = 1` is `0`.

This file therefore adds the hypothesis `0 ≤ p_{n,i}` (which holds
in the Bernoulli application, where `p_{n,i}` is a probability).
With it, the classical proof goes through: Newton's identities give
the convergence of the elementary symmetric sums
`e_j(p_n) → λ ^ j / j !`, the product `∏_i (1 - p_{n,i}) → e ^ (-λ)`
follows from the Taylor bound
`|log (1 - x) + x| ≤ 2 x ^ 2` for `|x| ≤ 1 / 2`, and the
Poisson-binomial mass is squeezed between
`(∏_i (1 - p_{n,i})) · e_j(p_n)` and that quantity divided by
`(1 - max_i p_{n,i}) ^ j`.

## Main results

* `ProbabilityTheory.elem_symm_poly_tendsto_poisson`: the corrected
  analytic core of Poisson convergence, as stated above. v1 writes the
  limit as `poissonPMFReal lam j`; that constant is deprecated in the
  Mathlib used here (in favor of `poissonMeasure`, which has a different
  type), so the limit is stated in its unfolded form
  `exp (-λ) * λ ^ j / j !`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Real Topology
open scoped ENNReal NNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {k : ℕ → ℕ} {p : (n : ℕ) → Fin (k n) → ℝ} {lam : ℝ≥0}

/-- The maximum of the `n`-th row `p n`, as the supremum of its range. -/
private noncomputable def rowMax (p : (n : ℕ) → Fin (k n) → ℝ) (n : ℕ) : ℝ :=
  sSup (Set.range (p n))

/-- The row maximum is nonnegative when the row is. -/
private theorem rowMax_nonneg (hp : ∀ n i, 0 ≤ p n i) (n : ℕ) : 0 ≤ rowMax p n := by
  by_cases hne : Nonempty (Fin (k n))
  · obtain ⟨i⟩ := hne
    exact (hp n i).trans (le_csSup (Set.Finite.bddAbove (Set.finite_range _)) ⟨i, rfl⟩)
  · have hrange : Set.range (p n) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun _ ⟨i, _⟩ => absurd ⟨i⟩ hne)
    rw [rowMax, hrange, Real.sSup_empty]

/-- Every entry of a row is at most the row maximum. -/
private theorem le_rowMax (n : ℕ) (i : Fin (k n)) : p n i ≤ rowMax p n :=
  le_csSup (Set.Finite.bddAbove (Set.finite_range _)) ⟨i, rfl⟩

/-- The row maximum is below `ε` if every entry is strictly below `ε`. -/
private theorem rowMax_lt_of_forall (n : ℕ) {ε : ℝ} (h : ∀ i : Fin (k n), p n i < ε)
    (hε : 0 < ε) : rowMax p n < ε := by
  by_cases hne : Nonempty (Fin (k n))
  · obtain ⟨i₀⟩ := hne
    have hmem : rowMax p n ∈ Set.range (p n) :=
      Set.Nonempty.csSup_mem ⟨p n i₀, ⟨i₀, rfl⟩⟩ (Set.finite_range _)
    obtain ⟨i, hi⟩ := hmem
    rw [← hi]
    exact h i
  · have hrange : Set.range (p n) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun _ ⟨i, _⟩ => absurd ⟨i⟩ hne)
    rw [rowMax, hrange, Real.sSup_empty]
    exact hε

/-- The row maximum tends to `0` when the one-sided maximum hypothesis holds. -/
private theorem tendsto_rowMax (hp : ∀ n i, 0 ≤ p n i)
    (hMax : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : Fin (k n), p n i < ε) :
    Filter.Tendsto (rowMax p) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hMax ε hε)
  exact ⟨N, fun n hn => by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (rowMax_nonneg hp n)]
    exact rowMax_lt_of_forall n (hN n hn) hε⟩

/-- The `j`-th elementary symmetric sum of a row. -/
private abbrev esymmSum {k : ℕ → ℕ} {n : ℕ} (q : Fin (k n) → ℝ) (j : ℕ) : ℝ :=
  ∑ A ∈ Finset.univ.powersetCard j, ∏ i ∈ A, q i

/-- The `m`-th power sum of a row. -/
private abbrev psumSum {k : ℕ → ℕ} {n : ℕ} (q : Fin (k n) → ℝ) (m : ℕ) : ℝ := ∑ i, (q i) ^ m

/-- Elementary symmetric sums are nonnegative for nonnegative rows. -/
private theorem esymmSum_nonneg {k : ℕ → ℕ} {n : ℕ} {q : Fin (k n) → ℝ}
    (hp : ∀ i, 0 ≤ q i) (j : ℕ) : 0 ≤ esymmSum q j := by
  apply Finset.sum_nonneg
  intro A _
  exact Finset.prod_nonneg (fun i _ => hp i)

/-- Power sums are nonnegative for nonnegative rows. -/
private theorem psumSum_nonneg {k : ℕ → ℕ} {n : ℕ} {q : Fin (k n) → ℝ}
    (hp : ∀ i, 0 ≤ q i) (m : ℕ) : 0 ≤ psumSum q m := by
  apply Finset.sum_nonneg
  intro i _
  exact pow_nonneg (hp i) m

/-- A sum over the antidiagonal with the top-left term removed, rewritten as a
range sum. -/
private theorem sum_filtered_antidiagonal (f : ℕ → ℕ → ℝ) (j : ℕ) :
    ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal j).filter (fun a => a.1 < j), f a.1 a.2
      = ∑ i ∈ Finset.range j, f i (j - i) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.HasAntidiagonal.antidiagonal j) (fun a => a.1 < j) (fun a => f a.1 a.2)
  have hnot : (Finset.HasAntidiagonal.antidiagonal j).filter (fun a => ¬ a.1 < j)
      = {(j, 0)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
      Finset.mem_singleton, Prod.mk.injEq, not_lt]
    constructor
    · rintro ⟨hab, haj⟩; omega
    · rintro ⟨rfl, rfl⟩; omega
  rw [hnot, Finset.sum_singleton] at hsplit
  have hrange := Finset.Nat.sum_antidiagonal_eq_sum_range_succ f j
  rw [Finset.sum_range_succ] at hrange
  simp only [Nat.sub_self] at hrange
  dsimp only at hsplit
  linarith [hsplit, hrange]

/-- Newton's identities, evaluated at a row: the `j`-th elementary symmetric
sum is related to the lower ones and to the power sums. The only surviving
term with a first power sum is `e_{j-1} · psum_1`; the rest involve power
sums of order at least `2`. -/
private theorem newton_identity {k : ℕ → ℕ} {n : ℕ} (q : Fin (k n) → ℝ) (j : ℕ) (hj : 1 ≤ j) :
    (j : ℝ) * esymmSum q j =
      esymmSum q (j - 1) * psumSum q 1 +
      (-1 : ℝ) ^ (j + 1) * ∑ i ∈ Finset.range (j - 1),
        (-1 : ℝ) ^ i * esymmSum q i * psumSum q (j - i) := by
  have hNewton := MvPolynomial.mul_esymm_eq_sum (Fin (k n)) ℝ j
  have h2 := congrArg (MvPolynomial.aeval q) hNewton
  have hpsum : ∀ m : ℕ,
      MvPolynomial.aeval q (MvPolynomial.psum (Fin (k n)) ℝ m) = psumSum q m := by
    intro m
    simp [MvPolynomial.psum, psumSum, map_sum]
  simp only [map_sum, map_mul, map_natCast, map_pow, map_neg, map_one,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Finset.esymm_map_val, hpsum] at h2
  have hanti := sum_filtered_antidiagonal
    (fun i m => (-1 : ℝ) ^ i * esymmSum q i * psumSum q m) j
  rw [hanti] at h2
  have hsplit : ∑ i ∈ Finset.range j,
        (-1 : ℝ) ^ i * esymmSum q i * psumSum q (j - i)
      = ∑ i ∈ Finset.range (j - 1),
          (-1 : ℝ) ^ i * esymmSum q i * psumSum q (j - i)
        + (-1 : ℝ) ^ (j - 1) * esymmSum q (j - 1) * psumSum q 1 := by
    nth_rewrite 1 [← Nat.sub_add_cancel hj]
    rw [Finset.sum_range_succ]
    have h1 : j - (j - 1) = 1 := by omega
    rw [h1]
  rw [hsplit] at h2
  have hsign : (-1 : ℝ) ^ (j + 1) * ((-1 : ℝ) ^ (j - 1) * esymmSum q (j - 1) * psumSum q 1)
      = esymmSum q (j - 1) * psumSum q 1 := by
    have hpow : (-1 : ℝ) ^ (j + 1) * (-1 : ℝ) ^ (j - 1) = 1 := by
      rw [← pow_add]
      have hEq : j + 1 + (j - 1) = 2 * j := by omega
      rw [hEq]
      exact Even.neg_one_pow ⟨j, by ring⟩
    calc (-1 : ℝ) ^ (j + 1) * ((-1 : ℝ) ^ (j - 1) * esymmSum q (j - 1) * psumSum q 1)
        = ((-1 : ℝ) ^ (j + 1) * (-1 : ℝ) ^ (j - 1)) * (esymmSum q (j - 1) * psumSum q 1) := by
          ring
      _ = esymmSum q (j - 1) * psumSum q 1 := by rw [hpow, one_mul]
  have hdist : (-1 : ℝ) ^ (j + 1) * (∑ i ∈ Finset.range (j - 1),
        (-1 : ℝ) ^ i * esymmSum q i * psumSum q (j - i)
        + (-1 : ℝ) ^ (j - 1) * esymmSum q (j - 1) * psumSum q 1)
      = (-1 : ℝ) ^ (j + 1) * ∑ i ∈ Finset.range (j - 1),
          (-1 : ℝ) ^ i * esymmSum q i * psumSum q (j - i)
        + esymmSum q (j - 1) * psumSum q 1 := by
    rw [mul_add, hsign]
  rw [hdist] at h2
  rw [add_comm] at h2
  exact h2

/-- Power sums of order at least `2` tend to `0`: they are bounded by
`(rowMax) ^ (m - 1) * (row sum)`. -/
private theorem psum_tendsto_zero (hp : ∀ n i, 0 ≤ p n i)
    (hMax : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : Fin (k n), p n i < ε)
    (hSum : Filter.Tendsto (fun n => ∑ i : Fin (k n), p n i) atTop (𝓝 (lam : ℝ)))
    {m : ℕ} (hm : 2 ≤ m) :
    Filter.Tendsto (fun n => psumSum (p n) m) atTop (𝓝 0) := by
  have hRow : Filter.Tendsto (rowMax p) atTop (𝓝 0) := tendsto_rowMax hp hMax
  have hBound : Filter.Tendsto (fun n => (rowMax p n) ^ (m - 1) * ∑ i : Fin (k n), p n i)
      atTop (𝓝 0) := by
    have hPow : Filter.Tendsto (fun n => (rowMax p n) ^ (m - 1)) atTop (𝓝 (0 ^ (m - 1))) :=
      hRow.pow (m - 1)
    rw [zero_pow (by omega : m - 1 ≠ 0)] at hPow
    simpa using hPow.mul hSum
  apply squeeze_zero' _ _ hBound
  · filter_upwards with n
    exact psumSum_nonneg (hp n) m
  · filter_upwards with n
    calc psumSum (p n) m
        = ∑ i : Fin (k n), (p n i) ^ (m - 1) * p n i := by
          apply Finset.sum_congr rfl
          intro i _
          conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ m by omega), pow_succ]
      _ ≤ ∑ i : Fin (k n), (rowMax p n) ^ (m - 1) * p n i := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_right _ (hp n i)
          apply pow_le_pow_left₀ (hp n i) (le_rowMax n i) (m - 1)
      _ = (rowMax p n) ^ (m - 1) * ∑ i : Fin (k n), p n i := by
          rw [Finset.mul_sum]

/-- The product `∏_i (1 - p_{n,i})` tends to `e ^ (-λ)`: its logarithm is
`-∑ p_{n,i}` up to an error bounded by `2 ∑ p_{n,i} ^ 2`, which tends to `0`
by the Taylor bound `|log (1 - x) + x| ≤ 2 x ^ 2` for `|x| ≤ 1 / 2`. -/
private theorem prod_one_sub_tendsto (hp : ∀ n i, 0 ≤ p n i)
    (hMax : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : Fin (k n), p n i < ε)
    (hSum : Filter.Tendsto (fun n => ∑ i : Fin (k n), p n i) atTop (𝓝 (lam : ℝ))) :
    Filter.Tendsto (fun n => ∏ i : Fin (k n), (1 - p n i)) atTop
      (𝓝 (Real.exp (-(lam : ℝ)))) := by
  have hRow : Filter.Tendsto (rowMax p) atTop (𝓝 0) := tendsto_rowMax hp hMax
  have hSmall : ∀ᶠ n in atTop, rowMax p n < 1 / 2 :=
    hRow.eventually_lt_const (by norm_num)
  have hLogBound : ∀ {x : ℝ}, |x| ≤ 1 / 2 → |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
    intro x hx
    have h1 : |x| < 1 := lt_of_le_of_lt hx (by norm_num)
    have h := Real.abs_log_sub_add_sum_range_le h1 1
    simp only [Finset.sum_range_one, zero_add, Nat.cast_zero, pow_one, div_one] at h
    have h2 : (0 : ℝ) < 1 - |x| := by linarith [abs_nonneg x]
    have h3 : |x| ^ 2 / (1 - |x|) ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ h2, sq_abs]
      nlinarith [sq_nonneg x, abs_nonneg x]
    have h4 : |Real.log (1 - x) + x| = |x + Real.log (1 - x)| := by rw [add_comm]
    rw [h4]
    exact h.trans h3
  have hErr : Filter.Tendsto (fun n => ∑ i : Fin (k n), (Real.log (1 - p n i) + p n i))
      atTop (𝓝 0) := by
    have hSq : Filter.Tendsto (fun n => ∑ i : Fin (k n), (p n i) ^ 2) atTop (𝓝 0) :=
      psum_tendsto_zero hp hMax hSum le_rfl
    have hBound : Filter.Tendsto (fun n => 2 * ∑ i : Fin (k n), (p n i) ^ 2) atTop (𝓝 0) := by
      simpa using hSq.const_mul 2
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero' _ _ hBound
    · filter_upwards with n
      exact abs_nonneg _
    · filter_upwards [hSmall] with n hn
      calc |∑ i : Fin (k n), (Real.log (1 - p n i) + p n i)|
          ≤ ∑ i : Fin (k n), |Real.log (1 - p n i) + p n i| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin (k n), 2 * (p n i) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            apply hLogBound
            rw [abs_of_nonneg (hp n i)]
            exact (le_rowMax n i).trans hn.le
        _ = 2 * ∑ i : Fin (k n), (p n i) ^ 2 := by rw [Finset.mul_sum]
  have hLogSum : Filter.Tendsto (fun n => ∑ i : Fin (k n), Real.log (1 - p n i))
      atTop (𝓝 (-(lam : ℝ))) := by
    have hSplit : (fun n => ∑ i : Fin (k n), Real.log (1 - p n i))
        = (fun n => ∑ i : Fin (k n), (Real.log (1 - p n i) + p n i)
          - ∑ i : Fin (k n), p n i) := by
      ext n
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hSplit]
    have hLim : Filter.Tendsto (fun n => ∑ i : Fin (k n), (Real.log (1 - p n i) + p n i)
        - ∑ i : Fin (k n), p n i) atTop (𝓝 (0 - (lam : ℝ))) := hErr.sub hSum
    simpa using hLim
  have hProdEq : ∀ᶠ n in atTop,
      (∏ i : Fin (k n), (1 - p n i))
        = Real.exp (∑ i : Fin (k n), Real.log (1 - p n i)) := by
    filter_upwards [hSmall] with n hn
    rw [← Real.log_prod]
    · exact (Real.exp_log (Finset.prod_pos (fun i _ => by
        have hpi : p n i ≤ rowMax p n := le_rowMax n i
        linarith [hp n i]))).symm
    · intro i _
      have hpi : p n i ≤ rowMax p n := le_rowMax n i
      linarith [hp n i]
  exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hProdEq)
    ((Real.continuous_exp.tendsto (-(lam : ℝ))).comp hLogSum)

/-- The elementary symmetric sums converge to the Poisson coefficients:
`e_j(p_n) → λ ^ j / j !`. By strong induction on `j`, using Newton's
identities: the remainder involves only power sums of order at least `2`,
which tend to `0`. -/
private theorem esymm_tendsto (hp : ∀ n i, 0 ≤ p n i)
    (hMax : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : Fin (k n), p n i < ε)
    (hSum : Filter.Tendsto (fun n => ∑ i : Fin (k n), p n i) atTop (𝓝 (lam : ℝ))) :
    ∀ j : ℕ, Filter.Tendsto (fun n => esymmSum (p n) j) atTop
      (𝓝 ((lam : ℝ) ^ j / (Nat.factorial j : ℝ))) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j IH =>
    cases j with
    | zero =>
      simp [esymmSum]
    | succ j =>
      have hNewton : ∀ n, ((j + 1 : ℕ) : ℝ) * esymmSum (p n) (j + 1)
          = esymmSum (p n) j * (∑ i : Fin (k n), p n i)
            + (-1 : ℝ) ^ (j + 2) * ∑ i ∈ Finset.range j,
              (-1 : ℝ) ^ i * esymmSum (p n) i * psumSum (p n) (j + 1 - i) := by
        intro n
        have h := newton_identity (p n) (j + 1) (Nat.succ_pos j)
        rw [Nat.add_sub_cancel] at h
        have hpsum1 : psumSum (p n) 1 = ∑ i : Fin (k n), p n i := by
          simp [psumSum]
        rw [hpsum1] at h
        simpa using h
      have hRem : Filter.Tendsto (fun n => ∑ i ∈ Finset.range j,
          (-1 : ℝ) ^ i * esymmSum (p n) i * psumSum (p n) (j + 1 - i)) atTop (𝓝 0) := by
        have hSum0 : Filter.Tendsto (fun n => ∑ i ∈ Finset.range j,
            (-1 : ℝ) ^ i * esymmSum (p n) i * psumSum (p n) (j + 1 - i)) atTop
            (𝓝 (∑ i ∈ Finset.range j,
              ((-1 : ℝ) ^ i * ((lam : ℝ) ^ i / (Nat.factorial i : ℝ))) * 0)) := by
          apply tendsto_finsetSum
          intro i hi
          have hi_lt : i < j + 1 := by
            have hmem := Finset.mem_range.mp hi
            omega
          have hEi := IH i hi_lt
          have hP : Filter.Tendsto (fun n => psumSum (p n) (j + 1 - i)) atTop (𝓝 0) :=
            psum_tendsto_zero hp hMax hSum (by
              have hmem := Finset.mem_range.mp hi
              omega)
          exact ((tendsto_const_nhds (x := (-1 : ℝ) ^ i)).mul hEi).mul hP
        simp only [mul_zero, Finset.sum_const_zero] at hSum0
        exact hSum0
      have hMain : Filter.Tendsto (fun n => ((j + 1 : ℕ) : ℝ) * esymmSum (p n) (j + 1))
          atTop (𝓝 ((lam : ℝ) ^ (j + 1) / (Nat.factorial j : ℝ))) := by
        have hLHS : Filter.Tendsto (fun n => ((j + 1 : ℕ) : ℝ) * esymmSum (p n) (j + 1))
            atTop (𝓝 ((lam : ℝ) ^ j / (Nat.factorial j : ℝ) * (lam : ℝ)
              + (-1 : ℝ) ^ (j + 2) * 0)) := by
          apply Filter.Tendsto.congr' _ ((IH j (Nat.lt_succ_self j)).mul hSum |>.add
            ((tendsto_const_nhds (x := (-1 : ℝ) ^ (j + 2))).mul hRem))
          filter_upwards with n
          exact (hNewton n).symm
        have hEq : (lam : ℝ) ^ j / (Nat.factorial j : ℝ) * (lam : ℝ)
              + (-1 : ℝ) ^ (j + 2) * 0
            = (lam : ℝ) ^ (j + 1) / (Nat.factorial j : ℝ) := by
          rw [mul_zero, add_zero, pow_succ, div_mul_eq_mul_div]
        rwa [hEq] at hLHS
      have hDiv : Filter.Tendsto (fun n => esymmSum (p n) (j + 1)) atTop
          (𝓝 (((j + 1 : ℕ) : ℝ)⁻¹ * ((lam : ℝ) ^ (j + 1) / (Nat.factorial j : ℝ)))) := by
        apply Filter.Tendsto.congr' _ (tendsto_const_nhds.mul hMain)
        filter_upwards with n
        have hne : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      have hGoal : ((j + 1 : ℕ) : ℝ)⁻¹ * ((lam : ℝ) ^ (j + 1) / (Nat.factorial j : ℝ))
          = (lam : ℝ) ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        field_simp
      rwa [hGoal] at hDiv

/-- The Poisson-binomial mass of the `n`-th row at `j`. -/
private abbrev probSum {k : ℕ → ℕ} {n : ℕ} (q : Fin (k n) → ℝ) (j : ℕ) : ℝ :=
  ∑ A ∈ Finset.univ.powersetCard j,
    (∏ i ∈ A, q i) * (∏ i ∈ Finset.univ \ A, (1 - q i))

/-- Splitting a product over the whole index set into the product over a
subset's complement times the product over the subset. -/
private theorem prod_univ_eq_prod_sdiff_mul {k : ℕ → ℕ} {n : ℕ} (q : Fin (k n) → ℝ)
    (A : Finset (Fin (k n))) :
    (∏ i : Fin (k n), (1 - q i))
      = (∏ i ∈ Finset.univ \ A, (1 - q i)) * (∏ i ∈ A, (1 - q i)) := by
  conv_lhs => rw [← Finset.sdiff_union_of_subset (Finset.subset_univ A)]
  rw [Finset.prod_union Finset.disjoint_sdiff.symm]

/-- Lower sandwich bound, eventually: the Poisson-binomial mass is at least
`(∏_i (1 - p_{n,i})) · e_j(p_n)`. -/
private theorem probSum_ge (hp : ∀ n i, 0 ≤ p n i)
    (hMax : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : Fin (k n), p n i < ε)
    (j : ℕ) :
    ∀ᶠ n in atTop, (∏ i : Fin (k n), (1 - p n i)) * esymmSum (p n) j
      ≤ probSum (p n) j := by
  have hSmall : ∀ᶠ n in atTop, rowMax p n < 1 / 2 :=
    (tendsto_rowMax hp hMax).eventually_lt_const (by norm_num)
  filter_upwards [hSmall] with n hn
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A hA
  have hA_nonneg : 0 ≤ ∏ i ∈ A, p n i := Finset.prod_nonneg (fun i _ => hp n i)
  have hComp_nonneg : 0 ≤ ∏ i ∈ Finset.univ \ A, (1 - p n i) := by
    apply Finset.prod_nonneg
    intro i _
    have hpi : p n i ≤ rowMax p n := le_rowMax n i
    linarith [hp n i]
  have hSub_le_one : (∏ i ∈ A, (1 - p n i)) ≤ 1 := by
    apply Finset.prod_le_one₀ (fun i _ => by linarith [hp n i, le_rowMax (p := p) n i])
    intro i _
    linarith [hp n i]
  have hProd_le : (∏ i : Fin (k n), (1 - p n i))
      ≤ ∏ i ∈ Finset.univ \ A, (1 - p n i) := by
    rw [prod_univ_eq_prod_sdiff_mul]
    calc (∏ i ∈ Finset.univ \ A, (1 - p n i)) * (∏ i ∈ A, (1 - p n i))
        ≤ (∏ i ∈ Finset.univ \ A, (1 - p n i)) * 1 :=
          mul_le_mul_of_nonneg_left hSub_le_one hComp_nonneg
      _ = ∏ i ∈ Finset.univ \ A, (1 - p n i) := mul_one _
  calc (∏ i : Fin (k n), (1 - p n i)) * (∏ i ∈ A, p n i)
      = (∏ i ∈ A, p n i) * (∏ i : Fin (k n), (1 - p n i)) := mul_comm _ _
    _ ≤ (∏ i ∈ A, p n i) * (∏ i ∈ Finset.univ \ A, (1 - p n i)) :=
        mul_le_mul_of_nonneg_left hProd_le hA_nonneg

/-- Upper sandwich bound, eventually: the Poisson-binomial mass is at most
`(∏_i (1 - p_{n,i})) · e_j(p_n) / (1 - rowMax p n) ^ j`. -/
private theorem probSum_le (hp : ∀ n i, 0 ≤ p n i)
    (hMax : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : Fin (k n), p n i < ε)
    (j : ℕ) :
    ∀ᶠ n in atTop, probSum (p n) j
      ≤ (∏ i : Fin (k n), (1 - p n i)) * esymmSum (p n) j / (1 - rowMax p n) ^ j := by
  have hSmall : ∀ᶠ n in atTop, rowMax p n < 1 / 2 :=
    (tendsto_rowMax hp hMax).eventually_lt_const (by norm_num)
  filter_upwards [hSmall] with n hn
  have h1m : 0 < 1 - rowMax p n := by linarith [rowMax_nonneg hp n]
  have h1m_pow : 0 < (1 - rowMax p n) ^ j := pow_pos h1m j
  calc probSum (p n) j
      ≤ ∑ A ∈ Finset.univ.powersetCard j,
          (∏ i ∈ A, p n i) * ((∏ i : Fin (k n), (1 - p n i)) / (1 - rowMax p n) ^ j) := by
        apply Finset.sum_le_sum
        intro A hA
        have hAcard : A.card = j := (Finset.mem_powersetCard.mp hA).2
        have hComp_nonneg : 0 ≤ ∏ i ∈ Finset.univ \ A, (1 - p n i) := by
          apply Finset.prod_nonneg
          intro i _
          have hpi : p n i ≤ rowMax p n := le_rowMax n i
          linarith [hp n i]
        have hw : (1 - rowMax p n) ^ j ≤ ∏ i ∈ A, (1 - p n i) := by
          have hprod := Finset.prod_le_prod₀
            (s := A) (f := fun _ => 1 - rowMax p n) (g := fun i => 1 - p n i)
            (fun i _ => by linarith [rowMax_nonneg hp n])
            (fun i _ => by linarith [le_rowMax (p := p) n i])
          rwa [Finset.prod_const, hAcard] at hprod
        have hComp_le : (∏ i ∈ Finset.univ \ A, (1 - p n i))
            ≤ (∏ i : Fin (k n), (1 - p n i)) / (1 - rowMax p n) ^ j := by
          rw [le_div_iff₀ h1m_pow]
          calc (∏ i ∈ Finset.univ \ A, (1 - p n i)) * (1 - rowMax p n) ^ j
              ≤ (∏ i ∈ Finset.univ \ A, (1 - p n i)) * (∏ i ∈ A, (1 - p n i)) :=
                mul_le_mul_of_nonneg_left hw hComp_nonneg
            _ = ∏ i : Fin (k n), (1 - p n i) := (prod_univ_eq_prod_sdiff_mul (p n) A).symm
        exact mul_le_mul_of_nonneg_left hComp_le
          (Finset.prod_nonneg (fun i _ => hp n i))
    _ = esymmSum (p n) j * ((∏ i : Fin (k n), (1 - p n i)) / (1 - rowMax p n) ^ j) := by
        rw [← Finset.sum_mul]
    _ = (∏ i : Fin (k n), (1 - p n i)) * esymmSum (p n) j / (1 - rowMax p n) ^ j := by
        ring

/-- **Analytic core of Poisson convergence.** Let $\lambda \ge 0$ be a real number, let
$k : \mathbb{N} \to \mathbb{N}$, and for each $n$ let $p_{n,i}$, $0 \le i < k(n)$, be real
numbers. Suppose that $p_{n,i} \ge 0$ for all $n$ and $i$, that for every $\varepsilon > 0$
we have $p_{n,i} < \varepsilon$ for all $i < k(n)$ once $n$ is large enough, and that
$\sum_{i < k(n)} p_{n,i} \to \lambda$ as $n \to \infty$. Then for every natural number $j$,
as $n \to \infty$ the Poisson-binomial mass
$$\sum_{|A| = j} \prod_{i \in A} p_{n,i} \prod_{i \notin A} (1 - p_{n,i})$$
tends to $e^{-\lambda} \lambda^j / j!$, where $A$ runs over the $j$-element subsets of
$\{0, \dots, k(n) - 1\}$ and $i \notin A$ ranges over the elements of that set not in $A$.

Without the hypothesis $p_{n,i} \ge 0$ the conclusion can fail. -/
theorem elem_symm_poly_tendsto_poisson
    (hp_nonneg : ∀ n i, 0 ≤ p n i)
    (hMaxTendsto : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : Fin (k n), p n i < ε)
    (hSumTendsto : Filter.Tendsto (fun n => ∑ i : Fin (k n), p n i) atTop (𝓝 (lam : ℝ)))
    (j : ℕ) :
    Filter.Tendsto (fun n => ∑ A ∈ (Finset.univ : Finset (Fin (k n))).powersetCard j,
        (∏ i ∈ A, p n i) * (∏ i ∈ Finset.univ \ A, (1 - p n i)))
      atTop (𝓝 (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ j / (Nat.factorial j : ℝ))) := by
  have hLow : Filter.Tendsto (fun n => (∏ i : Fin (k n), (1 - p n i)) * esymmSum (p n) j)
      atTop (𝓝 (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ j / (Nat.factorial j : ℝ))) := by
    have h := (prod_one_sub_tendsto hp_nonneg hMaxTendsto hSumTendsto).mul
      (esymm_tendsto hp_nonneg hMaxTendsto hSumTendsto j)
    have heq : Real.exp (-(lam : ℝ)) * ((lam : ℝ) ^ j / (Nat.factorial j : ℝ))
        = Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ j / (Nat.factorial j : ℝ) :=
      (mul_div_assoc _ _ _).symm
    rwa [heq] at h
  have hUp : Filter.Tendsto
      (fun n => (∏ i : Fin (k n), (1 - p n i)) * esymmSum (p n) j / (1 - rowMax p n) ^ j)
      atTop (𝓝 (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ j / (Nat.factorial j : ℝ))) := by
    have hDen : Filter.Tendsto (fun n => (1 - rowMax p n) ^ j) atTop (𝓝 1) := by
      have h1 : Filter.Tendsto (fun n => 1 - rowMax p n) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (tendsto_rowMax hp_nonneg hMaxTendsto)
      rw [sub_zero] at h1
      simpa using h1.pow j
    have hDiv := hLow.div hDen one_ne_zero
    rw [div_one] at hDiv
    exact hDiv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hLow hUp
    (probSum_ge hp_nonneg hMaxTendsto j) (probSum_le hp_nonneg hMaxTendsto j)

end ProbabilityTheory
