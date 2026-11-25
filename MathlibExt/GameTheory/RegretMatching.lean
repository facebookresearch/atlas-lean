/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.BlackwellApproachabilityAlmostSure
public import MathlibExt.GameTheory.CorrelatedEquilibrium
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.UniformSpace.HeineCantor
import MathlibExt.Analysis.Series.Kronecker
import MathlibExt.MeasureTheory.Function.ConditionalExpectation.FiniteValued
import MathlibExt.Probability.SqMartingaleConvergence

@[expose] public section

/-! # Regret matching leads to correlated equilibria

Hart and Mas-Colell's *regret matching* (2000): each period a player switches from its last
action `j` to another action `k` with probability proportional to its regret for not having played
`k` whenever it played `j`, and otherwise repeats `j`. Their Main Theorem,
`regretMatching_tendsto_correlatedEq`: when every player uses it, the empirical distribution of
play converges almost surely to the set of correlated equilibria.

## Main results

* `regretMatching`: the weights of regret matching, (2.2) of Hart and Mas-Colell, a mixed action
  under the bound on `μ` of their footnote 5.
* `regretMatching_tendsto_correlatedEq`: their Main Theorem.

## Proof outline

Fix a player `i` with cost function `c = cost i`. Let `N_t(j, k)` be its conditional regrets after
the rounds `0, …, t` (`condRegret`), `Πᵢ_t` its regret-matching transition matrix
(`Πᵢ_t(j, k) = N_t(j, k)⁺ / ((t + 1) μ)` for `k ≠ j`), `P_t` the product transition kernel of all
players, and `Q_t` the kernel that moves only player `i`, by `Πᵢ_t`. The bound on `μ` makes the
diagonal of `Πᵢ_t` at least some `q > 0`, for every history.

* Potential recursion (Blackwell's recursion for the nonpositive orthant; Hart and Mas-Colell
  2000, Steps M1 and M2): `V_t = ∑_{j,k} (N_t(j, k)⁺)²` satisfies
  `V_{t+1} ≤ V_t + 2 (t + 1) μ φ_t(s_{t+1}) + K`, where `φ_t = c − Q_t c` and `s_t` is the
  profile of round `t`: the cross term `∑_{j,k} N_t(j, k)⁺ (N_{t+1}(j, k) − N_t(j, k))` is exactly
  `(t + 1) μ φ_t(s_{t+1})`.
* Poisson decomposition: for a horizon `v`, `φ = f − P f + Pᵛ φ` with `f = ∑_{w < v} Pʷ φ`
  (for `P = P_t` and `φ = φ_t`). At `s_{t+1}` this splits `φ_t(s_{t+1})` into a martingale
  difference `f_t(s_{t+1}) − (P_t f_t)(s_t)`, a telescoping term `g_t(s_t) − g_t(s_{t+1})` with
  `g_t = P_t f_t`, and a remainder `(P_tᵛ φ_t)(s_{t+1})`.
* The remainder: as `P` is a product kernel, `Pᵛ (c − Q c)` only involves `Πᵢᵛ − Πᵢᵛ⁺¹`, and for
  a stochastic matrix with diagonal at least `q` every row of `Πᵛ⁺¹ − Πᵛ` has `ℓ¹`-norm at most
  `1 / (q √(v + 1))`. This is a quantitative strengthening of the Lemma in the proof of Step M7
  of Hart and Mas-Colell 2000, which bounds each entry of `Πᵛ⁺¹ − Πᵛ` by `O(v^(−1/2))` through a
  normal approximation: the bound here is on the absolute row sum, with an explicit constant
  that does not depend on the number of actions, and comes from the binomial expansion of
  `Π = q I + (1 − q) Λ` and the variance of the binomial distribution.
* The weighted martingale term `∑_{τ < t} (τ + 1) (f_τ(s_{τ+1}) − (P_τ f_τ)(s_τ))` is `o(t²)`
  almost surely (`MeasureTheory.ae_exists_tendsto_sum_div_succ` and Kronecker's lemma with the
  weights `(k + 1)²`, `MetaMathlibExt.tendsto_sum_range_add_one_sq_mul_div_of_tendsto`). The
  weighted telescoping term is `o(t²)` along every path, since the transition matrices move by
  `O(1 / t)` per round and `g` is a continuous function of them on a compact set.
* Hence `limsup V_t / (t + 1)² ≤ 2 μ M / (q √(v + 1))` for every `v`, so `N_t⁺ / (t + 1) → 0`
  almost surely for every player. By `isCorrelatedEq_empirical_iff` the empirical distributions
  are correlated `ε_t`-equilibria with `ε_t → 0`, and, the sets of correlated `ε`-equilibria being
  compact, such distributions approach the set of correlated equilibria.

The fixed horizon `v` and the Poisson equation for the frozen kernel `P_t` replace the comparison
process over growing blocks and the strong law of large numbers for dependent random variables
of Hart and Mas-Colell's Steps M3–M10.

## Implementation notes

`regretMatching` and `regretMatching_tendsto_correlatedEq` keep the full names and statements of
the former wanted declarations, so their namespace is `RegretMatchingWanted`. The theorem keeps
its docstring; the docstring of `regretMatching` now also says when its values are probabilities.

## References

* S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium",
  Econometrica 68(5) (2000), 1127–1150: (2.1)–(2.2) and footnote 5 (p. 1130), (2.3) and the Main
  Theorem (p. 1131), Appendix (pp. 1143–1149): Steps M1, M2 and the Lemma in the proof of Step M7
  (pp. 1148–1149).
* S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430: §4, Theorem 1.
-/

namespace MathlibExt.GameTheory.RegretMatchingWanted

open MeasureTheory Filter Topology Finset Matrix
open MathlibExt.GameTheory.NoRegretDynamics (empirical)
open MathlibExt.GameTheory.CorrelatedEquilibrium (IsCorrelatedEq condRegret switchGain
  isCorrelatedEq_empirical_iff isCompact_setOf_isCorrelatedEq isClosed_setOf_isCorrelatedEq)
open MathlibExt.GameTheory.BlackwellApproachabilityWanted (historySigma historySigma_mono
  historySigma_le measurable_historySigma)

section RegretMatching

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

/-- **Regret matching** (Hart and Mas-Colell 2000, (2.2), in cost form). After the history
`h` of the first `t + 1` rounds, let `j` be player `i`'s last action and
`R(j, k) = max(D(j, k), 0)` its regrets, where `D(j, k) = condRegret / (t + 1)` is the average
conditional regret (2.1b–c). The function gives each `k ≠ j` the weight `R(j, k) / μ` and gives
`j` the remaining weight `1 − ∑_{k ≠ j} R(j, k) / μ`, so the weights add up to `1`. They form a
probability distribution, the mixed action with which player `i` switches to each `k ≠ j` with
probability `R(j, k) / μ` and otherwise repeats `j`, under the sufficient bounds `|cost i s| ≤ M`
for all players and profiles and `μ > 2 M (|Sᵢ| − 1)` (Hart and Mas-Colell 2000, footnote 5):
every regret is then at most `2 M`. Without such a bound on `μ` the weights need not be
probabilities. -/
noncomputable def regretMatching (cost : ι → (∀ i, S i) → ℝ) (μ : ℝ) {t : ℕ}
    (h : Fin (t + 1) → ∀ i, S i) (i : ι) (k : S i) : ℝ :=
  if k = h (Fin.last t) i then
    1 - ∑ l ∈ univ.erase (h (Fin.last t) i),
      max (condRegret cost h i (h (Fin.last t) i) l / (t + 1)) 0 / μ
  else max (condRegret cost h i (h (Fin.last t) i) k / (t + 1)) 0 / μ

/-! ### Lazy stochastic matrices -/

/-- For the binomial weights `b(n, r) = C(n, r) pʳ (1 − p)ⁿ⁻ʳ`,
`(n + 1)(1 − p)(b(n + 1, r) − b(n, r)) = b(n + 1, r)(r − (n + 1) p)`. -/
private lemma mul_sub_binomial_eq (p : ℝ) (n r : ℕ) (hr : r ≤ n + 1) :
    ((n : ℝ) + 1) * (1 - p) * ((n + 1).choose r * p ^ r * (1 - p) ^ (n + 1 - r) -
      n.choose r * p ^ r * (1 - p) ^ (n - r)) =
      (n + 1).choose r * p ^ r * (1 - p) ^ (n + 1 - r) * (r - ((n : ℝ) + 1) * p) := by
  have hc : (n.choose r : ℝ) * ((n : ℝ) + 1) = (n + 1).choose r * ((n + 1 - r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_mul_succ_eq n r
  rcases Nat.lt_or_ge r (n + 1) with h | h
  · have h1 : n + 1 - r = (n - r) + 1 := by omega
    have h2 : ((n + 1 - r : ℕ) : ℝ) = (n : ℝ) + 1 - r := by
      rw [Nat.cast_sub hr]; push_cast; ring
    rw [h2] at hc
    rw [h1, pow_succ]
    linear_combination (-(p ^ r * (1 - p) ^ (n - r) * (1 - p))) * hc
  · have hrn : r = n + 1 := le_antisymm hr h
    subst hrn
    simp [Nat.choose_succ_self]
    ring

/-- The Bernstein polynomials evaluated at `p` are the binomial weights. -/
private lemma eval_bernstein (n ν : ℕ) (p : ℝ) :
    (bernsteinPolynomial ℝ n ν).eval p = n.choose ν * p ^ ν * (1 - p) ^ (n - ν) := by
  simp [bernsteinPolynomial]

/-- The mean absolute deviation of the binomial distribution `B(N, p)` is at most `√N`. -/
private lemma sum_binom_abs_le (N : ℕ) (hN : 0 < N) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ r ∈ range (N + 1), N.choose r * p ^ r * (1 - p) ^ (N - r) * |(r : ℝ) - N * p| ≤
      Real.sqrt N := by
  have hvar := congrArg (Polynomial.eval p) (bernsteinPolynomial.variance ℝ N)
  have hsum := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum ℝ N)
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
    Polynomial.eval_one, eval_bernstein, nsmul_eq_mul] at hvar hsum
  set a := Real.sqrt N with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have haa : a * a = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hb : ∀ r, 0 ≤ (N.choose r : ℝ) * p ^ r * (1 - p) ^ (N - r) := fun r => by
    have : 0 ≤ 1 - p := by linarith
    positivity
  have key : ∀ x : ℝ, |x| ≤ (x ^ 2 / a + a) / 2 := fun x => by
    rw [le_div_iff₀ two_pos, div_add' _ _ _ ha0.ne', le_div_iff₀ ha0]
    nlinarith [sq_abs x, sq_nonneg (|x| - a)]
  calc ∑ r ∈ range (N + 1), N.choose r * p ^ r * (1 - p) ^ (N - r) * |(r : ℝ) - N * p|
      ≤ ∑ r ∈ range (N + 1), N.choose r * p ^ r * (1 - p) ^ (N - r) *
          ((((N : ℝ) * p - r) ^ 2 / a + a) / 2) :=
        sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
          (by rw [abs_sub_comm]; exact key _) (hb r)
    _ = ((∑ r ∈ range (N + 1), ((N : ℝ) * p - r) ^ 2 *
          (N.choose r * p ^ r * (1 - p) ^ (N - r))) / a +
          a * ∑ r ∈ range (N + 1), (N.choose r : ℝ) * p ^ r * (1 - p) ^ (N - r)) / 2 := by
        rw [sum_div, mul_sum, ← sum_add_distrib, sum_div]
        refine sum_congr rfl fun r _ => by ring
    _ = (N * p * (1 - p) / a + a) / 2 := by rw [hvar, hsum, mul_one]
    _ ≤ a := by
        have hpq : p * (1 - p) ≤ 1 := by nlinarith
        have : (N : ℝ) * p * (1 - p) / a ≤ a := by
          rw [div_le_iff₀ ha0, haa]
          have := Nat.cast_nonneg (α := ℝ) N
          nlinarith
        linarith


open Matrix in
/-- **Powers of a lazy stochastic matrix.** If `P` is stochastic with diagonal entries at least
`q ∈ (0, 1)`, every row of `P ^ (n + 1) − P ^ n` has `ℓ¹`-norm at most `1 / (q √(n + 1))`. This
strengthens the Lemma in the proof of Step M7 of Hart and Mas-Colell 2000, which gives the
entrywise estimate `O(n^(−1/2))` with an unspecified constant. -/
private lemma rowL1_pow_succ_sub_pow_le {A : Type*} [Fintype A] [DecidableEq A]
    {P : Matrix A A ℝ} (hP : P ∈ rowStochastic ℝ A) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hdiag : ∀ j, q ≤ P j j) (n : ℕ) (j : A) :
    ∑ k, |(P ^ (n + 1) - P ^ n) j k| ≤ 1 / (q * Real.sqrt (n + 1)) := by
  set p := 1 - q with hp
  have hp0 : 0 < p := by linarith
  set L : Matrix A A ℝ := p⁻¹ • (P - q • 1) with hL
  have hPL : P = p • L + q • 1 := by
    rw [hL, smul_smul, mul_inv_cancel₀ hp0.ne', one_smul, sub_add_cancel]
  have hLs : L ∈ rowStochastic ℝ A := by
    rw [mem_rowStochastic_iff_sum]
    refine ⟨fun i k => ?_, fun i => ?_⟩
    · simp only [hL, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
      refine mul_nonneg (inv_nonneg.2 hp0.le) ?_
      split_ifs with h
      · subst h; linarith [hdiag i]
      · simpa using nonneg_of_mem_rowStochastic hP
    · simp only [hL, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul,
        ← mul_sum, sum_sub_distrib, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ite_true,
        sum_row_of_mem_rowStochastic hP]
      rw [← hp, inv_mul_cancel₀ hp0.ne']
  clear_value L
  have hpow : ∀ m : ℕ, ∀ j k, (P ^ m) j k =
      ∑ r ∈ range (m + 1), (m.choose r : ℝ) * p ^ r * q ^ (m - r) * (L ^ r) j k := by
    intro m j k
    have hc : Commute (p • L) (q • (1 : Matrix A A ℝ)) :=
      ((Commute.one_right L).smul_right q).smul_left p
    rw [hPL, hc.add_pow, Matrix.sum_apply]
    refine sum_congr rfl fun r _ => ?_
    rw [smul_pow, smul_pow, one_pow, ← nsmul_one, ← Nat.cast_smul_eq_nsmul ℝ]
    simp only [Matrix.mul_smul, mul_one, Matrix.smul_apply, smul_eq_mul]
    ring
  set d : ℕ → ℝ := fun r => (n + 1).choose r * p ^ r * q ^ (n + 1 - r) -
    n.choose r * p ^ r * q ^ (n - r) with hd
  have hdiff : ∀ k, (P ^ (n + 1) - P ^ n) j k = ∑ r ∈ range (n + 2), d r * (L ^ r) j k := by
    intro k
    have h0 : ∑ r ∈ range (n + 1), (n.choose r : ℝ) * p ^ r * q ^ (n - r) * (L ^ r) j k =
        ∑ r ∈ range (n + 1 + 1), (n.choose r : ℝ) * p ^ r * q ^ (n - r) * (L ^ r) j k := by
      rw [sum_range_succ _ (n + 1), Nat.choose_succ_self]; simp
    rw [Matrix.sub_apply, hpow, hpow, h0, ← sum_sub_distrib]
    exact sum_congr rfl fun r _ => by rw [hd]; ring
  have hLr : ∀ r, L ^ r ∈ rowStochastic ℝ A := fun r => pow_mem hLs r
  have hdabs : ∀ r ∈ range (n + 2), |d r| = (n + 1).choose r * p ^ r * (1 - p) ^ (n + 1 - r) *
      |(r : ℝ) - ((n + 1 : ℕ) : ℝ) * p| / ((n + 1) * q) := by
    intro r hr
    have hqp : q = 1 - p := by rw [hp]; ring
    have h := mul_sub_binomial_eq p n r (by simpa [Nat.lt_succ_iff] using hr)
    rw [← hqp] at h
    rw [eq_div_iff (by positivity), ← hqp]
    have hpos : (0 : ℝ) ≤ (n + 1).choose r * p ^ r * q ^ (n + 1 - r) := by positivity
    calc |d r| * ((n + 1) * q) = |((n : ℝ) + 1) * q * d r| := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n + 1) * q)]; ring
      _ = _ := by
          rw [hd]; dsimp only; rw [h, abs_mul, abs_of_nonneg hpos]; push_cast; ring
  calc ∑ k, |(P ^ (n + 1) - P ^ n) j k|
      ≤ ∑ k, ∑ r ∈ range (n + 2), |d r| * (L ^ r) j k := by
        refine sum_le_sum fun k _ => ?_
        rw [hdiff]
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun r _ => ?_))
        rw [abs_mul, abs_of_nonneg (nonneg_of_mem_rowStochastic (hLr r))]
    _ = ∑ r ∈ range (n + 2), |d r| := by
        rw [sum_comm]
        exact sum_congr rfl fun r _ => by rw [← mul_sum, sum_row_of_mem_rowStochastic (hLr r),
          mul_one]
    _ = (∑ r ∈ range (n + 1 + 1), (n + 1).choose r * p ^ r * (1 - p) ^ (n + 1 - r) *
          |(r : ℝ) - ((n + 1 : ℕ) : ℝ) * p|) / ((n + 1) * q) := by
        rw [sum_div]; exact sum_congr rfl hdabs
    _ ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) / ((n + 1) * q) := by
        gcongr
        exact sum_binom_abs_le (n + 1) n.succ_pos hp0.le (by linarith)
    _ = 1 / (q * Real.sqrt (n + 1)) := by
        have hs : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
        have hs0 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
        push_cast
        rw [div_eq_div_iff (by positivity) (by positivity)]
        nlinarith

/-! ### Product kernels -/

/-- The product kernel `s ↦ s' ↦ ∏ᵢ Aᵢ(sᵢ, s'ᵢ)` of independent moves of the players. -/
private def prodKernel (A : ∀ i, Matrix (S i) (S i) ℝ) : Matrix (∀ i, S i) (∀ i, S i) ℝ :=
  Matrix.of fun s s' => ∏ i, A i (s i) (s' i)

omit [∀ i, DecidableEq (S i)] in
/-- Product kernels compose coordinatewise. -/
private lemma prodKernel_mul (A B : ∀ i, Matrix (S i) (S i) ℝ) :
    prodKernel (A * B) = prodKernel A * prodKernel B := by
  ext s s''
  simp only [prodKernel, Matrix.of_apply, Matrix.mul_apply, Pi.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [← Finset.prod_mul_distrib]

omit [DecidableEq ι] [∀ i, Fintype (S i)] in
/-- The product of identity matrices is the identity. -/
private lemma prodKernel_one : prodKernel (1 : ∀ i, Matrix (S i) (S i) ℝ) = 1 := by
  ext s s'
  simp only [prodKernel, Matrix.of_apply, Pi.one_apply, Matrix.one_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

/-- Powers of product kernels are product kernels of powers. -/
private lemma prodKernel_pow (A : ∀ i, Matrix (S i) (S i) ℝ) (n : ℕ) :
    prodKernel (A ^ n) = prodKernel A ^ n := by
  induction n with
  | zero => simp [prodKernel_one]
  | succ n ih => rw [pow_succ, prodKernel_mul, ih, pow_succ]

/-- A product of stochastic matrices is stochastic. -/
private lemma prodKernel_mem_rowStochastic {A : ∀ i, Matrix (S i) (S i) ℝ}
    (hA : ∀ i, A i ∈ rowStochastic ℝ (S i)) : prodKernel A ∈ rowStochastic ℝ (∀ i, S i) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun s s' => prod_nonneg fun i _ => nonneg_of_mem_rowStochastic (hA i), fun s => ?_⟩
  simp only [prodKernel, Matrix.of_apply]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  exact prod_eq_one fun i _ => sum_row_of_mem_rowStochastic (hA i) (s i)

omit [∀ i, DecidableEq (S i)] in
/-- A product kernel applied to a function bounded by `G`. -/
private lemma abs_prodKernel_mulVec_le (B : ∀ i, Matrix (S i) (S i) ℝ) {g : (∀ i, S i) → ℝ}
    {G : ℝ} (hg : ∀ s, |g s| ≤ G) (s : ∀ i, S i) :
    |(prodKernel B *ᵥ g) s| ≤ (∏ i, ∑ a, |B i (s i) a|) * G := by
  simp only [mulVec, dotProduct, prodKernel, Matrix.of_apply]
  calc |∑ s' : ((i : ι) → S i), (∏ i, B i (s i) (s' i)) * g s'|
      ≤ ∑ s' : ((i : ι) → S i), (∏ i, |B i (s i) (s' i)|) * G := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s' _ => ?_)
        rw [abs_mul, Finset.abs_prod]
        exact mul_le_mul_of_nonneg_left (hg s') (prod_nonneg fun i _ => abs_nonneg _)
    _ = _ := by
        rw [← sum_mul, Finset.prod_univ_sum, Fintype.piFinset_univ]

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- Product kernels are linear in each factor. -/
private lemma prodKernel_update_sub (A : ∀ i, Matrix (S i) (S i) ℝ) (i : ι)
    (X Y : Matrix (S i) (S i) ℝ) :
    prodKernel (Function.update A i X) - prodKernel (Function.update A i Y) =
      prodKernel (Function.update A i (X - Y)) := by
  ext s s'
  simp only [prodKernel, Matrix.sub_apply, Matrix.of_apply]
  rw [← Finset.mul_prod_erase _ _ (mem_univ i), ← Finset.mul_prod_erase _ _ (mem_univ i),
    ← Finset.mul_prod_erase _ _ (mem_univ i)]
  simp only [Function.update_self]
  have : ∀ Z : Matrix (S i) (S i) ℝ, ∏ x ∈ univ.erase i, Function.update A i Z x (s x) (s' x) =
      ∏ x ∈ univ.erase i, A x (s x) (s' x) := fun Z =>
    prod_congr rfl fun x hx => by rw [Function.update_of_ne (ne_of_mem_erase hx)]
  rw [this, this, this, Matrix.sub_apply]
  ring

/-- The kernel that moves only player `i`, by the matrix `X`. -/
private lemma prodKernel_mulSingle_mulVec (i : ι) (X : Matrix (S i) (S i) ℝ)
    (c : (∀ i, S i) → ℝ) (s : ∀ i, S i) :
    (prodKernel (Pi.mulSingle i X) *ᵥ c) s = ∑ k, X (s i) k * c (Function.update s i k) := by
  simp only [mulVec, dotProduct, prodKernel, Matrix.of_apply]
  have h : ∀ s' : ∀ i, S i, ∏ x, (Pi.mulSingle i X : ∀ i, Matrix (S i) (S i) ℝ) x (s x) (s' x) =
      if s' = Function.update s i (s' i) then X (s i) (s' i) else 0 := by
    intro s'
    rw [← Finset.mul_prod_erase _ _ (mem_univ i), Pi.mulSingle_eq_same]
    have : ∏ x ∈ univ.erase i, (Pi.mulSingle i X : ∀ i, Matrix (S i) (S i) ℝ) x (s x) (s' x) =
        ∏ x ∈ univ.erase i, (if s x = s' x then 1 else 0) :=
      prod_congr rfl fun x hx => by
        rw [Pi.mulSingle_eq_of_ne (ne_of_mem_erase hx), Matrix.one_apply]
    rw [this, prod_boole]
    split_ifs with h1 h2 h2
    · simp
    · exfalso; apply h2; funext x
      by_cases hx : x = i
      · subst hx; simp
      · rw [Function.update_of_ne hx]; exact (h1 x (mem_erase.2 ⟨hx, mem_univ x⟩)).symm
    · exfalso; apply h1; intro x hx
      rw [h2, Function.update_of_ne (ne_of_mem_erase hx)]
    · simp
  simp_rw [h, ite_mul, zero_mul]
  rw [← sum_filter]
  refine sum_nbij' (fun s' => s' i) (fun k => Function.update s i k) (fun s' _ => mem_univ _)
    (fun k _ => by simp) (fun s' hs' => ?_) (fun k _ => by simp) (fun s' hs' => ?_)
  · exact ((mem_filter.1 hs').2).symm
  · rw [(mem_filter.1 hs').2]; simp


/-- A stochastic matrix maps functions bounded by `G` to functions bounded by `G`. -/
private lemma abs_mulVec_le_of_rowStochastic {B : Type*} [Fintype B] [DecidableEq B]
    {P : Matrix B B ℝ} (hP : P ∈ rowStochastic ℝ B) {g : B → ℝ} {G : ℝ} (hg : ∀ s, |g s| ≤ G)
    (s : B) : |(P *ᵥ g) s| ≤ G := by
  simp only [mulVec, dotProduct]
  calc |∑ s', P s s' * g s'| ≤ ∑ s', P s s' * G := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s' _ => ?_)
        rw [abs_mul, abs_of_nonneg (nonneg_of_mem_rowStochastic hP)]
        exact mul_le_mul_of_nonneg_left (hg s') (nonneg_of_mem_rowStochastic hP)
    _ = G := by rw [← sum_mul, sum_row_of_mem_rowStochastic hP, one_mul]

/-- The finite-horizon Poisson identity `φ = f − P f + Pᵛ φ` for `f = ∑_{w < v} Pʷ φ`. -/
private lemma poisson_identity {B : Type*} [Fintype B] [DecidableEq B] (P : Matrix B B ℝ)
    (φ : B → ℝ) (v : ℕ) :
    φ = (∑ w ∈ range v, P ^ w *ᵥ φ) - P *ᵥ (∑ w ∈ range v, P ^ w *ᵥ φ) + P ^ v *ᵥ φ := by
  have h : P *ᵥ (∑ w ∈ range v, P ^ w *ᵥ φ) = ∑ w ∈ range v, P ^ (w + 1) *ᵥ φ := by
    rw [mulVec_sum]
    exact sum_congr rfl fun w _ => by rw [mulVec_mulVec, pow_succ']
  rw [h, ← sum_sub_distrib, sum_range_sub' (fun w => P ^ w *ᵥ φ), pow_zero, one_mulVec]
  abel

/-- `Pʷ (c − Q c)` is small when player `i`'s matrix is lazy. -/
private lemma abs_pow_mulVec_sub_le {A : ∀ i, Matrix (S i) (S i) ℝ}
    (hA : ∀ i, A i ∈ rowStochastic ℝ (S i)) {i : ι} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hdiag : ∀ j, q ≤ A i j j) {c : (∀ i, S i) → ℝ} {M : ℝ} (hc : ∀ s, |c s| ≤ M) (w : ℕ)
    (s : ∀ i, S i) :
    |(prodKernel A ^ w *ᵥ (c - prodKernel (Pi.mulSingle i (A i)) *ᵥ c)) s| ≤
      M / (q * Real.sqrt (w + 1)) := by
  have h1 : A ^ w * Pi.mulSingle i (A i) = Function.update (A ^ w) i (A i ^ (w + 1)) := by
    funext i'
    by_cases hi : i' = i
    · subst hi; simp [pow_succ]
    · simp [Function.update_of_ne hi, Pi.mulSingle_eq_of_ne hi]
  have h2 : A ^ w = Function.update (A ^ w) i (A i ^ w) := by simp
  rw [mulVec_sub, mulVec_mulVec, ← prodKernel_pow, ← prodKernel_mul, h1, ← sub_mulVec]
  rw [show prodKernel (A ^ w) = prodKernel (Function.update (A ^ w) i (A i ^ w)) from
    congrArg _ h2, prodKernel_update_sub]
  refine (abs_prodKernel_mulVec_le _ hc s).trans ?_
  have hM : 0 ≤ M := (abs_nonneg _).trans (hc s)
  rw [Fintype.prod_eq_single i fun i' hi' => by
    rw [Function.update_of_ne hi', Pi.pow_apply]
    simp_rw [abs_of_nonneg (nonneg_of_mem_rowStochastic (pow_mem (hA i') w))]
    exact sum_row_of_mem_rowStochastic (pow_mem (hA i') w) _]
  rw [Function.update_self, div_eq_mul_inv, mul_comm M]
  refine mul_le_mul_of_nonneg_right ?_ hM
  have := rowL1_pow_succ_sub_pow_le (hA i) hq0 hq1 hdiag w (s i)
  rw [one_div] at this
  refine le_of_eq_of_le (sum_congr rfl fun a _ => ?_) this
  rw [Matrix.sub_apply, Matrix.sub_apply, abs_sub_comm]


/-! ### The regret-matching transition matrices -/

section Helpers

variable {cost : ι → (∀ i, S i) → ℝ} {M μ : ℝ}

/-- The transition matrix of regret matching for player `i` after the history `h`. -/
private noncomputable def rmMatrix (cost : ι → (∀ i, S i) → ℝ) (μ : ℝ) {t : ℕ}
    (h : Fin (t + 1) → ∀ i, S i) (i : ι) : Matrix (S i) (S i) ℝ :=
  Matrix.of fun j k => if k = j then
    1 - ∑ l ∈ univ.erase j, max (condRegret cost h i j l / (t + 1)) 0 / μ
  else max (condRegret cost h i j k / (t + 1)) 0 / μ


omit [Fintype ι] [∀ i, Fintype (S i)] in
/-- Switching gains are bounded by twice the cost bound. -/
private lemma abs_switchGain_le (hM : ∀ i s, |cost i s| ≤ M) (i : ι) (j k : S i)
    (s : ∀ i, S i) : |switchGain cost i j k s| ≤ 2 * M := by
  unfold switchGain
  split_ifs
  · linarith [abs_sub (cost i s) (cost i (Function.update s i k)), hM i s,
      hM i (Function.update s i k)]
  · simp only [abs_zero]; linarith [abs_nonneg (cost i s), hM i s]

omit [Fintype ι] [∀ i, Fintype (S i)] in
/-- Conditional regrets after `t + 1` rounds are bounded by `(t + 1) 2M`. -/
private lemma abs_condRegret_le (hM : ∀ i s, |cost i s| ≤ M) {t : ℕ}
    (h : Fin (t + 1) → ∀ i, S i) (i : ι) (j k : S i) :
    |condRegret cost h i j k| ≤ (t + 1) * (2 * M) := by
  unfold condRegret
  calc _ ≤ ∑ τ, |switchGain cost i j k (h τ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _τ : Fin (t + 1), 2 * M := sum_le_sum fun τ _ => abs_switchGain_le hM i j k _
    _ = _ := by simp

omit [Fintype ι] [∀ i, Fintype (S i)] in
/-- Average positive regrets are bounded by `2M`. -/
private lemma posRegret_le (hM : ∀ i s, |cost i s| ≤ M) {t : ℕ}
    (h : Fin (t + 1) → ∀ i, S i) (i : ι) (j k : S i) :
    max (condRegret cost h i j k / (t + 1)) 0 ≤ 2 * M := by
  have h1 := abs_condRegret_le hM h i j k
  have hM0 : 0 ≤ 2 * M := by
    linarith [abs_nonneg (cost i (h 0)), hM i (h 0)]
  refine max_le ?_ hM0
  rw [div_le_iff₀ (by positivity)]
  linarith [le_abs_self (condRegret cost h i j k)]

omit [Fintype ι] in
/-- Regret matching is a lazy stochastic matrix. -/
private lemma rmMatrix_mem_rowStochastic (hM : ∀ i s, |cost i s| ≤ M) {i : ι}
    (hμ : 2 * M * ((Fintype.card (S i) : ℝ) - 1) < μ) {t : ℕ} (h : Fin (t + 1) → ∀ i, S i) :
    rmMatrix cost μ h i ∈ rowStochastic ℝ (S i) ∧
      ∀ j, 1 - 2 * M * ((Fintype.card (S i) : ℝ) - 1) / μ ≤ rmMatrix cost μ h i j j := by
  have hM0 : 0 ≤ M := by linarith [abs_nonneg (cost i (h 0)), hM i (h 0)]
  have hcard : 1 ≤ Fintype.card (S i) := Fintype.card_pos_iff.2 ⟨h 0 i⟩
  have hcard' : (1 : ℝ) ≤ Fintype.card (S i) := by exact_mod_cast hcard
  have hμ0 : 0 < μ := lt_of_le_of_lt (by positivity) hμ
  have hlt : 2 * M * ((Fintype.card (S i) : ℝ) - 1) / μ < 1 := by
    rwa [div_lt_one hμ0]
  have hdiag : ∀ j, 1 - 2 * M * ((Fintype.card (S i) : ℝ) - 1) / μ ≤ rmMatrix cost μ h i j j := by
    intro j
    simp only [rmMatrix, Matrix.of_apply, ↓reduceIte]
    have hsum : ∑ l ∈ univ.erase j, max (condRegret cost h i j l / (t + 1)) 0 / μ ≤
        2 * M * ((Fintype.card (S i) : ℝ) - 1) / μ := by
      calc _ ≤ ∑ _l ∈ univ.erase j, 2 * M / μ := sum_le_sum fun l _ =>
            div_le_div_of_nonneg_right (posRegret_le hM h i j l) hμ0.le
        _ = _ := by
            rw [sum_const, card_erase_of_mem (mem_univ j), card_univ, nsmul_eq_mul,
              Nat.cast_sub hcard, Nat.cast_one]
            ring
    linarith
  refine ⟨?_, hdiag⟩
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun j k => ?_, fun j => ?_⟩
  · by_cases hk : k = j
    · subst hk; linarith [hdiag k]
    · simp only [rmMatrix, Matrix.of_apply, hk, ↓reduceIte]
      exact div_nonneg (le_max_right _ _) hμ0.le
  · rw [← add_sum_erase _ _ (mem_univ j)]
    simp only [rmMatrix, Matrix.of_apply, ↓reduceIte]
    rw [sum_congr rfl fun k hk => ite_eq_right_of_eq_false _ _ (eq_false (ne_of_mem_erase hk))]
    ring

omit [Fintype ι] [∀ i, Fintype (S i)] in
/-- The conditional regrets after one more round. -/
private lemma condRegret_succ (x : ℕ → ∀ i, S i) (t : ℕ) (i : ι) (j k : S i) :
    condRegret cost (fun τ : Fin (t + 2) => x τ) i j k =
      condRegret cost (fun τ : Fin (t + 1) => x τ) i j k + switchGain cost i j k (x (t + 1)) := by
  unfold condRegret
  rw [Fin.sum_univ_castSucc]
  simp

/-- The potential `∑_{j,k} (N(j,k)⁺)²` of the conditional regrets `N` of player `i`. -/
private noncomputable def regretPotential (cost : ι → (∀ i, S i) → ℝ) (i : ι) {t : ℕ}
    (h : Fin (t + 1) → ∀ i, S i) : ℝ :=
  ∑ j, ∑ k, max (condRegret cost h i j k) 0 ^ 2

/-- The drift `c − Q c` of player `i`'s cost under one move of its regret-matching matrix. -/
private noncomputable def drift (cost : ι → (∀ i, S i) → ℝ) (μ : ℝ) (i : ι) {t : ℕ}
    (h : Fin (t + 1) → ∀ i, S i) : (∀ i, S i) → ℝ :=
  cost i - prodKernel (Pi.mulSingle i (rmMatrix cost μ h i)) *ᵥ cost i

/-- The cross term of the potential recursion is the drift. -/
private lemma sum_posPart_mul_switchGain (hμ0 : μ ≠ 0) {t : ℕ} (h : Fin (t + 1) → ∀ i, S i)
    (i : ι) (hrow : ∀ j, ∑ k, rmMatrix cost μ h i j k = 1) (s : ∀ i, S i) :
    ∑ j, ∑ k, max (condRegret cost h i j k) 0 * switchGain cost i j k s =
      (t + 1) * μ * drift cost μ i h s := by
  have h1 : ∀ j, ∑ k, max (condRegret cost h i j k) 0 * switchGain cost i j k s =
      if s i = j then ∑ k, max (condRegret cost h i j k) 0 *
        (cost i s - cost i (Function.update s i k)) else 0 := by
    intro j
    split_ifs with hj <;> simp [switchGain, hj]
  simp only [h1, sum_ite_eq, mem_univ, ↓reduceIte, drift, Pi.sub_apply,
    prodKernel_mulSingle_mulVec]
  have h2 : cost i s - ∑ k, rmMatrix cost μ h i (s i) k * cost i (Function.update s i k) =
      ∑ k, rmMatrix cost μ h i (s i) k * (cost i s - cost i (Function.update s i k)) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hrow, one_mul]
  rw [h2, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  by_cases hk : k = s i
  · subst hk; simp
  · simp only [rmMatrix, Matrix.of_apply, hk, ↓reduceIte]
    have ht : (0 : ℝ) < t + 1 := by positivity
    rw [show (t + 1 : ℝ) * μ * (max (condRegret cost h i (s i) k / (t + 1)) 0 / μ *
        (cost i s - cost i (Function.update s i k))) =
        ((t + 1) * max (condRegret cost h i (s i) k / (t + 1)) 0) *
        (cost i s - cost i (Function.update s i k)) by field_simp]
    rw [mul_max_of_nonneg _ _ ht.le, mul_zero, mul_div_cancel₀ _ ht.ne']

/-- One step of the potential recursion. -/
private lemma regretPotential_succ_le (hM : ∀ i s, |cost i s| ≤ M) (hμ0 : μ ≠ 0)
    (x : ℕ → ∀ i, S i) (t : ℕ) (i : ι)
    (hrow : ∀ j, ∑ k, rmMatrix cost μ (fun τ : Fin (t + 1) => x τ) i j k = 1) :
    regretPotential cost i (fun τ : Fin (t + 2) => x τ) ≤
      regretPotential cost i (fun τ : Fin (t + 1) => x τ) +
        2 * ((t + 1) * μ * drift cost μ i (fun τ : Fin (t + 1) => x τ) (x (t + 1))) +
        Fintype.card (S i) ^ 2 * (2 * M) ^ 2 := by
  set h : Fin (t + 1) → ∀ i, S i := fun τ => x τ
  have hpos : ∀ a b : ℝ, max (a + b) 0 ^ 2 ≤ (max a 0 + b) ^ 2 := fun a b => by
    rcases le_or_gt (a + b) 0 with hab | hab
    · rw [max_eq_right hab]; nlinarith [sq_nonneg (max a 0 + b)]
    · rw [max_eq_left hab.le]
      exact pow_le_pow_left₀ hab.le (by linarith [le_max_left a 0]) 2
  have hsq : ∀ j k, switchGain cost i j k (x (t + 1)) ^ 2 ≤ (2 * M) ^ 2 := fun j k => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_switchGain_le hM i j k _) 2
  unfold regretPotential
  simp only [condRegret_succ]
  rw [← sum_posPart_mul_switchGain hμ0 h i hrow (x (t + 1))]
  calc ∑ j, ∑ k, max (condRegret cost h i j k + switchGain cost i j k (x (t + 1))) 0 ^ 2
      ≤ ∑ j, ∑ k, (max (condRegret cost h i j k) 0 + switchGain cost i j k (x (t + 1))) ^ 2 :=
        sum_le_sum fun j _ => sum_le_sum fun k _ => hpos _ _
    _ = ∑ j, ∑ k, max (condRegret cost h i j k) 0 ^ 2 +
          2 * ∑ j, ∑ k, max (condRegret cost h i j k) 0 * switchGain cost i j k (x (t + 1)) +
          ∑ j, ∑ k, switchGain cost i j k (x (t + 1)) ^ 2 := by
        simp only [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
    _ ≤ _ := by
        gcongr
        calc ∑ j, ∑ k, switchGain cost i j k (x (t + 1)) ^ 2
            ≤ ∑ _j : S i, ∑ _k : S i, (2 * M) ^ 2 :=
              sum_le_sum fun j _ => sum_le_sum fun k _ => hsq j k
          _ = _ := by simp [sq]; ring

/-- The potential recursion, summed. -/
private lemma regretPotential_le (hM : ∀ i s, |cost i s| ≤ M) {i : ι}
    (hμ : 2 * M * ((Fintype.card (S i) : ℝ) - 1) < μ) (x : ℕ → ∀ i, S i) (t : ℕ) :
    regretPotential cost i (fun τ : Fin (t + 1) => x τ) ≤
      (t + 1) * (Fintype.card (S i) ^ 2 * (2 * M) ^ 2) + 2 * μ * ∑ τ ∈ range t,
        ((τ : ℝ) + 1) * drift cost μ i (fun k : Fin (τ + 1) => x k) (x (τ + 1)) := by
  have hM0 : 0 ≤ M := by linarith [abs_nonneg (cost i (x 0)), hM i (x 0)]
  have hcard : (1 : ℝ) ≤ Fintype.card (S i) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨x 0 i⟩
  have hμ0 : 0 < μ := lt_of_le_of_lt (by nlinarith) hμ
  induction t with
  | zero =>
    simp only [range_zero, sum_empty, mul_zero, add_zero, CharP.cast_eq_zero, zero_add, one_mul]
    unfold regretPotential
    calc _ ≤ ∑ _j : S i, ∑ _k : S i, (2 * M) ^ 2 := sum_le_sum fun j _ => sum_le_sum fun k _ => by
          have h1 := abs_condRegret_le hM (fun τ : Fin (0 + 1) => x τ) i j k
          have h1' : |condRegret cost (fun τ : Fin (0 + 1) => x τ) i j k| ≤ 2 * M := by
            simpa using h1
          exact pow_le_pow_left₀ (le_max_right _ _)
            (max_le ((le_abs_self _).trans h1') (by linarith)) 2
      _ = _ := by simp [sq]; ring
  | succ t ih =>
    have h := regretPotential_succ_le hM hμ0.ne' x t i
      (fun j => sum_row_of_mem_rowStochastic (rmMatrix_mem_rowStochastic hM hμ _).1 j)
    rw [sum_range_succ]
    push_cast at h ⊢
    linarith

/-! ### The Poisson correction -/

/-- The truncated Poisson sum `∑_{w < v} Pʷ (c − Q c)` of the family of matrices `A`. -/
private noncomputable def corrSum (c : (∀ i, S i) → ℝ) (i : ι) (v : ℕ)
    (A : ∀ i, Matrix (S i) (S i) ℝ) : (∀ i, S i) → ℝ :=
  ∑ w ∈ range v, prodKernel A ^ w *ᵥ (c - prodKernel (Pi.mulSingle i (A i)) *ᵥ c)

/-- The Poisson correction `P ∑_{w < v} Pʷ (c − Q c)` of the family of matrices `A`. -/
private noncomputable def poissonCorr (c : (∀ i, S i) → ℝ) (i : ι) (v : ℕ)
    (A : ∀ i, Matrix (S i) (S i) ℝ) : (∀ i, S i) → ℝ :=
  prodKernel A *ᵥ corrSum c i v A

omit [DecidableEq ι] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- The product kernel depends continuously on its factors. -/
private lemma continuous_prodKernel :
    Continuous (prodKernel : (∀ i, Matrix (S i) (S i) ℝ) → Matrix (∀ i, S i) (∀ i, S i) ℝ) := by
  unfold prodKernel
  exact continuous_matrixOf.2 (continuous_pi fun s => continuous_pi fun s' =>
    continuous_finsetProd _ fun i _ => (continuous_apply i).matrix_elem (s i) (s' i))

/-- The Poisson correction depends continuously on the matrices. -/
private lemma continuous_poissonCorr (c : (∀ i, S i) → ℝ) (i : ι) (v : ℕ) :
    Continuous fun a : (∀ i, S i → S i → ℝ) => poissonCorr c i v fun i => Matrix.of (a i) := by
  have hA : Continuous fun a : (∀ i, S i → S i → ℝ) =>
      (fun i => Matrix.of (a i) : ∀ i, Matrix (S i) (S i) ℝ) :=
    continuous_pi fun i => continuous_matrixOf.2 (continuous_apply i)
  have hK := continuous_prodKernel.comp hA
  have hQ : Continuous fun a : (∀ i, S i → S i → ℝ) =>
      prodKernel (Pi.mulSingle i (Matrix.of (a i)) : ∀ i, Matrix (S i) (S i) ℝ) :=
    continuous_prodKernel.comp ((continuous_mulSingle i).comp
      (continuous_matrixOf.2 (continuous_apply i)))
  unfold poissonCorr corrSum
  exact hK.matrix_mulVec (continuous_finsetSum _ fun w _ => (hK.pow w).matrix_mulVec
    (continuous_const.sub (hQ.matrix_mulVec continuous_const)))

/-- A continuous function on a compact set turns slowly varying sequences into slowly varying
sequences. -/
private lemma tendsto_dist_comp_succ {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {K : Set E} (hK : IsCompact K) {f : E → F} (hf : Continuous f) {a : ℕ → E}
    (haK : ∀ t, a t ∈ K) (ha : Tendsto (fun t => dist (a (t + 1)) (a t)) atTop (𝓝 0)) :
    Tendsto (fun t => dist (f (a (t + 1))) (f (a t))) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ :=
    Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hf.continuousOn) ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ha δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at this ⊢
  exact h _ (haK _) _ (haK _) this

omit [Fintype ι] in
/-- The regret-matching matrices move by `O(1 / t)` per round. -/
private lemma abs_rmMatrix_succ_sub_le (hM : ∀ i s, |cost i s| ≤ M) (hμ0 : 0 < μ)
    (x : ℕ → ∀ i, S i) (t : ℕ) (i : ι) (j k : S i) :
    |rmMatrix cost μ (fun τ : Fin (t + 2) => x τ) i j k -
        rmMatrix cost μ (fun τ : Fin (t + 1) => x τ) i j k| ≤
      Fintype.card (S i) * (4 * M / μ) / (t + 2) := by
  have hM0 : 0 ≤ M := by linarith [abs_nonneg (cost i (x 0)), hM i (x 0)]
  have hcard : (1 : ℝ) ≤ Fintype.card (S i) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨x 0 i⟩
  have hR : ∀ l, |max (condRegret cost (fun τ : Fin (t + 2) => x τ) i j l / ((t + 1 : ℕ) + 1)) 0 -
      max (condRegret cost (fun τ : Fin (t + 1) => x τ) i j l / (t + 1)) 0| ≤ 4 * M / (t + 2) := by
    intro l
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [condRegret_succ]
    set N := condRegret cost (fun τ : Fin (t + 1) => x τ) i j l
    set g := switchGain cost i j l (x (t + 1))
    have hN := abs_condRegret_le hM (fun τ : Fin (t + 1) => x τ) i j l
    have hg := abs_switchGain_le hM i j l (x (t + 1))
    have ht : (0 : ℝ) < t + 1 := by positivity
    have he : (N + g) / (((t + 1 : ℕ) : ℝ) + 1) - N / (t + 1) =
        ((t + 1) * g - N) / ((t + 1) * (t + 2)) := by
      push_cast; field_simp; ring
    rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (t + 1) * (t + 2)),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : |(↑t + 1) * g - N| ≤ (t + 1) * (2 * M) + (t + 1) * (2 * M) := by
      refine (abs_sub _ _).trans (add_le_add ?_ hN)
      rw [abs_mul, abs_of_pos ht]
      exact mul_le_mul_of_nonneg_left hg ht.le
    nlinarith
  by_cases hkj : k = j
  · subst hkj
    simp only [rmMatrix, Matrix.of_apply, ↓reduceIte]
    rw [sub_sub_sub_cancel_left, ← sum_sub_distrib]
    calc |∑ l ∈ univ.erase k, (max (condRegret cost (fun τ : Fin (t + 1) => x τ) i k l / (t + 1))
          0 / μ - max (condRegret cost (fun τ : Fin (t + 2) => x τ) i k l /
            ((t + 1 : ℕ) + 1)) 0 / μ)|
        ≤ ∑ _l ∈ univ.erase k, 4 * M / (t + 2) / μ := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ => ?_)
          rw [← sub_div, abs_div, abs_of_pos hμ0, abs_sub_comm]
          exact div_le_div_of_nonneg_right (hR l) hμ0.le
      _ ≤ ∑ _l : S i, 4 * M / (t + 2) / μ :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => by positivity
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring
  · simp only [rmMatrix, Matrix.of_apply, hkj, ↓reduceIte]
    rw [← sub_div, abs_div, abs_of_pos hμ0]
    calc _ ≤ 4 * M / (t + 2) / μ := div_le_div_of_nonneg_right (hR k) hμ0.le
      _ = 1 * (4 * M / μ) / (t + 2) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcard (div_nonneg (by linarith) hμ0.le)) (by positivity)

/-- The telescoping term is `o(t²)`. -/
private lemma tendsto_sum_mul_sub_div_sq {a b : ℕ → ℝ} {B : ℝ} (ha : ∀ t, |a t| ≤ B)
    (hab : Tendsto (fun t => b t - a (t + 1)) atTop (𝓝 0)) :
    Tendsto (fun t : ℕ => (∑ τ ∈ range t, ((τ : ℝ) + 1) * (a τ - b τ)) / ((t : ℝ) + 1) ^ 2)
      atTop (𝓝 0) := by
  set c : ℕ → ℝ := fun t => b t - a (t + 1)
  have hid : ∀ t, ∑ τ ∈ range t, ((τ : ℝ) + 1) * (a τ - b τ) =
      ∑ τ ∈ range t, a τ - t * a t - ∑ τ ∈ range t, ((τ : ℝ) + 1) * c τ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [sum_range_succ, ih, sum_range_succ, sum_range_succ]; push_cast; ring
  have hB : 0 ≤ B := (abs_nonneg _).trans (ha 0)
  have hc : Tendsto (fun t => |c t|) atTop (𝓝 0) := by simpa using hab.abs
  have h1 : Tendsto (fun t : ℕ => 2 * B / ((t : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h2 := h1.add hc.cesaro
  rw [add_zero] at h2
  refine squeeze_zero_norm (fun t => ?_) h2
  rw [hid, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((t : ℝ) + 1) ^ 2)]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simpa using hB
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hA : |∑ τ ∈ range t, a τ - t * a t| ≤ 2 * B * t := by
    calc _ ≤ |∑ τ ∈ range t, a τ| + |(t : ℝ) * a t| := abs_sub _ _
      _ ≤ ∑ _τ ∈ range t, B + t * B := by
          gcongr
          · exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun τ _ => ha τ)
          · rw [abs_mul, Nat.abs_cast]; exact mul_le_mul_of_nonneg_left (ha t) ht'.le
      _ = 2 * B * t := by simp; ring
  have hC : |∑ τ ∈ range t, ((τ : ℝ) + 1) * c τ| ≤ t * ∑ τ ∈ range t, |c τ| := by
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun τ hτ => ?_)
    have : (τ : ℝ) + 1 ≤ t := by exact_mod_cast mem_range.1 hτ
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < τ + 1)]
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hsq : (t : ℝ) * ((t : ℝ) + 1) ≤ ((t : ℝ) + 1) ^ 2 := by nlinarith
  have hS : 0 ≤ ∑ τ ∈ range t, |c τ| := sum_nonneg fun _ _ => abs_nonneg _
  rw [div_le_iff₀ (by positivity)]
  calc |∑ τ ∈ range t, a τ - t * a t - ∑ τ ∈ range t, ((τ : ℝ) + 1) * c τ|
      ≤ 2 * B * t + t * ∑ τ ∈ range t, |c τ| := (abs_sub _ _).trans (add_le_add hA hC)
    _ ≤ (2 * B / ((t : ℝ) + 1) + (t : ℝ)⁻¹ * ∑ τ ∈ range t, |c τ|) * ((t : ℝ) + 1) ^ 2 := by
        have e : (2 * B / ((t : ℝ) + 1) + (t : ℝ)⁻¹ * ∑ τ ∈ range t, |c τ|) * ((t : ℝ) + 1) ^ 2 =
            2 * B * ((t : ℝ) + 1) + (((t : ℝ) + 1) ^ 2 / t) * ∑ τ ∈ range t, |c τ| := by
          field_simp
        have h3 : (t : ℝ) ≤ ((t : ℝ) + 1) ^ 2 / t := by rw [le_div_iff₀ ht']; nlinarith
        rw [e]
        nlinarith [mul_le_mul_of_nonneg_right h3 hS]

/-! ### The pathwise bound -/

omit [Fintype ι] in
/-- The factors of the kernel that moves only player `i` are stochastic. -/
private lemma mulSingle_mem_rowStochastic {A : ∀ i, Matrix (S i) (S i) ℝ}
    (hA : ∀ i, A i ∈ rowStochastic ℝ (S i)) (i i' : ι) :
    (Pi.mulSingle i (A i) : ∀ i, Matrix (S i) (S i) ℝ) i' ∈ rowStochastic ℝ (S i') := by
  by_cases h : i' = i
  · subst h; rw [Pi.mulSingle_eq_same]; exact hA i'
  · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem _

/-- The drift `c − Q c` is bounded by twice the bound on `c`. -/
private lemma abs_sub_mulVec_le {A : ∀ i, Matrix (S i) (S i) ℝ}
    (hA : ∀ i, A i ∈ rowStochastic ℝ (S i)) (i : ι) {c : (∀ i, S i) → ℝ} {M : ℝ}
    (hc : ∀ s, |c s| ≤ M) (s : ∀ i, S i) :
    |(c - prodKernel (Pi.mulSingle i (A i)) *ᵥ c) s| ≤ 2 * M := by
  rw [Pi.sub_apply]
  have := abs_mulVec_le_of_rowStochastic
    (prodKernel_mem_rowStochastic (mulSingle_mem_rowStochastic hA i)) hc s
  linarith [abs_sub (c s) ((prodKernel (Pi.mulSingle i (A i)) *ᵥ c) s), hc s]

/-- The truncated Poisson sum with horizon `v` is bounded by `v · 2M`. -/
private lemma abs_corrSum_le {A : ∀ i, Matrix (S i) (S i) ℝ}
    (hA : ∀ i, A i ∈ rowStochastic ℝ (S i)) (i : ι) {c : (∀ i, S i) → ℝ} {M : ℝ}
    (hc : ∀ s, |c s| ≤ M) (v : ℕ) (s : ∀ i, S i) : |corrSum c i v A s| ≤ v * (2 * M) := by
  unfold corrSum
  rw [Finset.sum_apply]
  calc _ ≤ ∑ w ∈ range v, |(prodKernel A ^ w *ᵥ
        (c - prodKernel (Pi.mulSingle i (A i)) *ᵥ c)) s| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _w ∈ range v, 2 * M := sum_le_sum fun w _ => abs_mulVec_le_of_rowStochastic
        (pow_mem (prodKernel_mem_rowStochastic hA) w) (abs_sub_mulVec_le hA i hc) s
    _ = _ := by simp

/-- The Poisson correction with horizon `v` is bounded by `v · 2M`. -/
private lemma abs_poissonCorr_le {A : ∀ i, Matrix (S i) (S i) ℝ}
    (hA : ∀ i, A i ∈ rowStochastic ℝ (S i)) (i : ι) {c : (∀ i, S i) → ℝ} {M : ℝ}
    (hc : ∀ s, |c s| ≤ M) (v : ℕ) (s : ∀ i, S i) : |poissonCorr c i v A s| ≤ v * (2 * M) :=
  abs_mulVec_le_of_rowStochastic (prodKernel_mem_rowStochastic hA) (abs_corrSum_le hA i hc v) s

/-- The finite-horizon Poisson identity for the drift `c − Q c`. -/
private lemma sub_mulVec_eq (A : ∀ i, Matrix (S i) (S i) ℝ) (i : ι) (c : (∀ i, S i) → ℝ)
    (v : ℕ) (s : ∀ i, S i) :
    (c - prodKernel (Pi.mulSingle i (A i)) *ᵥ c) s = corrSum c i v A s - poissonCorr c i v A s +
      (prodKernel A ^ v *ᵥ (c - prodKernel (Pi.mulSingle i (A i)) *ᵥ c)) s :=
  congrFun (poisson_identity (prodKernel A) _ v) s

/-- The pathwise bound on the normalised potential. -/
private lemma regretPotential_div_le (hM : ∀ i s, |cost i s| ≤ M)
    (hμ : ∀ i, 2 * M * ((Fintype.card (S i) : ℝ) - 1) < μ) (x : ℕ → ∀ i, S i) (i : ι) (v : ℕ)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hdiag : ∀ t j, q ≤ rmMatrix cost μ (fun k : Fin (t + 1) => x k) i j j) (t : ℕ) :
    regretPotential cost i (fun k : Fin (t + 1) => x k) / ((t : ℝ) + 1) ^ 2 ≤
      Fintype.card (S i) ^ 2 * (2 * M) ^ 2 / ((t : ℝ) + 1) + 2 * μ *
        ((∑ τ ∈ range t, ((τ : ℝ) + 1) *
            (corrSum (cost i) i v (rmMatrix cost μ fun k : Fin (τ + 1) => x k) (x (τ + 1)) -
              poissonCorr (cost i) i v (rmMatrix cost μ fun k : Fin (τ + 1) => x k) (x τ))) /
            ((t : ℝ) + 1) ^ 2 +
          (∑ τ ∈ range t, ((τ : ℝ) + 1) *
            (poissonCorr (cost i) i v (rmMatrix cost μ fun k : Fin (τ + 1) => x k) (x τ) -
              poissonCorr (cost i) i v (rmMatrix cost μ fun k : Fin (τ + 1) => x k) (x (τ + 1)))) /
            ((t : ℝ) + 1) ^ 2 + M / (q * Real.sqrt (v + 1))) := by
  have hM0 : 0 ≤ M := by linarith [abs_nonneg (cost i (x 0)), hM i (x 0)]
  have hcard : (1 : ℝ) ≤ Fintype.card (S i) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨x 0 i⟩
  have hμ0 : 0 < μ := lt_of_le_of_lt (by nlinarith) (hμ i)
  set A : ℕ → ∀ i, Matrix (S i) (S i) ℝ := fun τ => rmMatrix cost μ fun k : Fin (τ + 1) => x k
  have hA : ∀ τ i', A τ i' ∈ rowStochastic ℝ (S i') := fun τ i' =>
    (rmMatrix_mem_rowStochastic hM (hμ i') _).1
  set ε := M / (q * Real.sqrt (v + 1))
  set e : ℕ → ℝ := fun τ => corrSum (cost i) i v (A τ) (x (τ + 1)) -
    poissonCorr (cost i) i v (A τ) (x τ)
  set d : ℕ → ℝ := fun τ => poissonCorr (cost i) i v (A τ) (x τ) -
    poissonCorr (cost i) i v (A τ) (x (τ + 1))
  have hdec : ∀ τ, drift cost μ i (fun k : Fin (τ + 1) => x k) (x (τ + 1)) ≤ e τ + d τ + ε := by
    intro τ
    have h := sub_mulVec_eq (A τ) i (cost i) v (x (τ + 1))
    have hr := abs_pow_mulVec_sub_le (hA τ) hq0 hq1 (hdiag τ) (hM i) v (x (τ + 1))
    have : drift cost μ i (fun k : Fin (τ + 1) => x k) (x (τ + 1)) =
        (cost i - prodKernel (Pi.mulSingle i (A τ i)) *ᵥ cost i) (x (τ + 1)) := rfl
    rw [this, h]
    simp only [e, d]
    linarith [le_abs_self ((prodKernel (A τ) ^ v *ᵥ
      (cost i - prodKernel (Pi.mulSingle i (A τ i)) *ᵥ cost i)) (x (τ + 1)))]
  have hsum : ∑ τ ∈ range t, ((τ : ℝ) + 1) *
      drift cost μ i (fun k : Fin (τ + 1) => x k) (x (τ + 1)) ≤
      ∑ τ ∈ range t, ((τ : ℝ) + 1) * e τ + ∑ τ ∈ range t, ((τ : ℝ) + 1) * d τ +
        ((t : ℝ) + 1) ^ 2 * ε := by
    have hε : 0 ≤ ε := by positivity
    have h1 : ∑ τ ∈ range t, ((τ : ℝ) + 1) * ε ≤ ((t : ℝ) + 1) ^ 2 * ε := by
      rw [← sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ hε
      calc ∑ τ ∈ range t, ((τ : ℝ) + 1) ≤ ∑ _τ ∈ range t, ((t : ℝ) + 1) :=
            sum_le_sum fun τ hτ => by
              have : (τ : ℝ) < t := by exact_mod_cast mem_range.1 hτ
              linarith
        _ = t * ((t : ℝ) + 1) := by simp; ring
        _ ≤ _ := by nlinarith
    calc _ ≤ ∑ τ ∈ range t, ((τ : ℝ) + 1) * (e τ + d τ + ε) :=
          sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hdec τ) (by positivity)
      _ = ∑ τ ∈ range t, ((τ : ℝ) + 1) * e τ + ∑ τ ∈ range t, ((τ : ℝ) + 1) * d τ +
          ∑ τ ∈ range t, ((τ : ℝ) + 1) * ε := by
          rw [← sum_add_distrib, ← sum_add_distrib]
          exact sum_congr rfl fun τ _ => by ring
      _ ≤ _ := by linarith
  have hV := regretPotential_le hM (hμ i) x t
  have ht : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  rw [div_le_iff₀ (by positivity)]
  have key : (Fintype.card (S i) ^ 2 * (2 * M) ^ 2 / ((t : ℝ) + 1) + 2 * μ *
      ((∑ τ ∈ range t, ((τ : ℝ) + 1) * e τ) / ((t : ℝ) + 1) ^ 2 +
        (∑ τ ∈ range t, ((τ : ℝ) + 1) * d τ) / ((t : ℝ) + 1) ^ 2 + ε)) * ((t : ℝ) + 1) ^ 2 =
      ((t : ℝ) + 1) * (Fintype.card (S i) ^ 2 * (2 * M) ^ 2) + 2 * μ *
        (∑ τ ∈ range t, ((τ : ℝ) + 1) * e τ + ∑ τ ∈ range t, ((τ : ℝ) + 1) * d τ +
          ((t : ℝ) + 1) ^ 2 * ε) := by
    field_simp
  rw [key]
  nlinarith [mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2 * μ)]

/-- The telescoping term along any path is `o(t²)`. -/
private lemma tendsto_telescope (hM : ∀ i s, |cost i s| ≤ M)
    (hμ : ∀ i, 2 * M * ((Fintype.card (S i) : ℝ) - 1) < μ) (x : ℕ → ∀ i, S i) (i : ι)
    (v : ℕ) :
    Tendsto (fun t : ℕ => (∑ τ ∈ range t, ((τ : ℝ) + 1) *
        (poissonCorr (cost i) i v (rmMatrix cost μ fun k : Fin (τ + 1) => x k) (x τ) -
          poissonCorr (cost i) i v (rmMatrix cost μ fun k : Fin (τ + 1) => x k) (x (τ + 1)))) /
        ((t : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := by linarith [abs_nonneg (cost i (x 0)), hM i (x 0)]
  have hμ0 : 0 < μ := lt_of_le_of_lt (by
    have : (1 : ℝ) ≤ Fintype.card (S i) := by exact_mod_cast Fintype.card_pos_iff.2 ⟨x 0 i⟩
    nlinarith) (hμ i)
  set a : ℕ → (∀ i, S i → S i → ℝ) := fun τ i' j k =>
    rmMatrix cost μ (fun k : Fin (τ + 1) => x k) i' j k
  set F : (∀ i, S i → S i → ℝ) → (∀ i, S i) → ℝ :=
    fun b => poissonCorr (cost i) i v fun i => Matrix.of (b i)
  have hFa : ∀ τ, F (a τ) = poissonCorr (cost i) i v (rmMatrix cost μ fun k : Fin (τ + 1) => x k) :=
    fun τ => rfl
  have hA : ∀ τ i', rmMatrix cost μ (fun k : Fin (τ + 1) => x k) i' ∈ rowStochastic ℝ (S i') :=
    fun τ i' => (rmMatrix_mem_rowStochastic hM (hμ i') _).1
  have haK : ∀ τ, a τ ∈ Metric.closedBall (0 : ∀ i, S i → S i → ℝ) 1 := by
    intro τ
    rw [Metric.mem_closedBall, dist_pi_le_iff zero_le_one]
    intro i'
    rw [dist_pi_le_iff zero_le_one]
    intro j
    rw [dist_pi_le_iff zero_le_one]
    intro k
    rw [Real.dist_eq, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply, sub_zero,
      abs_of_nonneg (nonneg_of_mem_rowStochastic (hA τ i'))]
    exact le_one_of_mem_rowStochastic (hA τ i')
  set D : ℝ := ∑ i', (Fintype.card (S i') : ℝ)
  have hD : ∀ i', (Fintype.card (S i') : ℝ) ≤ D := fun i' =>
    single_le_sum (f := fun i' => (Fintype.card (S i') : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      (mem_univ i')
  have hda : ∀ τ, dist (a (τ + 1)) (a τ) ≤ D * (4 * M / μ) / (τ + 2) := by
    intro τ
    have h0 : 0 ≤ D * (4 * M / μ) / (τ + 2) := by
      have : 0 ≤ D := sum_nonneg fun _ _ => Nat.cast_nonneg _
      positivity
    rw [dist_pi_le_iff h0]
    intro i'
    rw [dist_pi_le_iff h0]
    intro j
    rw [dist_pi_le_iff h0]
    intro k
    rw [Real.dist_eq]
    refine (abs_rmMatrix_succ_sub_le hM hμ0 x τ i' j k).trans ?_
    gcongr
    exact hD i'
  have ha : Tendsto (fun τ => dist (a (τ + 1)) (a τ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun τ => dist_nonneg) hda ?_
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hF := tendsto_dist_comp_succ (isCompact_closedBall _ _) (continuous_poissonCorr (cost i) i v)
    haK ha
  refine tendsto_sum_mul_sub_div_sq (B := v * (2 * M))
    (fun τ => abs_poissonCorr_le (hA τ) i (hM i) v _) ?_
  refine squeeze_zero_norm (fun τ => ?_) hF
  rw [Real.norm_eq_abs, ← hFa, ← hFa, abs_sub_comm, ← Real.dist_eq]
  exact dist_le_pi_dist (F (a (τ + 1))) (F (a τ)) (x (τ + 1))
/-! ### The martingale part -/

/-- The martingale part of the decomposition is `o(t²)` almost surely. -/
private lemma ae_tendsto_martingale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hM : ∀ i s, |cost i s| ≤ M)
    (hμ : ∀ i, 2 * M * ((Fintype.card (S i) : ℝ) - 1) < μ) (X : ℕ → Ω → ∀ i, S i)
    (hX : ∀ t s, MeasurableSet {ω | X t ω = s})
    (hlaw : ∀ t s,
      P[{ω | X (t + 1) ω = s}.indicator (fun _ => (1 : ℝ)) | historySigma X t] =ᵐ[P]
        fun ω => ∏ i, regretMatching cost μ (fun k : Fin (t + 1) => X k ω) i (s i))
    (i : ι) (v : ℕ) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℕ => (∑ τ ∈ range t, ((τ : ℝ) + 1) *
      (corrSum (cost i) i v (rmMatrix cost μ fun k : Fin (τ + 1) => X k ω) (X (τ + 1) ω) -
        poissonCorr (cost i) i v (rmMatrix cost μ fun k : Fin (τ + 1) => X k ω) (X τ ω))) /
        ((t : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
  let ℱ : Filtration ℕ ‹MeasurableSpace Ω› :=
    ⟨historySigma X, historySigma_mono X, historySigma_le hX⟩
  set A : ℕ → Ω → ∀ i, Matrix (S i) (S i) ℝ :=
    fun τ ω => rmMatrix cost μ fun k : Fin (τ + 1) => X k ω with hAdef
  set F : ℕ → Ω → ℝ := fun τ ω => corrSum (cost i) i v (A τ ω) (X (τ + 1) ω) with hFdef
  set G : ℕ → Ω → ℝ := fun τ ω => poissonCorr (cost i) i v (A τ ω) (X τ ω) with hGdef
  have hA : ∀ τ ω i', A τ ω i' ∈ rowStochastic ℝ (S i') := fun τ ω i' =>
    (rmMatrix_mem_rowStochastic hM (hμ i') _).1
  have hAcongr : ∀ τ ω ω', (∀ k ≤ τ, X k ω = X k ω') → A τ ω = A τ ω' := by
    intro τ ω ω' h
    simp only [hAdef]
    congr 1
    funext k
    exact h k (Nat.lt_succ_iff.1 k.2)
  have hGm : ∀ τ, StronglyMeasurable[ℱ τ] (G τ) := fun τ =>
    (measurable_historySigma fun ω ω' h => by
      simp only [hGdef, hAcongr τ ω ω' h, h τ le_rfl]).stronglyMeasurable
  have hFm : ∀ τ, StronglyMeasurable[ℱ (τ + 1)] (F τ) := fun τ =>
    (measurable_historySigma fun ω ω' h => by
      simp only [hFdef, hAcongr τ ω ω' fun k hk => h k (hk.trans τ.le_succ),
        h (τ + 1) le_rfl]).stronglyMeasurable
  have hFK : ∀ τ ω, |F τ ω| ≤ v * (2 * M) := fun τ ω => abs_corrSum_le (hA τ ω) i (hM i) v _
  have hGK : ∀ τ ω, |G τ ω| ≤ v * (2 * M) := fun τ ω =>
    abs_poissonCorr_le (hA τ ω) i (hM i) v _
  have hFint : ∀ τ, Integrable (F τ) P := fun τ =>
    Integrable.of_bound ((hFm τ).mono (ℱ.le _)).aestronglyMeasurable _
      (ae_of_all _ fun ω => (Real.norm_eq_abs _).le.trans (hFK τ ω))
  have hGint : ∀ τ, Integrable (G τ) P := fun τ =>
    Integrable.of_bound ((hGm τ).mono (ℱ.le _)).aestronglyMeasurable _
      (ae_of_all _ fun ω => (Real.norm_eq_abs _).le.trans (hGK τ ω))
  set e : ℕ → Ω → ℝ := fun τ => F τ - G τ with hedef
  have he : ∀ τ, StronglyMeasurable[ℱ (τ + 1)] (e τ) := fun τ =>
    (hFm τ).sub ((hGm τ).mono (ℱ.mono τ.le_succ))
  have heK : ∀ τ, ∀ᵐ ω ∂P, |e τ ω| ≤ 2 * (v * (2 * M)) := fun τ => ae_of_all _ fun ω => by
    simp only [hedef, Pi.sub_apply]
    linarith [abs_sub (F τ ω) (G τ ω), hFK τ ω, hGK τ ω]
  have hce : ∀ τ, P[e τ | ℱ τ] =ᵐ[P] 0 := by
    intro τ
    have h1 := condExp_sub (hFint τ) (hGint τ) (ℱ τ : MeasurableSpace Ω)
    have h2 : P[G τ | ℱ τ] = G τ := condExp_of_stronglyMeasurable (ℱ.le τ) (hGm τ) (hGint τ)
    have h3 : P[F τ | ℱ τ] =ᵐ[P] G τ := by
      have hc := condExp_comp_eq_sum (μ := P) (ℱ.le τ) (hX (τ + 1))
        (g := fun s ω => corrSum (cost i) i v (A τ ω) s) (K := v * (2 * M))
        (fun s => (measurable_historySigma fun ω ω' h => by
          simp only [hAcongr τ ω ω' h]).stronglyMeasurable)
        (fun s ω => abs_corrSum_le (hA τ ω) i (hM i) v s)
      filter_upwards [hc, ae_all_iff.2 (hlaw τ)] with ω hc hl
      rw [hFdef, hc]
      simp only [hGdef, poissonCorr, mulVec, dotProduct, prodKernel, Matrix.of_apply]
      refine sum_congr rfl fun s _ => ?_
      rw [mul_comm]
      exact congrArg (· * _) (hl s)
    filter_upwards [h1, h3] with ω h1 h3
    rw [hedef]
    dsimp only
    rw [h1, Pi.sub_apply, h3, h2, sub_self, Pi.zero_apply]
  filter_upwards [ae_exists_tendsto_sum_div_succ (μ := P) ℱ he heK hce] with ω ⟨c, hc⟩
  refine (MetaMathlibExt.tendsto_sum_range_add_one_sq_mul_div_of_tendsto hc).congr fun t => ?_
  congr 1
  refine sum_congr rfl fun τ _ => ?_
  simp only [hedef, Pi.sub_apply, hFdef, hGdef, hAdef]
  field_simp

/-! ### Conclusion -/

/-- Correlated `ε`-equilibria are correlated `ε'`-equilibria for `ε ≤ ε'`. -/
private lemma isCorrelatedEq_of_le {ψ : (∀ i, S i) → ℝ} {ε ε' : ℝ}
    (h : IsCorrelatedEq cost ψ ε) (hε : ε ≤ ε') : IsCorrelatedEq cost ψ ε' :=
  ⟨h.1, fun i j k => (h.2 i j k).trans hε⟩

/-- Approximate correlated equilibria are close to correlated equilibria. -/
private lemma exists_forall_infDist_lt (cost : ι → (∀ i, S i) → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ ψ, IsCorrelatedEq cost ψ ε →
      Metric.infDist ψ {ψ | IsCorrelatedEq cost ψ 0} < δ := by
  set C := {ψ : (∀ i, S i) → ℝ | IsCorrelatedEq cost ψ 0}
  set T : ℕ → Set ((∀ i, S i) → ℝ) := fun n =>
    {ψ | IsCorrelatedEq cost ψ (1 / ((n : ℝ) + 1))} ∩ (Metric.thickening δ C)ᶜ
  have hdisj : Disjoint {ψ | IsCorrelatedEq cost ψ 1} (⋂ n, T n) := by
    rw [Set.disjoint_left]
    intro ψ _ hψ
    rw [Set.mem_iInter] at hψ
    have hC : ψ ∈ C := by
      refine ⟨(hψ 0).1.1, fun i j k => ?_⟩
      by_contra hpos
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (not_le.1 hpos)
      exact absurd ((hψ n).1.2 i j k) (not_le.2 hn)
    exact (hψ 0).2 (Metric.self_subset_thickening hδ C hC)
  have hanti : Antitone T := fun n m hnm => Set.inter_subset_inter_left _ fun ψ hψ =>
    isCorrelatedEq_of_le hψ (one_div_le_one_div_of_le (by positivity) (by
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      linarith))
  obtain ⟨n, hn⟩ := (isCompact_setOf_isCorrelatedEq cost 1).elim_directed_family_closed T
    (fun n => (isClosed_setOf_isCorrelatedEq cost _).inter Metric.isOpen_thickening.isClosed_compl)
    hdisj hanti.directed_ge
  refine ⟨1 / ((n : ℝ) + 1), by positivity, fun ψ hψ => ?_⟩
  have h1 : ψ ∈ {ψ | IsCorrelatedEq cost ψ 1} :=
    isCorrelatedEq_of_le hψ (by rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)])
  have h2 : ψ ∈ Metric.thickening δ C := by
    by_contra h
    exact Set.disjoint_left.1 hn h1 ⟨hψ, h⟩
  obtain ⟨z, hz, hd⟩ := Metric.mem_thickening_iff.1 h2
  exact (Metric.infDist_le_dist_of_mem hz).trans_lt hd

/-- Under regret matching, every conditional regret of every player is eventually at most
`(t + 1) δ`, almost surely. -/
private lemma ae_eventually_condRegret_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hM : ∀ i s, |cost i s| ≤ M)
    (hμ : ∀ i, 2 * M * ((Fintype.card (S i) : ℝ) - 1) < μ) (X : ℕ → Ω → ∀ i, S i)
    (hX : ∀ t s, MeasurableSet {ω | X t ω = s})
    (hlaw : ∀ t s,
      P[{ω | X (t + 1) ω = s}.indicator (fun _ => (1 : ℝ)) | historySigma X t] =ᵐ[P]
        fun ω => ∏ i, regretMatching cost μ (fun k : Fin (t + 1) => X k ω) i (s i))
    (i : ι) :
    ∀ᵐ ω ∂P, ∀ δ > 0, ∀ᶠ t : ℕ in atTop, ∀ j k,
      condRegret cost (fun k : Fin (t + 1) => X k ω) i j k ≤ ((t : ℝ) + 1) * δ := by
  filter_upwards [ae_all_iff.2 (ae_tendsto_martingale hM hμ X hX hlaw i)] with ω hmart
  intro δ hδ
  set x : ℕ → ∀ i, S i := fun t => X t ω
  have hM0 : 0 ≤ M := by linarith [abs_nonneg (cost i (x 0)), hM i (x 0)]
  have hcard : (1 : ℝ) ≤ Fintype.card (S i) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨x 0 i⟩
  have hμ0 : 0 < μ := lt_of_le_of_lt (by nlinarith) (hμ i)
  set q := min (1 - 2 * M * ((Fintype.card (S i) : ℝ) - 1) / μ) (1 / 2)
  have hq0 : 0 < q := lt_min (by rw [sub_pos, div_lt_one hμ0]; exact hμ i) (by norm_num)
  have hq1 : q < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hdiag : ∀ t j, q ≤ rmMatrix cost μ (fun k : Fin (t + 1) => x k) i j j := fun t j =>
    (min_le_left _ _).trans ((rmMatrix_mem_rowStochastic hM (hμ i) _).2 j)
  -- choose `v` with `2 μ M / (q √(v + 1)) < δ² / 2`
  have hsmall : Tendsto (fun v : ℕ => M / (q * Real.sqrt ((v : ℝ) + 1))) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop hq0 ?_)
    exact Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  obtain ⟨v, hv⟩ := (hsmall.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < δ ^ 2 / (4 * μ)))).exists
  have hlim : Tendsto (fun t : ℕ => Fintype.card (S i) ^ 2 * (2 * M) ^ 2 / ((t : ℝ) + 1) + 2 * μ *
      ((∑ τ ∈ range t, ((τ : ℝ) + 1) *
          (corrSum (cost i) i v (rmMatrix cost μ fun k : Fin (τ + 1) => x k) (x (τ + 1)) -
            poissonCorr (cost i) i v (rmMatrix cost μ fun k : Fin (τ + 1) => x k) (x τ))) /
          ((t : ℝ) + 1) ^ 2 +
        (∑ τ ∈ range t, ((τ : ℝ) + 1) *
          (poissonCorr (cost i) i v (rmMatrix cost μ fun k : Fin (τ + 1) => x k) (x τ) -
            poissonCorr (cost i) i v (rmMatrix cost μ fun k : Fin (τ + 1) => x k) (x (τ + 1)))) /
          ((t : ℝ) + 1) ^ 2 + M / (q * Real.sqrt (v + 1)))) atTop
      (𝓝 (0 + 2 * μ * (0 + 0 + M / (q * Real.sqrt (v + 1))))) :=
    (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1
      tendsto_natCast_atTop_atTop)).add
      (((hmart v).add (tendsto_telescope hM hμ x i v)).add tendsto_const_nhds |>.const_mul _)
  have hlt : 0 + 2 * μ * (0 + 0 + M / (q * Real.sqrt (v + 1))) < δ ^ 2 := by
    have : 2 * μ * (M / (q * Real.sqrt (v + 1))) < 2 * μ * (δ ^ 2 / (4 * μ)) :=
      mul_lt_mul_of_pos_left hv (by positivity)
    rw [show 2 * μ * (δ ^ 2 / (4 * μ)) = δ ^ 2 / 2 by field_simp; ring] at this
    nlinarith [sq_nonneg δ]
  filter_upwards [hlim.eventually (gt_mem_nhds hlt)] with t ht j k
  have hV := (regretPotential_div_le hM hμ x i v hq0 hq1 hdiag t).trans_lt ht
  have hjk : max (condRegret cost (fun k : Fin (t + 1) => x k) i j k) 0 ^ 2 ≤
      regretPotential cost i (fun k : Fin (t + 1) => x k) := by
    unfold regretPotential
    refine (single_le_sum (f := fun k => max (condRegret cost (fun k : Fin (t + 1) => x k) i j k)
      0 ^ 2) (fun _ _ => sq_nonneg _) (mem_univ k)).trans ?_
    exact single_le_sum (f := fun j => ∑ k, max (condRegret cost (fun k : Fin (t + 1) => x k)
      i j k) 0 ^ 2) (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (mem_univ j)
  have ht0 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have h2 : (max (condRegret cost (fun k : Fin (t + 1) => x k) i j k) 0 / ((t : ℝ) + 1)) ^ 2 <
      δ ^ 2 := by
    rw [div_pow]
    exact (div_le_div_of_nonneg_right hjk (by positivity)).trans_lt hV
  have h3 := (pow_lt_pow_iff_left₀ (div_nonneg (le_max_right _ _) ht0.le) hδ.le two_ne_zero).1 h2
  rw [div_lt_iff₀ ht0] at h3
  have := le_max_left (condRegret cost (fun k : Fin (t + 1) => x k) i j k) 0
  change condRegret cost (fun k : Fin (t + 1) => x k) i j k ≤ ((t : ℝ) + 1) * δ
  linarith


end Helpers

/-- **Regret matching leads to correlated equilibria** (Hart and Mas-Colell 2000, Main Theorem;
Hart 2005, Theorem 1). Let `|cost i s| ≤ M` and `μ > 2 M (|Sᵢ| − 1)` for every player
(footnote 5). If the first round is arbitrary and, given the history of the first `t + 1`
rounds, the players choose the next round's actions independently, each according to regret
matching (2.2), then almost surely the empirical distributions of play (2.3) converge to the set
of correlated equilibria. -/
theorem regretMatching_tendsto_correlatedEq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (cost : ι → (∀ i, S i) → ℝ) {M μ : ℝ}
    (hM : ∀ i s, |cost i s| ≤ M) (hμ : ∀ i, 2 * M * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (X : ℕ → Ω → ∀ i, S i) (hX : ∀ t s, MeasurableSet {ω | X t ω = s})
    (hlaw : ∀ t s,
      P[{ω | X (t + 1) ω = s}.indicator (fun _ => (1 : ℝ)) | historySigma X t] =ᵐ[P]
        fun ω => ∏ i, regretMatching cost μ (fun k : Fin (t + 1) => X k ω) i (s i)) :
    ∀ᵐ ω ∂P, Tendsto (fun T : ℕ => Metric.infDist
      (empirical (fun k : Fin (T + 1) => X k ω)) {ψ | IsCorrelatedEq cost ψ 0}) atTop (𝓝 0) := by
  filter_upwards [ae_all_iff.2 fun i => ae_eventually_condRegret_le hM hμ X hX hlaw i]
    with ω hω
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun T =>
    ha.trans_le Metric.infDist_nonneg, fun δ hδ => ?_⟩
  obtain ⟨ε, hε, hCE⟩ := exists_forall_infDist_lt cost hδ
  filter_upwards [eventually_all.2 fun i => hω i ε hε] with T hT
  refine hCE _ ((isCorrelatedEq_empirical_iff _ ε).2 fun i j k => ?_)
  have := hT i j k
  push_cast
  exact this

end RegretMatching

end MathlibExt.GameTheory.RegretMatchingWanted
