/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import MathlibExt.NumberTheory.ArithmeticFunction.GcdSumTotient

/-!
# The Dirichlet series of the squared mean gcd-sum function

The series of `gcdSumMean n ^ 2` factors as the fourth power of the Riemann zeta function
divided by its value at twice the argument, times an absolutely convergent correction series.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The mean gcd-sum function.** For a natural number $n$, let $P(n) = \sum_{j=1}^{n} \gcd(j, n)$
be Pillai's gcd-sum function. The mean gcd-sum function is the real-valued function given by
$A(n) = P(n)/n$ for $n \ge 1$ and $A(0) = 0$.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Section 1 (definition of `A(n)`). -/
noncomputable def gcdSumMean (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 n, (Nat.gcd j n : ℝ)) / n

/-- **The mean gcd-sum function at $1$.** The mean gcd-sum function $A$ satisfies $A(1) = 1$.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Section 1 (definition of `A(n)`). -/
theorem gcdSumMean_one : gcdSumMean 1 = 1 := by
  simp [gcdSumMean]

/-- **The mean gcd-sum function at $2$.** The mean gcd-sum function $A$ satisfies $A(2) = 3/2$,
since $A(2) = P(2)/2$, where $P(n) = \sum_{j=1}^{n} \gcd(j, n)$ is Pillai's gcd-sum function
and $P(2) = \gcd(1, 2) + \gcd(2, 2) = 3$.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Section 1 (definition of `A(n)`). -/
theorem gcdSumMean_two : gcdSumMean 2 = 3 / 2 := by
  rw [gcdSumMean, show Finset.Icc 1 2 = {1, 2} by decide]
  norm_num

/-- **Divisor-sum formula for the mean gcd-sum function.** For every natural number $n \ge 1$,
the mean gcd-sum function $A$ satisfies $A(n) = \sum_{d \mid n} \varphi(d)/d$, where $\varphi$ is
Euler's totient function and the sum runs over the positive divisors $d$ of $n$.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Section 1 (Pillai's identity). -/
theorem gcdSumMean_eq_sum_totient_div {n : ℕ} (hn : 0 < n) :
    gcdSumMean n = ∑ d ∈ n.divisors, (Nat.totient d : ℝ) / d := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (gcd_sum_eq_totient_sum n hn)
  push_cast at h
  rw [gcdSumMean, h]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end

namespace GcdSumMeanSquare

open ArithmeticFunction

private noncomputable def totientRatio : ArithmeticFunction ℝ :=
  ⟨fun n => (n.totient : ℝ) / n, by simp⟩

private lemma mean_eq (n : ℕ) :
    gcdSumMean n = ((zeta : ArithmeticFunction ℝ) * totientRatio) n := by
  cases n with
  | zero => simp [gcdSumMean]
  | succ n =>
    rw [coe_zeta_mul_apply]
    exact gcdSumMean_eq_sum_totient_div n.succ_pos

end GcdSumMeanSquare

open ArithmeticFunction GcdSumMeanSquare in
/-- **Multiplicativity of the mean gcd-sum function.** For coprime natural numbers $m$ and $n$,
the mean gcd-sum function satisfies $A(mn) = A(m)A(n)$.

Source: László Tóth, *Another generalization of the gcd-sum function*, Arab. J. Math. 2 (2013),
313–320, arXiv:1306.1020, Section 1, which gives, for $n \ge 1$, Pillai's identity
$A(n) = \sum_{d \mid n} \varphi(d)/d$ and the product formula
$A(n) = \prod_{p \mid n} (1 + \nu_p(n)(1 - 1/p))$ over the primes $p$ dividing $n$, where
$\nu_p(n)$ is the exponent of $p$ in $n$. Either one gives multiplicativity: the first writes $A$
as a sum over divisors of the multiplicative function $d \mapsto \varphi(d)/d$. -/
public theorem gcdSumMean_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    gcdSumMean (m * n) = gcdSumMean m * gcdSumMean n := by
  have hr : totientRatio.IsMultiplicative := by
    refine ⟨by simp [totientRatio], fun {m n} h => ?_⟩
    change ((m * n).totient : ℝ) / (m * n : ℕ) = _
    simp [totientRatio, Nat.totient_mul h, mul_div_mul_comm]
  simpa only [mean_eq] using (isMultiplicative_zeta.natCast.mul hr).2 h

/-- **Mean gcd-sum at a prime power.** For every prime $p$ and every nonnegative integer $k$,
the mean gcd-sum function satisfies $A(p^k) = 1 + k(1 - 1/p)$.

Source: László Tóth, *Another generalization of the gcd-sum function*, Arab. J. Math. 2 (2013),
313–320, arXiv:1306.1020, Section 1: the case $n = p^k$ of the product formula
$A(n) = \prod_{q \mid n} (1 + \nu_q(n)(1 - 1/q))$ over the primes $q$ dividing $n$, where
$\nu_q(n)$ is the exponent of $q$ in $n$. It also follows from Pillai's identity
$A(n) = \sum_{d \mid n} \varphi(d)/d$, given there too: for $n = p^k$ the divisor $1$
contributes $1$ and each divisor $p^j$ with $1 \le j \le k$ contributes
$\varphi(p^j)/p^j = 1 - 1/p$. -/
public theorem gcdSumMean_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    gcdSumMean (p ^ k) = 1 + k * (1 - (p : ℝ)⁻¹) := by
  rw [gcdSumMean_eq_sum_totient_div (pow_pos hp.pos _), Nat.sum_divisors_prime_pow hp]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Nat.totient_prime_pow_succ hp]
    have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    push_cast [Nat.cast_sub hp.one_le]
    rw [pow_succ]
    field_simp
    ring

/-- **Absolute summability from bounds at prime powers.** Let $F$ be a multiplicative complex
arithmetic function. Suppose $b,d$ are nonnegative summable sequences and
$|F(p^{k+1})| \le b(p)d(k)$ for every prime $p$ and every $k \ge 0$. Then $\sum_n |F(n)|$ is
finite.

Source: standard argument from unique factorization. Distinct $n \ge 1$ give distinct finite
sets of pairs $(p, \nu_p(n))$, where $p$ runs over the primes dividing $n$ and $\nu_p(n) \ge 1$ is
the exponent of $p$ in $n$, and multiplicativity bounds $|F(n)|$ by the product of
$b(p)\,d(\nu_p(n) - 1)$ over these pairs. Hence $\sum_{n \ge 1} |F(n)|$ is at most
the sum, over all finite sets of pairs $(p, k)$ with $p$ prime and $k \ge 1$, of the product of
$b(p)\,d(k - 1)$ over the set, and this sum is at most
$\exp\left(\sum_p b(p) \sum_k d(k)\right)$. -/
public theorem summable_of_prime_power_bound {F : ArithmeticFunction ℂ} (hF : F.IsMultiplicative)
    {b d : ℕ → ℝ} (hb : Summable b) (hd : Summable d)
    (hb₀ : ∀ n, 0 ≤ b n) (hd₀ : ∀ n, 0 ≤ d n)
    (h : ∀ p k : ℕ, p.Prime → ‖F (p ^ (k + 1))‖ ≤ b p * d k) :
    Summable (fun n => ‖F n‖) := by
  let w (q : ℕ × ℕ) := b q.1 * d (q.2 - 1)
  have hd' : Summable (fun e : ℕ => d (e - 1)) := (summable_nat_add_iff 1).mp (by simpa)
  have hw : Summable w := hb.mul_of_nonneg hd' hb₀ (fun k => hd₀ _)
  have hall := summable_finsetProd_of_summable_nonneg (f := w)
    (fun q => mul_nonneg (hb₀ _) (hd₀ _)) hw
  let graph (n : ℕ) := (n + 1).factorization.graph
  have hinj : Function.Injective graph := by
    intro m n hmn
    exact Nat.succ.inj (Nat.factorization_inj m.succ_ne_zero n.succ_ne_zero
      (Finsupp.graph_inj.mp hmn))
  apply (summable_nat_add_iff 1).mp
  refine (hall.comp_injective hinj).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
  change ‖F (n + 1)‖ ≤ ∏ q ∈ (n + 1).factorization.graph, w q
  rw [hF.multiplicative_factorization F n.succ_ne_zero, Finsupp.prod, norm_prod,
    Finsupp.graph, Finset.prod_map]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro p hp
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  change ‖F (p ^ _)‖ ≤ b p * d ((n + 1).factorization p - 1)
  simpa [hk] using h p k (Nat.prime_of_mem_primeFactors hp)

namespace GcdSumMeanSquare

open ArithmeticFunction Complex

-- The local correction is 1 + (u² - 4u)x + 4u x²/(1 + x), where u = 1/p.
private noncomputable def localCoeff (u : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => u ^ 2 - 4 * u
  | k + 2 => 4 * u * (-1) ^ k

private noncomputable def correction : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod fun p => localCoeff (p : ℝ)⁻¹, by simp⟩

private lemma correction_mult : correction.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨by simp [correction], fun hm hn h => ?_⟩
  simp only [correction, coe_mk, ite_eq_right hm, ite_eq_right hn, ite_eq_right (mul_ne_zero hm hn),
    Nat.factorization_mul_of_coprime h]
  apply Finsupp.prod_add_index_of_disjoint
  exact h.disjoint_primeFactors

private lemma correction_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    correction (p ^ k) = localCoeff (p : ℝ)⁻¹ k := by
  simp only [correction, coe_mk, pow_ne_zero k hp.ne_zero, ↓reduceIte, hp.factorization_pow]
  exact Finsupp.prod_single_index (by rfl)

private noncomputable def meanSquare : ArithmeticFunction ℝ :=
  ⟨fun n => gcdSumMean n ^ 2, by simp [gcdSumMean]⟩

private lemma meanSquare_mult : meanSquare.IsMultiplicative :=
  ⟨by simp [meanSquare, gcdSumMean_one], fun {m n} h => by
    simp [meanSquare, gcdSumMean_mul_of_coprime h, mul_pow]⟩

private noncomputable def twist (f : ArithmeticFunction ℝ) {s : ℂ} (hs : s ≠ 0) :
    ArithmeticFunction ℂ :=
  ⟨fun n => (f n : ℂ) * riemannZetaSummandHom hs n, by simp⟩

private lemma twist_mult {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    {s : ℂ} (hs : s ≠ 0) : (twist f hs).IsMultiplicative := by
  refine ⟨by simp [twist, hf.1], fun {m n} h => ?_⟩
  simp [twist, hf.2 h, mul_mul_mul_comm]

private lemma twist_term (f : ArithmeticFunction ℝ) {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    twist f hs n = LSeries.term (fun n => (f n : ℂ)) s n := by
  simp [twist, riemannZetaSummandHom, LSeries.term_of_ne_zero' hs, cpow_neg, div_eq_mul_inv]

private lemma twist_prime_pow (f : ArithmeticFunction ℝ) {s : ℂ} (hs : s ≠ 0) (p k : ℕ) :
    twist f hs (p ^ k) = (f (p ^ k) : ℂ) * ((p : ℂ) ^ (-s)) ^ k := by
  simp only [twist, coe_mk, map_pow]
  rfl

private lemma summable_twist {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    {s : ℂ} (hs : 0 < s.re) (hs₀ : s ≠ 0) {b : ℕ → ℝ} (hb : Summable b)
    (hb₀ : ∀ n, 0 ≤ b n) (h : ∀ p k : ℕ, p.Prime →
      |f (p ^ (k + 1))| * (p : ℝ) ^ (-s.re) ≤ b p * (k + 2 : ℝ) ^ 2) :
    Summable (fun n => ‖twist f hs₀ n‖) := by
  let r : ℝ := 2 ^ (-s.re)
  have hr₀ : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_of_nonneg hr₀]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs)
  have hd : Summable (fun k : ℕ => (k + 2 : ℝ) ^ 2 * r ^ k) := by
    refine (((summable_pow_mul_geometric_of_norm_lt_one 2 hr).add
      ((hasSum_coe_mul_geometric_of_norm_lt_one hr).summable.mul_left 4)).add
        ((summable_geometric_of_norm_lt_one hr).mul_left 4)).congr (fun k => ?_)
    ring
  apply summable_of_prime_power_bound (twist_mult hf hs₀) hb hd hb₀ (fun k => by positivity)
  intro p k hp
  have hpr : (p : ℝ) ^ (-s.re) ≤ r :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
  rw [twist_prime_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
    norm_natCast_cpow_of_pos hp.pos, neg_re, pow_succ' ((p : ℝ) ^ (-s.re))]
  calc
    _ = (|f (p ^ (k + 1))| * (p : ℝ) ^ (-s.re)) * ((p : ℝ) ^ (-s.re)) ^ k := by ring
    _ ≤ (b p * (k + 2 : ℝ) ^ 2) * r ^ k :=
      mul_le_mul (h p k hp) (pow_le_pow_left₀ (by positivity) hpr k) (by positivity)
        (mul_nonneg (hb₀ _) (sq_nonneg _))
    _ = _ := mul_assoc ..

private lemma inv_prime_bounds {p : ℕ} (hp : p.Prime) :
    0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1 :=
  ⟨by positivity, inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)⟩

private lemma meanSquare_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => ‖twist meanSquare (ne_zero_of_one_lt_re hs) n‖) := by
  apply summable_twist meanSquare_mult (zero_lt_one.trans hs) _
    (Real.summable_nat_rpow.mpr (show -s.re < -1 by linarith)) (fun n => by positivity)
  intro p k hp
  change |gcdSumMean (p ^ (k + 1)) ^ 2| * _ ≤ _
  rw [abs_of_nonneg (sq_nonneg _), gcdSumMean_prime_pow hp]
  obtain ⟨hu₀, hu₁⟩ := inv_prime_bounds hp
  rw [mul_comm ((p : ℝ) ^ (-s.re))]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  push_cast
  nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity) hu₀]

private lemma abs_localCoeff_le {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (k : ℕ) :
    |localCoeff u (k + 1)| ≤ 4 * u := by
  cases k with
  | zero =>
    change |u ^ 2 - 4 * u| ≤ 4 * u
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hu₀ (sub_nonneg.mpr hu₁), sq_nonneg u]
  | succ k => simp [localCoeff, abs_mul, abs_pow, abs_of_nonneg hu₀]

private lemma correction_summable {s : ℂ} (hs : 0 < s.re) (hs₀ : s ≠ 0) :
    Summable (fun n => ‖twist correction hs₀ n‖) := by
  apply summable_twist correction_mult hs hs₀
    ((Real.summable_nat_rpow.mpr (show -1 - s.re < -1 by linarith)).mul_left 4)
    (fun n => by positivity)
  intro p k hp
  obtain ⟨hu₀, hu₁⟩ := inv_prime_bounds hp
  rw [correction_prime_pow hp]
  calc
    _ ≤ 4 * (p : ℝ)⁻¹ * (p : ℝ) ^ (-s.re) := by
      gcongr
      exact abs_localCoeff_le hu₀ hu₁ k
    _ = 4 * (p : ℝ) ^ (-1 - s.re) := by
      rw [sub_eq_add_neg, Real.rpow_add (by exact_mod_cast hp.pos), Real.rpow_neg_one]
      ring
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) k])

private lemma mean_local_sum (u x : ℂ) (hx : ‖x‖ < 1) :
    ∑' k : ℕ, (1 + k * (1 - u)) ^ 2 * x ^ k =
      (1 - x)⁻¹ + 2 * (1 - u) * (x / (1 - x) ^ 2) +
        (1 - u) ^ 2 * (x * (1 + x) / (1 - x) ^ 3) := by
  apply HasSum.tsum_eq
  refine (((hasSum_geometric_of_norm_lt_one hx).add
    ((hasSum_coe_mul_geometric_of_norm_lt_one hx).mul_left (2 * (1 - u)))).add
      ((hasSum_sq_mul_geometric_of_norm_lt_one hx).mul_left ((1 - u) ^ 2))).congr_fun ?_
  intro k
  ring

private lemma correction_local_sum (u : ℝ) (x : ℂ) (hx : ‖x‖ < 1) :
    ∑' k : ℕ, (localCoeff u k : ℂ) * x ^ k =
      1 + ((u : ℂ) ^ 2 - 4 * u) * x + 4 * u * x ^ 2 * (1 + x)⁻¹ := by
  apply HasSum.tsum_eq
  rw [← hasSum_nat_add_iff' 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, localCoeff, ofReal_one, pow_zero,
    mul_one, zero_add, ofReal_sub, ofReal_pow, ofReal_mul, ofReal_ofNat, pow_one,
    add_sub_cancel_left]
  have hg := (hasSum_geometric_of_norm_lt_one (ξ := -x) (by simpa)).mul_left
    (4 * (u : ℂ) * x ^ 2)
  rw [sub_neg_eq_add] at hg
  apply hg.congr_fun
  intro k
  push_cast
  rw [neg_eq_neg_one_mul x, mul_pow, pow_add]
  ring

private lemma local_identity (u : ℝ) {x : ℂ} (hx : ‖x‖ < 1) :
    (∑' k : ℕ, (1 + k * (1 - (u : ℂ))) ^ 2 * x ^ k) * (1 - x ^ 2)⁻¹ =
      ((1 - x)⁻¹) ^ 4 * ∑' k : ℕ, (localCoeff u k : ℂ) * x ^ k := by
  have h₁ := (isUnit_one_sub_of_norm_lt_one hx).ne_zero
  have h₂ : 1 + x ≠ 0 := by
    simpa using (isUnit_one_sub_of_norm_lt_one (x := -x) (by simpa)).ne_zero
  have h₃ : 1 - x ^ 2 ≠ 0 := by
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
    exact mul_ne_zero h₁ h₂
  rw [mean_local_sum _ _ hx, correction_local_sum _ _ hx]
  field_simp
  ring

private lemma eulerProduct {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    {s : ℂ} (hs₀ : s ≠ 0) (hsum : Summable (fun n => ‖twist f hs₀ n‖)) :
    HasProd (fun p : Nat.Primes => ∑' k : ℕ, (f (p.val ^ k) : ℂ) * ((p : ℂ) ^ (-s)) ^ k)
      (LSeries (fun n => (f n : ℂ)) s) := by
  have h := (twist_mult hf hs₀).eulerProduct_hasProd hsum
  simp only [twist_prime_pow] at h
  simpa only [twist_term, LSeries] using h

end GcdSumMeanSquare

open GcdSumMeanSquare Complex

/-- **Dirichlet series of the square of the mean gcd-sum function.** Let $A$ be the mean gcd-sum
function. There is a function $h \colon \mathbb{N} \to \mathbb{C}$ such that the Dirichlet series
$\tilde G_{2,2}(s) = \sum_{n \ge 1} h(n) n^{-s}$ converges absolutely for every complex $s$ with
$\operatorname{Re} s > 0$, and for every complex $s$ with $\operatorname{Re} s > 1$,
$$\sum_{n \ge 1} A(n)^2 n^{-s} = \frac{\zeta(s)^4}{\zeta(2s)} \, \tilde G_{2,2}(s).$$

This is the case $k = 2$ of the paper's Theorem 5, which gives the absolute convergence of
$\tilde G_{2,2}(s)$ in every half-plane $\operatorname{Re} s > 1/N$ with $N \ge 1$, that is, for
$\operatorname{Re} s > 0$.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 5 (`integers-2026-A70-thm-5`). -/
public theorem LSeries_gcdSumMean_sq_eq_riemannZeta_pow_four_div :
    ∃ h : ℕ → ℂ, (∀ s : ℂ, 0 < s.re → LSeriesSummable h s) ∧
      ∀ s : ℂ, 1 < s.re →
        LSeries (fun n => ((gcdSumMean n ^ 2 : ℝ) : ℂ)) s =
          riemannZeta s ^ 4 / riemannZeta (2 * s) * LSeries h s := by
  refine ⟨fun n => (correction n : ℂ), ?_, ?_⟩
  · intro s hs
    have hs₀ : s ≠ 0 := fun h => by simp [h] at hs
    exact (correction_summable hs hs₀).of_norm.congr (twist_term correction hs₀)
  intro s hs
  have hs₀ := ne_zero_of_one_lt_re hs
  have h₂s : 1 < (2 * s).re := by rw [two_mul, add_re]; linarith
  have hA := eulerProduct meanSquare_mult hs₀ (meanSquare_summable hs)
  have hH := eulerProduct correction_mult hs₀ (correction_summable (by linarith) hs₀)
  have hleft := hA.mul (riemannZeta_eulerProduct_hasProd h₂s)
  have hright := ((riemannZeta_eulerProduct_hasProd hs).pow 4).mul hH
  have hEq : LSeries (fun n => (meanSquare n : ℂ)) s * riemannZeta (2 * s) =
      riemannZeta s ^ 4 * LSeries (fun n => (correction n : ℂ)) s := by
    apply hleft.unique (hright.congr_fun ?_)
    intro p
    have hx : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_natCast_cpow_of_pos p.prop.pos, neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
    simp only [meanSquare, ArithmeticFunction.coe_mk, gcdSumMean_prime_pow p.prop, ofReal_pow,
      ofReal_add, ofReal_one, ofReal_mul, ofReal_natCast, ofReal_sub, correction_prime_pow p.prop,
      show -(2 * s) = (2 : ℕ) * (-s) by push_cast; ring, cpow_nat_mul]
    exact local_identity (p.val : ℝ)⁻¹ hx
  change LSeries (fun n => (meanSquare n : ℂ)) s = _
  rw [div_mul_eq_mul_div, eq_div_iff (riemannZeta_ne_zero_of_one_lt_re h₂s)]
  exact hEq

end MetaMathlibExt
