/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.ExpectationMaximization
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# EM for mixtures of Bernoulli distributions

The EM algorithm for a mixture of `K` products of `d` independent Bernoulli distributions on
binary vectors `Fin d → Bool` (Bishop, *Pattern Recognition and Machine Learning*, Section 9.3.3),
as an instance of the generic EM of `LatentVariable/ExpectationMaximization.lean`.

Main results:

* `sum_mul_log_le_sum_mul_log_div`: the weighted log-likelihood `∑ c log w` over positive weights is
  bounded by its value at the normalized counts (Gibbs' inequality); with positive counts (as in
  the M-step) the bound is attained, giving both updates.
* `bernPMF`, `log_bernPMF`; `joint` on `ValidParams` (positive weights summing to one,
  probabilities in `(0, 1)`); `resp`: the E-step responsibilities are the posterior.
* The M-step `mStep`: `π k' = N k / N` (`mass`) and `p k j' = (∑ n, r n k xₙ j) / N k`
  (`ones`, `zeros`); it is valid on data with at least one point and both values in every
  coordinate (`Rich`, `mStep_valid`, `emStep`).
* `emQ_le_emStep`: **the M-step maximizes `Q(· | θ)`** over all valid parameters (`emQ_eq` splits
  it into the weights and one two-point term per component and coordinate).
* `logLik_le_emStep`: **each EM step does not decrease the log-likelihood**;
  `logLik_iterate_emStep_monotone`: monotone along the iterates.

## Cost model

None: the subject is the likelihood, over the reals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.LatentVariable.BernoulliMixture

open Real
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization

/-- **The weighted log-likelihood is bounded by its value at the normalized counts.** Let $Z$ be
a finite set, let $c \colon Z \to \mathbb{R}$ be nonnegative counts with positive total
$C = \sum_{z \in Z} c_z > 0$, and let $w \colon Z \to \mathbb{R}$ be positive weights with
$\sum_{z \in Z} w_z = 1$. Then $\sum_{z \in Z} c_z \log w_z \le \sum_{z \in Z} c_z \log(c_z / C)$
(Gibbs' inequality).

When every count is positive the normalized counts $c_z / C$ are themselves admissible weights,
so they maximize. -/
theorem sum_mul_log_le_sum_mul_log_div {Z : Type*} [Fintype Z] {c w : Z → ℝ}
    (hc : ∀ z, 0 ≤ c z) (hC : 0 < ∑ z, c z) (hw : ∀ z, 0 < w z) (hsum : ∑ z, w z = 1) :
    ∑ z, c z * log (w z) ≤ ∑ z, c z * log (c z / ∑ z', c z') := by
  set C := ∑ z, c z with hCdef
  have hq : IsDist fun z => c z / C :=
    ⟨fun z => div_nonneg (hc z) hC.le, by rw [← Finset.sum_div, div_self hC.ne']⟩
  have h := sum_mul_log_sub_le hw hq
  rw [hsum, log_one] at h
  have heq : ∑ z, c z * log (w z) - ∑ z, c z * log (c z / C) =
      C * ∑ z, c z / C * (log (w z) - log (c z / C)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    field_simp
  have : C * ∑ z, c z / C * (log (w z) - log (c z / C)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hC.le h
  linarith

/-! ## The model -/

variable {d K N : ℕ}

/-- **Product Bernoulli probability mass function.** For a vector $p \in \mathbb{R}^d$ of success
probabilities and a binary vector $x \in \{0, 1\}^d$, the probability of $x$ under the product of
$d$ independent Bernoulli distributions with parameters $p_1, \dots, p_d$ is
$$\prod_{j=1}^{d} p_j^{x_j} (1 - p_j)^{1 - x_j},$$
that is, the product over $j$ of $p_j$ when $x_j = 1$ and of $1 - p_j$ when $x_j = 0$. -/
noncomputable def bernPMF (p : Fin d → ℝ) (x : Fin d → Bool) : ℝ :=
  ∏ j, if x j then p j else 1 - p j

theorem bernPMF_pos {p : Fin d → ℝ} (h0 : ∀ j, 0 < p j) (h1 : ∀ j, p j < 1) (x : Fin d → Bool) :
    0 < bernPMF p x :=
  Finset.prod_pos fun j _ => by split_ifs <;> linarith [h0 j, h1 j]

theorem log_bernPMF {p : Fin d → ℝ} (h0 : ∀ j, 0 < p j) (h1 : ∀ j, p j < 1) (x : Fin d → Bool) :
    log (bernPMF p x) = ∑ j, if x j then log (p j) else log (1 - p j) := by
  rw [bernPMF, log_prod fun j _ => by split_ifs <;> linarith [h0 j, h1 j]]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> rfl

/-- **Parameters of a Bernoulli mixture.** The parameters of a mixture of $K$ products of $d$
Bernoulli distributions are real mixing weights $\pi_k$ for $k < K$ and real success
probabilities $p_{kj}$ for every component $k < K$ and coordinate $j < d$. No constraint is
imposed on these numbers here; the admissible ones are the valid parameters. -/
structure Params (d K : ℕ) where
  /-- The mixing weights. -/
  weight : Fin K → ℝ
  /-- The success probability of each coordinate in each component. -/
  prob : Fin K → Fin d → ℝ

/-- **Valid parameters of a Bernoulli mixture.** Parameters of a mixture of $K$ products of $d$
Bernoulli distributions, with mixing weights $\pi_k$ and success probabilities $p_{kj}$, are valid
when $\pi_k > 0$ for every $k < K$, $\sum_{k < K} \pi_k = 1$, and $0 < p_{kj} < 1$ for every
$k < K$ and $j < d$. -/
structure Params.Valid (θ : Params d K) : Prop where
  weight_pos : ∀ k, 0 < θ.weight k
  weight_sum : ∑ k, θ.weight k = 1
  prob_pos : ∀ k j, 0 < θ.prob k j
  prob_lt_one : ∀ k j, θ.prob k j < 1

/-- **The parameter space of a Bernoulli mixture.** The parameter space of EM for a mixture of
$K$ products of $d$ Bernoulli distributions is the set of valid parameters: mixing weights
$\pi_k$ and success probabilities $p_{kj}$ ($k < K$, $j < d$) with every $\pi_k > 0$,
$\sum_{k < K} \pi_k = 1$ and every $p_{kj}$ strictly between $0$ and $1$. -/
abbrev ValidParams (d K : ℕ) := {θ : Params d K // θ.Valid}

/-- **Joint distribution of the Bernoulli mixture.** For valid parameters $\theta$ of a mixture of
$K$ products of $d$ Bernoulli distributions, with mixing weights $\pi_k$ and success probabilities
$p_{kj}$, the joint probability of a binary vector $x \in \{0, 1\}^d$ and a component $k$ is
$$p_\theta(x, k) = \pi_k \prod_{j=1}^{d} p_{kj}^{x_j} (1 - p_{kj})^{1 - x_j},$$
that is, $\pi_k$ times the product Bernoulli probability of $x$ with parameters
$p_{k1}, \dots, p_{kd}$. -/
noncomputable def joint (θ : ValidParams d K) (x : Fin d → Bool) (k : Fin K) : ℝ :=
  θ.1.weight k * bernPMF (θ.1.prob k) x

theorem joint_pos (θ : ValidParams d K) (x : Fin d → Bool) (k : Fin K) : 0 < joint θ x k :=
  mul_pos (θ.2.weight_pos k) (bernPMF_pos (θ.2.prob_pos k) (θ.2.prob_lt_one k) x)

/-- **Responsibilities of a Bernoulli mixture.** Let $\theta$ be valid parameters of a mixture of
$K$ products of $d$ Bernoulli distributions, and write $p_\theta(x, k)$ for the joint probability
of a binary vector $x \in \{0,1\}^d$ and a component $k < K$ under $\theta$. The responsibility of
$k$ for $x$ is the posterior probability $r_k(x) = p_\theta(x, k) / \sum_{k' < K} p_\theta(x, k')$.
Computing it is the E-step of EM. -/
noncomputable def resp (θ : ValidParams d K) (x : Fin d → Bool) (k : Fin K) : ℝ :=
  posterior joint θ x k

theorem resp_pos (θ : ValidParams d K) (x : Fin d → Bool) (k : Fin K) : 0 < resp θ x k :=
  div_pos (joint_pos θ x k) (Finset.sum_pos (fun k _ => joint_pos θ x k) ⟨k, Finset.mem_univ k⟩)

theorem nonempty_of_valid (θ : ValidParams d K) : Nonempty (Fin K) := by
  by_contra h
  have : IsEmpty (Fin K) := not_nonempty_iff.1 h
  have := θ.2.weight_sum
  simp at this

theorem sum_resp (θ : ValidParams d K) (x : Fin d → Bool) : ∑ k, resp θ x k = 1 := by
  have := nonempty_of_valid θ
  exact (isDist_posterior (fun θ x k => joint_pos θ x k) θ x).2

/-! ## The M-step -/

variable (xs : Fin N → Fin d → Bool)

/-- **Effective number of points of a Bernoulli-mixture component.** For data
$x_1, \dots, x_N \in \{0, 1\}^d$ and valid parameters $\theta$ of a mixture of $K$ products of $d$
Bernoulli distributions, the effective number of points of component $k$ is
$N_k = \sum_{n=1}^{N} r_{nk}$, where $r_{nk}$ is the posterior probability (responsibility) of
component $k$ given $x_n$ under $\theta$. -/
noncomputable def mass (θ : ValidParams d K) (k : Fin K) : ℝ := ∑ n, resp θ (xs n) k

/-- **Responsibility-weighted count of ones.** For data $x_1, \dots, x_N \in \{0, 1\}^d$, valid
parameters $\theta$ of a mixture of $K$ products of $d$ Bernoulli distributions, a component $k$
and a coordinate $j$, this is the sum $\sum_{n \,:\, x_{nj} = 1} r_{nk}$, over the points whose
$j$-th coordinate is $1$, of the posterior probability $r_{nk}$ of component $k$ given $x_n$
under $\theta$. -/
noncomputable def ones (θ : ValidParams d K) (k : Fin K) (j : Fin d) : ℝ :=
  ∑ n, if xs n j then resp θ (xs n) k else 0

/-- **Responsibility-weighted count of zeros.** Let $\theta$ be valid parameters of a mixture of
$K$ products of $d$ Bernoulli distributions, let $x_0, \dots, x_{N-1} \in \{0,1\}^d$ be data, and
let $k < K$ be a component and $j < d$ a coordinate. Write $x_{nj}$ for the $j$-th coordinate of
$x_n$ and $r_k(x_n)$ for the responsibility of component $k$ for $x_n$ under $\theta$. The
weighted count is $\sum_{n < N,\ x_{nj} = 0} r_k(x_n)$, the sum of the responsibilities over the
points whose $j$-th coordinate is $0$. -/
noncomputable def zeros (θ : ValidParams d K) (k : Fin K) (j : Fin d) : ℝ :=
  ∑ n, if xs n j then 0 else resp θ (xs n) k

/-- **The M-step of the Bernoulli mixture.** Let $x_1, \dots, x_N \in \{0, 1\}^d$ be data and
$\theta$ valid parameters of a mixture of $K$ products of $d$ Bernoulli distributions. With $r_{nk}$
the posterior probability of component $k$ given $x_n$ under $\theta$, $N_k = \sum_n r_{nk}$ and
$A_{kj} = \sum_n r_{nk} x_{nj}$, the M-step returns the parameters with mixing weights
$\pi'_k = N_k / N$ and success probabilities $p'_{kj} = A_{kj} / N_k$, where a quotient by $0$ is
read as $0$. These parameters need not be valid. -/
noncomputable def mStep (θ : ValidParams d K) : Params d K where
  weight k := mass xs θ k / N
  prob k j := ones xs θ k j / mass xs θ k

/-- **Rich data for a Bernoulli mixture.** Data $x_0, \dots, x_{N-1} \in \{0,1\}^d$ are rich when
$N > 0$ and, for every coordinate $j < d$, some $x_n$ has $j$-th coordinate $1$ and some $x_m$
has $j$-th coordinate $0$. These are the data on which the M-step yields valid parameters. -/
structure Rich (xs : Fin N → Fin d → Bool) : Prop where
  pos : 0 < N
  both : ∀ j, (∃ n, xs n j = true) ∧ ∃ n, xs n j = false

variable {xs}

theorem ones_add_zeros (θ : ValidParams d K) (k : Fin K) (j : Fin d) :
    ones xs θ k j + zeros xs θ k j = mass xs θ k := by
  rw [ones, zeros, mass, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by split_ifs <;> simp

theorem ones_pos (hx : Rich xs) (θ : ValidParams d K) (k : Fin K) (j : Fin d) :
    0 < ones xs θ k j := by
  obtain ⟨n, hn⟩ := (hx.both j).1
  refine lt_of_lt_of_le ?_
    (Finset.single_le_sum (f := fun n => if xs n j then resp θ (xs n) k else 0)
      (fun m _ => by split_ifs; exacts [(resp_pos θ _ k).le, le_rfl]) (Finset.mem_univ n))
  simp only [hn, ↓reduceIte]
  exact resp_pos θ _ k

theorem zeros_pos (hx : Rich xs) (θ : ValidParams d K) (k : Fin K) (j : Fin d) :
    0 < zeros xs θ k j := by
  obtain ⟨n, hn⟩ := (hx.both j).2
  refine lt_of_lt_of_le ?_
    (Finset.single_le_sum (f := fun n => if xs n j then 0 else resp θ (xs n) k)
      (fun m _ => by split_ifs; exacts [le_rfl, (resp_pos θ _ k).le]) (Finset.mem_univ n))
  simp only [hn, Bool.false_eq_true, ↓reduceIte]
  exact resp_pos θ _ k

theorem mass_pos (hx : Rich xs) (θ : ValidParams d K) (k : Fin K) : 0 < mass xs θ k :=
  Finset.sum_pos (fun _ _ => resp_pos θ _ k) ⟨⟨0, hx.pos⟩, Finset.mem_univ _⟩

theorem sum_mass (θ : ValidParams d K) : ∑ k, mass xs θ k = N := by
  simp only [mass]
  rw [Finset.sum_comm]
  simp [sum_resp]

theorem mStep_valid (hx : Rich xs) (θ : ValidParams d K) : (mStep xs θ).Valid where
  weight_pos k := div_pos (mass_pos hx θ k) (by exact_mod_cast hx.pos)
  weight_sum := by
    simp only [mStep]
    rw [← Finset.sum_div, sum_mass, div_self (by exact_mod_cast hx.pos.ne')]
  prob_pos k j := div_pos (ones_pos hx θ k j) (mass_pos hx θ k)
  prob_lt_one k j := by
    simp only [mStep]
    rw [div_lt_one (mass_pos hx θ k), ← ones_add_zeros]
    linarith [zeros_pos hx θ k j]

variable (xs) in
/-- **One EM step for the Bernoulli mixture.** Let $x_1, \dots, x_N \in \{0, 1\}^d$ be data with
$N \ge 1$ in which every coordinate takes both values. For valid parameters $\theta$ of a mixture
of $K$ products of $d$ Bernoulli distributions, the EM step maps $\theta$ to the parameters with
mixing weights $\pi'_k = N_k / N$ and success probabilities $p'_{kj} = A_{kj} / N_k$, where
$r_{nk}$ is the posterior probability of component $k$ given $x_n$ under $\theta$,
$N_k = \sum_n r_{nk}$, and $A_{kj}$ is the sum of $r_{nk}$ over the points with $x_{nj} = 1$. On
such data these parameters are again valid. -/
noncomputable def emStep (hx : Rich xs) (θ : ValidParams d K) : ValidParams d K :=
  ⟨mStep xs θ, mStep_valid hx θ⟩

/-! ## The M-step maximizes `Q` -/

variable (xs) in
/-- **Decomposition of the EM objective for the Bernoulli mixture.** Let
$x_1, \dots, x_N \in \{0, 1\}^d$ be data and let $\theta$ and $\theta'$ be valid parameters of a
mixture of $K$ products of $d$ Bernoulli distributions (positive mixing weights summing to one and
success probabilities in $(0, 1)$), where $\theta'$ has mixing weights $\pi'_k$ and success
probabilities $p'_{kj}$. Write $p_\theta(x, k)$ for the joint probability of $x$ and component $k$
under $\theta$ (the mixing weight of $k$ times the product Bernoulli probability of $x$),
$r_{nk} = p_\theta(k \mid x_n) = p_\theta(x_n, k) / \sum_l p_\theta(x_n, l)$ for the posterior
probability of component $k$ given $x_n$, $N_k = \sum_n r_{nk}$, and $A_{kj}$ and $B_{kj}$ for the
sums of $r_{nk}$ over the points $x_n$ whose $j$-th coordinate $x_{nj}$ is $1$ and is $0$
respectively. Then the EM objective
$Q(\theta' \mid \theta) = \sum_n \sum_k r_{nk} \log p_{\theta'}(x_n, k)$ equals
$$\sum_{k=1}^{K} \Big( N_k \log \pi'_k + \sum_{j=1}^{d} \big( A_{kj} \log p'_{kj} +
B_{kj} \log (1 - p'_{kj}) \big) \Big).$$
The first term depends only on the mixing weights and each remaining term on a single $p'_{kj}$. -/
theorem emQ_eq (θ' θ : ValidParams d K) :
    emQ joint xs θ' θ = ∑ k, (mass xs θ k * log (θ'.1.weight k) +
      ∑ j, (ones xs θ k j * log (θ'.1.prob k j) + zeros xs θ k j * log (1 - θ'.1.prob k j))) := by
  have hlog : ∀ n k, log (joint θ' (xs n) k) = log (θ'.1.weight k) +
      ∑ j, (if xs n j then log (θ'.1.prob k j) else log (1 - θ'.1.prob k j)) := by
    intro n k
    rw [joint, log_mul (θ'.2.weight_pos k).ne'
      (bernPMF_pos (θ'.2.prob_pos k) (θ'.2.prob_lt_one k) _).ne',
      log_bernPMF (θ'.2.prob_pos k) (θ'.2.prob_lt_one k)]
  have hsplit : ∀ k j, ∑ n, posterior joint θ (xs n) k *
      (if xs n j then log (θ'.1.prob k j) else log (1 - θ'.1.prob k j)) =
      ones xs θ k j * log (θ'.1.prob k j) + zeros xs θ k j * log (1 - θ'.1.prob k j) := by
    intro k j
    rw [ones, zeros, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [resp]
    split_ifs <;> ring
  rw [emQ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hlog, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [mass, Finset.sum_mul, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  simp only [resp]
  rw [← Finset.sum_add_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => hsplit k j)

variable (xs) in
/-- **The M-step of the Bernoulli mixture maximizes the EM objective.** Let
$x_1, \dots, x_N \in \{0, 1\}^d$ be rich data: $N > 0$, and for every coordinate $j < d$ some
$x_n$ has $j$-th coordinate $1$ and some $x_m$ has $j$-th coordinate $0$. Let $\theta$ be valid
parameters of a mixture of $K$ products of $d$ Bernoulli distributions, and let $\theta^+$ be the
result of the EM step applied to $\theta$. Then every valid parameter $\theta'$ satisfies
$Q(\theta' \mid \theta) \le Q(\theta^+ \mid \theta)$, where $Q$ is the EM objective of the
mixture's joint distribution. -/
theorem emQ_le_emStep (hx : Rich xs) (θ' θ : ValidParams d K) :
    emQ joint xs θ' θ ≤ emQ joint xs (emStep xs hx θ) θ := by
  rw [emQ_eq, emQ_eq, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hN : (0 : ℝ) < N := by exact_mod_cast hx.pos
  refine add_le_add ?_ (Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => ?_)
  · -- the weights term
    have h := sum_mul_log_le_sum_mul_log_div (fun k => (mass_pos hx θ k).le)
      (by rw [sum_mass]; exact hN) θ'.2.weight_pos θ'.2.weight_sum
    rw [sum_mass] at h
    exact h
  · -- one coordinate: the two-point case over `Bool`
    have hm := mass_pos hx θ k
    have h := sum_mul_log_le_sum_mul_log_div (Z := Bool)
      (c := fun b => if b then ones xs θ k j else zeros xs θ k j)
      (w := fun b => if b then θ'.1.prob k j else 1 - θ'.1.prob k j)
      (fun b => by cases b <;> simp [(ones_pos hx θ k j).le, (zeros_pos hx θ k j).le])
      (by simp [ones_add_zeros, hm])
      (fun b => by cases b <;> simp [θ'.2.prob_pos k j, θ'.2.prob_lt_one k j])
      (by simp)
    simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true] at h
    rw [ones_add_zeros] at h
    have e1 : (emStep xs hx θ).1.prob k j = ones xs θ k j / mass xs θ k := rfl
    have e2 : 1 - (emStep xs hx θ).1.prob k j = zeros xs θ k j / mass xs θ k := by
      rw [e1, eq_div_iff hm.ne', sub_mul, one_mul, div_mul_cancel₀ _ hm.ne', ← ones_add_zeros]
      ring
    rw [e2, e1]
    linarith

variable (xs) in
/-- **Each EM step for the Bernoulli mixture does not decrease the log-likelihood.** Let
$x_1, \dots, x_N \in \{0, 1\}^d$ be rich data: $N > 0$, and for every coordinate $j < d$ some
$x_n$ has $j$-th coordinate $1$ and some $x_m$ has $j$-th coordinate $0$. Let $\theta$ be valid
parameters of a mixture of $K$ products of $d$ Bernoulli distributions. Then
$\ell(\theta) \le \ell(\theta^+)$, where $\ell$ is the log-likelihood of the data under the
mixture's joint distribution and $\theta^+$ is the result of the EM step applied to $\theta$. -/
theorem logLik_le_emStep (hx : Rich xs) (θ : ValidParams d K) :
    logLik joint xs θ ≤ logLik joint xs (emStep xs hx θ) := by
  have := nonempty_of_valid θ
  exact logLik_le_of_emQ_le (fun θ x k => joint_pos θ x k) xs (emQ_le_emStep xs hx θ θ)

variable (xs) in
/-- **The log-likelihood is monotone along the EM iterates of a Bernoulli mixture.** Let
$x_1, \dots, x_N \in \{0, 1\}^d$ be rich data: $N > 0$, and for every coordinate $j < d$ some
$x_n$ has $j$-th coordinate $1$ and some $x_m$ has $j$-th coordinate $0$. Let $\theta_0$ be valid
parameters of a mixture of $K$ products of $d$ Bernoulli distributions, and let $\theta_t$ be the
result of $t$ EM steps from $\theta_0$. Then $\ell(\theta_t)$ is nondecreasing in
$t \in \mathbb{N}$, where $\ell$ is the log-likelihood of the data under the mixture's joint
distribution. -/
theorem logLik_iterate_emStep_monotone (hx : Rich xs) (θ₀ : ValidParams d K) :
    Monotone fun t => logLik joint xs ((emStep xs hx)^[t] θ₀) := by
  have := nonempty_of_valid θ₀
  exact logLik_iterate_monotone (fun θ x k => joint_pos θ x k) xs (fun θ => emQ_le_emStep xs hx θ θ)
    θ₀

end Cslib.MachineLearning.LatentVariable.BernoulliMixture
