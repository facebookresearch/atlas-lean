/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import CSLibExt.MachineLearning.Hedge
public import CSLibExt.MachineLearning.Perceptron
import Mathlib.Algebra.BigOperators.Field

/-!
# AdaBoost: the training-error bound

AdaBoost (Freund and Schapire, *A decision-theoretic generalization of on-line learning and an
application to boosting*, J. Comput. Syst. Sci. 55, 1997; Shalev-Shwartz and Ben-David,
*Understanding Machine Learning*, Section 10.2) on `m` training points with labels
`y : Fin m → Bool`. The weak learner `wl` maps weights over the points to a hypothesis's
predictions on them. Round `t` takes the weak hypothesis `h_t = wl D_t` with weighted error `ε_t`,
gives it the weight `α_t = log ((1 - ε_t) / ε_t) / 2`, and reweights
`D_{t+1}(i) ∝ D_t(i) exp (-α_t yᵢ h_t(xᵢ))`, with labels and predictions read as `±1` by
`Perceptron.sign`. The final classifier is the sign of `F_T = ∑_{t < T} α_t h_t`.

Main results:

* `normalizer_eq`: the round's normalizer is `Z_t = 2 √(ε_t (1 - ε_t))`.
* `dist_mul_prod`: unrolling, `D_T(i) · m ∏_{t < T} Z_t = exp (-yᵢ F_T(xᵢ))`.
* `trainErr_le_prod`, `trainErr_le_prod_sqrt_of_round_errors`: **the training error is at most
  `∏_t 2 √(ε_t (1 - ε_t))`**, requiring `0 < ε_t < 1` only for `t < T`.
* `trainErr_le_exp_of_round_errors`: **with edge `γ` in the executed rounds
  (`0 < ε_t ≤ 1 / 2 - γ` for `t < T`), the training error after `T` rounds is at most
  `exp (-2 γ² T)`**; `two_mul_sqrt_le_exp` is the per-round estimate.

`WeakLearner` is a stronger, global assumption on every positive distribution, including those
never visited by the run. The existing `trainErr_le_prod_sqrt` and `trainErr_le_exp` APIs retain
that assumption as corollaries of the round-error bounds.

* `trainErr_le_prod_sqrt_of_eps`, `trainErr_le_exp_sum_sq`: **Freund and Schapire's Theorem 6 with
  per-round errors**: if every round has `ε_t ∈ (0, 1)`, the training error is at most
  `∏_t 2 √(ε_t (1 - ε_t)) ≤ exp (-2 ∑_t γ_t²)` with `γ_t = 1 / 2 - ε_t` (their equation (21));
  no uniform edge is assumed.
* `expLoss_score`, `expLoss_score_succ_le`: **AdaBoost is greedy coordinate descent on the
  exponential loss** `(1 / m) ∑ᵢ exp (-yᵢ F(xᵢ))`: the loss after `T` rounds is `∏_t Z_t`, and
  AdaBoost's step is at least as good as any step along any hypothesis that is no better a
  classifier under the current weights (`expLoss_score_mul_le_expLoss_add`).
* `marginErr_le`: **the training margins** (Schapire, Freund, Bartlett and Lee, *Boosting the
  margin*, Ann. Statist. 26, 1998, Theorem 5): the fraction of points with normalized margin at
  most `θ` is at most `∏_t 2 √(ε_t^{1 - θ} (1 - ε_t)^{1 + θ})`.

The weak-learning assumption excludes `ε_t = 0` (a perfect weak hypothesis, where `α_t` is
infinite and boosting would stop). The scalar estimates `√(1 - 4 γ²) ≤ exp (-2 γ²)` and their
products also appear in `Ch10.lean` of
`FormalizedTextbooks/UnderstandingMachineLearningFromTheoryToAlgorithms/`, which this layer cannot
import; that file has no algorithm. Multiplicative weights over experts is
`MachineLearning/Hedge.lean`; `reweight_eq_hedge_update` shows that AdaBoost's reweighting is a
normalized Hedge step over the training points (Freund and Schapire's Figure 2).

## Cost model

None: the subject is the training error, over the reals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.AdaBoost

open Real
open Cslib.MachineLearning.Perceptron (sign)

variable {m : ℕ}

/-- **Weighted training error.** For labels $y$, weights $D$ and predictions $h$ on $m$ training
points, the weighted training error of $h$ under $D$ is $\sum_{i : h(i) \ne y(i)} D(i)$, the total
weight of the points that $h$ misclassifies. -/
noncomputable def err (y : Fin m → Bool) (D : Fin m → ℝ) (h : Fin m → Bool) : ℝ :=
  ∑ i, if h i = y i then 0 else D i

/-- **AdaBoost's hypothesis weight.** A weak hypothesis with weighted error
$\varepsilon \in \mathbb{R}$ gets the weight
$\alpha(\varepsilon) = \frac{1}{2} \log \frac{1 - \varepsilon}{\varepsilon}$. -/
noncomputable def alpha (ε : ℝ) : ℝ := log ((1 - ε) / ε) / 2

/-- **Normalizer of a boosting round.** For labels $y$, weights $D$ and predictions $h$ on $m$
training points, let $\varepsilon$ be the weighted training error of $h$ under $D$ and
$\alpha = \alpha(\varepsilon)$ the hypothesis weight. The normalizer of the round is

$$Z = \sum_i D(i) \exp(-\alpha\, y_i h_i),$$

where the label $y_i$ and the prediction $h_i$ are read as $\pm 1$. -/
noncomputable def normalizer (y : Fin m → Bool) (D : Fin m → ℝ) (h : Fin m → Bool) : ℝ :=
  ∑ i, D i * exp (-(alpha (err y D h)) * ((sign (y i) : ℝ) * sign (h i)))

/-- **AdaBoost reweighting.** For labels $y$, weights $D$ and predictions $h$ on $m$ training
points, let $\varepsilon$ be the weighted training error of $h$ under $D$,
$\alpha = \alpha(\varepsilon)$ the hypothesis weight and $Z$ the normalizer of the round. The
reweighted weight of point $i$ is

$$D'(i) = \frac{D(i) \exp(-\alpha\, y_i h_i)}{Z},$$

where the label $y_i$ and the prediction $h_i$ are read as $\pm 1$. -/
noncomputable def reweight (y : Fin m → Bool) (D : Fin m → ℝ) (h : Fin m → Bool) (i : Fin m) :
    ℝ :=
  D i * exp (-(alpha (err y D h)) * ((sign (y i) : ℝ) * sign (h i))) / normalizer y D h

theorem sign_mul_sign_eq_ite (a b : Bool) :
    (sign a : ℝ) * sign b = if b = a then 1 else -1 := by
  cases a <;> cases b <;> simp [sign]

/-- **The normalizer of a round is $2\sqrt{\varepsilon(1 - \varepsilon)}$.** Let $y$ be labels on
$m$ training points, $D$ real weights on the points with $\sum_i D(i) = 1$, and $h$ predictions
whose weighted training error $\varepsilon$ under $D$ satisfies $0 < \varepsilon < 1$. Then the
normalizer of the round with weights $D$ and hypothesis $h$ equals
$2\sqrt{\varepsilon(1 - \varepsilon)}$. -/
theorem normalizer_eq (y : Fin m → Bool) {D : Fin m → ℝ} (hD : ∑ i, D i = 1)
    (h : Fin m → Bool) (h0 : 0 < err y D h) (h1 : err y D h < 1) :
    normalizer y D h = 2 * sqrt (err y D h * (1 - err y D h)) := by
  set ε := err y D h with hε
  have hcorrect : ∑ i, (if h i = y i then D i else 0) = 1 - ε := by
    rw [hε, err, ← hD, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  have hsplit : normalizer y D h = (1 - ε) * exp (-alpha ε) + ε * exp (alpha ε) := by
    rw [normalizer, ← hcorrect, hε, err, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sign_mul_sign_eq_ite]
    split_ifs <;> simp
  have ha : 0 < sqrt ε := sqrt_pos.2 h0
  have hb : 0 < sqrt (1 - ε) := sqrt_pos.2 (by linarith)
  have he : exp (alpha ε) = sqrt (1 - ε) / sqrt ε := by
    rw [alpha, exp_half, exp_log (div_pos (by linarith) h0), sqrt_div' _ h0.le]
  have hen : exp (-alpha ε) = sqrt ε / sqrt (1 - ε) := by
    rw [exp_neg, he, inv_div]
  rw [hsplit, he, hen, sqrt_mul h0.le]
  have h1 : sqrt ε ^ 2 = ε := sq_sqrt h0.le
  have h2 : sqrt (1 - ε) ^ 2 = 1 - ε := sq_sqrt (by linarith)
  field_simp
  nlinarith [h1, h2]

/-- **One round's factor is at most `exp (-2 γ²)`.** For real numbers $\varepsilon$ and $\gamma$
with $\gamma \ge 0$ and $\varepsilon \le 1/2 - \gamma$, we have
$2\sqrt{\varepsilon (1 - \varepsilon)} \le e^{-2\gamma^2}$, where the square root of a negative
number is taken to be $0$. -/
theorem two_mul_sqrt_le_exp {ε γ : ℝ} (hγ : 0 ≤ γ) (hε : ε ≤ 1 / 2 - γ) :
    2 * sqrt (ε * (1 - ε)) ≤ exp (-2 * γ ^ 2) := by
  have h4 : 4 * (ε * (1 - ε)) ≤ exp (-(4 * γ ^ 2)) := by
    have := add_one_le_exp (-(4 * γ ^ 2))
    nlinarith
  calc 2 * sqrt (ε * (1 - ε)) = sqrt (4 * (ε * (1 - ε))) := by
        rw [Real.sqrt_mul (x := 4) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ sqrt (exp (-(4 * γ ^ 2))) := sqrt_le_sqrt h4
    _ = exp (-2 * γ ^ 2) := by rw [← exp_half]; ring_nf

/-! ## The algorithm -/

variable (y : Fin m → Bool) (wl : (Fin m → ℝ) → Fin m → Bool)

/-- **AdaBoost's weights.** Given labels $y$ on $m$ training points and a weak learner
$\mathrm{wl}$, which maps weights on the points to a hypothesis's predictions on them,
AdaBoost's weights $D_t$ on the points are defined by $D_0(i) = 1/m$ for every point $i$, and
$D_{t+1}$ is the reweighting of $D_t$ by the hypothesis $\mathrm{wl}(D_t)$. -/
noncomputable def dist : ℕ → Fin m → ℝ
  | 0 => fun _ => 1 / m
  | t + 1 => reweight y (dist t) (wl (dist t))

/-- **Weak hypothesis of an AdaBoost round.** The weak hypothesis $h_t$ of round $t$ is the weak
learner's output $\mathrm{wl}(D_t)$ on the weights $D_t$ of round $t$. -/
noncomputable def hyp (t : ℕ) : Fin m → Bool := wl (dist y wl t)

/-- **Weighted error of an AdaBoost round.** The weighted error $\varepsilon_t$ of round $t$ is the
weighted training error of the weak hypothesis $h_t$ of round $t$ under the weights $D_t$ of
round $t$. -/
noncomputable def eps (t : ℕ) : ℝ := err y (dist y wl t) (hyp y wl t)

/-- **Normalizer of an AdaBoost round.** Run AdaBoost on training points with labels $y$, and
read labels and predictions as $\pm 1$. The normalizer of round $t$ is
$Z_t = \sum_i D_t(i) \exp(-\alpha_t y_i h_t(i))$, where $D_t$ are AdaBoost's weights in round
$t$, $h_t$ is the weak hypothesis of round $t$, and $\alpha_t$ is its weight. -/
noncomputable def zee (t : ℕ) : ℝ := normalizer y (dist y wl t) (hyp y wl t)

/-- **AdaBoost's combined score.** After $T$ rounds, the combined score of training point $i$ is

$$F_T(i) = \sum_{t < T} \alpha(\varepsilon_t)\, h_t(i),$$

where $\varepsilon_t$ is the weighted error and $h_t$ the weak hypothesis of round $t$,
$\alpha(\varepsilon) = \frac{1}{2} \log \frac{1 - \varepsilon}{\varepsilon}$ is the hypothesis
weight, and the prediction $h_t(i)$ is read as $\pm 1$. The final classifier is the sign of
$F_T$. -/
noncomputable def score (T : ℕ) (i : Fin m) : ℝ :=
  ∑ t ∈ Finset.range T, alpha (eps y wl t) * sign (hyp y wl t i)

/-- **Training error of AdaBoost.** Let AdaBoost run on $m$ training points with labels $y$,
read labels and predictions as $\pm 1$, and let $F_T$ be the combined score after $T$ rounds.
The training error after $T$ rounds is the number of training points $i$ with
$y_i F_T(i) \le 0$, divided by $m$; in particular a zero score counts as an error.

For $m = 0$ there is no training point and the value is $0$ ($0 / 0$), which is not a fraction;
the results below assume $0 < m$. -/
noncomputable def trainErr (T : ℕ) : ℝ :=
  (∑ i, if sign (y i) * score y wl T i ≤ 0 then (1 : ℝ) else 0) / m

variable {y wl}

theorem dist_pos (hm : 0 < m) : ∀ (t : ℕ) (i : Fin m), 0 < dist y wl t i
  | 0, i => by simp only [dist]; positivity
  | t + 1, i => by
      have hD := dist_pos hm t
      have hZ : 0 < normalizer y (dist y wl t) (wl (dist y wl t)) :=
        Finset.sum_pos (fun j _ => mul_pos (hD j) (exp_pos _)) ⟨i, Finset.mem_univ _⟩
      exact div_pos (mul_pos (hD i) (exp_pos _)) hZ

theorem zee_pos (hm : 0 < m) (t : ℕ) : 0 < zee y wl t := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact Finset.sum_pos (fun j _ => mul_pos (dist_pos hm t j) (exp_pos _)) Finset.univ_nonempty

theorem sum_dist (hm : 0 < m) : ∀ t : ℕ, ∑ i, dist y wl t i = 1
  | 0 => by
      simp only [dist, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
  | t + 1 => by
      simp only [dist, reweight]
      rw [← Finset.sum_div]
      exact div_self (zee_pos hm t).ne'

/-- **Unrolling the weights.** Run AdaBoost with labels $y$ on $m > 0$ training points and a
weak learner, and let $D_T$ be the weights on the points after $T$ rounds, $Z_t$ the normalizer
of round $t$, and $F_T$ the combined score after $T$ rounds. Then for every $T \in \mathbb{N}$ and
every training point $i$,

$$D_T(i) \cdot m \prod_{t < T} Z_t = \exp(-y_i F_T(i)),$$

where the label $y_i$ is read as $\pm 1$. -/
theorem dist_mul_prod (hm : 0 < m) : ∀ (T : ℕ) (i : Fin m),
    dist y wl T i * (m * ∏ t ∈ Finset.range T, zee y wl t) = exp (-(sign (y i) * score y wl T i))
  | 0, i => by
      simp only [dist, Finset.prod_range_zero, mul_one, score, Finset.sum_range_zero, mul_zero,
        neg_zero, exp_zero]
      field_simp
  | T + 1, i => by
      have ih := dist_mul_prod hm T i
      have hZ := (zee_pos (y := y) (wl := wl) hm T).ne'
      rw [Finset.prod_range_succ, score, Finset.sum_range_succ, mul_add, neg_add, exp_add,
        ← score, ← ih]
      simp only [dist, reweight, zee, eps, hyp] at hZ ⊢
      field_simp

/-- **The training error is at most the product of the normalizers.** Let AdaBoost run on
$m > 0$ training points with labels $y$ and an arbitrary weak learner, and write $Z_t$ for the
normalizer of round $t$. Then for every number of rounds $T$, the training error after $T$ rounds
is at most $\prod_{t < T} Z_t$. -/
theorem trainErr_le_prod (hm : 0 < m) (T : ℕ) :
    trainErr y wl T ≤ ∏ t ∈ Finset.range T, zee y wl t := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hP : 0 < ∏ t ∈ Finset.range T, zee y wl t :=
    Finset.prod_pos fun t _ => zee_pos hm t
  have hind : ∀ i, (if sign (y i) * score y wl T i ≤ 0 then (1 : ℝ) else 0) ≤
      dist y wl T i * (m * ∏ t ∈ Finset.range T, zee y wl t) := by
    intro i
    rw [dist_mul_prod hm]
    split_ifs with h
    · exact one_le_exp (by linarith)
    · exact (exp_pos _).le
  calc trainErr y wl T
      ≤ (∑ i, dist y wl T i * (m * ∏ t ∈ Finset.range T, zee y wl t)) / m :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hind i) hmR.le
    _ = ∏ t ∈ Finset.range T, zee y wl t := by
        rw [← Finset.sum_mul, sum_dist hm, one_mul]
        field_simp

/-- **The weak-learning assumption.** A weak learner, which maps weights on the $m$ training
points with labels $y$ to a hypothesis on those points, has edge $\gamma$ if for every weighting
$D$ of the training points with $D_i > 0$ for all $i$ and $\sum_i D_i = 1$, the hypothesis it
returns on $D$ has weighted error under $D$ in the interval $(0, 1/2 - \gamma]$. -/
def WeakLearner (y : Fin m → Bool) (wl : (Fin m → ℝ) → Fin m → Bool) (γ : ℝ) : Prop :=
  ∀ D : Fin m → ℝ, (∀ i, 0 < D i) → ∑ i, D i = 1 → 0 < err y D (wl D) ∧ err y D (wl D) ≤ 1 / 2 - γ

/-- AdaBoost's product bound requires errors in `(0, 1)` only on the rounds it executes. -/
theorem trainErr_le_prod_sqrt_of_round_errors (hm : 0 < m) (T : ℕ)
    (hε : ∀ t < T, 0 < eps y wl t ∧ eps y wl t < 1) :
    trainErr y wl T ≤ ∏ t ∈ Finset.range T, 2 * sqrt (eps y wl t * (1 - eps y wl t)) := by
  refine (trainErr_le_prod hm T).trans (le_of_eq (Finset.prod_congr rfl fun t ht => ?_))
  obtain ⟨h0, h1⟩ := hε t (Finset.mem_range.mp ht)
  exact normalizer_eq y (sum_dist hm t) _ h0 h1

/-- **The Freund–Schapire bound on AdaBoost's training error.** Let AdaBoost run on $m > 0$
training points with labels $y$ and a weak learner with edge $\gamma \ge 0$, that is, one that on
every weighting $D$ of the training points with $D_i > 0$ for all $i$ and $\sum_i D_i = 1$ returns
a hypothesis whose weighted error under $D$ lies in $(0, 1/2 - \gamma]$. Write $\varepsilon_t$ for
the weighted error of the weak hypothesis of round $t$ under AdaBoost's weights of that round.
Then for every number of rounds $T$, the training error after $T$ rounds is at most
$\prod_{t < T} 2\sqrt{\varepsilon_t (1 - \varepsilon_t)}$. -/
theorem trainErr_le_prod_sqrt (hm : 0 < m) {γ : ℝ} (hγ : 0 ≤ γ) (hwl : WeakLearner y wl γ)
    (T : ℕ) :
    trainErr y wl T ≤ ∏ t ∈ Finset.range T, 2 * sqrt (eps y wl t * (1 - eps y wl t)) := by
  apply trainErr_le_prod_sqrt_of_round_errors hm T
  intro t _
  obtain ⟨h0, h1⟩ := hwl _ (dist_pos hm t) (sum_dist hm t)
  change eps y wl t ≤ 1 / 2 - γ at h1
  exact ⟨h0, by linarith⟩

/-- AdaBoost's exponential bound requires the edge only on the rounds it executes. -/
theorem trainErr_le_exp_of_round_errors (hm : 0 < m) {γ : ℝ} (hγ : 0 ≤ γ) (T : ℕ)
    (hε : ∀ t < T, 0 < eps y wl t ∧ eps y wl t ≤ 1 / 2 - γ) :
    trainErr y wl T ≤ exp (-2 * γ ^ 2 * T) := by
  have herr : ∀ t < T, 0 < eps y wl t ∧ eps y wl t < 1 := by
    intro t ht
    obtain ⟨h0, h1⟩ := hε t ht
    exact ⟨h0, by linarith⟩
  refine (trainErr_le_prod_sqrt_of_round_errors hm T herr).trans ?_
  calc ∏ t ∈ Finset.range T, 2 * sqrt (eps y wl t * (1 - eps y wl t))
      ≤ ∏ _t ∈ Finset.range T, exp (-2 * γ ^ 2) := by
        refine Finset.prod_le_prod₀ (fun t _ => by positivity) fun t ht => ?_
        exact two_mul_sqrt_le_exp hγ (hε t (Finset.mem_range.mp ht)).2
    _ = exp (-2 * γ ^ 2 * T) := by
        rw [Finset.prod_const, Finset.card_range, ← exp_nat_mul]
        ring_nf

/-- **AdaBoost drives the training error down exponentially.** Let AdaBoost run on $m > 0$
training points with labels $y$ and a weak learner with edge $\gamma \ge 0$, that is, one that on
every weighting $D$ of the training points with $D_i > 0$ for all $i$ and $\sum_i D_i = 1$ returns
a hypothesis whose weighted error under $D$ lies in $(0, 1/2 - \gamma]$. Then for every number of
rounds $T$, the training error after $T$ rounds is at most $e^{-2\gamma^2 T}$. -/
theorem trainErr_le_exp (hm : 0 < m) {γ : ℝ} (hγ : 0 ≤ γ) (hwl : WeakLearner y wl γ) (T : ℕ) :
    trainErr y wl T ≤ exp (-2 * γ ^ 2 * T) := by
  apply trainErr_le_exp_of_round_errors hm hγ T
  intro t _
  exact hwl _ (dist_pos hm t) (sum_dist hm t)

/-! ## Per-round edges

Freund and Schapire's Theorem 6 needs no uniform weak-learning assumption: it holds whenever every
round's error lies in `(0, 1)`, even when some `ε_t ≥ 1 / 2`. Their equation (21) then rewrites the
bound in terms of the edges `γ_t = 1 / 2 - ε_t`. -/

/-- **A round's factor in terms of its edge.** For every real `ε`, with `γ = 1 / 2 - ε`,
`2 √(ε (1 - ε)) = √(1 - 4 γ²)` (Freund and Schapire, *J. Comput. Syst. Sci.* 55, 1997,
the first equality of equation (21)). -/
theorem two_mul_sqrt_eq_sqrt_one_sub (ε : ℝ) :
    2 * sqrt (ε * (1 - ε)) = sqrt (1 - 4 * (1 / 2 - ε) ^ 2) := by
  rw [show 1 - 4 * (1 / 2 - ε) ^ 2 = 4 * (ε * (1 - ε)) by ring,
    Real.sqrt_mul (x := 4) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- **A round's factor is at most `exp (-2 γ²)` for its own edge.** For every real `ε`, with
`γ = 1 / 2 - ε`, `2 √(ε (1 - ε)) ≤ exp (-2 γ²)` (Freund and Schapire, *J. Comput. Syst. Sci.*
55, 1997, the inequality of equation (21)); the square root of a negative number is `0`. -/
theorem two_mul_sqrt_le_exp_edge (ε : ℝ) :
    2 * sqrt (ε * (1 - ε)) ≤ exp (-2 * (1 / 2 - ε) ^ 2) := by
  have h4 : 4 * (ε * (1 - ε)) ≤ exp (-(4 * (1 / 2 - ε) ^ 2)) := by
    have := add_one_le_exp (-(4 * (1 / 2 - ε) ^ 2))
    nlinarith
  calc 2 * sqrt (ε * (1 - ε)) = sqrt (4 * (ε * (1 - ε))) := by
        rw [Real.sqrt_mul (x := 4) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ sqrt (exp (-(4 * (1 / 2 - ε) ^ 2))) := sqrt_le_sqrt h4
    _ = exp (-2 * (1 / 2 - ε) ^ 2) := by rw [← exp_half]; ring_nf

/-- **Freund and Schapire's Theorem 6** (*J. Comput. Syst. Sci.* 55, 1997, equation (14)):
for any weak learner, if every round `t < T` has weighted error `ε_t ∈ (0, 1)`, then the
training error after `T` rounds is at most `∏_{t < T} 2 √(ε_t (1 - ε_t))`. No edge is
assumed; rounds with `ε_t ≥ 1 / 2` are allowed. -/
theorem trainErr_le_prod_sqrt_of_eps (hm : 0 < m) (T : ℕ)
    (heps : ∀ t < T, 0 < eps y wl t ∧ eps y wl t < 1) :
    trainErr y wl T ≤ ∏ t ∈ Finset.range T, 2 * sqrt (eps y wl t * (1 - eps y wl t)) := by
  refine (trainErr_le_prod hm T).trans (le_of_eq (Finset.prod_congr rfl fun t ht => ?_))
  obtain ⟨h0, h1⟩ := heps t (Finset.mem_range.1 ht)
  exact normalizer_eq y (sum_dist hm t) _ h0 h1

/-- **AdaBoost's training error in terms of the edges** (Freund and Schapire, *J. Comput.
Syst. Sci.* 55, 1997, equation (21)): if every round `t < T` has weighted error
`ε_t ∈ (0, 1)`, then with `γ_t = 1 / 2 - ε_t` the training error after `T` rounds is at most
`exp (-2 ∑_{t < T} γ_t²)`. -/
theorem trainErr_le_exp_sum_sq (hm : 0 < m) (T : ℕ)
    (heps : ∀ t < T, 0 < eps y wl t ∧ eps y wl t < 1) :
    trainErr y wl T ≤ exp (-2 * ∑ t ∈ Finset.range T, (1 / 2 - eps y wl t) ^ 2) := by
  refine (trainErr_le_prod_sqrt_of_eps hm T heps).trans ?_
  calc ∏ t ∈ Finset.range T, 2 * sqrt (eps y wl t * (1 - eps y wl t))
      ≤ ∏ t ∈ Finset.range T, exp (-2 * (1 / 2 - eps y wl t) ^ 2) :=
        Finset.prod_le_prod₀ (fun t _ => by positivity) fun t _ => two_mul_sqrt_le_exp_edge _
    _ = exp (-2 * ∑ t ∈ Finset.range T, (1 / 2 - eps y wl t) ^ 2) := by
        rw [← exp_sum, Finset.mul_sum]

/-! ## AdaBoost as coordinate descent on the exponential loss -/

/-- **The exponential loss** `(1 / m) ∑ᵢ exp (-yᵢ F(xᵢ))` of a score vector `F` on the training
points, with labels read as `±1`. For `m = 0` there is no training point and the value is `0`
(`0 / 0`), not an average; the results below assume `0 < m`. -/
noncomputable def expLoss (y : Fin m → Bool) (F : Fin m → ℝ) : ℝ :=
  (∑ i, exp (-(sign (y i) * F i))) / m

private theorem err_nonneg (y : Fin m → Bool) {D : Fin m → ℝ} (hD : ∀ i, 0 ≤ D i)
    (h : Fin m → Bool) :
    0 ≤ err y D h :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hD i]

private theorem err_le_one (y : Fin m → Bool) {D : Fin m → ℝ} (hD : ∀ i, 0 ≤ D i)
    (hD1 : ∑ i, D i = 1) (h : Fin m → Bool) : err y D h ≤ 1 := by
  rw [← hD1]
  exact Finset.sum_le_sum fun i _ => by split_ifs <;> simp [hD i]

/-- **The reweighted mass along a hypothesis**: for weights `D` summing to `1`, a hypothesis `h`
and a step `a`, `∑ᵢ D i exp (-a yᵢ h(xᵢ)) = (1 - ε) exp (-a) + ε exp a`, where `ε` is the
weighted error of `h` under `D`. -/
theorem sum_mul_exp_eq (y : Fin m → Bool) {D : Fin m → ℝ} (hD : ∑ i, D i = 1)
    (h : Fin m → Bool) (a : ℝ) :
    ∑ i, D i * exp (-a * ((sign (y i) : ℝ) * sign (h i))) =
      (1 - err y D h) * exp (-a) + err y D h * exp a := by
  have hcorrect : ∑ i, (if h i = y i then D i else 0) = 1 - err y D h := by
    rw [err, ← hD, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  rw [← hcorrect, err, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sign_mul_sign_eq_ite]
  split_ifs <;> simp

private theorem two_mul_sqrt_mul_le_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    2 * sqrt (p * q) ≤ p + q := by
  rw [Real.sqrt_mul hp]
  nlinarith [sq_nonneg (sqrt p - sqrt q), sq_sqrt hp, sq_sqrt hq]

/-- **The exponential loss after `T` rounds is the product of the normalizers**:
`(1 / m) ∑ᵢ exp (-yᵢ F_T(xᵢ)) = ∏_{t < T} Z_t`. -/
theorem expLoss_score (hm : 0 < m) (T : ℕ) :
    expLoss y (score y wl T) = ∏ t ∈ Finset.range T, zee y wl t := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs : ∑ i, exp (-(sign (y i) * score y wl T i)) =
      ∑ i, dist y wl T i * (m * ∏ t ∈ Finset.range T, zee y wl t) :=
    Finset.sum_congr rfl fun i _ => (dist_mul_prod hm T i).symm
  rw [expLoss, hs, ← Finset.sum_mul, sum_dist hm, one_mul]
  field_simp

/-- **The exponential loss along a coordinate**: moving the score `F_T` along a hypothesis `h`
by a step `a` multiplies the exponential loss by
`∑ᵢ D_T(i) exp (-a yᵢ h(xᵢ))`. -/
theorem expLoss_score_add (hm : 0 < m) (T : ℕ) (h : Fin m → Bool) (a : ℝ) :
    expLoss y (fun i => score y wl T i + a * sign (h i)) =
      expLoss y (score y wl T) *
        ∑ i, dist y wl T i * exp (-a * ((sign (y i) : ℝ) * sign (h i))) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [expLoss_score hm, expLoss, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsplit : exp (-((sign (y i) : ℝ) * (score y wl T i + a * sign (h i)))) =
      exp (-((sign (y i) : ℝ) * score y wl T i)) *
        exp (-a * ((sign (y i) : ℝ) * sign (h i))) := by
    rw [← exp_add]; ring_nf
  rw [hsplit, ← dist_mul_prod hm T i]
  field_simp

/-- **No step along any hypothesis beats the factor `2 √(ε (1 - ε))`**: from the score `F_T`,
for every hypothesis `h` with weighted error `ε` under AdaBoost's weights `D_T` and every step
`a`, the exponential loss of `F_T + a h` is at least `2 √(ε (1 - ε))` times that of `F_T`. -/
theorem expLoss_score_mul_le_expLoss_add (hm : 0 < m) (T : ℕ) (h : Fin m → Bool) (a : ℝ) :
    expLoss y (score y wl T) *
        (2 * sqrt (err y (dist y wl T) h * (1 - err y (dist y wl T) h))) ≤
      expLoss y (fun i => score y wl T i + a * sign (h i)) := by
  have hD0 : ∀ i, 0 ≤ dist y wl T i := fun i => (dist_pos hm T i).le
  have h0 := err_nonneg y hD0 h
  have h1 := err_le_one y hD0 (sum_dist hm T) h
  rw [expLoss_score_add hm, sum_mul_exp_eq y (sum_dist hm T)]
  refine mul_le_mul_of_nonneg_left ?_ (by rw [expLoss_score hm]; exact
    (Finset.prod_pos fun t _ => zee_pos hm t).le)
  set ε := err y (dist y wl T) h
  have hpq : ((1 - ε) * exp (-a)) * (ε * exp a) = ε * (1 - ε) := by
    have : exp (-a) * exp a = 1 := by rw [← exp_add]; simp
    linear_combination (ε * (1 - ε)) * this
  calc 2 * sqrt (ε * (1 - ε)) = 2 * sqrt (((1 - ε) * exp (-a)) * (ε * exp a)) := by rw [hpq]
    _ ≤ (1 - ε) * exp (-a) + ε * exp a :=
        two_mul_sqrt_mul_le_add (by have := exp_pos (-a); nlinarith)
          (by have := exp_pos a; positivity)

/-- **One AdaBoost round multiplies the exponential loss by `2 √(ε_T (1 - ε_T))`** when the
round's error `ε_T` lies in `(0, 1)`. -/
theorem expLoss_score_succ (hm : 0 < m) (T : ℕ) (h0 : 0 < eps y wl T) (h1 : eps y wl T < 1) :
    expLoss y (score y wl (T + 1)) =
      expLoss y (score y wl T) * (2 * sqrt (eps y wl T * (1 - eps y wl T))) := by
  rw [expLoss_score hm, expLoss_score hm, Finset.prod_range_succ]
  congr 1
  exact normalizer_eq y (sum_dist hm T) _ h0 h1

/-- **AdaBoost is greedy coordinate descent on the exponential loss** (Breiman's observation, as
presented in Schapire, *Explaining AdaBoost*, Section 4): if the round's error `ε_T` satisfies
`0 < ε_T ≤ 1 / 2`, then for every hypothesis `h` whose weighted error under AdaBoost's weights
`D_T` lies in `[ε_T, 1 - ε_T]` (in particular every `h` when the weak learner returns a hypothesis
of minimum weighted error and the hypothesis class is closed under negation) and every step `a`,
AdaBoost's new score has exponential loss at most that of `F_T + a h`. With `h = h_T` this says
that `α_T` is an exact line search. -/
theorem expLoss_score_succ_le (hm : 0 < m) (T : ℕ) (h0 : 0 < eps y wl T)
    (hhalf : eps y wl T ≤ 1 / 2) (h : Fin m → Bool) (hlo : eps y wl T ≤ err y (dist y wl T) h)
    (hhi : err y (dist y wl T) h ≤ 1 - eps y wl T) (a : ℝ) :
    expLoss y (score y wl (T + 1)) ≤ expLoss y (fun i => score y wl T i + a * sign (h i)) := by
  refine le_trans ?_ (expLoss_score_mul_le_expLoss_add hm T h a)
  rw [expLoss_score_succ hm T h0 (by linarith)]
  refine mul_le_mul_of_nonneg_left ?_ (by rw [expLoss_score hm]; exact
    (Finset.prod_pos fun t _ => zee_pos hm t).le)
  have : eps y wl T * (1 - eps y wl T) ≤
      err y (dist y wl T) h * (1 - err y (dist y wl T) h) := by nlinarith
  gcongr

/-! ## Margins of the training examples -/

/-- **The training margin statistic**: the fraction of the `m` training points with
`yᵢ F_T(xᵢ) ≤ θ ∑_{t < T} α_t`, the cross-multiplied margin event. When `∑_{t < T} α_t > 0` it is
the training margin error, the fraction of training points whose normalized margin
`yᵢ F_T(xᵢ) / ∑_{t < T} α_t` is at most `θ`. For a zero or negative coefficient sum the two
events differ (one point, zero rounds and `θ = -1` give `1` here, and `0` for the quotient form
with `0 / 0 = 0`), and `marginErr_le` bounds the cross-multiplied statistic. For `m = 0` there is
no training point and the value is `0` (`0 / 0`), which is not a fraction; the results below
assume `0 < m`. -/
noncomputable def marginErr (y : Fin m → Bool) (wl : (Fin m → ℝ) → Fin m → Bool) (θ : ℝ)
    (T : ℕ) : ℝ :=
  (∑ i, if sign (y i) * score y wl T i ≤ θ * ∑ t ∈ Finset.range T, alpha (eps y wl t)
    then (1 : ℝ) else 0) / m

private theorem exp_mul_alpha_mul_two_sqrt {ε : ℝ} (θ : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    exp (θ * alpha ε) * (2 * sqrt (ε * (1 - ε))) =
      2 * sqrt (ε ^ (1 - θ) * (1 - ε) ^ (1 + θ)) := by
  have hb : 0 < 1 - ε := by linarith
  rw [sqrt_eq_rpow, sqrt_eq_rpow, rpow_def_of_pos (mul_pos h0 hb),
    rpow_def_of_pos (mul_pos (rpow_pos_of_pos h0 _) (rpow_pos_of_pos hb _)),
    log_mul h0.ne' hb.ne', log_mul (rpow_pos_of_pos h0 _).ne' (rpow_pos_of_pos hb _).ne',
    log_rpow h0, log_rpow hb, alpha, log_div hb.ne' h0.ne']
  have key : ∀ u v : ℝ, exp u * (2 * exp v) = 2 * exp (u + v) := by
    intro u v; rw [exp_add]; ring
  rw [key]
  congr 2
  ring

/-- **AdaBoost's training margins** (Schapire, Freund, Bartlett and Lee, *Boosting the margin*,
Ann. Statist. 26, 1998, Theorem 5): if every round `t < T` has weighted error `ε_t ∈ (0, 1)`,
then for every real `θ` the fraction of training points with `yᵢ F_T(xᵢ) ≤ θ ∑_{t < T} α_t`
is at most `∏_{t < T} 2 √(ε_t^{1 - θ} (1 - ε_t)^{1 + θ})`. For `θ = 0` this is the
training-error bound. -/
theorem marginErr_le (hm : 0 < m) (θ : ℝ) (T : ℕ)
    (heps : ∀ t < T, 0 < eps y wl t ∧ eps y wl t < 1) :
    marginErr y wl θ T ≤
      ∏ t ∈ Finset.range T, 2 * sqrt (eps y wl t ^ (1 - θ) * (1 - eps y wl t) ^ (1 + θ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hind : ∀ i, (if sign (y i) * score y wl T i ≤
      θ * ∑ t ∈ Finset.range T, alpha (eps y wl t) then (1 : ℝ) else 0) ≤
      exp (θ * ∑ t ∈ Finset.range T, alpha (eps y wl t)) *
        (dist y wl T i * (m * ∏ t ∈ Finset.range T, zee y wl t)) := by
    intro i
    rw [dist_mul_prod hm, ← exp_add]
    split_ifs with h
    · exact one_le_exp (by linarith)
    · exact (exp_pos _).le
  calc marginErr y wl θ T
      ≤ (∑ i, exp (θ * ∑ t ∈ Finset.range T, alpha (eps y wl t)) *
          (dist y wl T i * (m * ∏ t ∈ Finset.range T, zee y wl t))) / m :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hind i) hmR.le
    _ = exp (θ * ∑ t ∈ Finset.range T, alpha (eps y wl t)) *
          ∏ t ∈ Finset.range T, zee y wl t := by
        rw [← Finset.mul_sum, ← Finset.sum_mul, sum_dist hm, one_mul]
        field_simp
    _ = ∏ t ∈ Finset.range T, 2 * sqrt (eps y wl t ^ (1 - θ) * (1 - eps y wl t) ^ (1 + θ)) := by
        rw [Finset.mul_sum, exp_sum, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun t ht => ?_
        obtain ⟨h0, h1⟩ := heps t (Finset.mem_range.1 ht)
        rw [show zee y wl t = 2 * sqrt (eps y wl t * (1 - eps y wl t)) from
          normalizer_eq y (sum_dist hm t) _ h0 h1]
        exact exp_mul_alpha_mul_two_sqrt θ h0 h1

/-! ## AdaBoost runs Hedge on the training points -/

/-- **AdaBoost's reweighting is a normalized Hedge step** (Freund and Schapire, *J. Comput. Syst.
Sci.* 55, 1997, Figure 2, steps 4 and 5): for positive weights `D` on `m > 0` training points and
a hypothesis `h` with weighted error `ε`, AdaBoost's new weights are Hedge's update of `D` with
learning rate `log ((1 - ε) / ε)` (their `β = ε / (1 - ε)`) and the losses `ℓᵢ = 1` if `h` is
correct on point `i` and `0` otherwise, divided by the total weight. The examples play the
experts, and a point's weight shrinks when the weak hypothesis gets it right. -/
theorem reweight_eq_hedge_update (y : Fin m → Bool) {D : Fin m → ℝ} (hD : ∀ i, 0 < D i)
    (hm : 0 < m) (h : Fin m → Bool) :
    reweight y D h = fun i =>
      Hedge.update (log ((1 - err y D h) / err y D h)) D (fun j => if h j = y j then 1 else 0) i /
        Hedge.total (Hedge.update (log ((1 - err y D h) / err y D h)) D
          (fun j => if h j = y j then 1 else 0)) := by
  funext i
  set a := alpha (err y D h) with ha
  have hlog : log ((1 - err y D h) / err y D h) = 2 * a := by rw [ha, alpha]; ring
  have key : ∀ j, exp (-a * ((sign (y j) : ℝ) * sign (h j))) =
      exp a * exp (-(2 * a) * (if h j = y j then 1 else 0)) := by
    intro j
    rw [sign_mul_sign_eq_ite, ← exp_add]
    split_ifs <;> ring_nf
  have hnorm : normalizer y D h =
      exp a * Hedge.total (Hedge.update (2 * a) D (fun j => if h j = y j then 1 else 0)) := by
    simp only [normalizer, Hedge.total, Hedge.update, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ha, key]
    ring
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have htot : 0 < Hedge.total (Hedge.update (2 * a) D (fun j => if h j = y j then 1 else 0)) :=
    Finset.sum_pos (fun j _ => mul_pos (hD j) (exp_pos _)) Finset.univ_nonempty
  rw [hlog, reweight, hnorm, ← ha, key]
  simp only [Hedge.update]
  field_simp

end Cslib.MachineLearning.AdaBoost
