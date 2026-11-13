/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Rejection sampling

Sample from a target `p : PMF α` using a proposal `q` and an envelope constant `M` with
`p ≤ M q`. Draw `x ~ q` and accept it with probability `p x / (M q x)` (`acceptProb`).
Otherwise, try again.

* `trial`: one round, as a law on (proposal, accepted?). `trial_apply_true`: `x` is proposed and
  accepted with probability `p x / M`. `tsum_trial_true`: a round accepts with probability `1 / M`.
* `trial_true_div_tsum`: conditional on acceptance, the proposal has law `p`.
* `tsum_rejections_mul_trial` (**rejection sampling outputs the target law**): over independent
  rounds, the output is `x` after exactly `k` rejections with probability `r ^ k P(x, accepted)`,
  where `r` is the rejection probability. Summing the geometric series over `k` gives `p x`.
* `eq_of_firstStep`: equivalently, `p` is the only finite solution of the first-step equation
  `out x = P(x, accepted) + r out x` satisfied by the law of the loop's output.

## References

* C. P. Robert and G. Casella, *Monte Carlo Statistical Methods*, 2nd ed., Springer, 2004, §2.3.
* C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006, §11.1.2.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sampling

open scoped ENNReal

variable {α : Type*}

/-- **Biased coin.** For $r \in [0, \infty]$ with $r \le 1$, the biased coin with parameter $r$ is
the probability mass function on $\{\mathrm{true}, \mathrm{false}\}$ that gives $\mathrm{true}$
probability $r$ and $\mathrm{false}$ probability $1 - r$. -/
noncomputable def coin (r : ℝ≥0∞) (hr : r ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b ↦ cond b r (1 - r)) (by
    rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
    exact add_tsub_cancel_of_le hr)

/-- **Acceptance probability.** Given probability mass functions $p$ and $q$ on a type $\alpha$, a
constant $M \in [0, \infty]$ and a point $x \in \alpha$, the acceptance probability of the proposal
$x$ is $p(x) / (M\,q(x))$, computed in $[0, \infty]$, where $a / 0 = \infty$ for $a \ne 0$ and
$0 / 0 = 0$. -/
noncomputable def acceptProb (p q : PMF α) (M : ℝ≥0∞) (x : α) : ℝ≥0∞ := p x / (M * q x)

theorem acceptProb_le_one {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x) (x : α) :
    acceptProb p q M x ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hM x)

/-- **One round of rejection sampling.** Let $p$ and $q$ be probability mass functions on a type
$\alpha$ (the target and the proposal) and let $M \in [0, \infty]$ be an envelope constant with
$p(x) \le M\,q(x)$ for all $x \in \alpha$. One round of rejection sampling for target $p$, proposal
$q$ and envelope $M$ is the probability mass function on pairs
$(x, b) \in \alpha \times \{\mathrm{true}, \mathrm{false}\}$ obtained by drawing $x$ from $q$ and
then flipping a coin that lands $b = \mathrm{true}$ ("accepted") with probability
$p(x) / (M\,q(x))$. -/
noncomputable def trial (p q : PMF α) (M : ℝ≥0∞) (hM : ∀ x, p x ≤ M * q x) : PMF (α × Bool) :=
  q.bind fun x ↦ (coin (acceptProb p q M x) (acceptProb_le_one hM x)).map (Prod.mk x)

theorem trial_apply {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x) (x : α) (b : Bool) :
    trial p q M hM (x, b) = q x * coin (acceptProb p q M x) (acceptProb_le_one hM x) b := by
  classical
  rw [trial, PMF.bind_apply, tsum_eq_single x]
  · rw [PMF.map_apply, tsum_eq_single b]
    · simp
    · intro b' hb'
      simp [Ne.symm hb']
  · intro y hy
    rw [PMF.map_apply]
    simp [Ne.symm hy]

/-- **Probability that a round proposes and accepts a given point.** Let $p$ and $q$ be probability
mass functions on $\alpha$ and $M \in [0, \infty]$ with $p(y) \le M\,q(y)$ for all $y \in \alpha$.
For every $x \in \alpha$, one round of rejection sampling for target $p$, proposal $q$ and envelope
$M$ yields the pair $(x, \mathrm{true})$, that is, proposes $x$ and accepts it, with probability
$p(x) / M$. -/
theorem trial_apply_true {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x) (x : α) :
    trial p q M hM (x, true) = p x / M := by
  rw [trial_apply, coin, PMF.ofFintype_apply, Bool.cond_true, acceptProb]
  by_cases hq : q x = 0
  · have hp : p x = 0 := le_antisymm (by simpa [hq] using hM x) bot_le
    simp [hq, hp]
  · rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr (PMF.apply_ne_top q x)) (Or.inr hq)]
    calc q x * (p x * (M⁻¹ * (q x)⁻¹)) = p x * M⁻¹ * (q x * (q x)⁻¹) := by ring
      _ = p x * M⁻¹ := by rw [ENNReal.mul_inv_cancel hq (PMF.apply_ne_top q x), mul_one]

/-- **Probability that a round accepts.** Let $p$ and $q$ be probability mass functions on $\alpha$
and $M \in [0, \infty]$ with $p(x) \le M\,q(x)$ for all $x \in \alpha$. The sum over $x \in \alpha$
of the probabilities that one round of rejection sampling for target $p$, proposal $q$ and
envelope $M$ yields $(x, \mathrm{true})$ equals $M^{-1}$; that is, a round accepts with
probability $1 / M$. -/
theorem tsum_trial_true {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x) :
    ∑' x, trial p q M hM (x, true) = M⁻¹ := by
  simp_rw [trial_apply_true, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **Probability that a round rejects.** Let $p$ and $q$ be probability mass functions on $\alpha$
and $M \in [0, \infty]$ with $p(x) \le M\,q(x)$ for all $x \in \alpha$. Let $r$ be the sum over
$x \in \alpha$ of the probabilities that one round of rejection sampling for target $p$, proposal
$q$ and envelope $M$ yields $(x, \mathrm{false})$, that is, the probability that the round rejects.
Then $r + M^{-1} = 1$. -/
theorem tsum_trial_false_add {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x) :
    ∑' x, trial p q M hM (x, false) + M⁻¹ = 1 := by
  have hprod := ENNReal.tsum_prod (f := fun (a : α) (b : Bool) ↦ trial p q M hM (a, b))
  rw [← tsum_trial_true hM, ← ENNReal.tsum_add, ← (trial p q M hM).tsum_coe]
  refine Eq.trans ?_ hprod.symm
  exact tsum_congr fun x ↦ (tsum_bool (f := fun b ↦ trial p q M hM (x, b))).symm

/-- **Conditional on acceptance, the proposal has the target law.** Let $p$ and $q$ be probability
mass functions on $\alpha$ and $M \in [0, \infty]$ with $M \ne 0$, $M \ne \infty$ and
$p(y) \le M\,q(y)$ for all $y \in \alpha$. For one round of rejection sampling for target $p$,
proposal $q$ and envelope $M$, write $P(x, \mathrm{accepted})$ for the probability that the round
proposes $x$ and accepts it, and
$P(\mathrm{accepted}) = \sum_{y \in \alpha} P(y, \mathrm{accepted})$. Then
$P(x, \mathrm{accepted}) / P(\mathrm{accepted}) = p(x)$ for every $x \in \alpha$. -/
theorem trial_true_div_tsum {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x) (hM0 : M ≠ 0)
    (hMt : M ≠ ∞) (x : α) :
    trial p q M hM (x, true) / ∑' y, trial p q M hM (y, true) = p x := by
  rw [trial_apply_true, tsum_trial_true, div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_assoc,
    ENNReal.inv_mul_cancel hM0 hMt, mul_one]

/-- **Rejection sampling outputs the target law.** Let $p$ and $q$ be probability mass functions on
$\alpha$ and $M \in [0, \infty]$ with $M \ne 0$, $M \ne \infty$ and $p(y) \le M\,q(y)$ for all
$y \in \alpha$. For one round of rejection sampling for target $p$, proposal $q$ and envelope $M$,
write $P(x, \mathrm{accepted})$ for the probability that the round proposes $x$ and accepts it, and
$r$ for the sum over $y \in \alpha$ of the probabilities that it proposes $y$ and rejects it. Then
for every $x \in \alpha$,
$$\sum_{k=0}^{\infty} r^k \, P(x, \mathrm{accepted}) = p(x).$$

Here $r^k \, P(x, \mathrm{accepted})$ is the probability that repeating independent rounds until
one accepts outputs $x$ after exactly $k$ rejections, so the output of that loop has law $p$. -/
theorem tsum_rejections_mul_trial {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x)
    (hM0 : M ≠ 0) (hMt : M ≠ ∞) (x : α) :
    ∑' k : ℕ, (∑' y, trial p q M hM (y, false)) ^ k * trial p q M hM (x, true) = p x := by
  have hsum := tsum_trial_false_add hM
  have hrt : ∑' y, trial p q M hM (y, false) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hsum ▸ le_self_add)
  have hr : 1 - ∑' y, trial p q M hM (y, false) = M⁻¹ :=
    ENNReal.sub_eq_of_eq_add_rev hrt hsum.symm
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, hr, inv_inv, trial_apply_true,
    ENNReal.mul_div_cancel hM0 hMt]

/-- **Uniqueness for the first-step equation of rejection sampling.** Let $p$ and $q$ be
probability mass functions on $\alpha$ and $M \in [0, \infty]$ with $M \ne 0$, $M \ne \infty$ and
$p(y) \le M\,q(y)$ for all $y \in \alpha$. For one round of rejection sampling for target $p$,
proposal $q$ and envelope $M$, write $P(x, \mathrm{accepted})$ for the probability that the round
proposes $x$ and accepts it, and $r$ for the sum over $y \in \alpha$ of the probabilities that it
proposes $y$ and rejects it. If $f \colon \alpha \to [0, \infty]$ takes only finite values and
satisfies $f(x) = P(x, \mathrm{accepted}) + r \, f(x)$ for every $x \in \alpha$, then $f(x) = p(x)$
for every $x \in \alpha$.

The law of the output of the loop that repeats independent rounds until one accepts satisfies this
first-step equation, so this result identifies that law as $p$. -/
theorem eq_of_firstStep {p q : PMF α} {M : ℝ≥0∞} (hM : ∀ x, p x ≤ M * q x) (hM0 : M ≠ 0)
    (hMt : M ≠ ∞) {out : α → ℝ≥0∞} (hfin : ∀ x, out x ≠ ∞)
    (hout : ∀ x, out x = trial p q M hM (x, true) + (∑' y, trial p q M hM (y, false)) * out x)
    (x : α) : out x = p x := by
  set r := ∑' y, trial p q M hM (y, false)
  have hr1 : r ≤ 1 := by rw [← tsum_trial_false_add hM]; exact le_self_add
  have hrt : r * out x ≠ ∞ := ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hr1)
    (hfin x)
  have h1 : out x = r * out x + M⁻¹ * out x := by
    rw [← add_mul, tsum_trial_false_add hM, one_mul]
  have h2 : trial p q M hM (x, true) = M⁻¹ * out x := by
    have := (hout x).symm.trans h1
    rw [add_comm (r * out x)] at this
    exact (ENNReal.add_left_inj hrt).mp this
  rw [trial_apply_true, div_eq_mul_inv, mul_comm] at h2
  exact ((ENNReal.mul_right_inj (ENNReal.inv_ne_zero.mpr hMt) (ENNReal.inv_ne_top.mpr hM0)).mp
    h2).symm

end Cslib.MachineLearning.Sampling
