/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.ExpectationMaximization
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Variational inference: the ELBO and mean-field coordinate ascent

Variational inference on a finite latent space (Bishop, *Pattern Recognition and Machine
Learning*, Sections 10.1 and 10.1.1; Blei, Kucukelbir and McAuliffe, *Variational inference: a
review for statisticians*, J. Amer. Statist. Assoc. 112, 2017). For an unnormalized posterior
`p z = p(x, z) > 0` with evidence `evidence p = ∑ z, p z`, a distribution `q` has evidence lower
bound `elbo p q = ∑ z, q z (log p z - log q z)`. This is the per-point term of EM's ELBO
(`em_elbo_eq`, `LatentVariable/ExpectationMaximization.lean`).

Main results:

* `elbo_eq_log_evidence_sub_kl`: **ELBO = log evidence - KL(q ‖ posterior)**;
  `elbo_le_log_evidence`, `kl_posterior_nonneg`, `elbo_posterior`: the bound, nonnegativity of
  the KL divergence, and tightness at the posterior.
* Mean field on a product latent space `A × B`: `prodDist`, `expectedLog`, the coordinate-ascent
  (CAVI) updates `cavi` (`q₁ a ∝ exp E_{q₂}[log p(a, ·)]`) and `cavi₂`. `elbo_prodDist` splits
  the ELBO. `elbo_le_elbo_cavi`, `elbo_le_elbo_cavi₂`: **each update maximizes the ELBO over its
  factor**; `elbo_iterate_sweep_monotone`: **coordinate ascent never decreases the ELBO**, which
  stays below the log evidence (`elbo_prodDist_le_log_evidence`).

Two blocks cover the general mean-field step: the update of one factor given any distribution on
the others is `cavi` with `B` the product of the other factors.

## Cost model

None: the subject is the ELBO, over the reals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Variational

open Real
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization (IsDist sum_mul_log_sub_le
  sum_div_mul_log_sub)

variable {Z : Type*} [Fintype Z]

/-! ## The ELBO and the KL divergence -/

/-- **Evidence of an unnormalized posterior.** Let $Z$ be a finite set and let
$p : Z \to \mathbb{R}$ give the joint values $p(z) = p(x, z)$ of a fixed observation $x$ with each
latent value $z \in Z$ (an unnormalized posterior). The evidence is
$p(x) = \sum_{z \in Z} p(z)$. -/
def evidence (p : Z → ℝ) : ℝ := ∑ z, p z

/-- **Posterior of an unnormalized joint.** Let $Z$ be a finite set and let
$p : Z \to \mathbb{R}$ give the joint values $p(z) = p(x, z)$ of a fixed observation $x$ with each
latent value $z \in Z$. The posterior of $z$ is $p(z \mid x) = p(z) / p(x)$, where
$p(x) = \sum_{z' \in Z} p(z')$ is the evidence (the quotient is read as $0$ when $p(x) = 0$). -/
noncomputable def posterior (p : Z → ℝ) (z : Z) : ℝ := p z / evidence p

/-- **Evidence lower bound of a single observation.** Let $Z$ be a finite set, let
$p : Z \to \mathbb{R}$ give the joint values $p(z) = p(x, z)$ of a fixed observation $x$ with each
latent value $z \in Z$, and let $q : Z \to \mathbb{R}$. The evidence lower bound of $q$ is
$\mathrm{ELBO}(p, q) = \sum_{z \in Z} q(z) \bigl(\log p(z) - \log q(z)\bigr)$. -/
noncomputable def elbo (p q : Z → ℝ) : ℝ := ∑ z, q z * (log (p z) - log (q z))

/-- **Finite Kullback–Leibler formula.** Let $Z$ be a finite set and let $q, r : Z \to \mathbb{R}$.
The Kullback–Leibler formula of $q$ against $r$ is
$\mathrm{KL}(q \,\|\, r) = \sum_{z \in Z} q(z) \bigl(\log q(z) - \log r(z)\bigr)$; terms with
$q(z) = 0$ vanish.

This is the Kullback–Leibler divergence of $q$ from $r$ when $r(z) > 0$ for every $z$, the only
case used here (where $r$ is the posterior of a positive joint). If $r$ vanishes where $q$ does
not, the divergence is infinite, but this real-valued formula is finite, since it reads $\log 0$
as $0$. -/
noncomputable def kl (q r : Z → ℝ) : ℝ := ∑ z, q z * (log (q z) - log (r z))

/-- **Gibbs' inequality.** Let $Z$ be a finite set, let $q$ be a probability distribution on $Z$,
and let $r : Z \to \mathbb{R}$ satisfy $r(z) > 0$ for every $z \in Z$ and
$\sum_{z \in Z} r(z) = 1$. Then
$\mathrm{KL}(q \,\|\, r) = \sum_{z \in Z} q(z) \bigl(\log q(z) - \log r(z)\bigr) \ge 0$. -/
theorem kl_nonneg {q r : Z → ℝ} (hq : IsDist q) (hr : ∀ z, 0 < r z) (hrs : ∑ z, r z = 1) :
    0 ≤ kl q r := by
  have h := sum_mul_log_sub_le hr hq
  rw [hrs, log_one] at h
  have : kl q r = -∑ z, q z * (log (r z) - log (q z)) := by
    rw [kl, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  linarith

variable {p : Z → ℝ}

theorem evidence_pos [Nonempty Z] (hp : ∀ z, 0 < p z) : 0 < evidence p :=
  Finset.sum_pos (fun z _ => hp z) Finset.univ_nonempty

/-- **The ELBO is the log evidence minus the KL divergence.** Let $Z$ be a nonempty finite set
and let $p : Z \to \mathbb{R}$ give the joint values $p(z) = p(x, z)$ of a fixed observation $x$
with each latent value $z \in Z$, where $p(z) > 0$ for every $z \in Z$. Let
$p(x) = \sum_{z \in Z} p(z)$ be the evidence and $p(z \mid x) = p(z) / p(x)$ the posterior. For
$q, r : Z \to \mathbb{R}$ write
$\mathrm{ELBO}(p, q) = \sum_{z \in Z} q(z) \bigl(\log p(z) - \log q(z)\bigr)$ and
$\mathrm{KL}(q \,\|\, r) = \sum_{z \in Z} q(z) \bigl(\log q(z) - \log r(z)\bigr)$. Then for every
probability distribution $q$ on $Z$,
$\mathrm{ELBO}(p, q) = \log p(x) - \mathrm{KL}\bigl(q \,\|\, p(\cdot \mid x)\bigr)$. -/
theorem elbo_eq_log_evidence_sub_kl [Nonempty Z] (hp : ∀ z, 0 < p z) {q : Z → ℝ}
    (hq : IsDist q) : elbo p q = log (evidence p) - kl q (posterior p) := by
  have hE := evidence_pos hp
  have hpost : ∀ z, log (posterior p z) = log (p z) - log (evidence p) := fun z =>
    log_div (hp z).ne' hE.ne'
  simp only [elbo, kl, hpost]
  have : ∑ z, q z * (log (q z) - (log (p z) - log (evidence p))) =
      -∑ z, q z * (log (p z) - log (q z)) + log (evidence p) * ∑ z, q z := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [this, hq.2]
  ring

/-- **The ELBO is a lower bound.** Let $Z$ be a finite set and let $p : Z \to \mathbb{R}$ satisfy
$p(z) > 0$ for all $z$, with evidence $p(x) = \sum_{z \in Z} p(z)$. Then for every probability
distribution $q$ on $Z$,
$$\mathrm{ELBO}(p, q) = \sum_{z \in Z} q(z) (\log p(z) - \log q(z)) \le \log p(x).$$

This is Gibbs' inequality. -/
theorem elbo_le_log_evidence (hp : ∀ z, 0 < p z) {q : Z → ℝ} (hq : IsDist q) :
    elbo p q ≤ log (evidence p) :=
  sum_mul_log_sub_le hp hq

/-- **The KL divergence to the posterior is nonnegative.** Let $Z$ be a nonempty finite set, let
$p : Z \to \mathbb{R}$ satisfy $p(z) > 0$ for every $z \in Z$, and let $q$ be a probability
distribution on $Z$. Let $\pi(z) = p(z) / \sum_{z' \in Z} p(z')$ be the posterior of $p$. Then
$\mathrm{KL}(q \,\|\, \pi) = \sum_{z \in Z} q(z) \bigl(\log q(z) - \log \pi(z)\bigr) \ge 0$. -/
theorem kl_posterior_nonneg [Nonempty Z] (hp : ∀ z, 0 < p z) {q : Z → ℝ} (hq : IsDist q) :
    0 ≤ kl q (posterior p) := by
  have h1 := elbo_eq_log_evidence_sub_kl hp hq
  have h2 := elbo_le_log_evidence hp hq
  linarith

/-- **The ELBO bound is attained at the posterior.** Let $Z$ be a nonempty finite set and let
$p : Z \to \mathbb{R}$ satisfy $p(z) > 0$ for all $z$, with evidence $p(x) = \sum_{z \in Z} p(z)$
and posterior $p(z \mid x) = p(z) / p(x)$. Then $\mathrm{ELBO}(p, p(\cdot \mid x)) = \log p(x)$,
where $\mathrm{ELBO}(p, q) = \sum_{z} q(z) (\log p(z) - \log q(z))$. -/
theorem elbo_posterior [Nonempty Z] (hp : ∀ z, 0 < p z) :
    elbo p (posterior p) = log (evidence p) :=
  sum_div_mul_log_sub hp

/-- **The EM evidence lower bound is a sum of per-point ELBOs.** Let $Z$ be a finite set, let
$p_\theta(x, z)$ be real numbers indexed by parameters $\theta$, observations $x$ and latent values
$z \in Z$, let $x_1, \dots, x_N$ be data, let $\theta$ be a parameter and let
$q_1, \dots, q_N : Z \to \mathbb{R}$. Then the evidence lower bound of expectation-maximization,
$\sum_{n=1}^N \sum_{z \in Z} q_n(z) \bigl(\log p_\theta(x_n, z) - \log q_n(z)\bigr)$, equals
$\sum_{n=1}^N \mathrm{ELBO}(p_\theta(x_n, \cdot), q_n)$, the sum over the data points of the
single-observation evidence lower bound of $q_n$ for the joint values
$z \mapsto p_\theta(x_n, z)$. -/
theorem em_elbo_eq {Θ X : Type*} {N : ℕ} (p : Θ → X → Z → ℝ) (xs : Fin N → X) (θ : Θ)
    (q : Fin N → Z → ℝ) :
    LatentVariable.ExpectationMaximization.elbo p xs θ q = ∑ n, elbo (p θ (xs n)) (q n) := rfl

/-! ## Mean-field coordinate ascent -/

section MeanField

variable {A B : Type*} [Fintype A] [Fintype B]

/-- **Mean-field product distribution.** Let $A$ and $B$ be finite sets and let
$q_1 : A \to \mathbb{R}$ and $q_2 : B \to \mathbb{R}$. Their mean-field (product) distribution is
the function on $A \times B$ given by $q(a, b) = q_1(a) \, q_2(b)$. -/
noncomputable def prodDist (q₁ : A → ℝ) (q₂ : B → ℝ) (z : A × B) : ℝ := q₁ z.1 * q₂ z.2

theorem isDist_prodDist {q₁ : A → ℝ} {q₂ : B → ℝ} (h₁ : IsDist q₁) (h₂ : IsDist q₂) :
    IsDist (prodDist q₁ q₂) := by
  refine ⟨fun z => mul_nonneg (h₁.1 _) (h₂.1 _), ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [prodDist, ← Finset.mul_sum, h₂.2, mul_one, h₁.2]

/-- **Expected log-joint.** Let $A$ and $B$ be finite sets and let $p : A \times B \to \mathbb{R}$
and $q_2 : B \to \mathbb{R}$. For $a \in A$, the expected log-joint of $a$ under $q_2$ is
$\mathbb{E}_{q_2}[\log p(a, \cdot)] = \sum_{b \in B} q_2(b) \log p(a, b)$. -/
noncomputable def expectedLog (p : A × B → ℝ) (q₂ : B → ℝ) (a : A) : ℝ :=
  ∑ b, q₂ b * log (p (a, b))

/-- **Mean-field (CAVI) update of the first factor.** Let $A$ and $B$ be finite sets, let
$p : A \times B \to \mathbb{R}$ be a joint and let $q_2 : B \to \mathbb{R}$. The
coordinate-ascent update of the first factor is the function $q_1 : A \to \mathbb{R}$ given by
$$q_1(a) = \frac{\exp E(a)}{\sum_{a' \in A} \exp E(a')},$$
where $E(a) = \sum_{b \in B} q_2(b) \log p(a, b)$ is the expected log-joint of $a$ under $q_2$.
That is, $q_1(a) \propto \exp \mathbb{E}_{q_2}[\log p(a, \cdot)]$.

Here $\log$ is the real logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$. -/
noncomputable def cavi (p : A × B → ℝ) (q₂ : B → ℝ) (a : A) : ℝ :=
  exp (expectedLog p q₂ a) / ∑ a', exp (expectedLog p q₂ a')

theorem isDist_cavi [Nonempty A] (p : A × B → ℝ) (q₂ : B → ℝ) : IsDist (cavi p q₂) := by
  have hS : 0 < ∑ a', exp (expectedLog p q₂ a') :=
    Finset.sum_pos (fun a _ => exp_pos _) Finset.univ_nonempty
  refine ⟨fun a => (div_pos (exp_pos _) hS).le, ?_⟩
  simp only [cavi]
  rw [← Finset.sum_div, div_self hS.ne']

/-- **ELBO of a product distribution.** Let $A$ and $B$ be finite sets, let
$p : A \times B \to \mathbb{R}$ be a joint, and let $q_1$ and $q_2$ be probability distributions
on $A$ and $B$, with product $(q_1 q_2)(a, b) = q_1(a) q_2(b)$. Then
$$\mathrm{ELBO}(p, q_1 q_2) = \sum_{a \in A} q_1(a) \bigl(E(a) - \log q_1(a)\bigr) -
\sum_{b \in B} q_2(b) \log q_2(b),$$
where $E(a) = \sum_{b \in B} q_2(b) \log p(a, b)$ is the expected log-joint of $a$ under $q_2$
and $\mathrm{ELBO}(p, q) = \sum_{z} q(z) (\log p(z) - \log q(z))$. So the ELBO splits into a
$q_1$-term and the entropy of $q_2$.

Here $\log$ is the real logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$. -/
theorem elbo_prodDist (p : A × B → ℝ) {q₁ : A → ℝ} {q₂ : B → ℝ} (h₁ : IsDist q₁)
    (h₂ : IsDist q₂) :
    elbo p (prodDist q₁ q₂) =
      ∑ a, q₁ a * (expectedLog p q₂ a - log (q₁ a)) - ∑ b, q₂ b * log (q₂ b) := by
  have hterm : ∀ a b, prodDist q₁ q₂ (a, b) * (log (p (a, b)) - log (prodDist q₁ q₂ (a, b))) =
      q₁ a * (q₂ b * log (p (a, b))) - q₁ a * q₂ b * log (q₁ a) - q₁ a * (q₂ b * log (q₂ b)) := by
    intro a b
    simp only [prodDist]
    rcases (h₁.1 a).eq_or_lt with ha | ha
    · rw [← ha]; ring
    rcases (h₂.1 b).eq_or_lt with hb | hb
    · rw [← hb]; ring
    rw [log_mul ha.ne' hb.ne']
    ring
  rw [elbo, Fintype.sum_prod_type]
  simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h₂.2]
  rw [h₁.2, one_mul]
  simp only [expectedLog, mul_one, mul_sub, Finset.sum_sub_distrib]

/-- **The CAVI update maximizes the ELBO over the first factor.** Let $A$ and $B$ be finite sets
with $A$ nonempty, let $p : A \times B \to \mathbb{R}$ be a joint, and let $q_1$ and $q_2$ be
probability distributions on $A$ and $B$. Let $q_1^*$ be the CAVI update of the first factor
given $q_2$, $q_1^*(a) = \exp E(a) / \sum_{a' \in A} \exp E(a')$ with
$E(a) = \sum_{b \in B} q_2(b) \log p(a, b)$. Then
$\mathrm{ELBO}(p, q_1 q_2) \le \mathrm{ELBO}(p, q_1^* q_2)$, where
$(q_1 q_2)(a, b) = q_1(a) q_2(b)$ and
$\mathrm{ELBO}(p, q) = \sum_{z} q(z) (\log p(z) - \log q(z))$.

Here $\log$ is the real logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$. -/
theorem elbo_le_elbo_cavi [Nonempty A] (p : A × B → ℝ) {q₁ : A → ℝ} {q₂ : B → ℝ}
    (h₁ : IsDist q₁) (h₂ : IsDist q₂) :
    elbo p (prodDist q₁ q₂) ≤ elbo p (prodDist (cavi p q₂) q₂) := by
  rw [elbo_prodDist p h₁ h₂, elbo_prodDist p (isDist_cavi p q₂) h₂]
  have hg := sum_mul_log_sub_le (p := fun a => exp (expectedLog p q₂ a)) (fun a => exp_pos _) h₁
  have heq := sum_div_mul_log_sub (p := fun a => exp (expectedLog p q₂ a)) (fun a => exp_pos _)
  simp only [log_exp] at hg heq
  have : ∑ a, cavi p q₂ a * (expectedLog p q₂ a - log (cavi p q₂ a)) =
      log (∑ a, exp (expectedLog p q₂ a)) := heq
  linarith

/-- **Swapped joint.** Let $A$ and $B$ be finite sets and let $p : A \times B \to \mathbb{R}$. The
swapped joint of $p$ is the function on $B \times A$ given by $(b, a) \mapsto p(a, b)$. -/
noncomputable def swapJoint (p : A × B → ℝ) (z : B × A) : ℝ := p z.swap

theorem elbo_prodDist_swap (p : A × B → ℝ) (q₁ : A → ℝ) (q₂ : B → ℝ) :
    elbo p (prodDist q₁ q₂) = elbo (swapJoint p) (prodDist q₂ q₁) := by
  rw [elbo, elbo, ← (Equiv.prodComm A B).sum_comp]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [prodDist, swapJoint, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
    Prod.swap_swap, mul_comm (q₁ z.1)]

/-- **Mean-field (CAVI) update of the second factor.** Let $A$ and $B$ be finite sets, let
$p : A \times B \to \mathbb{R}$ be a joint and let $q_1 : A \to \mathbb{R}$. The
coordinate-ascent update of the second factor is the function $q_2 : B \to \mathbb{R}$ given by
$$q_2(b) = \frac{\exp F(b)}{\sum_{b' \in B} \exp F(b')},$$
where $F(b) = \sum_{a \in A} q_1(a) \log p(a, b)$. That is,
$q_2(b) \propto \exp \mathbb{E}_{q_1}[\log p(\cdot, b)]$; it is the update of the first factor
applied to the joint with its two factors swapped.

Here $\log$ is the real logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$. -/
noncomputable def cavi₂ (p : A × B → ℝ) (q₁ : A → ℝ) : B → ℝ := cavi (swapJoint p) q₁

/-- **The CAVI update of the second factor does not decrease the ELBO.** Let $A$ and $B$ be finite
sets with $B$ nonempty, let $p : A \times B \to \mathbb{R}$ be a joint, and let $q_1$ and $q_2$ be
probability distributions on $A$ and $B$. Let $q_2^*$ be the CAVI update of the second factor
given $q_1$, $q_2^*(b) = \exp F(b) / \sum_{b' \in B} \exp F(b')$ with
$F(b) = \sum_{a \in A} q_1(a) \log p(a, b)$. Then
$\mathrm{ELBO}(p, q_1 q_2) \le \mathrm{ELBO}(p, q_1 q_2^*)$, where
$(q_1 q_2)(a, b) = q_1(a) q_2(b)$ and
$\mathrm{ELBO}(p, q) = \sum_{z} q(z) (\log p(z) - \log q(z))$.

Here $\log$ is the real logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$. -/
theorem elbo_le_elbo_cavi₂ [Nonempty B] (p : A × B → ℝ) {q₁ : A → ℝ} {q₂ : B → ℝ}
    (h₁ : IsDist q₁) (h₂ : IsDist q₂) :
    elbo p (prodDist q₁ q₂) ≤ elbo p (prodDist q₁ (cavi₂ p q₁)) := by
  rw [elbo_prodDist_swap, elbo_prodDist_swap p q₁]
  exact elbo_le_elbo_cavi (swapJoint p) h₂ h₁

/-- **Mean-field coordinate-ascent sweep.** Let $A$ and $B$ be finite sets and
$p : A \times B \to \mathbb{R}$. One sweep of coordinate ascent (CAVI) sends a pair of factors
$(q_1, q_2)$, with $q_1 : A \to \mathbb{R}$ and $q_2 : B \to \mathbb{R}$, to $(q_1', q_2')$, where
$q_1'$ is the CAVI update of the first factor given $q_2$,
$q_1'(a) = \exp(\sum_b q_2(b) \log p(a, b)) / \sum_{a'} \exp(\sum_b q_2(b) \log p(a', b))$, and
$q_2'$ is the CAVI update of the second factor given the new first factor $q_1'$,
$q_2'(b) = \exp(\sum_a q_1'(a) \log p(a, b)) / \sum_{b'} \exp(\sum_a q_1'(a) \log p(a, b'))$.
The old first factor $q_1$ is not used.

Here $\log x$ means $\log |x|$ for $x \ne 0$ and $\log 0 = 0$, so $p$ need not be positive. -/
noncomputable def sweep (p : A × B → ℝ) (q : (A → ℝ) × (B → ℝ)) : (A → ℝ) × (B → ℝ) :=
  (cavi p q.2, cavi₂ p (cavi p q.2))

theorem isDist_sweep [Nonempty A] [Nonempty B] (p : A × B → ℝ) (q : (A → ℝ) × (B → ℝ)) :
    IsDist (sweep p q).1 ∧ IsDist (sweep p q).2 :=
  ⟨isDist_cavi p q.2, isDist_cavi (swapJoint p) _⟩

/-- **A sweep of coordinate ascent does not decrease the ELBO.** Let $A$ and $B$ be nonempty
finite sets, let $p : A \times B \to \mathbb{R}$ be a joint, and let $q_1$ and $q_2$ be probability
distributions on $A$ and $B$. One sweep replaces $q_1$ by its CAVI update $q_1'$ given $q_2$ and
then $q_2$ by its CAVI update $q_2'$ given $q_1'$, where
$q_1'(a) \propto \exp \sum_{b} q_2(b) \log p(a, b)$ and
$q_2'(b) \propto \exp \sum_{a} q_1'(a) \log p(a, b)$, each normalized to sum to $1$. Then
$\mathrm{ELBO}(p, q_1 q_2) \le \mathrm{ELBO}(p, q_1' q_2')$, where
$(q_1 q_2)(a, b) = q_1(a) q_2(b)$ and
$\mathrm{ELBO}(p, q) = \sum_{z} q(z) (\log p(z) - \log q(z))$.

Here $\log$ is the real logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$. -/
theorem elbo_le_elbo_sweep [Nonempty A] [Nonempty B] (p : A × B → ℝ) {q : (A → ℝ) × (B → ℝ)}
    (h : IsDist q.1 ∧ IsDist q.2) :
    elbo p (prodDist q.1 q.2) ≤ elbo p (prodDist (sweep p q).1 (sweep p q).2) :=
  le_trans (elbo_le_elbo_cavi p h.1 h.2)
    (elbo_le_elbo_cavi₂ p (isDist_cavi p q.2) h.2)

/-- **Mean-field coordinate ascent never decreases the ELBO.** Let $A$ and $B$ be nonempty finite
sets, let $p : A \times B \to \mathbb{R}$ be a joint, and let $q_1^{(0)}$ and $q_2^{(0)}$ be
probability distributions on $A$ and $B$. A sweep of coordinate ascent replaces $q_1$ by its CAVI
update $q_1'(a) \propto \exp \sum_{b} q_2(b) \log p(a, b)$ and then $q_2$ by its CAVI update
$q_2'(b) \propto \exp \sum_{a} q_1'(a) \log p(a, b)$, each normalized to sum to $1$. Let
$(q_1^{(t)}, q_2^{(t)})$ be the result of $t$ sweeps from $(q_1^{(0)}, q_2^{(0)})$. Then
$t \mapsto \mathrm{ELBO}(p, q_1^{(t)} q_2^{(t)})$ is monotone on $\mathbb{N}$, where
$(q_1 q_2)(a, b) = q_1(a) q_2(b)$ and
$\mathrm{ELBO}(p, q) = \sum_{z} q(z) (\log p(z) - \log q(z))$.

Here $\log$ is the real logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$. -/
theorem elbo_iterate_sweep_monotone [Nonempty A] [Nonempty B] (p : A × B → ℝ)
    {q₀ : (A → ℝ) × (B → ℝ)} (h₀ : IsDist q₀.1 ∧ IsDist q₀.2) :
    Monotone fun t => elbo p (prodDist ((sweep p)^[t] q₀).1 ((sweep p)^[t] q₀).2) := by
  have hdist : ∀ t, IsDist ((sweep p)^[t] q₀).1 ∧ IsDist ((sweep p)^[t] q₀).2 := by
    intro t
    induction t with
    | zero => exact h₀
    | succ t _ => rw [Function.iterate_succ_apply']; exact isDist_sweep p _
  refine monotone_nat_of_le_succ fun t => ?_
  simp only [Function.iterate_succ_apply']
  exact elbo_le_elbo_sweep p (hdist t)

theorem elbo_prodDist_le_log_evidence {p : A × B → ℝ} (hp : ∀ z, 0 < p z) {q₁ : A → ℝ}
    {q₂ : B → ℝ}
    (h₁ : IsDist q₁) (h₂ : IsDist q₂) : elbo p (prodDist q₁ q₂) ≤ log (evidence p) :=
  elbo_le_log_evidence hp (isDist_prodDist h₁ h₂)

end MeanField

end Cslib.MachineLearning.Variational
