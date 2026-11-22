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

/-- The evidence `p(x) = ∑ z, p(x, z)` of an unnormalized posterior `p z = p(x, z)`. -/
def evidence (p : Z → ℝ) : ℝ := ∑ z, p z

/-- The posterior `p(z | x) = p(x, z) / p(x)`. -/
noncomputable def posterior (p : Z → ℝ) (z : Z) : ℝ := p z / evidence p

/-- The evidence lower bound `∑ z, q z (log p(x, z) - log q z)` of a distribution `q`. -/
noncomputable def elbo (p q : Z → ℝ) : ℝ := ∑ z, q z * (log (p z) - log (q z))

/-- The finite Kullback-Leibler formula `∑ z, q z (log q z - log r z)` (terms with `q z = 0`
vanish). It is the KL divergence `KL(q ‖ r)` when `r` has full support (`r z > 0` for all `z`),
which is the only case used here (`r` is the posterior of a positive joint). If `r` vanishes where
`q` does not, the divergence is infinite but this real-valued formula is not (it uses
`Real.log 0 = 0`; see the tests). -/
noncomputable def kl (q r : Z → ℝ) : ℝ := ∑ z, q z * (log (q z) - log (r z))

/-- **Gibbs' inequality**: `KL(q ‖ r) ≥ 0` for a distribution `q` and a full-support distribution
`r`. -/
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

/-- **ELBO = log evidence - KL**: for every distribution `q`,
`elbo p q = log p(x) - KL(q ‖ p(· | x))`. -/
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

/-- **The ELBO is a lower bound**: `elbo p q ≤ log p(x)` (Gibbs' inequality). -/
theorem elbo_le_log_evidence (hp : ∀ z, 0 < p z) {q : Z → ℝ} (hq : IsDist q) :
    elbo p q ≤ log (evidence p) :=
  sum_mul_log_sub_le hp hq

/-- **The KL divergence to the posterior is nonnegative.** -/
theorem kl_posterior_nonneg [Nonempty Z] (hp : ∀ z, 0 < p z) {q : Z → ℝ} (hq : IsDist q) :
    0 ≤ kl q (posterior p) := by
  have h1 := elbo_eq_log_evidence_sub_kl hp hq
  have h2 := elbo_le_log_evidence hp hq
  linarith

/-- The bound is attained at the posterior. -/
theorem elbo_posterior [Nonempty Z] (hp : ∀ z, 0 < p z) :
    elbo p (posterior p) = log (evidence p) :=
  sum_div_mul_log_sub hp

/-- EM's evidence lower bound is the sum of the per-point ELBOs. -/
theorem em_elbo_eq {Θ X : Type*} {N : ℕ} (p : Θ → X → Z → ℝ) (xs : Fin N → X) (θ : Θ)
    (q : Fin N → Z → ℝ) :
    LatentVariable.ExpectationMaximization.elbo p xs θ q = ∑ n, elbo (p θ (xs n)) (q n) := rfl

/-! ## Mean-field coordinate ascent -/

section MeanField

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The mean-field (product) distribution `q(a, b) = q₁ a q₂ b`. -/
noncomputable def prodDist (q₁ : A → ℝ) (q₂ : B → ℝ) (z : A × B) : ℝ := q₁ z.1 * q₂ z.2

theorem isDist_prodDist {q₁ : A → ℝ} {q₂ : B → ℝ} (h₁ : IsDist q₁) (h₂ : IsDist q₂) :
    IsDist (prodDist q₁ q₂) := by
  refine ⟨fun z => mul_nonneg (h₁.1 _) (h₂.1 _), ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [prodDist, ← Finset.mul_sum, h₂.2, mul_one, h₁.2]

/-- The expected log-joint of `a` under `q₂`: `E_{q₂}[log p(a, ·)]`. -/
noncomputable def expectedLog (p : A × B → ℝ) (q₂ : B → ℝ) (a : A) : ℝ :=
  ∑ b, q₂ b * log (p (a, b))

/-- The coordinate-ascent (CAVI) update of the first factor:
`q₁ a ∝ exp (E_{q₂}[log p(a, ·)])`. -/
noncomputable def cavi (p : A × B → ℝ) (q₂ : B → ℝ) (a : A) : ℝ :=
  exp (expectedLog p q₂ a) / ∑ a', exp (expectedLog p q₂ a')

theorem isDist_cavi [Nonempty A] (p : A × B → ℝ) (q₂ : B → ℝ) : IsDist (cavi p q₂) := by
  have hS : 0 < ∑ a', exp (expectedLog p q₂ a') :=
    Finset.sum_pos (fun a _ => exp_pos _) Finset.univ_nonempty
  refine ⟨fun a => (div_pos (exp_pos _) hS).le, ?_⟩
  simp only [cavi]
  rw [← Finset.sum_div, div_self hS.ne']

/-- The ELBO of a product distribution splits into a `q₁`-term and the entropy of `q₂`. -/
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

/-- **The CAVI update maximizes the ELBO over the first factor**: for every `q₁`, replacing it by
`cavi p q₂` does not decrease the ELBO. -/
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

/-- The joint with its two factors swapped. -/
noncomputable def swapJoint (p : A × B → ℝ) (z : B × A) : ℝ := p z.swap

theorem elbo_prodDist_swap (p : A × B → ℝ) (q₁ : A → ℝ) (q₂ : B → ℝ) :
    elbo p (prodDist q₁ q₂) = elbo (swapJoint p) (prodDist q₂ q₁) := by
  rw [elbo, elbo, ← (Equiv.prodComm A B).sum_comp]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [prodDist, swapJoint, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
    Prod.swap_swap, mul_comm (q₁ z.1)]

/-- The CAVI update of the second factor: `q₂ b ∝ exp (E_{q₁}[log p(·, b)])`. -/
noncomputable def cavi₂ (p : A × B → ℝ) (q₁ : A → ℝ) : B → ℝ := cavi (swapJoint p) q₁

/-- **The CAVI update of the second factor does not decrease the ELBO.** -/
theorem elbo_le_elbo_cavi₂ [Nonempty B] (p : A × B → ℝ) {q₁ : A → ℝ} {q₂ : B → ℝ}
    (h₁ : IsDist q₁) (h₂ : IsDist q₂) :
    elbo p (prodDist q₁ q₂) ≤ elbo p (prodDist q₁ (cavi₂ p q₁)) := by
  rw [elbo_prodDist_swap, elbo_prodDist_swap p q₁]
  exact elbo_le_elbo_cavi (swapJoint p) h₂ h₁

/-- One sweep of coordinate ascent: update the first factor, then the second. -/
noncomputable def sweep (p : A × B → ℝ) (q : (A → ℝ) × (B → ℝ)) : (A → ℝ) × (B → ℝ) :=
  (cavi p q.2, cavi₂ p (cavi p q.2))

theorem isDist_sweep [Nonempty A] [Nonempty B] (p : A × B → ℝ) (q : (A → ℝ) × (B → ℝ)) :
    IsDist (sweep p q).1 ∧ IsDist (sweep p q).2 :=
  ⟨isDist_cavi p q.2, isDist_cavi (swapJoint p) _⟩

/-- **A sweep of coordinate ascent does not decrease the ELBO.** -/
theorem elbo_le_elbo_sweep [Nonempty A] [Nonempty B] (p : A × B → ℝ) {q : (A → ℝ) × (B → ℝ)}
    (h : IsDist q.1 ∧ IsDist q.2) :
    elbo p (prodDist q.1 q.2) ≤ elbo p (prodDist (sweep p q).1 (sweep p q).2) :=
  le_trans (elbo_le_elbo_cavi p h.1 h.2)
    (elbo_le_elbo_cavi₂ p (isDist_cavi p q.2) h.2)

/-- **Mean-field coordinate ascent never decreases the ELBO**: along the sweeps from any product
distribution the ELBO is monotone, and (for a positive joint) it stays below the log evidence. -/
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
