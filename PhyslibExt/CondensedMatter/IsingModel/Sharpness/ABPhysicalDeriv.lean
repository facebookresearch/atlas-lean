/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABGhostInfluence
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.BetaReparam

/-!
# β-derivatives of percolation probabilities with a ghost field

Chain rule for probabilities under parameters depending on a real variable, applied to the edge
probabilities `1 - e^{-βJ_e}` with a fixed ghost parameter.

## i. Overview

If each edge parameter `r_e(t)` is differentiable, the probability of an increasing event is
differentiable with derivative `∑_e r_e'(t) P(e pivotal)`. For the parameters `p_e(β) = 1 -
e^{-βJ_e}` off the ghost edges and a fixed value `q` on them, `∂_β P(A) = ∑_{e ∉ ghost} J_e
e^{-βJ_e} P(e pivotal)`, which equals `∑_e J_e P(e closed and pivotal)`.

## ii. Key results

- `abpd_hasDerivAt_probV_profile` : the chain rule
- `abpdBetaFieldParams` : the parameters `1 - e^{-βJ_e}` with ghost parameter `q`
- `abpd_deriv_beta_field_profile_closed` : `∂_β P(A) = ∑_e J_e P(e closed pivotal)`

## iii. Table of contents

- A. The chain rule
- B. The β-dependence

## iv. References

- M. Aizenman, D. J. Barsky, "Sharpness of the phase transition in percolation models", Comm. Math.
  Phys. 108 (1987) 489–526

-/

@[expose] public section

open Finset Set

namespace StatMech
namespace Sharpness

open ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## A. The chain rule -/

lemma abpd_hasDerivAt_configWeightV_profile
    (r : ℝ → E → ℝ) (r' : E → ℝ) (t : ℝ)
    (hr : ∀ e, HasDerivAt (fun u => r u e) (r' e) t)
    (omega : ConfigSpace E) :
    HasDerivAt (fun u => configWeightV (r u) omega)
      (∑ e, (if omega e then r' e else -(r' e)) * weightOffV (r t) e omega) t := by
  have hedge : ∀ e, HasDerivAt (fun u => edgeWeightV (r u) omega e)
      (if omega e then r' e else -(r' e)) t := by
    intro e
    by_cases he : omega e
    · simpa [edgeWeightV, he] using hr e
    · simp only [edgeWeightV, he]
      exact ((hasDerivAt_const t (1 : ℝ)).sub (hr e)).congr_deriv (by simp)
  have hprod := HasDerivAt.fun_finsetProd
    (u := (Finset.univ : Finset E))
    (f := fun e u => edgeWeightV (r u) omega e)
    (f' := fun e => if omega e then r' e else -(r' e))
    (x := t) (fun e _ => hedge e)
  unfold configWeightV
  refine hprod.congr_deriv ?_
  apply Finset.sum_congr rfl
  intro e _
  simp only [smul_eq_mul, weightOffV]
  ring

lemma abpd_hasDerivAt_probV_profile
    (r : ℝ → E → ℝ) (r' : E → ℝ) (t : ℝ)
    (hr : ∀ e, HasDerivAt (fun u => r u e) (r' e) t)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    HasDerivAt (fun u => probV (r u) A)
      (∑ e, r' e * pivotalProbV (r t) A e) t := by
  unfold probV
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (ConfigSpace E)))
    (fun omega _ =>
      (abpd_hasDerivAt_configWeightV_profile r r' t hr omega).const_mul
        (A.indicator (fun _ => (1 : ℝ)) omega))
  refine hsum.congr_deriv ?_
  calc
    (∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
        (∑ e, (if omega e then r' e else -(r' e)) * weightOffV (r t) e omega)) =
      ∑ omega, ∑ e, r' e *
        (A.indicator (fun _ => (1 : ℝ)) omega *
          ((if omega e then (1 : ℝ) else -1) * weightOffV (r t) e omega)) := by
            apply Finset.sum_congr rfl
            intro omega _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e _
            by_cases he : omega e <;> simp [he] <;> ring
    _ = ∑ e, ∑ omega, r' e *
        (A.indicator (fun _ => (1 : ℝ)) omega *
          ((if omega e then (1 : ℝ) else -1) * weightOffV (r t) e omega)) :=
      Finset.sum_comm
    _ = ∑ e, r' e * (∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
        ((if omega e then (1 : ℝ) else -1) * weightOffV (r t) e omega)) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.mul_sum]
    _ = ∑ e, r' e * pivotalProbV (r t) A e := by
          apply Finset.sum_congr rfl
          intro e _
          rw [abfd_russo_per_edge (r t) A hA e]

/-! ## B. The β-dependence -/

/-- Edge parameters `1 - e^{-βJ_e}` off `s` and `q` on `s`. -/
noncomputable def abpdBetaFieldParams (s : Finset E) (q : ℝ) (J : E → ℝ)
    (beta : ℝ) : E → ℝ :=
  paramOn s q (fun e => pBeta (J e) beta)

lemma abpd_hasDerivAt_beta_field_profile (s : Finset E) (q : ℝ) (J : E → ℝ)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (beta : ℝ) :
    HasDerivAt (fun b => probV (abpdBetaFieldParams s q J b) A)
      (∑ e, (if e ∈ s then 0 else J e * Real.exp (-beta * J e)) *
        pivotalProbV (abpdBetaFieldParams s q J beta) A e) beta := by
  refine abpd_hasDerivAt_probV_profile _ _ beta ?_ A hA
  intro e
  unfold abpdBetaFieldParams paramOn
  by_cases he : e ∈ s
  · simp only [he, ite_true]
    exact hasDerivAt_const beta q
  · simp only [he, ite_false]
    exact shr_pBeta_hasDerivAt (J e) beta

lemma abpd_deriv_beta_field_profile (s : Finset E) (q : ℝ) (J : E → ℝ)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (beta : ℝ) :
    deriv (fun b => probV (abpdBetaFieldParams s q J b) A) beta =
      ∑ e, (if e ∈ s then 0 else J e * Real.exp (-beta * J e)) *
        pivotalProbV (abpdBetaFieldParams s q J beta) A e :=
  (abpd_hasDerivAt_beta_field_profile s q J A hA beta).deriv

lemma abpd_deriv_beta_field_profile_closed (s : Finset E) (q : ℝ) (J : E → ℝ)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (beta : ℝ) :
    deriv (fun b => probV (abpdBetaFieldParams s q J b) A) beta =
      ∑ e, if e ∈ s then 0 else
        J e * probV (abpdBetaFieldParams s q J beta) (abgiClosedPivotal e A) := by
  rw [abpd_deriv_beta_field_profile s q J A hA beta]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e ∈ s
  · simp [he]
  · simp only [he, ite_false]
    rw [abgi_probV_closedPivotal]
    have hclosed : 1 - abpdBetaFieldParams s q J beta e =
        Real.exp (-beta * J e) := by
      simp [abpdBetaFieldParams, paramOn, he, pBeta]
    rw [hclosed]
    ring

end Sharpness
end StatMech
