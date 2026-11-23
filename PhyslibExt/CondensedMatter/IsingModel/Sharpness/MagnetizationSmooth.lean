/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.GHSConcavity

/-!
# Smoothness of the finite-volume magnetization in the field

Gibbs expectations of a finite Ising model are `C^∞` functions of the external field, and a
nonpositive second field derivative gives concavity on `[0, ∞)`.

## i. Overview

Every Boltzmann weight `exp(β(∑ σ_xσ_y + h ∑ σ_x))` is smooth in `h`, so the partition function and
every Gibbs expectation are smooth, being quotients of finite sums with a positive denominator. In
particular the magnetization and its derivative are differentiable everywhere, which supplies the
regularity hypotheses of the second-derivative test for concavity.

## ii. Key results

- `gtd_expectation_contDiff` : Gibbs expectations are smooth in `h`
- `gtd_magnetization_concaveOn_of_deriv2_nonpos` : a nonpositive second field derivative on `(0, ∞)`
  makes the magnetization concave on `[0, ∞)`

## iii. Table of contents

- A. Smoothness in the field
- B. Concavity from the second derivative

## iv. References

-/

@[expose] public section

open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Walls

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Smoothness in the field -/

omit [DecidableEq V] in
lemma gtd_isingWeight_contDiff (β : ℝ) (s : ConfigSpace V) :
    ContDiff ℝ ⊤ (fun h => isingWeight G β h s) := by
  unfold isingWeight hamiltonian
  apply ContDiff.exp
  apply ContDiff.mul contDiff_const
  apply ContDiff.sub contDiff_const
  exact ContDiff.mul contDiff_id contDiff_const

lemma gtd_num_contDiff (β : ℝ) (f : ConfigSpace V → ℝ) :
    ContDiff ℝ ⊤ (fun h => ∑ s : ConfigSpace V, f s * isingWeight G β h s) :=
  ContDiff.sum (fun s _ => contDiff_const.mul (gtd_isingWeight_contDiff G β s))

lemma gtd_isingZ_contDiff (β : ℝ) :
    ContDiff ℝ ⊤ (fun h => isingZ G β h) :=
  ContDiff.sum (fun s _ => gtd_isingWeight_contDiff G β s)

lemma gtd_expectation_contDiff (β : ℝ) (f : ConfigSpace V → ℝ) :
    ContDiff ℝ ⊤ (fun h => isingExpectation G β h f) := by
  have hfun : (fun h => isingExpectation G β h f)
      = (fun h => (∑ s : ConfigSpace V, f s * isingWeight G β h s) / isingZ G β h) := by
    funext h; exact expectation_eq_div G β h f
  rw [hfun]
  exact ContDiff.div (gtd_num_contDiff G β f) (gtd_isingZ_contDiff G β)
    (fun h => isingZ_ne_zero G β h)

lemma gtd_magnetization_contDiff (β : ℝ) (o : V) :
    ContDiff ℝ ⊤ (fun h => isingExpectation G β h (fun s => spin s o)) :=
  gtd_expectation_contDiff G β _

lemma gtd_magnetization_differentiable (β : ℝ) (o : V) :
    Differentiable ℝ (fun h => isingExpectation G β h (fun s => spin s o)) :=
  (gtd_magnetization_contDiff G β o).differentiable (by simp)

lemma gtd_deriv_magnetization_contDiff (β : ℝ) (o : V) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv (fun h => isingExpectation G β h (fun s => spin s o))) := by
  have h : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun h => isingExpectation G β h (fun s => spin s o)) :=
    (gtd_magnetization_contDiff G β o).of_le le_top
  have := h.iterate_deriv 1
  simpa using this

lemma gtd_deriv_magnetization_differentiable (β : ℝ) (o : V) :
    Differentiable ℝ (deriv (fun h => isingExpectation G β h (fun s => spin s o))) :=
  (gtd_deriv_magnetization_contDiff G β o).differentiable (by simp)

lemma gtd_magnetization_differentiableAt_deriv (β : ℝ) (h : ℝ) (o : V) :
    DifferentiableAt ℝ (deriv (fun h => isingExpectation G β h (fun s => spin s o))) h :=
  gtd_deriv_magnetization_differentiable G β o h

/-! ## B. Concavity from the second derivative -/

lemma gtd_magnetization_continuousOn (β : ℝ) (o : V) :
    ContinuousOn (fun h => isingExpectation G β h (fun s => spin s o)) (Ici 0) :=
  (gtd_magnetization_differentiable G β o).continuous.continuousOn

lemma gtd_magnetization_differentiableOn_interior (β : ℝ) (o : V) :
    DifferentiableOn ℝ (fun h => isingExpectation G β h (fun s => spin s o))
      (interior (Ici 0)) :=
  (gtd_magnetization_differentiable G β o).differentiableOn

lemma gtd_deriv_magnetization_differentiableOn_interior (β : ℝ) (o : V) :
    DifferentiableOn ℝ (deriv (fun h => isingExpectation G β h (fun s => spin s o)))
      (interior (Ici 0)) :=
  (gtd_deriv_magnetization_differentiable G β o).differentiableOn

lemma gtd_magnetization_concaveOn_of_deriv2_nonpos (β : ℝ) (o : V)
    (hu3 : ∀ h ∈ interior (Ici (0 : ℝ)),
      deriv^[2] (fun h => isingExpectation G β h (fun s => spin s o)) h ≤ 0) :
    ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)) :=
  shg_concaveOn_of_deriv2_nonpos _
    (gtd_magnetization_continuousOn G β o)
    (gtd_magnetization_differentiableOn_interior G β o)
    (gtd_deriv_magnetization_differentiableOn_interior G β o)
    hu3

end Walls

end StatMech
