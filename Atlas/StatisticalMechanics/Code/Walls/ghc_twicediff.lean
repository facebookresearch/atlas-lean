/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































import Mathlib
import Code.Ising.GKS
import Code.Sharpness.GHSFull
import Code.Sharpness.GHSConcavity

open scoped BigOperators
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace StatMech

namespace Walls

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]









theorem gtd_isingWeight_contDiff (β : ℝ) (s : ConfigSpace V) :
    ContDiff ℝ ⊤ (fun h => isingWeight G β h s) := by
  unfold isingWeight hamiltonian
  apply ContDiff.exp
  apply ContDiff.mul contDiff_const
  apply ContDiff.sub contDiff_const
  exact ContDiff.mul contDiff_id contDiff_const



theorem gtd_num_contDiff (β : ℝ) (f : ConfigSpace V → ℝ) :
    ContDiff ℝ ⊤ (fun h => ∑ s : ConfigSpace V, f s * isingWeight G β h s) :=
  ContDiff.sum (fun s _ => contDiff_const.mul (gtd_isingWeight_contDiff G β s))


theorem gtd_isingZ_contDiff (β : ℝ) :
    ContDiff ℝ ⊤ (fun h => isingZ G β h) :=
  ContDiff.sum (fun s _ => gtd_isingWeight_contDiff G β s)





theorem gtd_expectation_contDiff (β : ℝ) (f : ConfigSpace V → ℝ) :
    ContDiff ℝ ⊤ (fun h => isingExpectation G β h f) := by
  have hfun : (fun h => isingExpectation G β h f)
      = (fun h => (∑ s : ConfigSpace V, f s * isingWeight G β h s) / isingZ G β h) := by
    funext h; exact expectation_eq_div G β h f
  rw [hfun]
  exact ContDiff.div (gtd_num_contDiff G β f) (gtd_isingZ_contDiff G β)
    (fun h => isingZ_ne_zero G β h)







theorem gtd_magnetization_contDiff (β : ℝ) (o : V) :
    ContDiff ℝ ⊤ (fun h => isingExpectation G β h (fun s => spin s o)) :=
  gtd_expectation_contDiff G β _


theorem gtd_magnetization_differentiable (β : ℝ) (o : V) :
    Differentiable ℝ (fun h => isingExpectation G β h (fun s => spin s o)) :=
  (gtd_magnetization_contDiff G β o).differentiable (by simp)




theorem gtd_deriv_magnetization_contDiff (β : ℝ) (o : V) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv (fun h => isingExpectation G β h (fun s => spin s o))) := by
  have h : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun h => isingExpectation G β h (fun s => spin s o)) :=
    (gtd_magnetization_contDiff G β o).of_le le_top
  have := h.iterate_deriv 1
  simpa using this




theorem gtd_deriv_magnetization_differentiable (β : ℝ) (o : V) :
    Differentiable ℝ (deriv (fun h => isingExpectation G β h (fun s => spin s o))) :=
  (gtd_deriv_magnetization_contDiff G β o).differentiable (by simp)



theorem gtd_magnetization_differentiableAt_deriv (β : ℝ) (h : ℝ) (o : V) :
    DifferentiableAt ℝ (deriv (fun h => isingExpectation G β h (fun s => spin s o))) h :=
  gtd_deriv_magnetization_differentiable G β o h





theorem gtd_magnetization_continuousOn (β : ℝ) (o : V) :
    ContinuousOn (fun h => isingExpectation G β h (fun s => spin s o)) (Ici 0) :=
  (gtd_magnetization_differentiable G β o).continuous.continuousOn



theorem gtd_magnetization_differentiableOn_interior (β : ℝ) (o : V) :
    DifferentiableOn ℝ (fun h => isingExpectation G β h (fun s => spin s o))
      (interior (Ici 0)) :=
  (gtd_magnetization_differentiable G β o).differentiableOn



theorem gtd_deriv_magnetization_differentiableOn_interior (β : ℝ) (o : V) :
    DifferentiableOn ℝ (deriv (fun h => isingExpectation G β h (fun s => spin s o)))
      (interior (Ici 0)) :=
  (gtd_deriv_magnetization_differentiable G β o).differentiableOn














theorem gtd_magnetization_concaveOn_of_deriv2_nonpos (β : ℝ) (o : V)
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
