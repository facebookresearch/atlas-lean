/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.Ising.GKS
import Code.Ising.GKS2
import Code.Sharpness.GHSFull

open scoped BigOperators
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace StatMech

namespace Sharpness

open StatMech.Ising











theorem shg_concaveOn_antitoneOn_deriv (φ : ℝ → ℝ)
    (hconc : ConcaveOn ℝ (Ici 0) φ) (hdiff : ∀ h ∈ Ici (0 : ℝ), DifferentiableAt ℝ φ h) :
    AntitoneOn (deriv φ) (Ici 0) :=
  ConcaveOn.antitoneOn_deriv hconc hdiff




theorem shg_concaveOn_slope_anti (φ : ℝ → ℝ) (hconc : ConcaveOn ℝ (Ici 0) φ)
    {x : ℝ} (hx : x ∈ Ici (0 : ℝ)) :
    AntitoneOn (slope φ x) ((Ici 0) \ {x}) :=
  hconc.slope_anti hx









theorem shg_concaveOn_deriv_le_slope (φ : ℝ → ℝ) (hconc : ConcaveOn ℝ (Ici 0) φ)
    {a b : ℝ} (ha : a ∈ Ici (0 : ℝ)) (hb : b ∈ Ici (0 : ℝ)) (hab : a < b)
    (hd : DifferentiableAt ℝ φ b) :
    deriv φ b ≤ (φ b - φ a) / (b - a) := by
  have h := hconc.deriv_le_slope ha hb hab hd
  rwa [slope_def_field] at h









theorem shg_concaveOn_slope_anti_adjacent (φ : ℝ → ℝ) (hconc : ConcaveOn ℝ (Ici 0) φ)
    {x y z : ℝ} (hx : x ∈ Ici (0 : ℝ)) (hz : z ∈ Ici (0 : ℝ)) (hxy : x < y) (hyz : y < z) :
    (φ z - φ y) / (z - y) ≤ (φ y - φ x) / (y - x) :=
  hconc.slope_anti_adjacent hx hz hxy hyz



















theorem shg_concaveOn_of_deriv2_nonpos (φ : ℝ → ℝ)
    (hcont : ContinuousOn φ (Ici 0))
    (hf' : DifferentiableOn ℝ φ (interior (Ici 0)))
    (hf'' : DifferentiableOn ℝ (deriv φ) (interior (Ici 0)))
    (hu3 : ∀ h ∈ interior (Ici (0 : ℝ)), deriv^[2] φ h ≤ 0) :
    ConcaveOn ℝ (Ici 0) φ :=
  concaveOn_of_deriv2_nonpos (convex_Ici 0) hcont hf' hf'' hu3








variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]





theorem shg_magnetization_differentiable (β : ℝ) (o : V) :
    ∀ h ∈ Ici (0 : ℝ),
      DifferentiableAt ℝ (fun h => isingExpectation G β h (fun s => spin s o)) h :=
  fun h _ => (hasDerivAt_magnetization G β h o).differentiableAt






theorem shg_magnetization_antitoneOn_deriv (β : ℝ) (o : V)
    (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o))) :
    AntitoneOn (deriv (fun h => isingExpectation G β h (fun s => spin s o))) (Ici 0) :=
  shg_concaveOn_antitoneOn_deriv _ hconc (shg_magnetization_differentiable G β o)







theorem shg_magnetization_deriv_le_slope (β : ℝ) (o : V)
    (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)))
    {a b : ℝ} (ha : a ∈ Ici (0 : ℝ)) (hb : b ∈ Ici (0 : ℝ)) (hab : a < b) :
    deriv (fun h => isingExpectation G β h (fun s => spin s o)) b
      ≤ (isingExpectation G β b (fun s => spin s o)
          - isingExpectation G β a (fun s => spin s o)) / (b - a) :=
  shg_concaveOn_deriv_le_slope _ hconc ha hb hab
    ((hasDerivAt_magnetization G β b o).differentiableAt)




theorem shg_magnetization_slope_anti (β : ℝ) (o : V)
    (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)))
    {x : ℝ} (hx : x ∈ Ici (0 : ℝ)) :
    AntitoneOn (slope (fun h => isingExpectation G β h (fun s => spin s o)) x)
      ((Ici 0) \ {x}) :=
  shg_concaveOn_slope_anti _ hconc hx











theorem shg_magnetization_susceptibility_bound (β h : ℝ) (hh : 0 < h) (o : V)
    (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o))) :
    deriv (fun h => isingExpectation G β h (fun s => spin s o)) h
      ≤ isingExpectation G β h (fun s => spin s o) / h := by
  have hslope := shg_magnetization_deriv_le_slope G β o hconc
    (mem_Ici.mpr le_rfl) (mem_Ici.mpr hh.le) hh
  rwa [magnetization_zero_field G β o, sub_zero, sub_zero] at hslope

end Sharpness

end StatMech
