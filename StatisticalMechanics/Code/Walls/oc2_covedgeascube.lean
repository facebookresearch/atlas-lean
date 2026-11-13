/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Code.OSSS.GrandCoupling
import Code.OSSS.Lindeberg
import Code.OSSS.CovLowerBound

open scoped BigOperators
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace Walls

open StatMech.OSSS
open StatMech.OSSS.Coding
open StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]












noncomputable def oc2_cubeCov (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (F G : ConfigSpace E → ℝ) : ℝ :=
  (∫ u, F (codeMap μ σ u) * G (codeMap μ σ u) ∂(Vcube n))
    - (∫ u, F (codeMap μ σ u) ∂(Vcube n)) * (∫ u, G (codeMap μ σ u) ∂(Vcube n))











theorem oc2_cubeIntegral_eq_mean (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) :
    ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) = Lindeberg.mean μ g :=
  integral_g_codeMap μ hpos hμ1 σ g













theorem oc2_cubeCov_eq_cov (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (F G : ConfigSpace E → ℝ) :
    oc2_cubeCov μ (σ : Fin n → E) F G = Lindeberg.cov μ F G := by
  unfold oc2_cubeCov
  
  rw [show (fun u => F (codeMap μ (σ : Fin n → E) u) * G (codeMap μ (σ : Fin n → E) u))
        = (fun u => (fun ω => F ω * G ω) (codeMap μ (σ : Fin n → E) u)) from rfl]
  rw [oc2_cubeIntegral_eq_mean μ hpos hμ1 σ (fun ω => F ω * G ω)]
  
  rw [oc2_cubeIntegral_eq_mean μ hpos hμ1 σ F]
  rw [oc2_cubeIntegral_eq_mean μ hpos hμ1 σ G]
  
  rw [Lindeberg.cov]













theorem oc2_cov_edge_as_cube (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    Lindeberg.cov μ f (Lindeberg.coord e)
      = oc2_cubeCov μ (σ : Fin n → E) f (Lindeberg.coord e) :=
  (oc2_cubeCov_eq_cov μ hpos hμ1 σ f (Lindeberg.coord e)).symm







theorem oc2_cov_edge_as_cube_coordI (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    Lindeberg.cov μ f (CovLowerBound.coordI e)
      = oc2_cubeCov μ (σ : Fin n → E) f (CovLowerBound.coordI e) :=
  (oc2_cubeCov_eq_cov μ hpos hμ1 σ f (CovLowerBound.coordI e)).symm

end Walls
end StatMech
