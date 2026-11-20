/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























import Code.OSSS.AdaptMConditional
import Code.OSSS.GrandCouplingAssembly

open scoped BigOperators
open Finset MeasureTheory

namespace StatMech

namespace OSSS

namespace CouplingStructure

open OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]
















theorem osss_coupling {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (U V : Fin n → ℝ) :
    
    (f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) 0))
        = f (codeMap μ (σ : Fin n → E) U))
    
    ∧ (∀ (h : ConfigSpace E → ConfigSpace E → ℝ) {Ch : ℝ}, (∀ x y, |h x y| ≤ Ch) →
        ∫ p, h (codeMap μ (σ : Fin n → E) p.1)
              (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) n))
            ∂((Vcube n).prod (Vcube n))
          = ∑ x, (∑ y, h x y * μ y) * μ x)
    
    ∧ (∀ t : ℕ, stopVal μ σ f U < t →
        codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) t)
          = codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) (t - 1))) := by
  refine ⟨f_adapt_zero_eq σ U V, ?_, fun t ht => adapt_step_eq_of_gt_stop σ U V t ht⟩
  intro h Ch hC
  
  have hWn : ∀ p : (Fin n → ℝ) × (Fin n → ℝ),
      adaptWt p.1 p.2 (stopVal μ σ f p.1) n = p.2 :=
    fun p => adaptWt_card p.1 p.2 (stopVal μ σ f p.1)
  have hrw : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        h (codeMap μ (σ : Fin n → E) p.1)
          (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) n)))
      = (fun p => h (codeMap μ (σ : Fin n → E) p.1) (codeMap μ (σ : Fin n → E) p.2)) := by
    funext p; rw [hWn p]
  rw [show (∫ p, h (codeMap μ (σ : Fin n → E) p.1)
              (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) n))
            ∂((Vcube n).prod (Vcube n)))
        = ∫ p, h (codeMap μ (σ : Fin n → E) p.1) (codeMap μ (σ : Fin n → E) p.2)
            ∂((Vcube n).prod (Vcube n)) from by rw [hrw]]
  exact integral_two_codeMap μ hpos hμ1 σ h hC

end CouplingStructure

end OSSS

end StatMech
