/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Code.OSSS.FKSharpnessAssembly
import Code.OSSS.BetaCMatch

open scoped BigOperators Classical
open Finset Real Set Filter Topology

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace OSSS
namespace OSFKAssemblyClose

open StatMech.OSSS.Lindeberg
open StatMech.OSSS.SharpnessFK
open StatMech.OSSS.Integration
open StatMech.OSSS.BetaCMatch
open StatMech.FK
open MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V]











theorem ofa_russoPrefactor_ge_four {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (4 : ℝ) ≤ russoPrefactor p := by
  rw [russoPrefactor, le_div_iff₀ (mul_pos hp (by linarith))]
  nlinarith [sq_nonneg (p - 1 / 2)]






















theorem ofa_fk_q2_differential_inequality (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A)
    (hbridge : ∑ e, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)
          = ∑ e ∈ G.edgeFinset, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)) :
    russoPrefactor p * (fkProbOf G p 2 A * (1 - fkProbOf G p 2 A))
      ≤ deriv (fun p => fkProbOf G p 2 A) p :=
  fk_differential_inequality G hp hp1 (by norm_num : (1 : ℝ) ≤ 2) A hA hbridge




























theorem ofa_fk_q2_subcritical_decay (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A)
    (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hbridge : ∀ x ∈ Icc a b,
        ∑ e, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)
          = ∑ e ∈ G.edgeFinset, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
    (hθub : ∀ x ∈ Icc a b, fkProbOf G x 2 A ≤ 1 - κ) :
    fkProbOf G a 2 A ≤ Real.exp (-(4 * κ * (b - a))) := by
  
  have hxbounds : ∀ x ∈ Icc a b, 0 < x ∧ x < 1 := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hb1⟩
  have hdi : ∀ x ∈ Icc a b,
       russoPrefactor x * (fkProbOf G x 2 A * (1 - fkProbOf G x 2 A))
        ≤ deriv (fun p => fkProbOf G p 2 A) x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hxbounds x hx
    exact ofa_fk_q2_differential_inequality G hx0 hx1 A hA (hbridge x hx)
  
  have hrlb : ∀ x ∈ Icc a b, (4 * κ) ≤ russoPrefactor x * κ := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hxbounds x hx
    exact mul_le_mul_of_nonneg_right (ofa_russoPrefactor_ge_four hx0 hx1) hκ.le
  exact fk_subcritical_decay G (by norm_num : (1 : ℝ) ≤ 2) A a b κ hab ha0 hb1 hκ hdi hθub
    (4 * κ) (by positivity) hrlb



















theorem ofa_fk_meanField_lower
    (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β' β fβ fβ' m : ℝ)
    (hββ : β' ≤ β) (hm1 : 1 ≤ m)
    (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
    (hmlim : Tendsto mseq atTop (𝓝 m))
    (hbound : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β') :
    β - β' ≤ fβ - fβ' :=
  Integration.meanField_lower T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hbound

















theorem ofa_betaC_eq_threshold (Θ : ℝ → ℝ) (β₁ : ℝ)
    (hP1 : ∀ β, β < β₁ → Θ β = 0)
    (hP2 : ∀ β, β₁ < β → 0 < Θ β) :
    sSup (bcm_subcriticalSet Θ) = β₁ :=
  bcm_betaC_eq_threshold Θ β₁ hP1 hP2






























theorem ofa_fk_q2_sharpness (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A)
    (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hbridge : ∀ x ∈ Icc a b,
        ∑ e, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)
          = ∑ e ∈ G.edgeFinset, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
    (hθub : ∀ x ∈ Icc a b, fkProbOf G x 2 A ≤ 1 - κ)
    (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β' β fβ fβ' m : ℝ)
    (hββ : β' ≤ β) (hm1 : 1 ≤ m)
    (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
    (hmlim : Tendsto mseq atTop (𝓝 m))
    (hboundMF : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β')
    (Θ : ℝ → ℝ) (β₁ : ℝ)
    (hP1 : ∀ b₀, b₀ < β₁ → Θ b₀ = 0)
    (hP2 : ∀ b₀, β₁ < b₀ → 0 < Θ b₀) :
    (fkProbOf G a 2 A ≤ Real.exp (-(4 * κ * (b - a))))
      ∧ (β - β' ≤ fβ - fβ')
      ∧ sSup (bcm_subcriticalSet Θ) = β₁ :=
  ⟨ofa_fk_q2_subcritical_decay G A hA a b κ hab ha0 hb1 hκ hbridge hθub,
   ofa_fk_meanField_lower T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hboundMF,
   ofa_betaC_eq_threshold Θ β₁ hP1 hP2⟩
















theorem ofa_potts_decay (q : ℝ) (hq : 2 ≤ q) (c pottsCorr θ : ℝ)
    (hES : pottsCorr = (q - 1) / q * θ)
    (hθ_nonneg : 0 ≤ θ) (hθ_decay : θ ≤ Real.exp (-c)) :
    0 ≤ pottsCorr ∧ pottsCorr ≤ Real.exp (-c) :=
  SharpnessFK.potts_decay_of_fk q hq c pottsCorr θ hES hθ_nonneg hθ_decay











theorem ofa_hcov_residueFree (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A) :
    fkProbOf G p q A * (1 - fkProbOf G p q A)
      ≤ ∑ e, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) :=
  fk_poincare_indicator G hp hp1 hq A hA






















theorem ofa_summary (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A)
    (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hbridge : ∀ x ∈ Icc a b,
        ∑ e, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)
          = ∑ e ∈ G.edgeFinset, fkCov G x 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
    (hθub : ∀ x ∈ Icc a b, fkProbOf G x 2 A ≤ 1 - κ) :
    (fkProbOf G a 2 A * (1 - fkProbOf G a 2 A)
        ≤ ∑ e, fkCov G a 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
    ∧ (fkProbOf G a 2 A ≤ Real.exp (-(4 * κ * (b - a)))) :=
  ⟨ofa_hcov_residueFree G ha0 (by linarith) (by norm_num : (1 : ℝ) ≤ 2) A hA,
   ofa_fk_q2_subcritical_decay G A hA a b κ hab ha0 hb1 hκ hbridge hθub⟩

end OSFKAssemblyClose
end OSSS
end StatMech
