/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Code.OSSS.MonotonicOSSS
import Code.Walls.oc_core

open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace StatMech
namespace Walls

open StatMech.OSSS
open StatMech.OSSS.MonotonicMeasure
open StatMech.OSSS.MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]












noncomputable def oc2_meanCorr (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  genMean (fkMass G p q) g



noncomputable def oc2_covCorr (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  genCov (fkMass G p q) f g




noncomputable def oc2_coordRead (e : Sym2 V) : ConfigSpace (Sym2 V) → ℝ :=
  (genCoord e : ConfigSpace (Sym2 V) → ℝ)




lemma oc2_meanCorr_eq (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) :
    oc2_meanCorr G p q g = ∑ ω, g ω * fkMass G p q ω := rfl


lemma oc2_covCorr_def (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) :
    oc2_covCorr G p q f g
      = oc2_meanCorr G p q (fun ω => f ω * g ω)
        - oc2_meanCorr G p q f * oc2_meanCorr G p q g := rfl


lemma oc2_coordRead_apply (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    oc2_coordRead e ω = if ω e then (1 : ℝ) else 0 := rfl




lemma oc2_meanCorr_eq_fkMean (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) :
    oc2_meanCorr G p q g = FK.fkMean G p q g :=
  genMean_fkMass G p q g


lemma oc2_covCorr_eq_fkCov (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) :
    oc2_covCorr G p q f g = FK.fkCov G p q f g :=
  genCov_fkMass G p q f g


lemma oc2_coordRead_eq_coord (e : Sym2 V) :
    oc2_coordRead e = (FK.coord e : ConfigSpace (Sym2 V) → ℝ) :=
  genCoord_eq_coord e




lemma oc2_covCorr_symm (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) :
    oc2_covCorr G p q f g = oc2_covCorr G p q g f := by
  simp only [oc2_covCorr, genCov, genMean]
  rw [mul_comm (∑ ω, f ω * fkMass G p q ω)]
  congr 1
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma oc2_covCorr_add_right (p q : ℝ) (f g h : ConfigSpace (Sym2 V) → ℝ) :
    oc2_covCorr G p q f (fun ω => g ω + h ω)
      = oc2_covCorr G p q f g + oc2_covCorr G p q f h := by
  rw [oc2_covCorr_eq_fkCov, oc2_covCorr_eq_fkCov, oc2_covCorr_eq_fkCov]
  exact FK.fkCov_add_right G p q f g h


lemma oc2_covCorr_sum_right (p q : ℝ) {ι : Type*} (s : Finset ι)
    (f : ConfigSpace (Sym2 V) → ℝ) (g : ι → ConfigSpace (Sym2 V) → ℝ) :
    oc2_covCorr G p q f (fun ω => ∑ i ∈ s, g i ω)
      = ∑ i ∈ s, oc2_covCorr G p q f (g i) := by
  rw [oc2_covCorr_eq_fkCov]
  rw [show (∑ i ∈ s, oc2_covCorr G p q f (g i))
      = ∑ i ∈ s, FK.fkCov G p q f (g i) from
    Finset.sum_congr rfl (fun i _ => oc2_covCorr_eq_fkCov G p q f (g i))]
  exact FK.fkCov_sum_right G p q s f g


lemma oc2_meanCorr_const_mul (p q : ℝ) (c : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) :
    oc2_meanCorr G p q (fun ω => c * g ω) = c * oc2_meanCorr G p q g := by
  rw [oc2_meanCorr_eq_fkMean, oc2_meanCorr_eq_fkMean]
  exact FK.fkMean_const_mul G p q c g


lemma oc2_meanCorr_add (p q : ℝ) (g h : ConfigSpace (Sym2 V) → ℝ) :
    oc2_meanCorr G p q (fun ω => g ω + h ω)
      = oc2_meanCorr G p q g + oc2_meanCorr G p q h := by
  rw [oc2_meanCorr_eq_fkMean, oc2_meanCorr_eq_fkMean, oc2_meanCorr_eq_fkMean]
  exact FK.fkMean_add G p q g h


lemma oc2_covCorr_smul_right (p q : ℝ) (c : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) :
    oc2_covCorr G p q f (fun ω => c * g ω) = c * oc2_covCorr G p q f g := by
  rw [oc2_covCorr_def, oc2_covCorr_def,
      show (fun ω => f ω * (c * g ω)) = (fun ω => c * (f ω * g ω)) from by funext ω; ring,
      oc2_meanCorr_const_mul G p q c (fun ω => f ω * g ω),
      oc2_meanCorr_const_mul G p q c g]
  ring



lemma oc2_covCorr_const_right (p q : ℝ) (f : ConfigSpace (Sym2 V) → ℝ) {c : ℝ}
    (hZ : FK.fkZ G p q ≠ 0) :
    oc2_covCorr G p q f (fun _ => c) = 0 := by
  rw [oc2_covCorr_def]
  have hc : oc2_meanCorr G p q (fun _ => c) = c := by
    rw [oc2_meanCorr_eq_fkMean]; exact FK.fkMean_const G p q hZ
  have hfc : oc2_meanCorr G p q (fun ω => f ω * (fun _ => c) ω)
      = c * oc2_meanCorr G p q f := by
    rw [show (fun ω => f ω * (fun _ => c) ω) = (fun ω => c * f ω) from by funext ω; ring]
    exact oc2_meanCorr_const_mul G p q c f
  rw [hfc, hc]
  ring


lemma oc2_meanCorr_one (p q : ℝ) (hZ : FK.fkZ G p q ≠ 0) :
    oc2_meanCorr G p q (fun _ => (1 : ℝ)) = 1 := by
  rw [oc2_meanCorr_eq_fkMean]; exact FK.fkMean_const G p q hZ








noncomputable def oc2_covCorrSum (p q : ℝ) (f : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, oc2_covCorr G p q f (oc2_coordRead e)


noncomputable def oc2_thetaCorr (p q : ℝ) (f : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  oc2_meanCorr G p q f



lemma oc2_covCorrSum_eq_fkCovSum (p q : ℝ) (f : ConfigSpace (Sym2 V) → ℝ) :
    oc2_covCorrSum G p q f
      = ∑ e ∈ G.edgeFinset, FK.fkCov G p q f (FK.coord e) := by
  unfold oc2_covCorrSum
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [oc2_covCorr_eq_fkCov, oc2_coordRead_eq_coord]


lemma oc2_thetaCorr_eq_fkProbOf (p q : ℝ) (A : Set (ConfigSpace (Sym2 V))) :
    oc2_thetaCorr G p q (A.indicator (fun _ => (1 : ℝ)))
      = FK.fkProbOf G p q A := by
  unfold oc2_thetaCorr FK.fkProbOf
  exact oc2_meanCorr_eq_fkMean G p q _



lemma oc2_var_indicator_ccf (p q : ℝ) (A : Set (ConfigSpace (Sym2 V))) :
    oc2_covCorr G p q (A.indicator (fun _ => (1 : ℝ))) (A.indicator (fun _ => (1 : ℝ)))
      = FK.fkProbOf G p q A * (1 - FK.fkProbOf G p q A) := by
  rw [show oc2_covCorr G p q (A.indicator (fun _ => (1 : ℝ))) (A.indicator (fun _ => (1 : ℝ)))
        = genVar (fkMass G p q) (A.indicator (fun _ => (1 : ℝ))) from rfl]
  exact fkVar_indicator G p q A










variable {E : Type*} [Fintype E] [DecidableEq E]






theorem oc2_covCorrFrame_hits_bridge {ν : E → Bool → ℝ}
    (f : ConfigSpace E → ℝ) (θμ covCorr : ℝ) :
    oc_CodingCovBridge (ν := ν) f θμ covCorr
      ↔ (covCorr = ∑ e, cov ν (CovLowerBound.coordI e) f ∧ θμ = expect ν f) :=
  Iff.rfl






theorem oc2_covCorrFrame_codingFixedPoint {ν : E → Bool → ℝ} (f : ConfigSpace E → ℝ) :
    oc_CodingCovBridge (ν := ν) f (expect ν f) (∑ e, cov ν (CovLowerBound.coordI e) f) :=
  ⟨rfl, rfl⟩





theorem oc2_covCorrFrame_pinned {ν : E → Bool → ℝ}
    (f : ConfigSpace E → ℝ) (θμ covCorr : ℝ)
    (hbridge : oc_CodingCovBridge (ν := ν) f θμ covCorr) :
    covCorr = ∑ e, cov ν (CovLowerBound.coordI e) f ∧ θμ = expect ν f :=
  hbridge












theorem oc2_correlated_covLowerBound_frame
    {ν : Sym2 V → Bool → ℝ} (hν : IsProbWeight ν)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A)
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (T : κ → DecisionTree (Sym2 V))
    (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
    (R : κ → Sym2 V → ℝ) (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDnn : 0 ≤ D) (hsum : ∀ e, (∑ k, R k e) ≤ D)
    (p qf : ℝ)
    (hbridge : oc_CodingCovBridge (ν := ν) (A.indicator (fun _ => (1 : ℝ)))
      (oc2_thetaCorr G p qf (A.indicator (fun _ => (1 : ℝ))))
      (oc2_covCorrSum G p qf (A.indicator (fun _ => (1 : ℝ))))) :
    (Fintype.card κ : ℝ) * c₀
        * (oc2_thetaCorr G p qf (A.indicator (fun _ => (1 : ℝ)))
            * (1 - oc2_thetaCorr G p qf (A.indicator (fun _ => (1 : ℝ)))))
      ≤ D * oc2_covCorrSum G p qf (A.indicator (fun _ => (1 : ℝ))) :=
  oc_correlated_covLowerBound_of_bridge (ν := ν) hν hA T hT R hreach c₀ hc₀nn hc₀ D hDnn hsum
    _ _ hbridge

end Walls
end StatMech
