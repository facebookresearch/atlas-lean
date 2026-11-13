/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































































import Code.OSSS.RevealmentCrossBox
import Code.OSSS.SharpnessFK
import Code.Walls.oc_boxcrossingscalesum
import Code.Walls.oc_boxobjects

open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace StatMech
namespace Walls

open StatMech.OSSS
open StatMech.OSSS.DecisionTree
open StatMech.OSSS.Revealment
open StatMech.OSSS.RevealmentConstruction
open StatMech.Lattice
open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]














section Family

variable {d : ℕ}






noncomputable def oc_clusterTree (endU endV : E → Site d) (o : Site d) (n : ℕ) (l : List E)
    (discF : ℕ → Finset (Site d)) (k : ℕ) : DecisionTree E :=
  crossTree endU endV o (vertexBoundary d n) l (discF k)












theorem oc_perScaleRevealment {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (n : ℕ) (l : List E)
    (discF : ℕ → Finset (Site d))
    (hdisc : ∀ k, ∀ x ∈ discF k, x ∈ vertexBoundary d k)
    (k : ℕ) (e : E) :
    reveal ν (oc_clusterTree endU endV o n l discF k) e
      ≤ (expect ν fun ω =>
            if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
        + (expect ν fun ω =>
            if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) :=
  reveal_crossTree_le_connected hν hinj hcoh hadj o (vertexBoundary d n) k l (discF k)
    (hdisc k) e






theorem oc_perScaleRevealment_family {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (n : ℕ) (l : List E)
    (discF : ℕ → Finset (Site d))
    (hdisc : ∀ k, ∀ x ∈ discF k, x ∈ vertexBoundary d k)
    {κ : Type*} (kscale : κ → ℕ) (k : κ) (e : E) :
    reveal ν (oc_clusterTree endU endV o n l discF (kscale k)) e
      ≤ (expect ν fun ω =>
            if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d (kscale k))
            then (1 : ℝ) else 0)
        + (expect ν fun ω =>
            if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d (kscale k))
            then (1 : ℝ) else 0) :=
  oc_perScaleRevealment hν hinj hcoh hadj o n l discF hdisc (kscale k) e










theorem oc_familyTrees_compute
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (n : ℕ) (l : List E) (hl : ∀ e, e ∈ l)
    (discF : ℕ → Finset (Site d)) (k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (ho : o ∈ box d (k - 1))
    (hBdisc : ∀ b ∈ vertexBoundary d k, b ∈ discF k) (hoB : o ∉ discF k)
    (ω : ConfigSpace E)
    [Decidable (ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n))] :
    (oc_clusterTree endU endV o n l discF k).evalR ω
      = if ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n) then (1 : ℝ) else 0 :=
  evalR_crossTree_connected hinj hcoh hadj k n hk hkn o ho l hl (discF k) hBdisc hoB ω

end Family










section Averaged

variable {d : ℕ}
















theorem oc_familyAveraged_covLowerBound {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (T : κ → DecisionTree E) (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
    (R : κ → E → ℝ) (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDnn : 0 ≤ D) (hsum : ∀ e, (∑ k, R k e) ≤ D) :
    (Fintype.card κ : ℝ) * c₀
        * (expect ν (A.indicator (fun _ => (1 : ℝ)))
            * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))))
      ≤ D * ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ))) :=
  SharpnessFK.covSum_ge_of_indicator hν hA T hT R hreach c₀ hc₀nn hc₀ D hDnn hsum





theorem oc_familyAveraged_covLowerBound_div {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (T : κ → DecisionTree E) (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
    (R : κ → E → ℝ) (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDpos : 0 < D) (hsum : ∀ e, (∑ k, R k e) ≤ D) :
    ((Fintype.card κ : ℝ) * c₀ / D)
        * (expect ν (A.indicator (fun _ => (1 : ℝ)))
            * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))))
      ≤ ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
  have hmain := oc_familyAveraged_covLowerBound hν hA T hT R hreach c₀ hc₀nn hc₀ D hDpos.le hsum
  rw [div_mul_eq_mul_div, div_le_iff₀ hDpos]
  calc (Fintype.card κ : ℝ) * c₀
        * (expect ν (A.indicator (fun _ => (1 : ℝ)))
            * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))))
      ≤ D * ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ))) := hmain
    _ = (∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ)))) * D := by ring

end Averaged















section Headline

variable {d : ℕ}



abbrev oc_ScaleIdx (n : ℕ) : Type := ↥(Finset.Icc 1 n)



noncomputable def oc_Rscale {ν : E → Bool → ℝ} (edge : E → Sym2 (Site d))
    (endU endV : E → Site d) (n : ℕ) (k : oc_ScaleIdx n) (e : E) : ℝ :=
  (expect ν fun ω =>
      if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k.1) then (1 : ℝ) else 0)
    + (expect ν fun ω =>
        if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k.1) then (1 : ℝ) else 0)












theorem oc_scaleSum_le {ν : E → Bool → ℝ} (edge : E → Sym2 (Site d))
    (endU endV : E → Site d) (n : ℕ)
    (μTrans : Site d → ℕ → ℝ) (hμ : ∀ x j, 0 ≤ μTrans x j)
    (Λ : Finset (Site d)) (hΛne : Λ.Nonempty)
    (rdist : Site d → ℕ) (e : E)
    (hru : endU e ∈ Λ) (hrv : endV e ∈ Λ)
    (hruN : rdist (endU e) ≤ n) (hrvN : rdist (endV e) ≤ n)
    (hcompu : ∀ k,
      (expect ν fun ω =>
          if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μTrans (endU e) ((k : ℤ) - (rdist (endU e) : ℤ)).natAbs)
    (hcompv : ∀ k,
      (expect ν fun ω =>
          if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μTrans (endV e) ((k : ℤ) - (rdist (endV e) : ℤ)).natAbs) :
    (∑ k : oc_ScaleIdx n, oc_Rscale (ν := ν) edge endU endV n k e)
      ≤ 4 * Λ.sup' hΛne (fun x => ∑ j ∈ Finset.range (n + 1), μTrans x j) := by
  
  have hreindex : (∑ k : oc_ScaleIdx n, oc_Rscale (ν := ν) edge endU endV n k e)
      = ∑ k ∈ Finset.Icc 1 n,
          ((expect ν fun ω =>
              if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
            + (expect ν fun ω =>
                if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k)
                then (1 : ℝ) else 0)) := by
    simp only [oc_Rscale]
    exact Finset.sum_coe_sort (Finset.Icc 1 n)
      (fun k => (expect ν fun ω =>
          if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
        + (expect ν fun ω =>
            if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0))
  rw [hreindex]
  exact oc_box_crossing_scale_sum Λ hΛne μTrans hμ n (rdist (endU e)) (rdist (endV e))
    hruN hrvN (endU e) (endV e) hru hrv
    (fun k => expect ν fun ω =>
      if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
    (fun k => expect ν fun ω =>
      if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0)
    hcompu hcompv























theorem oc_corOSSS {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (n : ℕ) (hn : 1 ≤ n) (l : List E)
    (discF : ℕ → Finset (Site d))
    (hdisc : ∀ k, ∀ x ∈ discF k, x ∈ vertexBoundary d k)
    (hT : ∀ k : oc_ScaleIdx n,
      (oc_clusterTree endU endV o n l discF k.1).evalR = A.indicator (fun _ => (1 : ℝ)))
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (μTrans : Site d → ℕ → ℝ) (hμ : ∀ x j, 0 ≤ μTrans x j)
    (Λ : Finset (Site d)) (hΛne : Λ.Nonempty)
    (rdist : Site d → ℕ)
    (hru : ∀ e, endU e ∈ Λ) (hrv : ∀ e, endV e ∈ Λ)
    (hruN : ∀ e, rdist (endU e) ≤ n) (hrvN : ∀ e, rdist (endV e) ≤ n)
    (hcompu : ∀ e k,
      (expect ν fun ω =>
          if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μTrans (endU e) ((k : ℤ) - (rdist (endU e) : ℤ)).natAbs)
    (hcompv : ∀ e k,
      (expect ν fun ω =>
          if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μTrans (endV e) ((k : ℤ) - (rdist (endV e) : ℤ)).natAbs) :
    (Fintype.card (oc_ScaleIdx n) : ℝ) * c₀
        * (expect ν (A.indicator (fun _ => (1 : ℝ)))
            * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))))
      ≤ (4 * Λ.sup' hΛne (fun x => ∑ j ∈ Finset.range (n + 1), μTrans x j))
          * ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
  haveI : Nonempty (oc_ScaleIdx n) := ⟨⟨1, by simp [Finset.mem_Icc]; omega⟩⟩
  refine oc_familyAveraged_covLowerBound hν hA
    (fun k => oc_clusterTree endU endV o n l discF k.1) hT
    (fun k e => oc_Rscale (ν := ν) edge endU endV n k e) ?_ c₀ hc₀nn hc₀
    (4 * Λ.sup' hΛne (fun x => ∑ j ∈ Finset.range (n + 1), μTrans x j)) ?_ ?_
  · 
    intro k e
    exact oc_perScaleRevealment hν hinj hcoh hadj o n l discF hdisc k.1 e
  · 
    have hsup : 0 ≤ Λ.sup' hΛne (fun x => ∑ j ∈ Finset.range (n + 1), μTrans x j) := by
      obtain ⟨x, hx⟩ := hΛne
      exact le_trans (Finset.sum_nonneg (fun j _ => hμ x j))
        (Finset.le_sup' (fun x => ∑ j ∈ Finset.range (n + 1), μTrans x j) hx)
    positivity
  · 
    intro e
    exact oc_scaleSum_le edge endU endV n μTrans hμ Λ hΛne rdist e
      (hru e) (hrv e) (hruN e) (hrvN e) (hcompu e) (hcompv e)

end Headline














section SharpForm

variable {d : ℕ}










theorem oc_sharp_covLowerBound {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (T : κ → DecisionTree E) (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
    (R : κ → E → ℝ) (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D Sn : ℝ) (hDnn : 0 ≤ D) (hsum : ∀ e, (∑ k, R k e) ≤ D)
    (hDS : D ≤ 8 * Sn)
    (hcovnn : 0 ≤ ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ)))) :
    (Fintype.card κ : ℝ) * c₀
        * (expect ν (A.indicator (fun _ => (1 : ℝ)))
            * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))))
      ≤ (8 * Sn) * ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
  refine le_trans (oc_familyAveraged_covLowerBound hν hA T hT R hreach c₀ hc₀nn hc₀ D hDnn hsum)
    ?_
  exact mul_le_mul_of_nonneg_right hDS hcovnn






theorem oc_fourD_le_eight_S {V : Type*} [Fintype V] [DecidableEq V]
    (Gf : ℕ → SimpleGraph V) [∀ n, DecidableRel (Gf n).Adj]
    (Af : ℕ → Set (ConfigSpace (Sym2 V))) (n : ℕ) (β : ℝ)
    (D : ℝ) (hD : D ≤ 2 * oc_S Gf Af n β) :
    4 * D ≤ 8 * oc_S Gf Af n β := by
  linarith

end SharpForm






















section Residue

variable {d : ℕ}










def oc_CodingCovBridge {ν : E → Bool → ℝ}
    (f : ConfigSpace E → ℝ) (θμ covCorr : ℝ) : Prop :=
  covCorr = ∑ e, cov ν (CovLowerBound.coordI e) f
    ∧ θμ = expect ν f













theorem oc_correlated_covLowerBound_of_bridge {ν : E → Bool → ℝ}
    (hν : IsProbWeight ν) {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (T : κ → DecisionTree E) (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
    (R : κ → E → ℝ) (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDnn : 0 ≤ D) (hsum : ∀ e, (∑ k, R k e) ≤ D)
    (θμ covCorr : ℝ)
    (hbridge : oc_CodingCovBridge (ν := ν) (A.indicator (fun _ => (1 : ℝ))) θμ covCorr) :
    (Fintype.card κ : ℝ) * c₀ * (θμ * (1 - θμ)) ≤ D * covCorr := by
  obtain ⟨hcov, hmean⟩ := hbridge
  rw [hmean, hcov]
  exact oc_familyAveraged_covLowerBound hν hA T hT R hreach c₀ hc₀nn hc₀ D hDnn hsum





theorem oc_codingCovBridge_refl {ν : E → Bool → ℝ} (f : ConfigSpace E → ℝ) :
    oc_CodingCovBridge (ν := ν) f (expect ν f) (∑ e, cov ν (CovLowerBound.coordI e) f) :=
  ⟨rfl, rfl⟩

end Residue

end Walls
end StatMech
