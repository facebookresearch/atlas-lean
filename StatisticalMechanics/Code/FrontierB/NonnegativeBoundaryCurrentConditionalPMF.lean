/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierB.NonnegativeCurrentFiniteMarginal
import Code.FrontierB.BoundaryCurrentParity









open MeasureTheory
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



noncomputable def boundaryNonnegativeParityPMF
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior : Finset V) : PMF (Finset (Sym2 V)) :=
  PMF.map (currentParitySupport G)
    (boundaryCurrentPMF G beta J hbeta hJ interior)

noncomputable def boundaryNonnegativeParityRawMass
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V)
    (H : Finset (Sym2 V)) : ℝ≥0∞ := by
  classical
  exact if boundaryParityAllowed G interior H then
    ENNReal.ofReal
      (inhomogeneousParityFiberMass G (fun e => beta * J e) H)
  else 0



theorem boundaryNonnegativeParityPMF_apply
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (interior : Finset V)
    (H : Finset (Sym2 V)) :
    boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior H =
      boundaryNonnegativeParityRawMass G beta J interior H *
        (ENNReal.ofReal (boundaryCurrentSum G beta J interior))⁻¹ := by
  classical
  rw [boundaryNonnegativeParityPMF, PMF.map_apply]
  by_cases hvalid : boundaryParityAllowed G interior H
  · rw [boundaryNonnegativeParityRawMass, if_pos hvalid]
    have hsources (m : EdgeCurrent G)
        (hm : currentParitySupport G m = H) :
        sources G (ofEdgeFun G m) ∩ interior = ∅ := by
      rw [sources_eq_sources_currentParitySupport G m, hm]
      exact hvalid.2
    let f : EdgeCurrent G → ℝ := fun m =>
      if H = currentParitySupport G m then
        weight G beta J (ofEdgeFun G m) else 0
    have hfnonneg : ∀ m, 0 ≤ f m := by
      intro m
      unfold f
      split
      · unfold weight
        exact Finset.prod_nonneg fun e _ =>
          div_nonneg (pow_nonneg (mul_nonneg hbeta.le (hJ e)) _)
            (Nat.cast_nonneg _)
      · exact le_rfl
    have hfsummable : Summable f := by
      simpa only [f, eq_comm] using
        summable_fixedParity_weight_nonnegative G beta hbeta J
          (fun e => hJ e.1) H hvalid.1
    have hftsum : ∑' m, f m =
        inhomogeneousParityFiberMass G (fun e => beta * J e) H := by
      simpa only [f, eq_comm] using
        fixedParity_weight_tsum_nonnegative G beta hbeta J
          (fun e => hJ e.1) H hvalid.1
    calc
      _ = ∑' m : EdgeCurrent G,
            ENNReal.ofReal (f m) *
              (ENNReal.ofReal (boundaryCurrentSum G beta J interior))⁻¹ := by
        apply tsum_congr
        intro m
        by_cases hm : H = currentParitySupport G m
        · simp [f, hm, boundaryCurrentPMF_apply,
            boundaryCurrentRawMass, hsources m hm.symm]
        · simp [f, hm]
      _ = (∑' m : EdgeCurrent G, ENNReal.ofReal (f m)) *
            (ENNReal.ofReal (boundaryCurrentSum G beta J interior))⁻¹ := by
        rw [ENNReal.tsum_mul_right]
      _ = ENNReal.ofReal (∑' m : EdgeCurrent G, f m) *
            (ENNReal.ofReal (boundaryCurrentSum G beta J interior))⁻¹ := by
        rw [ENNReal.ofReal_tsum_of_nonneg hfnonneg hfsummable]
      _ = _ := by rw [hftsum]
  · rw [boundaryNonnegativeParityRawMass, if_neg hvalid, zero_mul]
    rw [ENNReal.tsum_eq_zero]
    intro m
    by_cases hm : currentParitySupport G m = H
    · have hsrc : sources G (ofEdgeFun G m) ∩ interior ≠ ∅ := by
        intro hs
        apply hvalid
        refine ⟨hm ▸ currentParitySupport_subset G m, ?_⟩
        rw [← hm, ← sources_eq_sources_currentParitySupport G m]
        exact hs
      simp [hm, boundaryCurrentPMF_apply,
        boundaryCurrentRawMass, hsrc]
    · simp [Ne.symm hm]



theorem boundaryCurrentPMF_apply_eq_nonnegativeParity_factor
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (interior : Finset V)
    (m : EdgeCurrent G) :
    boundaryCurrentPMF G beta J hbeta.le hJ interior m =
      boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior
          (currentParitySupport G m) *
        nonnegativeFiniteParityPMF G.edgeFinset (fun e => beta * J e)
          (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1))
          (fun e : G.edgeFinset => e.1 ∈ currentParitySupport G m) m := by
  let H := currentParitySupport G m
  have hH : H ⊆ G.edgeFinset := currentParitySupport_subset G m
  rw [boundaryNonnegativeParityPMF_apply G beta hbeta J hJ interior H,
    nonnegativeFiniteParityPMF_apply, boundaryCurrentPMF_apply]
  classical
  unfold boundaryNonnegativeParityRawMass
  by_cases hsrc : sources G (ofEdgeFun G m) ∩ interior = ∅
  · have hallowed : boundaryParityAllowed G interior H := by
      refine ⟨hH, ?_⟩
      rw [← sources_eq_sources_currentParitySupport G m]
      exact hsrc
    rw [if_pos hallowed]
    have hfactor := weight_eq_nonnegativeParityFiberMass_mul_kernel
      G beta hbeta J (fun e => hJ e.1) H hH m rfl
    have hfiber := inhomogeneousParityFiberMass_nonneg G
      (fun e => beta * J e) (fun e => mul_nonneg hbeta.le (hJ e.1)) H
    have hkernel : nonnegativeParityCurrentKernel G
          (fun e => beta * J e) H m =
        nonnegativeFiniteParityKernel G.edgeFinset (fun e => beta * J e)
          (fun e : G.edgeFinset => e.1 ∈ currentParitySupport G m) m := by
      simp only [nonnegativeParityCurrentKernel,
        nonnegativeFiniteParityKernel, H]
    rw [boundaryCurrentRawMass, if_pos hsrc, hfactor,
      ENNReal.ofReal_mul hfiber]
    change ENNReal.ofReal
          (inhomogeneousParityFiberMass G (fun e => beta * J e) H) *
        ENNReal.ofReal (nonnegativeParityCurrentKernel G
          (fun e => beta * J e) H m) *
          (ENNReal.ofReal (boundaryCurrentSum G beta J interior))⁻¹ = _
    rw [hkernel]
    ac_rfl
  · have hnotAllowed : ¬boundaryParityAllowed G interior H := by
      intro h
      apply hsrc
      rw [sources_eq_sources_currentParitySupport G m]
      exact h.2
    rw [if_neg hnotAllowed]
    simp [boundaryCurrentRawMass, hsrc]



theorem boundaryCurrentPMF_eq_nonnegativeParity_bind
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (interior : Finset V) :
    boundaryCurrentPMF G beta J hbeta.le hJ interior =
      (boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior).bind
        (fun H => nonnegativeFiniteParityPMF G.edgeFinset
          (fun e => beta * J e)
          (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1))
          (fun e : G.edgeFinset => e.1 ∈ H)) := by
  apply PMF.ext
  intro m
  rw [PMF.bind_apply,
    boundaryCurrentPMF_apply_eq_nonnegativeParity_factor
      G beta hbeta J hJ interior m]
  symm
  rw [tsum_eq_single (currentParitySupport G m)]
  intro H hne
  by_cases hH : H ⊆ G.edgeFinset
  · have hk : nonnegativeParityCurrentKernel G
        (fun e => beta * J e) H m = 0 :=
      nonnegativeParityCurrentKernel_eq_zero_of_support_ne
        G (fun e => beta * J e) H hH m (Ne.symm hne)
    have hk' : nonnegativeFiniteParityKernel G.edgeFinset
        (fun e => beta * J e) (fun e : G.edgeFinset => e.1 ∈ H) m = 0 := by
      simpa only [nonnegativeFiniteParityKernel,
        nonnegativeParityCurrentKernel] using hk
    rw [nonnegativeFiniteParityPMF_apply, hk']
    simp
  · rw [boundaryNonnegativeParityPMF_apply G beta hbeta J hJ interior H]
    classical
    unfold boundaryNonnegativeParityRawMass
    rw [if_neg (fun h => hH h.1)]
    simp



theorem boundaryCurrentFiniteMarginal_eq_nonnegativeParity_bind
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (interior : Finset V)
    (S : Finset G.edgeFinset) :
    PMF.map (restrictCurrent S)
        (boundaryCurrentPMF G beta J hbeta.le hJ interior) =
      (PMF.map (restrictParity G S)
        (boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior)).bind
          (nonnegativeFiniteParityPMF S
            (fun e : G.edgeFinset => beta * J e.1)
            (fun e : ↑S => mul_nonneg hbeta.le (hJ e.1.1))) := by
  rw [boundaryCurrentPMF_eq_nonnegativeParity_bind
    G beta hbeta J hJ interior, PMF.map_bind, PMF.bind_map]
  congr 1
  funext H
  rw [nonnegativeParityPMF_map_restrictCurrent G
    (fun e => beta * J e)
    (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1)) H S]
  rfl

end StatMech.FrontierB
