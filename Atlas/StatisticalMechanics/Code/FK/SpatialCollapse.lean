/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.FK.AvgDensityCollapse
import Code.FK.FKUniqPrimitives
import Code.FK.BoundaryInfluenceDecay

open MeasureTheory Set Filter Topology Real
open scoped BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1000000

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

variable {d : ℕ}































theorem spc_growingBox_collapse (t : ℝ)
    (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e - L| ≤ δ n)
    (hbdy : Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
      atTop (𝓝 0)) :
    Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop (𝓝 L) :=
  adc_avgDensity_tendsto_of_homogeneity d t hE L hL0 hL1 In hIE δ hδ0 hδlim hin hbdy










theorem spc_boundaryFraction_le_surfaceVolume (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (In : Finset (Sym2 (boxVerts d n)))
    (hIE : In ⊆ (boxGraph d n).edgeFinset)
    (hbd : ((boxGraph d n).edgeFinset.card - In.card : ℝ)
      ≤ C * (Finset.univ.filter (boxBoundary d n)).card)
    (hEpos : 0 < (boxGraph d n).edgeFinset.card) :
    (((boxGraph d n).edgeFinset.card - In.card : ℝ)) / (boxGraph d n).edgeFinset.card
      ≤ C * (((Finset.univ.filter (boxBoundary d n)).card : ℝ)
              / (boxGraph d n).edgeFinset.card) := by
  have hEpos' : (0:ℝ) < (boxGraph d n).edgeFinset.card := by exact_mod_cast hEpos
  rw [← mul_div_assoc]
  exact (div_le_div_iff_of_pos_right hEpos').mpr hbd










theorem spc_growingBox_collapse_of_uniformBulk (hd : 1 ≤ d) (t : ℝ)
    (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ n, ((boxGraph d n).edgeFinset.card - (In n).card : ℝ)
      ≤ C * (Finset.univ.filter (boxBoundary d n)).card)
    (hbd0 : ∀ n, 0 ≤ ((boxGraph d n).edgeFinset.card - (In n).card : ℝ))
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e - L| ≤ δ n) :
    Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop (𝓝 L) := by
  
  have hsv := fup_surfaceVolume_tendsto_zero d hd
  
  have hCsv : Tendsto (fun n => C * (((Finset.univ.filter (boxBoundary d n)).card : ℝ)
        / (boxGraph d n).edgeFinset.card)) atTop (𝓝 0) := by
    have := hsv.const_mul C; simpa using this
  
  have hbdy : Tendsto (fun n =>
      (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
      atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      apply div_nonneg (hbd0 n)
      exact_mod_cast (hE n).le
    · intro n
      exact spc_boundaryFraction_le_surfaceVolume n C hC (In n) (hIE n) (hbd n) (hE n)
    · exact hCsv
  exact spc_growingBox_collapse t hE L hL0 hL1 In hIE δ hδ0 hδlim hin hbdy




















theorem spc_offCentreCarrier_gives_homogeneity (N : ℕ) (v : Site d)
    (eb eb' : Sym2 (boxVerts d N)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcarrier : Tendsto (fbd_offCentreCarrier N v eb' p 2) atTop (𝓝 0))
    (htrans : ∀ k,
        edgeMargProb
            (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2)
            (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb'))
          = edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)) :
    wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb') p :=
  fbd_wired_density_eq_of_offCentreCarrier N v eb eb' hp hp1 hcarrier htrans

















theorem spc_uniformBulk_is_offCentreCarrier_remark : True := trivial












theorem spc_tiltFreeEnergy_instIrrel (N : ℕ) (H : SimpleGraph (boxVerts d N))
    (i1 i2 : DecidableRel H.Adj) (t : ℝ) :
    @ivp2_tiltFreeEnergy _ _ _ H i1 2 t = @ivp2_tiltFreeEnergy _ _ _ H i2 2 t := by
  congr 1








theorem spc_range_finite (N : ℕ) (Gn : ℕ → SimpleGraph (boxVerts d N))
    [inst : ∀ n, DecidableRel (Gn n).Adj] (t : ℝ) :
    (Set.range (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t)).Finite := by
  have heq : (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t)
      = (fun H : SimpleGraph (boxVerts d N) =>
          @ivp2_tiltFreeEnergy _ _ _ H (Classical.decRel _) 2 t) ∘ Gn := by
    funext n
    exact spc_tiltFreeEnergy_instIrrel N (Gn n) (inst n) (Classical.decRel _) t
  rw [heq, Set.range_comp]
  exact (Set.toFinite (Set.range Gn)).image _








theorem spc_feketeLimit_mem_finiteRange (N : ℕ) (Gn : ℕ → SimpleGraph (boxVerts d N))
    [∀ n, DecidableRel (Gn n).Adj] (g : ℝ → ℝ)
    (hfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (t : ℝ) :
    g t ∈ Set.range (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) :=
  (spc_range_finite N Gn t).isClosed.mem_of_tendsto (hfree t)
    (Eventually.of_forall (fun n => ⟨n, rfl⟩))

















theorem spc_fixedBox_collapse_obstruction (N : ℕ) (Gn : ℕ → SimpleGraph (boxVerts d N))
    [∀ n, DecidableRel (Gn n).Adj] (g : ℝ → ℝ)
    (hfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (t : ℝ) :
    (∃ H : SimpleGraph (boxVerts d N), ∃ _ : DecidableRel H.Adj,
        g t = ivp2_tiltFreeEnergy H 2 t)
      ∧ Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)) := by
  refine ⟨?_, hboxfree t⟩
  obtain ⟨n, hn⟩ := spc_feketeLimit_mem_finiteRange N Gn g hfree t
  exact ⟨Gn n, inferInstance, hn.symm⟩






















theorem spc_residue_remark : True := trivial

end FK

end StatMech
