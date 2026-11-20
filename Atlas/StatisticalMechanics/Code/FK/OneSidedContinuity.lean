/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.FK.FKUniqPrimitives
import Code.FK.FKUniquenessClose2
import Code.FK.DensityFiniteToInfinite
import Code.FK.MonotoneVolumeLimit
import Code.FK.ComparisonHolley

open MeasureTheory Set Filter Topology Real SimpleGraph Finset Function
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

variable {d : ℕ}





theorem osc_fsc_logistic_continuous : Continuous fsc_logistic := by
  unfold fsc_logistic
  exact Real.continuous_exp.div (continuous_const.add Real.continuous_exp)
    (fun s => by positivity)



theorem osc_edgeProduct_continuous {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω : ConfigSpace (Sym2 V)) :
    Continuous (fun p : ℝ => edgeProduct G p ω) := by
  unfold edgeProduct
  apply continuous_finsetProd
  intro e _
  by_cases h : ω e
  · simp only [h, if_true]; exact continuous_id
  · simp only [h]; exact continuous_const.sub continuous_id











theorem osc_freeBoxMarg_continuous {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) :
    Continuous (fun s : ℝ => edgeMargProb (fkProb G (fsc_logistic s) 2) e) := by
  have hweight : ∀ ω : ConfigSpace (Sym2 V),
      Continuous (fun s : ℝ => fkWeight G (fsc_logistic s) 2 ω) := by
    intro ω
    unfold fkWeight
    exact ((osc_edgeProduct_continuous G ω).comp osc_fsc_logistic_continuous).mul continuous_const
  have hZ : Continuous (fun s : ℝ => fkZ G (fsc_logistic s) 2) := by
    unfold fkZ
    exact continuous_finsetSum _ (fun ω _ => hweight ω)
  have hZpos : ∀ s : ℝ, 0 < fkZ G (fsc_logistic s) 2 :=
    fun s => fkZ_pos G (fsc_logistic_pos s) (fsc_logistic_lt_one s) (by norm_num)
  have hprob : ∀ ω : ConfigSpace (Sym2 V),
      Continuous (fun s : ℝ => fkProb G (fsc_logistic s) 2 ω) := by
    intro ω
    unfold fkProb
    exact (hweight ω).div hZ (fun s => (hZpos s).ne')
  unfold edgeMargProb
  exact continuous_finsetSum _ (fun ω _ => continuous_const.mul (hprob ω))







theorem osc_wiredBoxMarg_continuous {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (bdry : V → Prop) [DecidablePred bdry]
    (e : Sym2 V) :
    Continuous (fun s : ℝ => edgeMargProb (wiredFkProb G bdry (fsc_logistic s) 2) e) := by
  have hweight : ∀ ω : ConfigSpace (Sym2 V),
      Continuous (fun s : ℝ => wiredFkWeight G bdry (fsc_logistic s) 2 ω) := by
    intro ω
    unfold wiredFkWeight
    exact ((osc_edgeProduct_continuous G ω).comp osc_fsc_logistic_continuous).mul continuous_const
  have hZ : Continuous (fun s : ℝ => wiredFkZ G bdry (fsc_logistic s) 2) := by
    unfold wiredFkZ
    exact continuous_finsetSum _ (fun ω _ => hweight ω)
  have hZpos : ∀ s : ℝ, 0 < wiredFkZ G bdry (fsc_logistic s) 2 :=
    fun s => wiredFkZ_pos G bdry (fsc_logistic_pos s) (fsc_logistic_lt_one s) (by norm_num)
  have hprob : ∀ ω : ConfigSpace (Sym2 V),
      Continuous (fun s : ℝ => wiredFkProb G bdry (fsc_logistic s) 2 ω) := by
    intro ω
    unfold wiredFkProb
    exact (hweight ω).div hZ (fun s => (hZpos s).ne')
  unfold edgeMargProb
  exact continuous_finsetSum _ (fun ω _ => continuous_const.mul (hprob ω))
















theorem osc_fkEdgeMarg_monotone_in_p {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) {p1 p2 : ℝ}
    (hp1 : 0 < p1) (hp1' : p1 < 1) (hp2 : 0 < p2) (hp2' : p2 < 1) (hle : p1 ≤ p2) :
    edgeMargProb (fkProb G p1 2) e ≤ edgeMargProb (fkProb G p2 2) e := by
  
  have hAinc : IsIncreasing {ω : ConfigSpace (Sym2 V) | ω e = true} := by
    intro x y hxy hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have hle' := hxy e; rw [hx] at hle'; exact le_antisymm (by simp) hle'
  
  have hind : ∀ {p : ℝ}, edgeMargProb (fkProb G p 2) e
      = ∑ ω, ({ω : ConfigSpace (Sym2 V) | ω e = true}).indicator (fun _ => (1:ℝ)) ω
          * fkProb G p 2 ω := by
    intro p
    unfold edgeMargProb
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases h : ω e
    · simp [Set.indicator, Set.mem_setOf_eq, h]
    · simp [Set.indicator, Set.mem_setOf_eq, h]
  rw [hind, hind]
  exact holley_dominates (fun ω => fkProb_nonneg G hp1 hp1' (by norm_num) ω)
    (fun ω => fkProb_nonneg G hp2 hp2' (by norm_num) ω)
    (by rw [fkProb_sum_eq_one G hp1 hp1' (by norm_num),
        fkProb_sum_eq_one G hp2 hp2' (by norm_num)])
    (fun a b => fkProb_cross G hp1 hp1' hp2 hp2' hle (by norm_num) a b) hAinc









theorem osc_freeEdgeDensity_q2_monotoneOn (d N : ℕ) (eb : Sym2 (boxVerts d N)) :
    MonotoneOn (freeEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0 : ℝ) 1) := by
  intro p1 hp1mem p2 hp2mem hle
  obtain ⟨hp1, hp1'⟩ := hp1mem
  obtain ⟨hp2, hp2'⟩ := hp2mem
  have htend1 := dfi_free_density_eq_limit N eb hp1 hp1'
  have htend2 := dfi_free_density_eq_limit N eb hp2 hp2'
  have hmono : ∀ k,
      edgeMargProb (fkProb (boxGraph d (N+k)) p1 2) (innerEdgeLE d (Nat.le_add_right N k) eb)
        ≤ edgeMargProb (fkProb (boxGraph d (N+k)) p2 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb) :=
    fun k => osc_fkEdgeMarg_monotone_in_p (boxGraph d (N+k)) _ hp1 hp1' hp2 hp2' hle
  exact le_of_tendsto_of_tendsto htend1 htend2 (Filter.Eventually.of_forall hmono)








theorem osc_freeEdgeDensity_logistic_monotone (d N : ℕ) (eb : Sym2 (boxVerts d N)) :
    Monotone (fun s => freeEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic s)) := by
  intro s1 s2 hs
  exact osc_freeEdgeDensity_q2_monotoneOn d N eb (fsc_logistic_mem_Ioo s1)
    (fsc_logistic_mem_Ioo s2) (fsc_logistic_strictMono.monotone hs)




theorem osc_wiredEdgeDensity_logistic_monotone (d N : ℕ) (eb : Sym2 (boxVerts d N)) :
    Monotone (fun s => wiredEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic s)) := by
  intro s1 s2 hs
  exact wiredEdgeDensity_q2_monotoneOn d N eb (fsc_logistic_mem_Ioo s1)
    (fsc_logistic_mem_Ioo s2) (fsc_logistic_strictMono.monotone hs)

















theorem osc_freeEdgeDensity_left_continuous (d N : ℕ) (eb : Sym2 (boxVerts d N)) (t : ℝ) :
    ContinuousWithinAt
      (fun s => freeEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic s)) (Iio t) t := by
  set F := fun s => freeEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic s) with hF
  have hFmono : Monotone F := osc_freeEdgeDensity_logistic_monotone d N eb
  rw [hFmono.continuousWithinAt_Iio_iff_leftLim_eq]
  
  have hle1 : leftLim F t ≤ F t := hFmono.leftLim_le le_rfl
  
  set G : ℕ → ℝ → ℝ := fun k s =>
    edgeMargProb (fkProb (boxGraph d (N+k)) (fsc_logistic s) 2)
      (innerEdgeLE d (Nat.le_add_right N k) eb) with hG
  
  have hFtend : Tendsto F (𝓝[<] t) (𝓝 (leftLim F t)) := hFmono.tendsto_leftLim t
  
  have hGle : ∀ k, G k t ≤ leftLim F t := by
    intro k
    have hGcont : Continuous (G k) := osc_freeBoxMarg_continuous (boxGraph d (N+k)) _
    have hGtend : Tendsto (G k) (𝓝[<] t) (𝓝 (G k t)) :=
      (hGcont.continuousWithinAt (s := Iio t) (x := t)).tendsto
    
    have hpt : ∀ᶠ s in 𝓝[<] t, G k s ≤ F s := by
      filter_upwards with s
      exact dfi_free_per_edge_le N (N+k) (Nat.le_add_right N k) eb
        (fsc_logistic_pos s) (fsc_logistic_lt_one s)
    exact le_of_tendsto_of_tendsto hGtend hFtend hpt
  
  have hFlim : Tendsto (fun k => G k t) atTop (𝓝 (F t)) :=
    dfi_free_density_eq_limit N eb (fsc_logistic_pos t) (fsc_logistic_lt_one t)
  have hle2 : F t ≤ leftLim F t := le_of_tendsto hFlim (Filter.Eventually.of_forall hGle)
  exact le_antisymm hle1 hle2














theorem osc_wiredEdgeDensity_right_continuous (d N : ℕ) (eb : Sym2 (boxVerts d N)) (t : ℝ) :
    ContinuousWithinAt
      (fun s => wiredEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic s)) (Ioi t) t := by
  set F := fun s => wiredEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic s) with hF
  have hFmono : Monotone F := osc_wiredEdgeDensity_logistic_monotone d N eb
  rw [hFmono.continuousWithinAt_Ioi_iff_rightLim_eq]
  
  have hle1 : F t ≤ rightLim F t := hFmono.le_rightLim le_rfl
  set G : ℕ → ℝ → ℝ := fun k s =>
    edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) (fsc_logistic s) 2)
      (innerEdgeLE d (Nat.le_add_right N k) eb) with hG
  have hFtend : Tendsto F (𝓝[>] t) (𝓝 (rightLim F t)) := hFmono.tendsto_rightLim t
  have hGge : ∀ k, rightLim F t ≤ G k t := by
    intro k
    have hGcont : Continuous (G k) :=
      osc_wiredBoxMarg_continuous (boxGraph d (N+k)) (boxBoundary d (N+k)) _
    have hGtend : Tendsto (G k) (𝓝[>] t) (𝓝 (G k t)) :=
      (hGcont.continuousWithinAt (s := Ioi t) (x := t)).tendsto
    have hpt : ∀ᶠ s in 𝓝[>] t, F s ≤ G k s := by
      filter_upwards with s
      exact dfi_wired_per_edge_ge N (N+k) (Nat.le_add_right N k) eb
        (fsc_logistic_pos s) (fsc_logistic_lt_one s)
    exact le_of_tendsto_of_tendsto hFtend hGtend hpt
  have hFlim : Tendsto (fun k => G k t) atTop (𝓝 (F t)) :=
    dfi_wired_density_eq_limit N eb (fsc_logistic_pos t) (fsc_logistic_lt_one t)
  have hle2 : rightLim F t ≤ F t := ge_of_tendsto hFlim (Filter.Eventually.of_forall hGge)
  exact le_antisymm hle2 hle1

































theorem osc_fk_uniqueness_of_collapse (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hEfree : ∀ n, 0 < (Gn n).edgeFinset.card)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (hwcol : wpd_AvgWiredDensityCollapse (d := d) N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fup_fk_uniqueness_of_collapse hd N eb Gn hEfree hEbox hg hfree hboxfree hcol hwcol
    (fun e' t => osc_freeEdgeDensity_left_continuous d N e' t)
    (fun e' t => osc_wiredEdgeDensity_right_continuous d N e' t)

end FK

end StatMech
