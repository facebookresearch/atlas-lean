/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.FK.EdgeMarginal
import Code.FK.FiniteEnergy
import Code.FK.DensityBounds
import Code.FK.InfiniteVolume
import Code.FK.DensityFiniteToInfinite
import Code.FK.WiredDomChain
import Code.FK.FKUniquenessDensity
import Code.FK.FKUniquenessSkeleton
import Code.FK.RotationInvariance
import Code.FK.UniformBulkDeviation
import Code.FK.WiredPressureDeriv
import Code.FK.OneSidedContinuity
import Code.FK.BoxFeketePerVolume
import Code.FK.FKUniqPrimitives

open Set Filter Topology
open scoped BigOperators
open StatMech.FK

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false

namespace StatMech
namespace FK










variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fpe2_edgeProduct_toggle_invariant {p : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G p (setOpen e ω) = edgeProduct G p (setClosed e ω) := by
  unfold edgeProduct
  apply Finset.prod_congr rfl
  intro e' he'
  have hne : e' ≠ e := fun h => he (h ▸ he')
  rw [setOpen_of_ne hne, setClosed_of_ne hne]


theorem fpe2_fkWeight_toggle_invariant {p q : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p q (setOpen e ω) = fkWeight G p q (setClosed e ω) := by
  unfold fkWeight
  rw [fpe2_edgeProduct_toggle_invariant G he ω,
    numClusters_congr_openSub G (openSub_setOpen_eq_setClosed_of_notMem G he ω)]


theorem fpe2_fkProb_toggle_invariant {p q : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    fkProb G p q (setOpen e ω) = fkProb G p q (setClosed e ω) := by
  unfold fkProb
  rw [fpe2_fkWeight_toggle_invariant G he ω]


theorem fpe2_wiredFkWeight_toggle_invariant (bdry : V → Prop) [DecidablePred bdry]
    {p q : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    wiredFkWeight G bdry p q (setOpen e ω) = wiredFkWeight G bdry p q (setClosed e ω) := by
  unfold wiredFkWeight
  rw [fpe2_edgeProduct_toggle_invariant G he ω]
  congr 1
  unfold StatMech.Lattice.numClustersWired StatMech.Lattice.wiredGraph
  rw [← openSub_eq_openGraph, ← openSub_eq_openGraph,
    openSub_setOpen_eq_setClosed_of_notMem G he ω]


theorem fpe2_wiredFkProb_toggle_invariant (bdry : V → Prop) [DecidablePred bdry]
    {p q : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    wiredFkProb G bdry p q (setOpen e ω) = wiredFkProb G bdry p q (setClosed e ω) := by
  unfold wiredFkProb
  rw [fpe2_wiredFkWeight_toggle_invariant G bdry he ω]









theorem fpe2_edgeMargProb_eq_openFiber (μ : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
    edgeMargProb μ e
      = ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ω e = true), μ ω := by
  unfold edgeMargProb
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω e <;> simp [h]


theorem fpe2_edgeMargProb_eq_closedFiber (μ : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
    edgeMargProb μ e
      = ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false),
          μ (setOpen e ψ) := by
  rw [fpe2_edgeMargProb_eq_openFiber]
  apply Finset.sum_nbij' (fun ω => setClosed e ω) (fun ψ => setOpen e ψ)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    simp [setClosed]
  · intro ψ hψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢
    simp [setOpen]
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    funext x; by_cases hx : x = e
    · subst hx; simp [hω]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]
  · intro ψ hψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ
    funext x; by_cases hx : x = e
    · subst hx; simp [hψ]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    congr 1
    funext x; by_cases hx : x = e
    · subst hx; simp [hω]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]


theorem fpe2_closedFiber_pairMass_eq_sum (μ : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
    ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false),
        (μ (setOpen e ψ) + μ (setClosed e ψ)) = ∑ ω, μ ω := by
  rw [Finset.sum_add_distrib]
  rw [← fpe2_edgeMargProb_eq_closedFiber μ e]
  rw [fpe2_edgeMargProb_eq_openFiber μ e]
  have hclosed : (∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false),
        μ (setClosed e ψ))
      = ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ω e = false), μ ω := by
    apply Finset.sum_congr rfl
    intro ψ hψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ
    congr 1
    funext x; by_cases hx : x = e
    · subst hx; simp [hψ]
    · simp [setClosed_of_ne hx]
  rw [hclosed]
  have hne : (Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ω e = false))
      = Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ¬ ω e = true) := by
    ext ω; simp
  rw [hne, Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun ω : ConfigSpace (Sym2 V) => ω e = true) μ]





theorem fpe2_edgeMargProb_half_of_toggle_invariant
    (μ : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V)
    (hsum : ∑ ω, μ ω = 1)
    (hinv : ∀ ψ : ConfigSpace (Sym2 V), μ (setOpen e ψ) = μ (setClosed e ψ)) :
    edgeMargProb μ e = 1 / 2 := by
  have hpair := fpe2_closedFiber_pairMass_eq_sum μ e
  rw [hsum] at hpair
  have h2 : ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false),
        (μ (setOpen e ψ) + μ (setClosed e ψ))
      = 2 * edgeMargProb μ e := by
    rw [fpe2_edgeMargProb_eq_closedFiber μ e, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ψ _
    rw [← hinv ψ]; ring
  rw [h2] at hpair
  linarith










open StatMech.Lattice

variable {d : ℕ}


theorem fpe2_innerEdgeLE_mk (N m : ℕ) (hNm : N ≤ m) (u v : boxVerts d N) :
    innerEdgeLE d hNm (s(u, v) : Sym2 (boxVerts d N))
      = s(boxVertInclLE d hNm u, boxVertInclLE d hNm v) := by
  unfold innerEdgeLE
  rw [Sym2.map_mk]




theorem fpe2_innerEdgeLE_notMem_edgeFinset (N m : ℕ) (hNm : N ≤ m) (e' : Sym2 (boxVerts d N))
    (he' : e' ∉ (boxGraph d N).edgeFinset) :
    innerEdgeLE d hNm e' ∉ (boxGraph d m).edgeFinset := by
  induction e' with
  | h u v =>
    rw [fpe2_innerEdgeLE_mk N m hNm u v]
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he' ⊢
    intro hadj
    apply he'
    rw [boxGraph, SimpleGraph.comap_adj] at hadj ⊢
    simpa [boxVertInclLE] using hadj


theorem fpe2_free_finite_marg_nonEdge (m : ℕ) (e : Sym2 (boxVerts d m))
    (he : e ∉ (boxGraph d m).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    edgeMargProb (fkProb (boxGraph d m) p 2) e = 1 / 2 :=
  fpe2_edgeMargProb_half_of_toggle_invariant (fkProb (boxGraph d m) p 2) e
    (fkProb_sum_eq_one (boxGraph d m) hp hp1 (by norm_num))
    (fun ψ => fpe2_fkProb_toggle_invariant (boxGraph d m) he ψ)


theorem fpe2_wired_finite_marg_nonEdge (m : ℕ) (e : Sym2 (boxVerts d m))
    (he : e ∉ (boxGraph d m).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) e = 1 / 2 :=
  fpe2_edgeMargProb_half_of_toggle_invariant
    (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) e
    (wiredFkProb_sum_eq_one (boxGraph d m) (boxBoundary d m) hp hp1 (by norm_num))
    (fun ψ => fpe2_wiredFkProb_toggle_invariant (boxGraph d m) (boxBoundary d m) he ψ)


theorem fpe2_free_density_nonEdge (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∉ (boxGraph d N).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (edgeIncl d N e') p = 1 / 2 := by
  have hlim := dfi_free_density_eq_limit N e' hp hp1
  have hconst : (fun k => edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
      (innerEdgeLE d (Nat.le_add_right N k) e')) = fun _ => (1 / 2 : ℝ) := by
    funext k
    exact fpe2_free_finite_marg_nonEdge (N+k) _
      (fpe2_innerEdgeLE_notMem_edgeFinset N (N+k) (Nat.le_add_right N k) e' he') hp hp1
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim |>.symm


theorem fpe2_wired_density_nonEdge (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∉ (boxGraph d N).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d N e') p = 1 / 2 := by
  have hlim := dfi_wired_density_eq_limit N e' hp hp1
  have hconst : (fun k => edgeMargProb
      (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
      (innerEdgeLE d (Nat.le_add_right N k) e')) = fun _ => (1 / 2 : ℝ) := by
    funext k
    exact fpe2_wired_finite_marg_nonEdge (N+k) _
      (fpe2_innerEdgeLE_notMem_edgeFinset N (N+k) (Nat.le_add_right N k) e' he') hp hp1
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim |>.symm







theorem fpe2_halfLin_rightDeriv (t : ℝ) :
    pressureRightDeriv (fun s : ℝ => (1/2) * s) t = 1/2 := by
  unfold pressureRightDeriv
  have h1 : HasDerivWithinAt (fun s : ℝ => (1/2) * s) (1/2) (Ioi t) t := by
    simpa using ((hasDerivWithinAt_id t (Ioi t)).const_mul (1/2 : ℝ))
  rw [h1.derivWithin (uniqueDiffWithinAt_Ioi t)]


theorem fpe2_halfLin_leftDeriv (t : ℝ) :
    pressureLeftDeriv (fun s : ℝ => (1/2) * s) t = 1/2 := by
  unfold pressureLeftDeriv
  have h1 : HasDerivWithinAt (fun s : ℝ => (1/2) * s) (1/2) (Iio t) t := by
    simpa using ((hasDerivWithinAt_id t (Iio t)).const_mul (1/2 : ℝ))
  rw [h1.derivWithin (uniqueDiffWithinAt_Iio t)]


theorem fpe2_halfLin_convex : ConvexOn ℝ univ (fun s : ℝ => (1/2) * s) := by
  have : (fun s : ℝ => (1/2) * s) = fun s : ℝ => (1/2 : ℝ) • s := by funext s; rfl
  rw [this]
  exact (convexOn_id convex_univ).smul (by norm_num : (0:ℝ) ≤ 1/2)








open Classical in



noncomputable def fpe2_perEdgeG (d N : ℕ) (G : ℝ → ℝ) :
    Sym2 (boxVerts d N) → ℝ → ℝ :=
  fun e' => if e' ∈ (boxGraph d N).edgeFinset then G else (fun s => (1/2) * s)


def fpe2_GenuineFreeIsLeftDeriv (d N : ℕ) (G : ℝ → ℝ) : Prop :=
  ∀ e' ∈ (boxGraph d N).edgeFinset, ∀ t : ℝ,
    freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureLeftDeriv G t


def fpe2_GenuineWiredIsRightDeriv (d N : ℕ) (G : ℝ → ℝ) : Prop :=
  ∀ e' ∈ (boxGraph d N).edgeFinset, ∀ t : ℝ,
    wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureRightDeriv G t


theorem fpe2_perEdgeG_convex (d N : ℕ) {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (e' : Sym2 (boxVerts d N)) :
    ConvexOn ℝ univ (fpe2_perEdgeG d N G e') := by
  unfold fpe2_perEdgeG
  by_cases he' : e' ∈ (boxGraph d N).edgeFinset
  · rw [if_pos he']; exact hG
  · rw [if_neg he']; exact fpe2_halfLin_convex


theorem fpe2_ha_eq (d N : ℕ) {G : ℝ → ℝ}
    (hfree : fpe2_GenuineFreeIsLeftDeriv d N G)
    (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    edgeMargProb (fuc_freeMass d N t) e' = pressureLeftDeriv (fpe2_perEdgeG d N G e') t := by
  rw [fuc_edgeMargProb_free]
  unfold fpe2_perEdgeG
  by_cases he' : e' ∈ (boxGraph d N).edgeFinset
  · rw [if_pos he']; exact hfree e' he' t
  · rw [if_neg he', fpe2_halfLin_leftDeriv]
    exact fpe2_free_density_nonEdge N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)


theorem fpe2_hb_eq (d N : ℕ) {G : ℝ → ℝ}
    (hwired : fpe2_GenuineWiredIsRightDeriv d N G)
    (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    edgeMargProb (fuc_wiredMass d N t) e' = pressureRightDeriv (fpe2_perEdgeG d N G e') t := by
  rw [fuc_edgeMargProb_wired]
  unfold fpe2_perEdgeG
  by_cases he' : e' ∈ (boxGraph d N).edgeFinset
  · rw [if_pos he']; exact hwired e' he' t
  · rw [if_neg he', fpe2_halfLin_rightDeriv]
    exact fpe2_wired_density_nonEdge N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)



theorem fpe2_wired_genuine_eq_ref (hd : 0 < d) (N : ℕ)
    {eb e' : Sym2 (boxVerts d N)} (he' : e' ∈ (boxGraph d N).edgeFinset)
    (heb : eb ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    edgeMargProb (fuc_wiredMass d N t) e' = edgeMargProb (fuc_wiredMass d N t) eb := by
  rw [fuc_edgeMargProb_wired, fuc_edgeMargProb_wired,
    rot_wired_box_edge_const hd N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t),
    rot_wired_box_edge_const hd N eb heb (fsc_logistic_pos t) (fsc_logistic_lt_one t)]





theorem fpe2_hlink (hd : 0 < d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset) :
    ∀ t : ℝ, ContinuousAt (fun t => edgeMargProb (fuc_wiredMass d N t) eb) t →
      ∀ e' : Sym2 (boxVerts d N),
        ContinuousAt (fun t => edgeMargProb (fuc_wiredMass d N t) e') t := by
  intro t hcont e'
  by_cases he' : e' ∈ (boxGraph d N).edgeFinset
  · 
    have heq : (fun t => edgeMargProb (fuc_wiredMass d N t) e')
        = fun t => edgeMargProb (fuc_wiredMass d N t) eb :=
      funext (fun t => fpe2_wired_genuine_eq_ref hd N he' heb t)
    rw [heq]; exact hcont
  · 
    have heq : (fun t => edgeMargProb (fuc_wiredMass d N t) e') = fun _ => (1/2 : ℝ) := by
      funext t
      rw [fuc_edgeMargProb_wired]
      exact fpe2_wired_density_nonEdge N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)
    rw [heq]; exact continuousAt_const




















theorem fpe2_fk_uniqueness_of_genuine (hd : 0 < d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset) {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hfree : fpe2_GenuineFreeIsLeftDeriv d N G)
    (hwired : fpe2_GenuineWiredIsRightDeriv d N G) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  choose P hP using fuc_hcoup d N
  exact fud_countable_phi_ne_of_convexPerEdge
    (fun t => fuc_freeMass d N t) (fun t => fuc_wiredMass d N t) eb P hP
    (fuc_hmono d N eb)
    (fpe2_perEdgeG d N G) (fpe2_perEdgeG_convex d N hG)
    (fpe2_ha_eq d N hfree) (fpe2_hb_eq d N hwired)
    (fpe2_hlink hd N eb heb)














def fpe2_GenuineFreeCollapse (d N : ℕ) : Prop :=
  ∀ e' ∈ (boxGraph d N).edgeFinset, ∀ t : ℝ,
    Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop
      (𝓝 (freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)))


def fpe2_GenuineWiredCollapse (d N : ℕ) : Prop :=
  ∀ e' ∈ (boxGraph d N).edgeFinset, ∀ t : ℝ,
    Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t) atTop
      (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)))


theorem fpe2_genuineFreeIsLeftDeriv (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpe2_GenuineFreeCollapse d N) :
    fpe2_GenuineFreeIsLeftDeriv d N g := by
  intro e' he' t
  
  have hbL : ∀ s, pressureLeftDeriv g s
      ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s) := by
    intro s
    exact fdd_leftDeriv_le_avgLimit
      (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2) g
      (fun n => fpd_avgDensity (boxGraph d n))
      (fun n => ivp2_tiltFreeEnergy_convexOn (boxGraph d n) 2 (by norm_num) (hEbox n))
      (fun n u => fpd_tiltFreeEnergy_deriv_eq_avgDensity (boxGraph d n) (hEbox n) u)
      hboxfree s _ hg (hcol e' he' s)
  have hbR : ∀ s, freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)
      ≤ pressureRightDeriv g s := by
    intro s
    exact fdd_avgLimit_le_rightDeriv
      (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2) g
      (fun n => fpd_avgDensity (boxGraph d n))
      (fun n => ivp2_tiltFreeEnergy_convexOn (boxGraph d n) 2 (by norm_num) (hEbox n))
      (fun n u => fpd_tiltFreeEnergy_deriv_eq_avgDensity (boxGraph d n) (hEbox n) u)
      hboxfree s _ hg (hcol e' he' s)
  exact fdd_eq_leftDeriv_of_bracket_leftContinuous hg hbL hbR
    (osc_freeEdgeDensity_left_continuous d N e' t)




theorem fpe2_genuineWiredIsRightDeriv (hd : 1 ≤ d) (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hcolfree : fpe2_GenuineFreeCollapse d N)
    (hcolwired : fpe2_GenuineWiredCollapse d N) :
    fpe2_GenuineWiredIsRightDeriv d N g := by
  
  have hsv := fup_surfaceVolume_tendsto_zero d hd
  have hwiredlim : ∀ t,
      Tendsto (fun n => wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 t)
        atTop (𝓝 (g t)) :=
    fun t => wpd_wiredTiltFreeEnergy_tendsto 2 (by norm_num) hEbox g t (hboxfree t) hsv
  intro e' he' t
  
  have hbL : ∀ s, pressureLeftDeriv g s
      ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s) := by
    intro s
    refine (?_ : pressureLeftDeriv g s
        ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)).trans
      (freeEdgeDensity_q2_le_wiredEdgeDensity d N e' (fsc_logistic_pos s) (fsc_logistic_lt_one s))
    exact fdd_leftDeriv_le_avgLimit
      (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2) g
      (fun n => fpd_avgDensity (boxGraph d n))
      (fun n => ivp2_tiltFreeEnergy_convexOn (boxGraph d n) 2 (by norm_num) (hEbox n))
      (fun n u => fpd_tiltFreeEnergy_deriv_eq_avgDensity (boxGraph d n) (hEbox n) u)
      hboxfree s _ hg (hcolfree e' he' s)
  
  have hbR : ∀ s, wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)
      ≤ pressureRightDeriv g s := by
    intro s
    exact wpd_wiredAvgDensity_le_rightDeriv 2 (by norm_num) hEbox g hg hwiredlim s _
      (hcolwired e' he' s)
  exact fdd_eq_rightDeriv_of_bracket_rightContinuous hg hbL hbR
    (osc_wiredEdgeDensity_right_continuous d N e' t)









theorem fpe2_fk_uniqueness_of_boxFekete (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hcolfree : fpe2_GenuineFreeCollapse d N)
    (hcolwired : fpe2_GenuineWiredCollapse d N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fpe2_fk_uniqueness_of_genuine (lt_of_lt_of_le one_pos hd) N eb heb hg
    (fpe2_genuineFreeIsLeftDeriv N hEbox hg hboxfree hcolfree)
    (fpe2_genuineWiredIsRightDeriv hd N hEbox hg hboxfree hcolfree hcolwired)




















theorem fpe2_fk_uniqueness_of_perVolume (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hdata : ∀ t, bpv_PerVolumeFreeEnergyData d t)
    (hcolfree : fpe2_GenuineFreeCollapse d N)
    (hcolwired : fpe2_GenuineWiredCollapse d N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  obtain ⟨G, hboxfree, hG⟩ := bpv_exists_convex_ivPressure_of_perVolume hEbox hdata
  exact fpe2_fk_uniqueness_of_genuine (lt_of_lt_of_le one_pos hd) N eb heb hG
    (fpe2_genuineFreeIsLeftDeriv N hEbox hG hboxfree hcolfree)
    (fpe2_genuineWiredIsRightDeriv hd N hEbox hG hboxfree hcolfree hcolwired)















theorem fpe2_genuineFreeCollapse_of_all (N : ℕ)
    (hcol : ubd_FreeGrowingBoxCollapse (d := d) N) :
    fpe2_GenuineFreeCollapse d N :=
  fun e' _ t => hcol e' t


theorem fpe2_genuineWiredCollapse_of_all (N : ℕ)
    (hcol : wpd_AvgWiredDensityCollapse (d := d) N) :
    fpe2_GenuineWiredCollapse d N :=
  fun e' _ t => hcol e' t





theorem fpe2_genuineFree_target_const (hd : 0 < d) (N : ℕ)
    {e₁ e₂ : Sym2 (boxVerts d N)} (h1 : e₁ ∈ (boxGraph d N).edgeFinset)
    (h2 : e₂ ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    freeEdgeDensity d 2 (edgeIncl d N e₁) (fsc_logistic t)
      = freeEdgeDensity d 2 (edgeIncl d N e₂) (fsc_logistic t) := by
  rw [rot_free_box_edge_const hd N e₁ h1 (fsc_logistic_pos t) (fsc_logistic_lt_one t),
    rot_free_box_edge_const hd N e₂ h2 (fsc_logistic_pos t) (fsc_logistic_lt_one t)]

end FK
end StatMech
