/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.RotationInvariance

/-!
# Uniqueness of the `q = 2` measure on box events from per-edge free-energy data

Per-edge form of the convex free-energy uniqueness argument for the `q = 2` random-cluster model:
non-edges of the box have density `1/2` and are handled by a linear function, and genuine edges
share one convex free energy.

## i. Overview

A coordinate `e` that is not an edge of the box graph does not affect the FK weight, so under the
free and wired finite-volume measures it is open with probability `1/2`; the same holds in infinite
volume. Such coordinates get the convex function `s ↦ s/2`, whose one-sided derivatives are `1/2`.
Genuine edges get the free energy `G`; by rotation and translation invariance all genuine edges have
the same wired density, so continuity at one edge gives continuity at all. Under the hypotheses that
the free and wired box densities are the left and right derivatives of `G` (derived from the
free-energy limit and density-collapse hypotheses), the free and wired `q = 2` measures agree on
every increasing box event for all but countably many `t`.

## ii. Key results

- `fpe2_edgeMargProb_half_of_toggle_invariant` : a toggle-invariant coordinate has marginal `1/2`.
- `fpe2_free_density_nonEdge`, `fpe2_wired_density_nonEdge` : non-edges have infinite-volume
  density `1/2`.
- `fpe2_fk_uniqueness_of_genuine` : countable-exception uniqueness from per-edge derivative data.

## iii. Table of contents

- A. Coordinates outside the graph
- B. Non-edges of the box
- C. Per-edge free energies
- D. Uniqueness from derivative data
- E. Uniqueness from free-energy limits and density collapse

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 4.63.
-/

@[expose] public section

open Set Filter Topology
open scoped BigOperators
open StatMech.FK

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace StatMech
namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Coordinates outside the graph -/

lemma fpe2_edgeProduct_toggle_invariant {p : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G p (setOpen e ω) = edgeProduct G p (setClosed e ω) := by
  unfold edgeProduct
  apply Finset.prod_congr rfl
  intro e' he'
  have hne : e' ≠ e := fun h => he (h ▸ he')
  rw [setOpen_of_ne hne, setClosed_of_ne hne]

lemma fpe2_fkWeight_toggle_invariant {p q : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p q (setOpen e ω) = fkWeight G p q (setClosed e ω) := by
  unfold fkWeight
  rw [fpe2_edgeProduct_toggle_invariant G he ω,
    numClusters_congr_openSub G (openSub_setOpen_eq_setClosed_of_notMem G he ω)]

lemma fpe2_fkProb_toggle_invariant {p q : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    fkProb G p q (setOpen e ω) = fkProb G p q (setClosed e ω) := by
  unfold fkProb
  rw [fpe2_fkWeight_toggle_invariant G he ω]

lemma fpe2_wiredFkWeight_toggle_invariant (bdry : V → Prop) [DecidablePred bdry]
    {p q : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    wiredFkWeight G bdry p q (setOpen e ω) = wiredFkWeight G bdry p q (setClosed e ω) := by
  unfold wiredFkWeight
  rw [fpe2_edgeProduct_toggle_invariant G he ω]
  congr 1
  unfold StatMech.Lattice.numClustersWired StatMech.Lattice.wiredGraph
  rw [← openSub_eq_openGraph, ← openSub_eq_openGraph,
    openSub_setOpen_eq_setClosed_of_notMem G he ω]

lemma fpe2_wiredFkProb_toggle_invariant (bdry : V → Prop) [DecidablePred bdry]
    {p q : ℝ} {e : Sym2 V} (he : e ∉ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    wiredFkProb G bdry p q (setOpen e ω) = wiredFkProb G bdry p q (setClosed e ω) := by
  unfold wiredFkProb
  rw [fpe2_wiredFkWeight_toggle_invariant G bdry he ω]

lemma fpe2_edgeMargProb_eq_openFiber (μ : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
    edgeMargProb μ e
      = ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ω e = true), μ ω := by
  unfold edgeMargProb
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω e <;> simp [h]

lemma fpe2_edgeMargProb_eq_closedFiber (μ : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
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

lemma fpe2_closedFiber_pairMass_eq_sum (μ : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
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

/-- A coordinate whose toggle preserves a probability mass function is open with probability `1/2`.
-/
lemma fpe2_edgeMargProb_half_of_toggle_invariant
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

/-! ## B. Non-edges of the box -/

lemma fpe2_innerEdgeLE_mk (N m : ℕ) (hNm : N ≤ m) (u v : boxVerts d N) :
    innerEdgeLE d hNm (s(u, v) : Sym2 (boxVerts d N))
      = s(boxVertInclLE d hNm u, boxVertInclLE d hNm v) := by
  unfold innerEdgeLE
  rw [Sym2.map_mk]

lemma fpe2_innerEdgeLE_notMem_edgeFinset (N m : ℕ) (hNm : N ≤ m) (e' : Sym2 (boxVerts d N))
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

lemma fpe2_free_finite_marg_nonEdge (m : ℕ) (e : Sym2 (boxVerts d m))
    (he : e ∉ (boxGraph d m).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    edgeMargProb (fkProb (boxGraph d m) p 2) e = 1 / 2 :=
  fpe2_edgeMargProb_half_of_toggle_invariant (fkProb (boxGraph d m) p 2) e
    (fkProb_sum_eq_one (boxGraph d m) hp hp1 (by norm_num))
    (fun ψ => fpe2_fkProb_toggle_invariant (boxGraph d m) he ψ)

lemma fpe2_wired_finite_marg_nonEdge (m : ℕ) (e : Sym2 (boxVerts d m))
    (he : e ∉ (boxGraph d m).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) e = 1 / 2 :=
  fpe2_edgeMargProb_half_of_toggle_invariant
    (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) e
    (wiredFkProb_sum_eq_one (boxGraph d m) (boxBoundary d m) hp hp1 (by norm_num))
    (fun ψ => fpe2_wiredFkProb_toggle_invariant (boxGraph d m) (boxBoundary d m) he ψ)

lemma fpe2_free_density_nonEdge (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∉ (boxGraph d N).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (edgeIncl d N e') p = 1 / 2 := by
  have hlim := dfi_free_density_eq_limit N e' hp hp1
  have hconst : (fun k => edgeMargProb (fkProb (boxGraph d (N + k)) p 2)
      (innerEdgeLE d (Nat.le_add_right N k) e')) = fun _ => (1 / 2 : ℝ) := by
    funext k
    exact fpe2_free_finite_marg_nonEdge (N + k) _
      (fpe2_innerEdgeLE_notMem_edgeFinset N (N + k) (Nat.le_add_right N k) e' he') hp hp1
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim |>.symm

lemma fpe2_wired_density_nonEdge (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∉ (boxGraph d N).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d N e') p = 1 / 2 := by
  have hlim := dfi_wired_density_eq_limit N e' hp hp1
  have hconst : (fun k => edgeMargProb
      (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
      (innerEdgeLE d (Nat.le_add_right N k) e')) = fun _ => (1 / 2 : ℝ) := by
    funext k
    exact fpe2_wired_finite_marg_nonEdge (N + k) _
      (fpe2_innerEdgeLE_notMem_edgeFinset N (N + k) (Nat.le_add_right N k) e' he') hp hp1
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim |>.symm

/-! ## C. Per-edge free energies -/

lemma fpe2_halfLin_rightDeriv (t : ℝ) :
    pressureRightDeriv (fun s : ℝ => (1/2) * s) t = 1/2 := by
  unfold pressureRightDeriv
  have h1 : HasDerivWithinAt (fun s : ℝ => (1/2) * s) (1/2) (Ioi t) t := by
    simpa using ((hasDerivWithinAt_id t (Ioi t)).const_mul (1/2 : ℝ))
  rw [h1.derivWithin (uniqueDiffWithinAt_Ioi t)]

lemma fpe2_halfLin_leftDeriv (t : ℝ) :
    pressureLeftDeriv (fun s : ℝ => (1/2) * s) t = 1/2 := by
  unfold pressureLeftDeriv
  have h1 : HasDerivWithinAt (fun s : ℝ => (1/2) * s) (1/2) (Iio t) t := by
    simpa using ((hasDerivWithinAt_id t (Iio t)).const_mul (1/2 : ℝ))
  rw [h1.derivWithin (uniqueDiffWithinAt_Iio t)]

lemma fpe2_halfLin_convex : ConvexOn ℝ univ (fun s : ℝ => (1/2) * s) := by
  have : (fun s : ℝ => (1/2) * s) = fun s : ℝ => (1/2 : ℝ) • s := by funext s; rfl
  rw [this]
  exact (convexOn_id convex_univ).smul (by norm_num : (0 : ℝ) ≤ 1/2)

open Classical in
/-- The per-coordinate free energy on `Λ_N`: `G` on edges of the box graph and `s ↦ s/2` on
non-edges.
-/
noncomputable def fpe2_perEdgeG (d N : ℕ) (G : ℝ → ℝ) :
    Sym2 (boxVerts d N) → ℝ → ℝ :=
  fun e' => if e' ∈ (boxGraph d N).edgeFinset then G else (fun s => (1/2) * s)

/-- Every edge of `Λ_N` has free `q = 2` density at `p = logistic(t)` equal to the left derivative
`G'₋(t)`.
-/
def fpe2_GenuineFreeIsLeftDeriv (d N : ℕ) (G : ℝ → ℝ) : Prop :=
  ∀ e' ∈ (boxGraph d N).edgeFinset, ∀ t : ℝ,
    freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureLeftDeriv G t

/-- Every edge of `Λ_N` has wired `q = 2` density at `p = logistic(t)` equal to the right
derivative
`G'₊(t)`.
-/
def fpe2_GenuineWiredIsRightDeriv (d N : ℕ) (G : ℝ → ℝ) : Prop :=
  ∀ e' ∈ (boxGraph d N).edgeFinset, ∀ t : ℝ,
    wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureRightDeriv G t

lemma fpe2_perEdgeG_convex (d N : ℕ) {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (e' : Sym2 (boxVerts d N)) :
    ConvexOn ℝ univ (fpe2_perEdgeG d N G e') := by
  unfold fpe2_perEdgeG
  by_cases he' : e' ∈ (boxGraph d N).edgeFinset
  · rw [ite_eq_left he']; exact hG
  · rw [ite_eq_right he']; exact fpe2_halfLin_convex

lemma fpe2_ha_eq (d N : ℕ) {G : ℝ → ℝ}
    (hfree : fpe2_GenuineFreeIsLeftDeriv d N G)
    (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    edgeMargProb (fuc_freeMass d N t) e' = pressureLeftDeriv (fpe2_perEdgeG d N G e') t := by
  rw [fuc_edgeMargProb_free]
  unfold fpe2_perEdgeG
  by_cases he' : e' ∈ (boxGraph d N).edgeFinset
  · rw [ite_eq_left he']; exact hfree e' he' t
  · rw [ite_eq_right he', fpe2_halfLin_leftDeriv]
    exact fpe2_free_density_nonEdge N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)

lemma fpe2_hb_eq (d N : ℕ) {G : ℝ → ℝ}
    (hwired : fpe2_GenuineWiredIsRightDeriv d N G)
    (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    edgeMargProb (fuc_wiredMass d N t) e' = pressureRightDeriv (fpe2_perEdgeG d N G e') t := by
  rw [fuc_edgeMargProb_wired]
  unfold fpe2_perEdgeG
  by_cases he' : e' ∈ (boxGraph d N).edgeFinset
  · rw [ite_eq_left he']; exact hwired e' he' t
  · rw [ite_eq_right he', fpe2_halfLin_rightDeriv]
    exact fpe2_wired_density_nonEdge N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)

lemma fpe2_wired_genuine_eq_ref (hd : 0 < d) (N : ℕ)
    {eb e' : Sym2 (boxVerts d N)} (he' : e' ∈ (boxGraph d N).edgeFinset)
    (heb : eb ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    edgeMargProb (fuc_wiredMass d N t) e' = edgeMargProb (fuc_wiredMass d N t) eb := by
  rw [fuc_edgeMargProb_wired, fuc_edgeMargProb_wired,
    rot_wired_box_edge_const hd N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t),
    rot_wired_box_edge_const hd N eb heb (fsc_logistic_pos t) (fsc_logistic_lt_one t)]

lemma fpe2_hlink (hd : 0 < d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset) :
    ∀ t : ℝ, ContinuousAt (fun t => edgeMargProb (fuc_wiredMass d N t) eb) t →
      ∀ e' : Sym2 (boxVerts d N),
        ContinuousAt (fun t => edgeMargProb (fuc_wiredMass d N t) e') t := by
  intro t hcont e'
  by_cases he' : e' ∈ (boxGraph d N).edgeFinset
  · have heq : (fun t => edgeMargProb (fuc_wiredMass d N t) e')
        = fun t => edgeMargProb (fuc_wiredMass d N t) eb :=
      funext (fun t => fpe2_wired_genuine_eq_ref hd N he' heb t)
    rw [heq]; exact hcont
  · have heq : (fun t => edgeMargProb (fuc_wiredMass d N t) e') = fun _ => (1/2 : ℝ) := by
      funext t
      rw [fuc_edgeMargProb_wired]
      exact fpe2_wired_density_nonEdge N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)
    rw [heq]; exact continuousAt_const

/-! ## D. Uniqueness from derivative data -/

/-- If the free and wired densities of the edges of `Λ_N` are the left and right derivatives of one
convex `G`, the free and wired `q = 2` measures agree on increasing events of `Λ_N` for all but
countably many `t`.
-/
lemma fpe2_fk_uniqueness_of_genuine (hd : 0 < d) (N : ℕ) (eb : Sym2 (boxVerts d N))
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

/-! ## E. Uniqueness from free-energy limits and density collapse -/

/-- The average free edge density of `Λ_n` converges to the free infinite-volume density of every
edge
of `Λ_N`.
-/
def fpe2_GenuineFreeCollapse (d N : ℕ) : Prop :=
  ∀ e' ∈ (boxGraph d N).edgeFinset, ∀ t : ℝ,
    Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop
      (𝓝 (freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)))

/-- The average wired edge density of `Λ_n` converges to the wired infinite-volume density of every
edge of `Λ_N`.
-/
def fpe2_GenuineWiredCollapse (d N : ℕ) : Prop :=
  ∀ e' ∈ (boxGraph d N).edgeFinset, ∀ t : ℝ,
    Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t) atTop
      (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)))

lemma fpe2_genuineFreeCollapse_of_all (N : ℕ)
    (hcol : ubd_FreeGrowingBoxCollapse (d := d) N) :
    fpe2_GenuineFreeCollapse d N :=
  fun e' _ t => hcol e' t

lemma fpe2_genuineWiredCollapse_of_all (N : ℕ)
    (hcol : wpd_AvgWiredDensityCollapse (d := d) N) :
    fpe2_GenuineWiredCollapse d N :=
  fun e' _ t => hcol e' t

lemma fpe2_genuineFree_target_const (hd : 0 < d) (N : ℕ)
    {e₁ e₂ : Sym2 (boxVerts d N)} (h1 : e₁ ∈ (boxGraph d N).edgeFinset)
    (h2 : e₂ ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    freeEdgeDensity d 2 (edgeIncl d N e₁) (fsc_logistic t)
      = freeEdgeDensity d 2 (edgeIncl d N e₂) (fsc_logistic t) := by
  rw [rot_free_box_edge_const hd N e₁ h1 (fsc_logistic_pos t) (fsc_logistic_lt_one t),
    rot_free_box_edge_const hd N e₂ h2 (fsc_logistic_pos t) (fsc_logistic_lt_one t)]

end FK
end StatMech
