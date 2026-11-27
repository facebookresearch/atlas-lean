/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.StatisticalMechanics.RandomCluster.FKPressureDeriv
import PhyslibExt.StatisticalMechanics.RandomCluster.EdgePartitionFunction
import Mathlib.Data.Sym.Card
import MathlibExt.Combinatorics.SimpleGraph.Lattice.CycleRank

/-!
# Pressure regression and retained finite-graph coverage

A fixed finite carrier cannot be isomorphic to its double and have an edge. In contrast,
a constant sequence on one edge jointly satisfies the retained convex-limit hypotheses.
The existing edge-restricted box convergence theorem is instantiated in dimension one;
this is not convergence of the raw, uncentered partition function.

Densities as one-sided derivatives are required on the edges of the box only: over every pair of
`Λ₁ ⊆ ℤ`, loops included, no function satisfies them, while on its edges the limit of the
centered box free energies does.
-/

open SimpleGraph Filter Topology
open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKPressureDeriv

example {V : Type*} [Fintype V] [DecidableEq V]
    (G : ℕ → SimpleGraph V) [∀ n, DecidableRel (G n).Adj]
    (hjux : ∀ m n, G (m + n) ≃g G m ⊕g G n) :
    ¬ 0 < (G 1).edgeFinset.card := by
  have h := Fintype.card_congr (hjux 1 1).toEquiv
  rw [Fintype.card_sum] at h
  let : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
  have hempty : (G 1).edgeFinset = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro e he
    induction e using Sym2.ind with
    | _ a b => exact isEmptyElim a
  simp [hempty]

private abbrev oneEdge : SimpleGraph (Fin 2) := ⊤
private lemma oneEdge_card : oneEdge.edgeFinset.card = 1 := by decide
private lemma oneEdge_pos : 0 < oneEdge.edgeFinset.card := by rw [oneEdge_card]; decide

example (t : ℝ) : HasDerivAt (ivp2_ambientTiltLogZ oneEdge 2)
    (fpd_avgDensity oneEdge t) t :=
  fpd_ambientTiltLogZ_deriv_eq_avgDensity oneEdge oneEdge_pos t

-- No juxtaposition or growing-edge premise is needed by this retained fixed-carrier API.
example : ConvexOn ℝ Set.univ (ivp2_ambientTiltLogZ oneEdge 2) := by
  have hc := ivp2_ambientTiltLogZ_convexOn oneEdge 2 (by norm_num) oneEdge_pos
  exact (fpd_ambientLogZ_convexDeriv_facts (fun _ : ℕ => oneEdge) (fun _ => hc)
    (ivp2_ambientTiltLogZ oneEdge 2) (fun _ => tendsto_const_nhds)).1

-- The two unused loop coordinates already multiply the raw one-edge partition function by4.
example (p q : ℝ) : fkZ oneEdge p q = 4 * ecz_fkZEdge oneEdge p q := by
  have hNE : ecz_NE oneEdge = 2 := by
    rw [ecz_NE_eq, Sym2.card, oneEdge_card]
    norm_num
  rw [ecz_factorization, hNE]
  norm_num

-- The two unused coordinates contribute an additive offset, not physical edge free energy.
private lemma oneEdge_ambient_offset (q : ℝ) (hq : 0 < q) (t : ℝ) :
    ivp2_ambientTiltLogZ oneEdge q t
      - (Real.log (ecz_fkZEdge oneEdge (fsc_logistic t) q) + Real.log (1 + Real.exp t))
      = 2 * Real.log 2 := by
  have hNE : ecz_NE oneEdge = 2 := by
    rw [ecz_NE_eq, Sym2.card, oneEdge_card]
    norm_num
  have hZ := ecz_fkZEdge_pos oneEdge (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
  simp only [ivp2_ambientTiltLogZ, oneEdge_card, Nat.cast_one, div_one, one_mul]
  rw [ecz_factorization, hNE, Real.log_mul (by norm_num) hZ.ne', Real.log_pow]
  push_cast
  ring

example (q : ℝ) (hq : 0 < q) (t : ℝ) :
    ivp2_ambientTiltLogZ oneEdge q t ≠
      Real.log (ecz_fkZEdge oneEdge (fsc_logistic t) q) + Real.log (1 + Real.exp t) := by
  have hoffset := oneEdge_ambient_offset q hq t
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  intro heq
  rw [heq, sub_self] at hoffset
  linarith

-- Centering cancels exactly that offset.
example (q : ℝ) (hq : 0 < q) (t : ℝ) :
    cfe_centered oneEdge q t =
      (Real.log (ecz_fkZEdge oneEdge (fsc_logistic t) q) + Real.log (1 + Real.exp t))
      - (Real.log (ecz_fkZEdge oneEdge (fsc_logistic 0) q) + Real.log (1 + Real.exp 0)) := by
  unfold cfe_centered
  linarith [oneEdge_ambient_offset q hq t, oneEdge_ambient_offset q hq 0]

-- The raw helper remains totalized at zero edges; this is not a pressure interpretation.
example (q t : ℝ) :
    ivp2_ambientTiltLogZ (⊥ : SimpleGraph (Fin 1)) q t = Real.log (1 + Real.exp t) := by
  simp [ivp2_ambientTiltLogZ]

-- Genuine growing boxes, with all positive-index edge hypotheses discharged together.
example (t : ℝ) : ecz_PerEdgeDensityConverges 1 t :=
  ecz_perEdgeDensityConverges (by norm_num) t
    (fun n hn => ecz_box_edge_pos 1 (by norm_num) hn)

/-! ### The edge-restricted collapse condition in dimension one

The box `Λ_m ⊆ ℤ` is a path, so each of its edges is a bridge of every open subgraph and is open
with probability `p / (p + 2 (1 - p))` under the free `q = 2` measure of every box. The free
infinite-volume density of an edge and the average density of `Λ_N` therefore take this value,
and the constant sequence `Λ_N` satisfies the edge-restricted collapse condition. A loop has free
density `1/2`, so no sequence satisfies the condition over all pairs. -/

section OneDim

/-- Removing an edge of `Λ_m ⊆ ℤ` disconnects its endpoints. -/
private lemma box1_not_reachable (m : ℕ) {u v : boxVerts 1 m} (huv : (boxGraph 1 m).Adj u v) :
    ¬ ((boxGraph 1 m).deleteEdges {s(u, v)}).Reachable u v := by
  have hadj : ∀ a b : boxVerts 1 m, (boxGraph 1 m).Adj a b ↔ (a.1 0 - b.1 0).natAbs = 1 := by
    intro a b
    simp [boxGraph, hypercubicLattice_adj]
  have hext : ∀ a b : boxVerts 1 m, a.1 0 = b.1 0 → a = b := by
    intro a b h
    apply Subtype.ext
    funext i
    rw [Subsingleton.elim i 0]
    exact h
  -- Sites left of the edge `{a, a + 1}` are closed under adjacency once the edge is removed.
  have hleft : ∀ a b : boxVerts 1 m, (boxGraph 1 m).Adj a b → b.1 0 = a.1 0 + 1 →
      ∀ x y, ((boxGraph 1 m).deleteEdges {s(a, b)}).Reachable x y →
        x.1 0 ≤ a.1 0 → y.1 0 ≤ a.1 0 := by
    intro a b _ hab x y ⟨w⟩
    induction w with
    | nil => exact id
    | @cons x z y hxz _ ih =>
      intro hx
      apply ih
      rw [deleteEdges_adj, hadj] at hxz
      by_contra hz
      have hxa : x.1 0 = a.1 0 := by omega
      have hzb : z.1 0 = b.1 0 := by omega
      exact hxz.2 (by rw [hext x a hxa, hext z b hzb]; rfl)
  rcases Int.natAbs_eq_iff.mp ((hadj u v).mp huv) with h | h
  · intro hr
    have := hleft v u huv.symm (by push_cast at h; omega) v u (by
      rw [Sym2.eq_swap]; exact hr.symm) le_rfl
    push_cast at h
    omega
  · intro hr
    have := hleft u v huv (by push_cast at h; omega) u v hr le_rfl
    push_cast at h
    omega

/-- Closing a bridge of `G` adds exactly one cluster. -/
private lemma numClusters_setClosed_bridge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v)
    (hbr : ¬ (G.deleteEdges {s(u, v)}).Reachable u v) (ω : ConfigSpace (Sym2 V)) :
    FK.numClusters G (setClosed s(u, v) ω) = FK.numClusters G (setOpen s(u, v) ω) + 1 := by
  have hsup : openSub G (setOpen s(u, v) ω) = openSub G (setClosed s(u, v) ω) ⊔ edge u v := by
    ext a b
    simp only [openSub_adj, sup_adj, edge_adj]
    by_cases hab : s(a, b) = s(u, v)
    · rw [hab, setOpen_self, setClosed_self]
      have hab' := Sym2.eq_iff.mp hab
      have hne : a ≠ b := by
        rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact G.ne_of_adj huv
        · exact (G.ne_of_adj huv).symm
      have hG : G.Adj a b := by
        rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact huv
        · exact huv.symm
      simp only [and_true, Bool.false_eq_true, and_false, false_or]
      exact ⟨fun _ => ⟨hab', hne⟩, fun _ => hG⟩
    · rw [setOpen_of_ne hab, setClosed_of_ne hab]
      have : ¬ ((a = u ∧ b = v ∨ a = v ∧ b = u) ∧ a ≠ b) := by
        rintro ⟨h | h, _⟩ <;> obtain ⟨rfl, rfl⟩ := h
        · exact hab rfl
        · exact hab Sym2.eq_swap
      simp [this]
  have hnr : ¬ (openSub G (setClosed s(u, v) ω)).Reachable u v := by
    refine fun h => hbr (h.mono fun a b hab => ?_)
    rw [openSub_adj] at hab
    rw [deleteEdges_adj, Set.mem_singleton_iff]
    refine ⟨hab.1, fun he => ?_⟩
    rw [he, setClosed_self] at hab
    exact Bool.false_ne_true hab.2
  have h := card_components_sup_edge_of_not_reachable _ u v hnr
  rw [← hsup] at h
  unfold FK.numClusters
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  omega

/-- At `q = 2`, a bridge of `G` is open with probability `p / (p + 2 (1 - p))`. -/
private lemma edgeMargProb_bridge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v)
    (hbr : ¬ (G.deleteEdges {s(u, v)}).Reachable u v) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    edgeMargProb (fkProb G p 2) s(u, v) = p / (p + 2 * (1 - p)) := by
  have he : s(u, v) ∈ G.edgeFinset := G.mem_edgeFinset.mpr huv
  have hZ := fkZ_pos G hp hp1 (by norm_num : (0 : ℝ) < 2)
  have hden : 0 < p + 2 * (1 - p) := by linarith
  have hpair := fpe2_closedFiber_pairMass_eq_sum (fkProb G p 2) s(u, v)
  rw [fkProb_sum_eq_one G hp hp1 (by norm_num)] at hpair
  rw [fpe2_edgeMargProb_eq_closedFiber, Finset.sum_congr rfl (g := fun ψ =>
      p / (p + 2 * (1 - p)) * (fkProb G p 2 (setOpen s(u, v) ψ)
        + fkProb G p 2 (setClosed s(u, v) ψ))), ← Finset.mul_sum, hpair, mul_one]
  intro ψ _
  unfold fkProb fkWeight
  rw [edgeProduct_setOpen G p he, edgeProduct_setClosed G p he,
    numClusters_setClosed_bridge G huv hbr ψ]
  field_simp
  ring

/-- Every edge of `Λ_m ⊆ ℤ` is open with probability `p / (p + 2 (1 - p))` at `q = 2`. -/
private lemma box1_edgeMargProb (m : ℕ) {e : Sym2 (boxVerts 1 m)}
    (he : e ∈ (boxGraph 1 m).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    edgeMargProb (fkProb (boxGraph 1 m) p 2) e = p / (p + 2 * (1 - p)) := by
  induction e using Sym2.ind with
  | _ u v =>
    have huv : (boxGraph 1 m).Adj u v := (boxGraph 1 m).mem_edgeFinset.mp he
    exact edgeMargProb_bridge _ huv (box1_not_reachable m huv) hp hp1

/-- The free infinite-volume `q = 2` density of an edge of `ℤ` is `p / (p + 2 (1 - p))`. -/
private lemma box1_freeEdgeDensity (N : ℕ) {e' : Sym2 (boxVerts 1 N)}
    (he' : e' ∈ (boxGraph 1 N).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity 1 2 (edgeIncl 1 N e') p = p / (p + 2 * (1 - p)) := by
  have hlim := dfi_free_density_eq_limit N e' hp hp1
  have hconst : (fun k => edgeMargProb (fkProb (boxGraph 1 (N + k)) p 2)
      (innerEdgeLE 1 (Nat.le_add_right N k) e')) = fun _ => p / (p + 2 * (1 - p)) := by
    funext k
    exact box1_edgeMargProb (N + k) (ocs_innerEdgeLE_mem_edgeFinset 1 _ e' he') hp hp1
  rw [hconst] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

/-- In dimension one the constant sequence `Λ_N` satisfies the collapse condition. -/
private lemma box1_avgDensityCollapse (N : ℕ) :
    fpd_AvgDensityCollapse 1 N (fun _ => boxGraph 1 N) := by
  intro e' he' t
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  have hcard : ((boxGraph 1 N).edgeFinset.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨e', he'⟩).ne'
  have havg : fpd_avgDensity (boxGraph 1 N) t = freeEdgeDensity 1 2 (edgeIncl 1 N e')
      (fsc_logistic t) := by
    rw [box1_freeEdgeDensity N he' hp hp1, adc_avgDensity_eq_sum_edgeMarg,
      Finset.sum_congr rfl (fun e he => box1_edgeMargProb N he hp hp1), Finset.sum_const,
      nsmul_eq_mul]
    field_simp
  simp only [havg]
  exact tendsto_const_nhds

/-- **All-pairs obstruction.** At `t = 0`, no sequence of graphs on `Λ₁ ⊆ ℤ` has average densities
converging to the free density of every pair of `Λ₁`: the loop at zero has free density `1/2`,
the edge from zero to one has free density `1/3`. -/
example (Gn : ℕ → SimpleGraph (boxVerts 1 1)) [∀ n, DecidableRel (Gn n).Adj] :
    ¬ ∀ (e' : Sym2 (boxVerts 1 1)) (t : ℝ),
      Tendsto (fun n => fpd_avgDensity (Gn n) t) atTop
        (𝓝 (freeEdgeDensity 1 2 (edgeIncl 1 1 e') (fsc_logistic t))) := by
  intro h
  have hp : (0 : ℝ) < 1 / 2 := by norm_num
  have hp1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hlogistic : fsc_logistic 0 = 1 / 2 := by norm_num [fsc_logistic]
  let z : boxVerts 1 1 := ⟨0, ocs_zero_mem_box 1 1⟩
  have hloop := fpe2_free_density_nonEdge 1 s(z, z) (by simp [SimpleGraph.mem_edgeFinset]) hp hp1
  have hedge := box1_freeEdgeDensity 1 (ocs_unitEdge1_mem_edgeFinset 1 (0, true)) hp hp1
  have heq := tendsto_nhds_unique (h s(z, z) 0) (h (ocs_unitEdge 1 1 le_rfl (0, true)) 0)
  rw [hlogistic, hloop, hedge] at heq
  norm_num at heq

/-- **Non-vacuity.** The box `Λ₁ ⊆ ℤ` has an edge, and the constant sequence `Λ_N` satisfies the
edge-restricted collapse condition. -/
example : (boxGraph 1 1).edgeFinset.Nonempty ∧
    ∀ N, fpd_AvgDensityCollapse 1 N (fun _ => boxGraph 1 N) :=
  ⟨⟨_, ocs_unitEdge1_mem_edgeFinset 1 (0, true)⟩, box1_avgDensityCollapse⟩

/-- The hypotheses of the free bracketing lemma hold together on `Λ₁ ⊆ ℤ`. -/
example (e' : Sym2 (boxVerts 1 1)) (he' : e' ∈ (boxGraph 1 1).edgeFinset) (t : ℝ) :
    pressureLeftDeriv (ivp2_ambientTiltLogZ (boxGraph 1 1) 2) t
        ≤ freeEdgeDensity 1 2 (edgeIncl 1 1 e') (fsc_logistic t)
      ∧ freeEdgeDensity 1 2 (edgeIncl 1 1 e') (fsc_logistic t)
        ≤ pressureRightDeriv (ivp2_ambientTiltLogZ (boxGraph 1 1) 2) t := by
  have hE : 0 < (boxGraph 1 1).edgeFinset.card := Finset.card_pos.mpr ⟨e', he'⟩
  exact fdd_freeDensity_bracket 1 (fun _ => boxGraph 1 1) (fun _ => hE) _
    (ivp2_ambientTiltLogZ_convexOn (boxGraph 1 1) 2 (by norm_num) hE)
    (fun _ => tendsto_const_nhds) (box1_avgDensityCollapse 1) e' he' t

end OneDim

run_cmd do
  if (← Lean.getEnv).contains `StatMech.FK.fpd_exists_convex_ivPressure then
    throwError "Retired fixed-carrier existence wrapper is still present"

run_cmd do
  let env ← Lean.getEnv
  for name in #[`StatMech.FK.ivp2_tiltFreeEnergy, `StatMech.FK.wpd_wiredTiltFreeEnergy,
      `StatMech.FK.bpv_PerVolumeFreeEnergyData] do
    if env.contains name then
      throwError m!"Ambient normalizer still exported as physical free energy: {name}"

/-! ### Edge densities as one-sided derivatives -/

-- The condition is the pair of genuine-edge conditions of `FKUniqPerEdge`.
example (d N : ℕ) (g : ℝ → ℝ) :
    fpd_IVDensityIsOneSidedDeriv d N g ↔
      fpe2_GenuineWiredIsRightDeriv d N g ∧ fpe2_GenuineFreeIsLeftDeriv d N g :=
  Iff.rfl

-- Over every pair of `Λ₁ ⊆ ℤ`, loops included, the free half would be unsatisfiable: at
-- `t = log(1/3)`, so `p = 1/4`, the loop at `0` has free density `1/2`, while the edge `{0, 1}`
-- has free density at most its wired density, which is at most `p`.
example (g : ℝ → ℝ) :
    ¬ ∀ e : Sym2 (boxVerts 1 1),
      freeEdgeDensity 1 2 (edgeIncl 1 1 e) (fsc_logistic (Real.log (1 / 3))) =
        pressureLeftDeriv g (Real.log (1 / 3)) := by
  intro h
  have hp : (0 : ℝ) < 1 / 4 := by norm_num
  have hp1 : (1 / 4 : ℝ) < 1 := by norm_num
  have hlogistic : fsc_logistic (Real.log (1 / 3)) = 1 / 4 := by
    rw [fsc_logistic, Real.exp_log (by norm_num : (0 : ℝ) < 1 / 3)]
    norm_num
  rw [hlogistic] at h
  let z : boxVerts 1 1 := ⟨0, ocs_zero_mem_box 1 1⟩
  have hloop := fpe2_free_density_nonEdge 1 s(z, z) (by simp [SimpleGraph.mem_edgeFinset]) hp hp1
  let e := ocs_unitEdge 1 1 le_rfl (0, true)
  have he : e ∈ (boxGraph 1 1).edgeFinset := ocs_unitEdge1_mem_edgeFinset 1 (0, true)
  have hfinite := dfi_wired_per_edge_ge 1 1 le_rfl e hp hp1
  rw [← ocs_unitEdge_eq_innerEdgeLE 1 1 le_rfl (0, true)] at hfinite
  have hbound : freeEdgeDensity 1 2 (edgeIncl 1 1 e) (1 / 4) ≤ 1 / 4 := by
    refine (freeEdgeDensity_q2_le_wiredEdgeDensity 1 1 e hp hp1).trans (hfinite.trans ?_)
    rw [fuc_edgeMargProb_eq_eventMassProb]
    refine (wiredFkProb_le_fkProbOne_increasing (boxGraph 1 1) (boxBoundary 1 1)
      hp hp1 (by norm_num : (1 : ℝ) ≤ 2) (boxEdgeOpenEvent_isIncreasing 1 1 e)).trans_eq ?_
    simp only [dfi_indicator_boxEdgeOpenEvent]
    simpa using fkProbOne_cylinder (boxGraph 1 1) hp hp1 {e} (Finset.singleton_subset_iff.mpr he)
  rw [h e, ← h s(z, z), hloop] at hbound
  norm_num at hbound

-- On the edges of `Λ₁ ⊆ ℤ`, the limit of the centered box free energies satisfies the condition.
private lemma oneSidedDeriv_witness :
    ∃ g : ℝ → ℝ, ConvexOn ℝ Set.univ g ∧ fpd_IVDensityIsOneSidedDeriv 1 1 g := by
  have hbox (n : ℕ) (hn : 1 ≤ n) : 0 < (boxGraph 1 n).edgeFinset.card :=
    ecz_box_edge_pos 1 le_rfl hn
  obtain ⟨g, hlim, hg, _⟩ := ecz_centeredConvergence le_rfl hbox fun t =>
    ecz_blockOscillation_of_perEdgeDensity t (ecz_perEdgeDensityConverges le_rfl t hbox)
  have hfree := ecz_genuineFreeCollapse_n1 le_rfl 1 hbox
  exact ⟨g, hg, ecz_genuineWiredIsRightDeriv_n1 le_rfl 1 hbox hg hlim hfree
      (ecz_genuineWiredCollapse_n1 le_rfl 1 hbox),
    ecz_genuineFreeIsLeftDeriv_n1 1 hbox hg hlim hfree⟩

-- The box has an edge, so the condition is not vacuous there.
example : (boxGraph 1 1).edgeFinset.Nonempty ∧
    ∃ g : ℝ → ℝ, ConvexOn ℝ Set.univ g ∧ fpd_IVDensityIsOneSidedDeriv 1 1 g :=
  ⟨⟨_, ocs_unitEdge1_mem_edgeFinset 1 (0, true)⟩, oneSidedDeriv_witness⟩

-- Its consequences apply to that witness: the free-energy hypothesis for an edge, and
-- uniqueness off a countable set.
example : fsc_FreeEnergyData 1 1 (ocs_unitEdge 1 1 le_rfl (0, true)) := by
  obtain ⟨g, hg, hres⟩ := oneSidedDeriv_witness
  exact fpd_densityDeriv_imp_fsc 1 1 hg hres _ (ocs_unitEdge1_mem_edgeFinset 1 (0, true))

example (eb : Sym2 (boxVerts 1 1)) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts 1 1))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass 1 1 t) A
          ≠ eventMassProb (fuc_wiredMass 1 1 t) A}.Countable := by
  obtain ⟨g, hg, hres⟩ := oneSidedDeriv_witness
  exact fpd_fk_uniqueness 1 1 eb hg hres

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKPressureDeriv
