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
