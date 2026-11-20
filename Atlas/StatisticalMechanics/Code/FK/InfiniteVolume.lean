/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoundaryConditions
import Code.FK.RandomCluster
import Code.Foundations.Prokhorov
import Code.Foundations.WeakConvergence

open MeasureTheory
open scoped BigOperators




set_option linter.unusedSectionVars false

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice









variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]




noncomputable def wiredFkWeight (p q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  edgeProduct G p ω * q ^ numClustersWired G bdry ω


theorem wiredFkWeight_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 < wiredFkWeight G bdry p q ω :=
  mul_pos (edgeProduct_pos G hp hp1 ω) (pow_pos hq _)

theorem wiredFkWeight_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 ≤ wiredFkWeight G bdry p q ω :=
  (wiredFkWeight_pos G bdry hp hp1 hq ω).le


noncomputable def wiredFkZ (p q : ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), wiredFkWeight G bdry p q ω

theorem wiredFkZ_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < wiredFkZ G bdry p q :=
  Finset.sum_pos (fun ω _ => wiredFkWeight_pos G bdry hp hp1 hq ω) Finset.univ_nonempty

theorem wiredFkZ_ne_zero {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    wiredFkZ G bdry p q ≠ 0 :=
  (wiredFkZ_pos G bdry hp hp1 hq).ne'


noncomputable def wiredFkProb (p q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  wiredFkWeight G bdry p q ω / wiredFkZ G bdry p q

theorem wiredFkProb_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 ≤ wiredFkProb G bdry p q ω :=
  div_nonneg (wiredFkWeight_nonneg G bdry hp hp1 hq ω) (wiredFkZ_pos G bdry hp hp1 hq).le

theorem wiredFkProb_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ω : ConfigSpace (Sym2 V), wiredFkProb G bdry p q ω = 1 := by
  unfold wiredFkProb
  rw [← Finset.sum_div]
  exact div_self (wiredFkZ_ne_zero G bdry hp hp1 hq)



noncomputable def wiredFkPMF {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (ConfigSpace (Sym2 V)) :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (wiredFkProb G bdry p q ω)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun ω _ => wiredFkProb_nonneg G bdry hp hp1 hq ω,
      wiredFkProb_sum_eq_one G bdry hp hp1 hq]
    simp




abbrev boxVerts (d n : ℕ) : Type := {x : Site d // x ∈ box d n}

noncomputable instance instFintypeBoxVerts (d n : ℕ) : Fintype (boxVerts d n) :=
  (box_finite d n).fintype

instance instDecidableEqBoxVerts (d n : ℕ) : DecidableEq (boxVerts d n) :=
  Subtype.instDecidableEq




def boxGraph (d n : ℕ) : SimpleGraph (boxVerts d n) :=
  SimpleGraph.comap Subtype.val (hypercubicLattice d)

noncomputable instance instDecidableRelBoxGraph (d n : ℕ) :
    DecidableRel (boxGraph d n).Adj :=
  Classical.decRel _





def boxBoundary (d n : ℕ) (x : boxVerts d n) : Prop := (x : Site d) ∈ vertexBoundary d n

noncomputable instance instDecidablePredBoxBoundary (d n : ℕ) :
    DecidablePred (boxBoundary d n) :=
  fun _ => Classical.dec _



def edgeIncl (d n : ℕ) : Sym2 (boxVerts d n) → Sym2 (Site d) :=
  Sym2.map (Subtype.val : boxVerts d n → Site d)

theorem edgeIncl_injective (d n : ℕ) : Function.Injective (edgeIncl d n) :=
  Sym2.map.injective Subtype.val_injective





noncomputable def extendEdge (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    ConfigSpace (Sym2 (Site d)) :=
  fun e => if h : e ∈ Set.range (edgeIncl d n) then ω h.choose else false



theorem measurable_extendEdge (d n : ℕ) : Measurable (extendEdge d n) :=
  Measurable.of_discrete





noncomputable def freeFiniteMeasure (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  ⟨((fkPMF (boxGraph d n) hp hp1 hq).toMeasure).map (extendEdge d n),
    Measure.isProbabilityMeasure_map (measurable_extendEdge d n).aemeasurable⟩





noncomputable def wiredFiniteMeasure (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  ⟨((wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq).toMeasure).map (extendEdge d n),
    Measure.isProbabilityMeasure_map (measurable_extendEdge d n).aemeasurable⟩















noncomputable def freeInfiniteVolume (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  (prokhorov_seq_compact (fun n => freeFiniteMeasure d n hp hp1 hq)).choose







theorem freeInfiniteVolume_isLimit (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
        (freeInfiniteVolume d hp hp1 hq) := by
  obtain ⟨φ, hφ, htends⟩ :=
    (prokhorov_seq_compact (fun n => freeFiniteMeasure d n hp hp1 hq)).choose_spec
  exact ⟨φ, hφ, htends⟩







noncomputable def wiredInfiniteVolume (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  (prokhorov_seq_compact (fun n => wiredFiniteMeasure d n hp hp1 hq)).choose







theorem wiredInfiniteVolume_isLimit (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
        (wiredInfiniteVolume d hp hp1 hq) := by
  obtain ⟨φ, hφ, htends⟩ :=
    (prokhorov_seq_compact (fun n => wiredFiniteMeasure d n hp hp1 hq)).choose_spec
  exact ⟨φ, hφ, htends⟩

end FK

end StatMech
