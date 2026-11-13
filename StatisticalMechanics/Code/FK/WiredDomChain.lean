/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Mathlib
import Code.FK.InducedBC
import Code.FK.WiredBoxLimit
import Code.FK.BoxTailLimit
import Code.FK.IvProperties
import Code.FK.TailLimit
import Code.IsingFK.MagPercoIdBox
import Code.Foundations.MonotoneLimit
import Code.Percolation.SubcriticalDecay

open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}













noncomputable def outProj (d n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    ConfigSpace (Sym2 (boxVerts d (n+1))) :=
  psiExt d n ρ (fun _ => false)

theorem outProj_eq_false_of_range (n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {e : Sym2 (boxVerts d (n+1))} (he : e ∈ Set.range (innerEdge d n)) :
    outProj d n ρ e = false := by
  obtain ⟨e', rfl⟩ := he
  unfold outProj
  rw [psiExt_innerEdge]

theorem outProj_eq_of_not_range (n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {e : Sym2 (boxVerts d (n+1))} (he : e ∉ Set.range (innerEdge d n)) :
    outProj d n ρ e = ρ e := by
  unfold outProj
  rw [psiExt_eq_psi_of_not_range _ _ _ _ he]



theorem agreesOff_outProj (n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    AgreesOff (innerEdgeFinset d n) (outProj d n ρ) ρ := by
  intro e he
  rw [mem_innerEdgeFinset] at he
  exact (outProj_eq_of_not_range n ρ he).symm


theorem outProj_idem (n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    outProj d n (outProj d n ρ) = outProj d n ρ := by
  funext e
  by_cases hin : e ∈ Set.range (innerEdge d n)
  · rw [outProj_eq_false_of_range n _ hin, outProj_eq_false_of_range n ρ hin]
  · rw [outProj_eq_of_not_range n _ hin]





theorem filter_outProj_eq_condFibre (n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (hψ : outProj d n ψ = ψ) :
    Finset.univ.filter (fun ρ => outProj d n ρ = ψ)
      = condFibre (innerEdgeFinset d n) ψ := by
  ext ρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_condFibre]
  refine ⟨fun h e he => by
    rw [mem_innerEdgeFinset] at he
    rw [← outProj_eq_of_not_range n ρ he, h], ?_⟩
  intro h
  have hpr : outProj d n ρ = outProj d n ψ := by
    funext e
    by_cases hin : e ∈ Set.range (innerEdge d n)
    · rw [outProj_eq_false_of_range n ρ hin, outProj_eq_false_of_range n ψ hin]
    · have he : e ∉ innerEdgeFinset d n := by rw [mem_innerEdgeFinset]; exact hin
      rw [outProj_eq_of_not_range n ρ hin, outProj_eq_of_not_range n ψ hin, h e he]
  rw [hpr, hψ]








theorem condFibre_congr_dom {V : Type*} [Fintype V] [DecidableEq V]
    {F : Finset (Sym2 V)} {ψ ψ' : ConfigSpace (Sym2 V)} (h : AgreesOff F ψ ψ') :
    condFibre F ψ = condFibre F ψ' := by
  ext σ
  rw [mem_condFibre, mem_condFibre, agreesOff_congr h]




theorem condBcProb_congr_dom {V : Type*} [Fintype V] [DecidableEq V] (G C : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel C.Adj]
    (p q : ℝ) (F : Finset (Sym2 V)) (ψ ψ' ω : ConfigSpace (Sym2 V)) (h : AgreesOff F ψ ψ') :
    condBcProb G C p q F ψ ω = condBcProb G C p q F ψ' ω := by
  have hcond : AgreesOff F ψ ω ↔ AgreesOff F ψ' ω := by rw [agreesOff_congr h]
  have hfibre : condFibre F ψ = condFibre F ψ' := condFibre_congr_dom h
  unfold condBcProb inducedBcZ
  rw [hfibre]
  by_cases hω : AgreesOff F ψ ω
  · rw [if_pos hω, if_pos (hcond.mp hω)]
  · rw [if_neg hω, if_neg (fun h' => hω (hcond.mpr h'))]






theorem sum_fibreMass_eq_one (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
        (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
          bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q σ) = 1 := by
  classical
  set C := boundaryCliqueGraph (boxBoundary d (n+1))
  set F := innerEdgeFinset d n
  set G := boxGraph d (n+1)
  rw [show (∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
        (∑ σ ∈ condFibre F ψ, bcProb G C p q σ))
      = ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
        (∑ σ ∈ Finset.univ.filter (fun ρ => outProj d n ρ = ψ), bcProb G C p q σ) from ?_]
  · rw [Finset.sum_fiberwise_of_maps_to
        (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, outProj_idem n ρ⟩)]
    exact bcProb_sum_eq_one G C hp hp1 hq
  · apply Finset.sum_congr rfl
    intro ψ hψ
    rw [Finset.mem_filter] at hψ
    rw [filter_outProj_eq_condFibre n ψ hψ.2]















theorem wiredSucc_bcProb_decompose (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (B : Set (ConfigSpace (Sym2 (boxVerts d (n+1))))) :
    (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ
        * bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q ρ)
      = ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
          (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
            bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q σ)
          * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ
              * condBcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q
                  (innerEdgeFinset d n) ψ ρ) := by
  classical
  set C := boundaryCliqueGraph (boxBoundary d (n+1))
  set F := innerEdgeFinset d n
  set G := boxGraph d (n+1)
  rw [← Finset.sum_fiberwise_of_maps_to
      (g := outProj d n) (t := Finset.univ.filter (fun ψ => outProj d n ψ = ψ))
      (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, outProj_idem n ρ⟩)]
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [Finset.mem_filter] at hψ
  rw [filter_outProj_eq_condFibre n ψ hψ.2]
  
  have hRHS : (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = ∑ ρ ∈ condFibre F ψ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro ρ _ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb
    rw [if_neg hρ, mul_zero]
  rw [hRHS, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mem_condFibre] at hρ
  have hbc := bcProb_eq_fibreMass_mul_condBcProb G C hp hp1 hq F ρ
  have hfib : condFibre F ρ = condFibre F ψ := by
    ext σ
    rw [mem_condFibre, mem_condFibre, agreesOff_congr (agreesOff_symm hρ)]
  rw [hfib] at hbc
  have hcc : condBcProb G C p q F ρ ρ = condBcProb G C p q F ψ ρ :=
    condBcProb_congr_dom G C p q F ρ ψ ρ (agreesOff_symm hρ)
  rw [hcc] at hbc
  rw [hbc]
  ring
















theorem condBcProb_innerRestrict_le (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA₀ : IsIncreasing A₀) :
    (∑ ρ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ
        * condBcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q
            (innerEdgeFinset d n) ψ ρ)
      ≤ ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  rw [condBcProb_psiExt_sum_eq_inducedBox d n hp hp1 hq0 ψ (innerRestrict d n ⁻¹' A₀)]
  have hpre : psiExt d n ψ ⁻¹' (innerRestrict d n ⁻¹' A₀) = A₀ := by
    ext ω
    simp only [Set.mem_preimage, innerRestrict_psiExt]
  rw [hpre]
  exact condBcProb_psiExt_dominated_wired d n ψ hp hp1 hq hA₀















theorem wiredSucc_bcProb_innerEvent_le (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA₀ : IsIncreasing A₀) :
    (∑ ρ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ
        * bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q ρ)
      ≤ ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  set c := ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω
      * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω with hc
  rw [wiredSucc_bcProb_decompose n hp hp1 hq0 (innerRestrict d n ⁻¹' A₀)]
  calc ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
          (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
            bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q σ)
          * (∑ ρ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ
              * condBcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q
                  (innerEdgeFinset d n) ψ ρ)
        ≤ ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
            (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
              bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q σ) * c := by
            apply Finset.sum_le_sum
            intro ψ _
            apply mul_le_mul_of_nonneg_left (condBcProb_innerRestrict_le n hp hp1 hq ψ hA₀)
            exact Finset.sum_nonneg (fun σ _ =>
              bcProb_nonneg (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) hp hp1 hq0 σ)
    _ = (∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
            (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
              bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q σ)) * c := by
            rw [Finset.sum_mul]
    _ = c := by rw [sum_fibreMass_eq_one n hp hp1 hq0, one_mul]











theorem wiredFiniteMeasure_succ_real_innerRestrictEvent (n : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (S : Set (ConfigSpace (Sym2 (boxVerts d n))))
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S)
      = ∑ ρ : ConfigSpace (Sym2 (boxVerts d (n+1))),
          (innerRestrict d n ⁻¹' S).indicator (fun _ => (1:ℝ)) ρ
            * bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p 2 ρ := by
  have hw : (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
        (boxRestrict d n ⁻¹' S)
      = ((wiredFkPMF (boxGraph d (n+1)) (boxBoundary d (n+1)) hp hp1
            (by norm_num : (0:ℝ) < 2)).toMeasure
          (extendEdge d (n+1) ⁻¹' (boxRestrict d n ⁻¹' S))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d (n+1)) hmeas]
  have hpre : extendEdge d (n+1) ⁻¹' (boxRestrict d n ⁻¹' S) = innerRestrict d n ⁻¹' S := by
    ext ρ
    simp only [Set.mem_preimage, boxRestrict_extendEdge_succ]
  rw [hw, hpre, wiredFkPMF_toMeasure_toReal d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2)]
  exact Finset.sum_congr rfl (fun ρ _ => by rw [bcProb_clique_eq_wiredFkProb])













theorem wiredFiniteMeasure_succ_le_smallerBox (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hS : IsIncreasing S)
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S)
      ≤ ∑ ω, S.indicator (fun _ => (1:ℝ)) ω
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
  rw [wiredFiniteMeasure_succ_real_innerRestrictEvent n hp hp1 S hmeas]
  exact wiredSucc_bcProb_innerEvent_le n hp hp1 (by norm_num) hS











theorem isIncreasing_connToBdryEvent (n : ℕ) :
    IsIncreasing {ω : ConfigSpace (Sym2 (boxVerts d n)) |
      ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)} := by
  intro a b hab ha
  simp only [Set.mem_setOf_eq] at ha ⊢
  obtain ⟨y, hy, hconn⟩ := ha
  exact ⟨y, hy, hconn.mono (openSub_mono _ hab)⟩













theorem wiredFiniteMeasure_succ_le_boxBdryConnEvent (n : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      ≤ (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  have hS : IsIncreasing {ω : ConfigSpace (Sym2 (boxVerts d n)) |
      ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)} :=
    isIncreasing_connToBdryEvent n
  have hmeas : MeasurableSet (boxBdryConnEvent d n) := measurableSet_boxBdryConnEvent d n
  
  have hdom := wiredFiniteMeasure_succ_le_smallerBox n hp hp1 hS hmeas
  rw [wiredFiniteMeasure_real_boxBdryConnEvent_sum d n hp hp1]
  exact hdom













theorem openSub_succ_adj_inner (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x y : boxVerts d n) :
    (openSub (boxGraph d (n+1)) (boxRestrict d (n+1) ω)).Adj
        (boxVertIncl d n x) (boxVertIncl d n y)
      ↔ (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y := by
  rw [openSub_adj, openSub_adj, boxGraph_adj_boxVertIncl]
  have he : s(boxVertIncl d n x, boxVertIncl d n y) = innerEdge d n s(x, y) := by
    rw [innerEdge, Sym2.map_mk]
  rw [he,
    show boxRestrict d (n+1) ω (innerEdge d n s(x,y))
        = ω (edgeIncl d (n+1) (innerEdge d n s(x,y))) from rfl,
    edgeIncl_innerEdge]
  rfl






theorem boxBoundary_of_openSub_succ_adj_outer (n : ℕ) (hn : 1 ≤ n)
    (ω : ConfigSpace (Sym2 (Site d)))
    {x : boxVerts d n} {z : boxVerts d (n+1)} (hz : ¬ IsInnerVert d n z)
    (h : (openSub (boxGraph d (n+1)) (boxRestrict d (n+1) ω)).Adj (boxVertIncl d n x) z) :
    boxBoundary d n x := by
  rw [openSub_adj] at h
  obtain ⟨hadj, _⟩ := h
  have hnn : StatMech.Lattice.NearestNeighbour d (x : Site d) (z : Site d) := by
    have hcp := hadj; rw [boxGraph, SimpleGraph.comap_adj] at hcp; exact hcp
  exact ⟨x.2, notMem_box_pred_of_adj_outer hn x.2 hnn hz⟩



theorem boxVertIncl_boxOrigin (n : ℕ) :
    boxVertIncl d n (IsingFK.boxOrigin d n) = IsingFK.boxOrigin d (n+1) :=
  Subtype.ext rfl












theorem connToBdry_succ_of_connToBdry (n : ℕ) (hn : 1 ≤ n) (ω : ConfigSpace (Sym2 (Site d)))
    {v : boxVerts d (n+1)} (hv : boxBoundary d (n+1) v)
    (h : (openSub (boxGraph d (n+1)) (boxRestrict d (n+1) ω)).Reachable
        (IsingFK.boxOrigin d (n+1)) v) :
    ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω) (IsingFK.boxOrigin d n) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  set OS := openSub (boxGraph d (n+1)) (boxRestrict d (n+1) ω)
  set os := openSub (boxGraph d n) (boxRestrict d n ω)
  suffices H : ∀ w : boxVerts d (n+1),
      Relation.ReflTransGen OS.Adj (IsingFK.boxOrigin d (n+1)) w →
      (ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω) (IsingFK.boxOrigin d n)
        ∨ ∃ x : boxVerts d n, boxVertIncl d n x = w
            ∧ os.Reachable (IsingFK.boxOrigin d n) x) by
    rcases H v h with hdone | ⟨x, hx, hreach⟩
    · exact hdone
    · exfalso
      have hvinner : IsInnerVert d n v := by rw [← hx]; exact isInnerVert_boxVertIncl d n x
      rw [boxBoundary, mem_vertexBoundary] at hv
      exact hv.2 (by simpa using hvinner)
  intro w hw
  induction hw with
  | refl => exact Or.inr ⟨IsingFK.boxOrigin d n, boxVertIncl_boxOrigin n, SimpleGraph.Reachable.refl _⟩
  | @tail u w hru hadj ih =>
      rcases ih with hdone | ⟨x, hx, hreach⟩
      · exact Or.inl hdone
      · subst hx
        by_cases hw_inner : IsInnerVert d n w
        · obtain ⟨x', rfl⟩ := (isInnerVert_iff_range d n w).mp hw_inner
          exact Or.inr ⟨x', rfl,
            hreach.trans ((openSub_succ_adj_inner n ω x x').mp hadj).reachable⟩
        · exact Or.inl ⟨x, boxBoundary_of_openSub_succ_adj_outer n hn ω hw_inner hadj, hreach⟩





theorem boxBdryConnEvent_succ_subset (n : ℕ) (hn : 1 ≤ n) :
    boxBdryConnEvent d (n+1) ⊆ boxBdryConnEvent d n := by
  intro ω hω
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_setOf_eq, ConnToBdry] at hω ⊢
  obtain ⟨v, hv, hconn⟩ := hω
  exact connToBdry_succ_of_connToBdry n hn ω hv hconn

























theorem wiredFiniteMeasure_boxBdryConnEvent_antitone (n : ℕ) (hn : 1 ≤ n) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d (n+1))
      ≤ (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  refine le_trans ?_ (wiredFiniteMeasure_succ_le_boxBdryConnEvent n hp hp1)
  exact measureReal_mono (boxBdryConnEvent_succ_subset n hn)










def boxVertInclLE (d : ℕ) {n m : ℕ} (h : n ≤ m) (x : boxVerts d n) : boxVerts d m :=
  ⟨(x : Site d), box_mono d h x.2⟩


def innerEdgeLE (d : ℕ) {n m : ℕ} (h : n ≤ m) : Sym2 (boxVerts d n) → Sym2 (boxVerts d m) :=
  Sym2.map (boxVertInclLE d h)



theorem edgeIncl_innerEdgeLE (d : ℕ) {n m : ℕ} (h : n ≤ m) (e : Sym2 (boxVerts d n)) :
    edgeIncl d m (innerEdgeLE d h e) = edgeIncl d n e := by
  unfold edgeIncl innerEdgeLE boxVertInclLE
  rw [Sym2.map_map]
  rfl


noncomputable def boxRestrictLE (d : ℕ) {n m : ℕ} (h : n ≤ m)
    (η : ConfigSpace (Sym2 (boxVerts d m))) : ConfigSpace (Sym2 (boxVerts d n)) :=
  fun eb => η (innerEdgeLE d h eb)



theorem boxRestrictLE_boxRestrict (d : ℕ) {n m : ℕ} (h : n ≤ m)
    (ω : ConfigSpace (Sym2 (Site d))) :
    boxRestrictLE d h (boxRestrict d m ω) = boxRestrict d n ω := by
  funext eb
  show ω (edgeIncl d m (innerEdgeLE d h eb)) = ω (edgeIncl d n eb)
  rw [edgeIncl_innerEdgeLE]

theorem boxRestrictLE_monotone (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    Monotone (boxRestrictLE d h) :=
  fun a b hab eb => hab (innerEdgeLE d h eb)




noncomputable def connToBdryEventLE (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    Set (ConfigSpace (Sym2 (boxVerts d m))) :=
  boxRestrictLE d h ⁻¹' {ω : ConfigSpace (Sym2 (boxVerts d n)) |
    ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)}

theorem isIncreasing_connToBdryEventLE (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    IsIncreasing (connToBdryEventLE d h) := by
  intro a b hab ha
  simp only [connToBdryEventLE, Set.mem_preimage, Set.mem_setOf_eq] at ha ⊢
  obtain ⟨y, hy, hconn⟩ := ha
  exact ⟨y, hy, hconn.mono (openSub_mono _ (boxRestrictLE_monotone d h hab))⟩




theorem boxBdryConnEvent_eq_boxRestrict_preimage (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    boxBdryConnEvent d n = boxRestrict d m ⁻¹' (connToBdryEventLE d h) := by
  ext ω
  simp only [boxBdryConnEvent, connToBdryEventLE, Set.mem_preimage, Set.mem_setOf_eq,
    boxRestrictLE_boxRestrict]

theorem measurableSet_boxRestrict_connToBdryEventLE (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    MeasurableSet (boxRestrict d m ⁻¹' (connToBdryEventLE d h)) := by
  rw [← boxBdryConnEvent_eq_boxRestrict_preimage d h]
  exact measurableSet_boxBdryConnEvent d n





theorem wiredFiniteMeasure_real_boxRestrictEvent (m : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (S : Set (ConfigSpace (Sym2 (boxVerts d m))))
    (hmeas : MeasurableSet (boxRestrict d m ⁻¹' S)) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d m)),
          S.indicator (fun _ => (1:ℝ)) ω * wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω := by
  have hw : (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
        (boxRestrict d m ⁻¹' S)
      = ((wiredFkPMF (boxGraph d m) (boxBoundary d m) hp hp1
            (by norm_num : (0:ℝ) < 2)).toMeasure
          (extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d m) hmeas]
  have hpre : extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S) = S := by
    ext ω
    simp only [Set.mem_preimage, boxRestrict_extendEdge]
  rw [hw, hpre, wiredFkPMF_toMeasure_toReal d m hp hp1 (by norm_num : (0:ℝ) < 2)]










theorem wiredFiniteMeasure_succ_le_boxBdryConnEvent_le (n m : ℕ) (h : n ≤ m) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d (m+1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  have hmeas := measurableSet_boxRestrict_connToBdryEventLE d h
  have hstep := wiredFiniteMeasure_succ_le_smallerBox m hp hp1
    (isIncreasing_connToBdryEventLE d h) hmeas
  rw [boxBdryConnEvent_eq_boxRestrict_preimage d h (n := n),
    wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 (connToBdryEventLE d h) hmeas]
  exact hstep





theorem wiredFiniteMeasure_boxBdryConnEvent_antitone_radius (n k : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d (n+k+1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      ≤ (wiredFiniteMeasure d (n+k) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) :=
  wiredFiniteMeasure_succ_le_boxBdryConnEvent_le n (n+k) (Nat.le_add_right n k) hp hp1











theorem openSubgraph_adj_of_boxGraph (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {x y : boxVerts d n} (h : (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y) :
    (openSubgraph d ω).Adj (x : Site d) (y : Site d) := by
  rw [openSub_adj] at h
  obtain ⟨hadj, hopen⟩ := h
  rw [boxGraph, SimpleGraph.comap_adj] at hadj
  refine ⟨hadj, ?_⟩
  have hev : boxRestrict d n ω s(x, y) = ω s((x:Site d), (y:Site d)) := by
    show ω (edgeIncl d n s(x,y)) = ω s((x:Site d),(y:Site d))
    unfold edgeIncl
    rw [Sym2.map_mk]
  rw [hev] at hopen
  exact hopen




theorem connected_of_boxConnected (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {x y : boxVerts d n}
    (h : (openSub (boxGraph d n) (boxRestrict d n ω)).Reachable x y) :
    StatMech.Lattice.Connected d ω (x : Site d) (y : Site d) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  unfold StatMech.Lattice.Connected
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u w _ hadj ih => exact ih.tail (openSubgraph_adj_of_boxGraph n ω hadj)




theorem boxBdryConnEvent_subset_crossingEvent (n : ℕ) :
    boxBdryConnEvent d n ⊆ crossingEvent d n := by
  intro ω hω
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_setOf_eq, ConnToBdry] at hω
  obtain ⟨v, hv, hconn⟩ := hω
  rw [mem_crossingEvent]
  refine ⟨(v : Site d), connected_of_boxConnected n ω hconn, ?_⟩
  rw [boxBoundary, mem_vertexBoundary] at hv
  exact hv.2


theorem boxGraph_open_of_openSubgraph (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {x y : boxVerts d n} (h : (openSubgraph d ω).Adj (x : Site d) (y : Site d)) :
    (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y := by
  rw [openSubgraph_adj] at h
  obtain ⟨hadj, hopen⟩ := h
  rw [openSub_adj]
  refine ⟨by rw [boxGraph, SimpleGraph.comap_adj]; exact hadj, ?_⟩
  show ω (edgeIncl d n s(x,y)) = true
  unfold edgeIncl
  rw [Sym2.map_mk]
  exact hopen











theorem boxBdryConn_of_crossing (n : ℕ) (hn : 1 ≤ n) (ω : ConfigSpace (Sym2 (Site d)))
    {v : Site d} (hv : v ∉ box d n)
    (h : (openSubgraph d ω).Reachable (origin d) v) :
    ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω) (IsingFK.boxOrigin d n) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  set OS := openSubgraph d ω
  set os := openSub (boxGraph d n) (boxRestrict d n ω)
  suffices H : ∀ w : Site d, Relation.ReflTransGen OS.Adj (origin d) w →
      (ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω) (IsingFK.boxOrigin d n)
        ∨ ∃ x : boxVerts d n, (x : Site d) = w ∧ os.Reachable (IsingFK.boxOrigin d n) x) by
    rcases H v h with hdone | ⟨x, hx, _⟩
    · exact hdone
    · exact absurd (hx ▸ x.2) hv
  intro w hw
  induction hw with
  | refl => exact Or.inr ⟨IsingFK.boxOrigin d n, rfl, SimpleGraph.Reachable.refl _⟩
  | @tail u w hru hadj ih =>
      rcases ih with hdone | ⟨x, hx, hreach⟩
      · exact Or.inl hdone
      · subst hx
        by_cases hw_box : w ∈ box d n
        · refine Or.inr ⟨⟨w, hw_box⟩, rfl,
            hreach.trans (boxGraph_open_of_openSubgraph n ω hadj).reachable⟩
        · left
          rw [openSubgraph_adj] at hadj
          obtain ⟨hnn, _⟩ := hadj
          rw [hypercubicLattice_adj] at hnn
          have hnn' : StatMech.Lattice.NearestNeighbour d (x : Site d) w := hnn
          exact ⟨x, ⟨x.2, notMem_box_pred_of_adj_outer hn x.2 hnn' hw_box⟩, hreach⟩




theorem crossingEvent_succ_subset_boxBdryConnEvent (n : ℕ) (hn : 1 ≤ n) :
    crossingEvent d (n+1) ⊆ boxBdryConnEvent d n := by
  intro ω hω
  rw [mem_crossingEvent] at hω
  obtain ⟨v, hconn, hv⟩ := hω
  simp only [Nat.add_sub_cancel] at hv
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_setOf_eq]
  exact boxBdryConn_of_crossing n hn ω hv hconn






theorem wiredIv_boxBdryConnEvent_tendsto {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    Tendsto (fun n => ((wiredInfiniteVolume d hp hp1 hq :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
        Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n))
      atTop (𝓝 (fkTheta d hp hp1 hq (q := q))) := by
  set μ : Measure (ConfigSpace (Sym2 (Site d))) :=
    ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))) with hμ
  have htail : Tendsto (fun n => μ.real (crossingEvent d n)) atTop
      (𝓝 (fkTheta d hp hp1 hq (q := q))) :=
    fkBoundaryConnReal_tendsto_fkTheta hp hp1 hq
  have htail_shift : Tendsto (fun n => μ.real (crossingEvent d (n+1))) atTop
      (𝓝 (fkTheta d hp hp1 hq (q := q))) := htail.comp (tendsto_add_atTop_nat 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' htail_shift htail ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact measureReal_mono (crossingEvent_succ_subset_boxBdryConnEvent n hn)
  · filter_upwards with n
    exact measureReal_mono (boxBdryConnEvent_subset_crossingEvent n)





theorem boxBdryConnEvent_subset_le (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    boxBdryConnEvent d n ⊆ boxBdryConnEvent d k := by
  induction n with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge k (m+1) with hlt | _
      · exact (boxBdryConnEvent_succ_subset m (by omega)).trans (ih (by omega))
      · rw [show k = m+1 by omega]




theorem radius_antitone (k : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Antitone (fun j => (wiredFiniteMeasure d (k+j) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k)) := by
  apply antitone_nat_of_succ_le
  intro j
  have := wiredFiniteMeasure_succ_le_boxBdryConnEvent_le (d := d) k (k+j)
    (Nat.le_add_right k j) hp hp1
  simpa [Nat.add_assoc] using this




theorem tendsto_of_antitone_of_subseq {a : ℕ → ℝ} {L : ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hanti : Antitone a) (hbdd : BddBelow (Set.range a))
    (hsub : Tendsto (fun m => a (φ m)) atTop (𝓝 L)) :
    Tendsto a atTop (𝓝 L) := by
  have hinf : Tendsto a atTop (𝓝 (⨅ n, a n)) := tendsto_atTop_ciInf hanti hbdd
  rw [tendsto_nhds_unique hsub (hinf.comp hφ.tendsto_atTop)]
  exact hinf










theorem wiredFiniteMeasure_radius_tendsto (k : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun j => (wiredFiniteMeasure d (k+j) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k))
      atTop (𝓝 (((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
          Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k))) := by
  classical
  have hq : (0:ℝ) < 2 := by norm_num
  set a' := fun j => (wiredFiniteMeasure d (k+j) hp hp1 hq
      : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k) with ha'
  set bk := ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k) with hbk
  obtain ⟨φ, hφ, hconv⟩ := wiredInfiniteVolume_isLimit d hp hp1 hq
  have hport : Tendsto (fun m => (wiredFiniteMeasure d (φ m) hp hp1 hq
      : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k))
      atTop (𝓝 bk) := hconv.tendsto_real_of_isClopen (isClopen_boxBdryConnEvent d k)
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨m₀, hm₀⟩ := (hφtop.eventually_ge_atTop k).exists_forall_of_atTop
  refine tendsto_of_antitone_of_subseq (φ := fun m => φ (m + m₀) - k) ?_
    (radius_antitone k hp hp1) ⟨0, by rintro x ⟨j, rfl⟩; exact measureReal_nonneg⟩ ?_
  · intro i j hij
    simp only
    have hi : k ≤ φ (i + m₀) := hm₀ (i + m₀) (by omega)
    have hj : k ≤ φ (j + m₀) := hm₀ (j + m₀) (by omega)
    have hlt : φ (i + m₀) < φ (j + m₀) := hφ (by omega)
    omega
  · have hsub : Tendsto (fun m => (wiredFiniteMeasure d (φ (m+m₀)) hp hp1 hq
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k))
        atTop (𝓝 bk) := hport.comp (tendsto_add_atTop_nat m₀)
    refine hsub.congr (fun m => ?_)
    have hge : k ≤ φ (m + m₀) := hm₀ (m + m₀) (by omega)
    simp only [ha']
    have : k + (φ (m + m₀) - k) = φ (m + m₀) := by omega
    rw [this]
























theorem boxBdryConnEvent_diag_tendsto {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n))
      atTop (𝓝 (fkTheta d hp hp1 (by norm_num : (0:ℝ) < 2) (q := 2))) := by
  classical
  have hq : (0:ℝ) < 2 := by norm_num
  set μ := fun m => (wiredFiniteMeasure d m hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) with hμ
  set ν := ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))) with hν
  set aN := fun n => (μ n).real (boxBdryConnEvent d n) with haN
  set bN := fun k => ν.real (boxBdryConnEvent d k) with hbN
  set fk := fkTheta d hp hp1 hq (q := 2) with hfk
  have haprime : ∀ k, Tendsto (fun j => (μ (k+j)).real (boxBdryConnEvent d k)) atTop (𝓝 (bN k)) :=
    fun k => wiredFiniteMeasure_radius_tendsto k hp hp1
  
  set a1 := fun j => aN (j+1) with ha1
  have ha1_anti : Antitone a1 := by
    apply antitone_nat_of_succ_le
    intro j
    exact wiredFiniteMeasure_boxBdryConnEvent_antitone (j+1) (by omega) hp hp1
  have ha1_bdd : BddBelow (Set.range a1) := ⟨0, by rintro x ⟨j, rfl⟩; exact measureReal_nonneg⟩
  have haN_tendsto : Tendsto aN atTop (𝓝 (⨅ j, a1 j)) :=
    (tendsto_add_atTop_iff_nat (f := aN) 1).mp (tendsto_atTop_ciInf ha1_anti ha1_bdd)
  set L := ⨅ j, a1 j with hL
  suffices hLfk : L = fk by rw [hLfk] at haN_tendsto; exact haN_tendsto
  have hbN_tendsto : Tendsto bN atTop (𝓝 fk) := wiredIv_boxBdryConnEvent_tendsto hp hp1 hq
  apply le_antisymm
  · 
    have hLle : ∀ k, 1 ≤ k → L ≤ bN k := by
      intro k hk
      have hbound : ∀ j, aN (k+j) ≤ (μ (k+j)).real (boxBdryConnEvent d k) := fun j =>
        measureReal_mono (boxBdryConnEvent_subset_le k (k+j) hk (Nat.le_add_right k j))
      have hktop : Tendsto (fun j => k + j) atTop atTop :=
        tendsto_atTop_mono (fun j => Nat.le_add_left j k) tendsto_id
      have hL1 : Tendsto (fun j => aN (k+j)) atTop (𝓝 L) := haN_tendsto.comp hktop
      exact le_of_tendsto_of_tendsto' hL1 (haprime k) hbound
    refine ge_of_tendsto hbN_tendsto ?_
    filter_upwards [eventually_ge_atTop 1] with k hk using hLle k hk
  · 
    have hbk_le : ∀ k, bN k ≤ aN k := by
      intro k
      have hanti_k := radius_antitone (d := d) k hp hp1
      have hle : bN k ≤ (μ (k+0)).real (boxBdryConnEvent d k) := by
        refine le_of_tendsto (haprime k) ?_
        filter_upwards [eventually_ge_atTop 0] with j _ using hanti_k (Nat.zero_le j)
      have hk0 : aN k = (μ (k+0)).real (boxBdryConnEvent d k) := by simp [haN]
      rw [hk0]; exact hle
    exact le_of_tendsto_of_tendsto' hbN_tendsto haN_tendsto hbk_le











theorem boxBoundaryConnProfile_tendsto {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0:ℝ) < 2) n)
      atTop (𝓝 (fkTheta d hp hp1 (by norm_num : (0:ℝ) < 2) (q := 2))) :=
  boxBoundaryConnProfile_tendsto_of_diag d hp hp1 (boxBdryConnEvent_diag_tendsto hp hp1)

end FK

end StatMech
