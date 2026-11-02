/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.InducedBC
public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredBoxLimit
public import PhyslibExt.StatisticalMechanics.RandomCluster.BoxTailLimit
public import PhyslibExt.StatisticalMechanics.RandomCluster.IvProperties
public import PhyslibExt.StatisticalMechanics.RandomCluster.TailLimit
public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.MagPercoIdBox
public import MathlibExt.Probability.Configuration.MonotoneLimit
public import MathlibExt.Probability.Percolation.SubcriticalDecay
/-!
# Wired random-cluster measures decrease with the box

The wired `q = 2` random-cluster measures on the boxes `Λ_n ⊂ ℤ^d` decrease in `n` on
increasing events of a fixed box, and the probability that the origin is connected to `∂Λ_n`
converges to the wired percolation probability `θ¹(p, 2)`.

## i. Overview

Condition the wired measure on `Λ_(n+1)` on the configuration `ψ` outside `Λ_n`. By the domain
Markov property, the conditional law on `Λ_n` is a random-cluster measure with the boundary
wiring induced by `ψ`, which is dominated by the fully wired measure on `Λ_n` for `q ≥ 1`.
Averaging over `ψ` shows that the wired measure on `Λ_(n+1)` gives every increasing event of
`Λ_n` at most its wired `Λ_n` probability. Iterating gives the domination for all larger boxes.

Applied to the increasing event "the origin is connected to `∂Λ_k` inside `Λ_k`", this makes the
box probabilities antitone in the radius, hence convergent along the whole sequence of boxes;
the limit agrees with the wired infinite-volume measure, and the diagonal sequence
`φ¹_{Λ_n}(0 ↔ ∂Λ_n)` converges to `θ¹(p, 2)`.

## ii. Key results

- `wiredSucc_bcProb_innerEvent_le` : the wired measure on `Λ_(n+1)` gives every increasing
  event of `Λ_n` at most its wired `Λ_n` probability (`q ≥ 1`).
- `wiredFiniteMeasure_succ_le_smallerBox` : the same for the measures pushed to `ℤ^d` (`q = 2`).
- `wiredIv_boxBdryConnEvent_tendsto` : under the wired infinite-volume measure,
  `P(0 ↔ ∂Λ_n) → θ¹(p, q)`.
- `boxBdryConnEvent_diag_tendsto` : `φ¹_{Λ_n}(0 ↔ ∂Λ_n) → θ¹(p, 2)`.

## iii. Table of contents

- A. Conditioning on the configuration outside the inner box
- B. Domination by the smaller wired box
- C. Box-boundary connection events
- D. Restriction between nested boxes
- E. Convergence of box-boundary connection probabilities

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 4.
-/

@[expose] public section

open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}

/-! ## A. Conditioning on the configuration outside the inner box -/

/-- Project a configuration on `Λ_(n+1)` to its outer part: edges of `Λ_n` closed, the others
unchanged. -/
noncomputable def outProj (d n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    ConfigSpace (Sym2 (boxVerts d (n + 1))) :=
  psiExt d n ρ (fun _ => false)

/-- The projection closes edges of `Λ_n`. -/
lemma outProj_eq_false_of_range (n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    {e : Sym2 (boxVerts d (n + 1))} (he : e ∈ Set.range (innerEdge d n)) :
    outProj d n ρ e = false := by
  obtain ⟨e', rfl⟩ := he
  unfold outProj
  rw [psiExt_innerEdge]

/-- The projection keeps edges outside `Λ_n`. -/
lemma outProj_eq_of_not_range (n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    {e : Sym2 (boxVerts d (n + 1))} (he : e ∉ Set.range (innerEdge d n)) :
    outProj d n ρ e = ρ e := by
  unfold outProj
  rw [psiExt_eq_psi_of_not_range _ _ _ _ he]

/-- The projection agrees with the configuration off the edges of `Λ_n`. -/
lemma agreesOff_outProj (n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    AgreesOff (innerEdgeFinset d n) (outProj d n ρ) ρ := by
  intro e he
  rw [mem_innerEdgeFinset] at he
  exact (outProj_eq_of_not_range n ρ he).symm

/-- The projection is idempotent. -/
lemma outProj_idem (n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    outProj d n (outProj d n ρ) = outProj d n ρ := by
  funext e
  by_cases hin : e ∈ Set.range (innerEdge d n)
  · rw [outProj_eq_false_of_range n _ hin, outProj_eq_false_of_range n ρ hin]
  · rw [outProj_eq_of_not_range n _ hin]

/-- The configurations with outer part `ψ` form the conditioning fibre of `ψ`. -/
lemma filter_outProj_eq_condFibre (n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
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

/-- Configurations agreeing off `F` have the same conditioning fibre. -/
lemma condFibre_congr_dom {V : Type*} [Fintype V] [DecidableEq V]
    {F : Finset (Sym2 V)} {ψ ψ' : ConfigSpace (Sym2 V)} (h : AgreesOff F ψ ψ') :
    condFibre F ψ = condFibre F ψ' := by
  ext σ
  rw [mem_condFibre, mem_condFibre, agreesOff_congr h]

/-- Configurations agreeing off `F` give the same conditional random-cluster probabilities. -/
lemma condBcProb_congr_dom {V : Type*} [Fintype V] [DecidableEq V] (G C : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel C.Adj]
    (p q : ℝ) (F : Finset (Sym2 V)) (ψ ψ' ω : ConfigSpace (Sym2 V)) (h : AgreesOff F ψ ψ') :
    condBcProb G C p q F ψ ω = condBcProb G C p q F ψ' ω := by
  have hcond : AgreesOff F ψ ω ↔ AgreesOff F ψ' ω := by rw [agreesOff_congr h]
  have hfibre : condFibre F ψ = condFibre F ψ' := condFibre_congr_dom h
  unfold condBcProb inducedBcZ
  rw [hfibre]
  by_cases hω : AgreesOff F ψ ω
  · rw [ite_eq_left hω, ite_eq_left (hcond.mp hω)]
  · rw [ite_eq_right hω, ite_eq_right (fun h' => hω (hcond.mpr h'))]

/-- The masses of the conditioning fibres over all outer configurations sum to `1`. -/
lemma sum_fibreMass_eq_one (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
        (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
          bcProb (boxGraph d (n + 1)) (boundaryCliqueGraph (boxBoundary d (n + 1))) p q σ) = 1 := by
  classical
  set C := boundaryCliqueGraph (boxBoundary d (n + 1))
  set F := innerEdgeFinset d n
  set G := boxGraph d (n + 1)
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

/-- Decomposition of the wired measure on `Λ_(n+1)` over the configuration outside `Λ_n`. -/
lemma wiredSucc_bcProb_decompose (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (B : Set (ConfigSpace (Sym2 (boxVerts d (n + 1))))) :
    (∑ ρ, B.indicator (fun _ => (1 : ℝ)) ρ
        * bcProb (boxGraph d (n + 1)) (boundaryCliqueGraph (boxBoundary d (n + 1))) p q ρ)
      = ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
          (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
            bcProb (boxGraph d (n + 1)) (boundaryCliqueGraph (boxBoundary d (n + 1))) p q σ)
          * (∑ ρ, B.indicator (fun _ => (1 : ℝ)) ρ
              * condBcProb (boxGraph d (n + 1)) (boundaryCliqueGraph (boxBoundary d (n + 1))) p q
                  (innerEdgeFinset d n) ψ ρ) := by
  classical
  set C := boundaryCliqueGraph (boxBoundary d (n + 1))
  set F := innerEdgeFinset d n
  set G := boxGraph d (n + 1)
  rw [← Finset.sum_fiberwise_of_maps_to
      (g := outProj d n) (t := Finset.univ.filter (fun ψ => outProj d n ψ = ψ))
      (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, outProj_idem n ρ⟩)]
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [Finset.mem_filter] at hψ
  rw [filter_outProj_eq_condFibre n ψ hψ.2]
  have hRHS : (∑ ρ, B.indicator (fun _ => (1 : ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = ∑ ρ ∈ condFibre F ψ, B.indicator (fun _ => (1 : ℝ)) ρ * condBcProb G C p q F ψ ρ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro ρ _ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb
    rw [ite_eq_right hρ, mul_zero]
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

/-! ## B. Domination by the smaller wired box -/

/-- For `q ≥ 1`, conditionally on any outer configuration, the wired measure on `Λ_(n+1)` gives an
increasing event of `Λ_n` at most its wired `Λ_n` probability. -/
lemma condBcProb_innerRestrict_le (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n + 1))))
    {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA₀ : IsIncreasing A₀) :
    (∑ ρ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1 : ℝ)) ρ
        * condBcProb (boxGraph d (n + 1)) (boundaryCliqueGraph (boxBoundary d (n + 1))) p q
            (innerEdgeFinset d n) ψ ρ)
      ≤ ∑ ω, A₀.indicator (fun _ => (1 : ℝ)) ω
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  rw [condBcProb_psiExt_sum_eq_inducedBox d n hp hp1 hq0 ψ (innerRestrict d n ⁻¹' A₀)]
  have hpre : psiExt d n ψ ⁻¹' (innerRestrict d n ⁻¹' A₀) = A₀ := by
    ext ω
    simp only [Set.mem_preimage, innerRestrict_psiExt]
  rw [hpre]
  exact condBcProb_psiExt_dominated_wired d n ψ hp hp1 hq hA₀

/-- For `q ≥ 1`, the wired measure on `Λ_(n+1)` gives an increasing event of `Λ_n` at most its wired
`Λ_n` probability. -/
lemma wiredSucc_bcProb_innerEvent_le (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA₀ : IsIncreasing A₀) :
    (∑ ρ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1 : ℝ)) ρ
        * bcProb (boxGraph d (n + 1)) (boundaryCliqueGraph (boxBoundary d (n + 1))) p q ρ)
      ≤ ∑ ω, A₀.indicator (fun _ => (1 : ℝ)) ω
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  set c := ∑ ω, A₀.indicator (fun _ => (1 : ℝ)) ω
      * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω with hc
  rw [wiredSucc_bcProb_decompose n hp hp1 hq0 (innerRestrict d n ⁻¹' A₀)]
  calc ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
          (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
            bcProb (boxGraph d (n + 1)) (boundaryCliqueGraph (boxBoundary d (n + 1))) p q σ)
          * (∑ ρ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1 : ℝ)) ρ
              * condBcProb (boxGraph d (n + 1)) (boundaryCliqueGraph (boxBoundary d (n + 1))) p q
                  (innerEdgeFinset d n) ψ ρ)
        ≤ ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
            (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
              bcProb (boxGraph d (n + 1))
                (boundaryCliqueGraph (boxBoundary d (n + 1))) p q σ) * c := by
            apply Finset.sum_le_sum
            intro ψ _
            apply mul_le_mul_of_nonneg_left (condBcProb_innerRestrict_le n hp hp1 hq ψ hA₀)
            exact Finset.sum_nonneg (fun σ _ =>
              bcProb_nonneg (boxGraph d (n + 1))
                (boundaryCliqueGraph (boxBoundary d (n + 1))) hp hp1 hq0 σ)
    _ = (∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ),
            (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ,
              bcProb (boxGraph d (n + 1))
                (boundaryCliqueGraph (boxBoundary d (n + 1))) p q σ)) * c := by
            rw [Finset.sum_mul]
    _ = c := by rw [sum_fibreMass_eq_one n hp hp1 hq0, one_mul]

/-- The wired `Λ_(n+1)` measure of a `Λ_n` cylinder event, as a finite sum. -/
lemma wiredFiniteMeasure_succ_real_innerRestrictEvent (n : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (S : Set (ConfigSpace (Sym2 (boxVerts d n))))
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (wiredFiniteMeasure d (n + 1) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S)
      = ∑ ρ : ConfigSpace (Sym2 (boxVerts d (n + 1))),
          (innerRestrict d n ⁻¹' S).indicator (fun _ => (1 : ℝ)) ρ
            * bcProb (boxGraph d (n + 1)) (boundaryCliqueGraph (boxBoundary d (n + 1))) p 2 ρ := by
  have hw : (wiredFiniteMeasure d (n + 1) hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _).real
        (boxRestrict d n ⁻¹' S)
      = ((wiredFkPMF (boxGraph d (n + 1)) (boxBoundary d (n + 1)) hp hp1
            (by norm_num : (0 : ℝ) < 2)).toMeasure
          (extendEdge d (n + 1) ⁻¹' (boxRestrict d n ⁻¹' S))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d (n + 1)) hmeas]
  have hpre : extendEdge d (n + 1) ⁻¹' (boxRestrict d n ⁻¹' S) = innerRestrict d n ⁻¹' S := by
    ext ρ
    simp only [Set.mem_preimage, boxRestrict_extendEdge_succ]
  rw [hw, hpre, wiredFkPMF_toMeasure_toReal d (n + 1) hp hp1 (by norm_num : (0 : ℝ) < 2)]
  exact Finset.sum_congr rfl (fun ρ _ => by rw [bcProb_clique_eq_wiredFkProb])

/-- For `q = 2`, the wired `Λ_(n+1)` measure of an increasing `Λ_n` cylinder event is at most its
wired `Λ_n` probability. -/
lemma wiredFiniteMeasure_succ_le_smallerBox (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hS : IsIncreasing S)
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (wiredFiniteMeasure d (n + 1) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S)
      ≤ ∑ ω, S.indicator (fun _ => (1 : ℝ)) ω
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
  rw [wiredFiniteMeasure_succ_real_innerRestrictEvent n hp hp1 S hmeas]
  exact wiredSucc_bcProb_innerEvent_le n hp hp1 (by norm_num) hS

/-! ## C. Box-boundary connection events -/

/-- The event that the origin is connected to the box boundary is increasing. -/
lemma isIncreasing_connToBdryEvent (n : ℕ) :
    IsIncreasing {ω : ConfigSpace (Sym2 (boxVerts d n)) |
      ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)} := by
  intro a b hab ha
  simp only [Set.mem_ofPred_eq] at ha ⊢
  obtain ⟨y, hy, hconn⟩ := ha
  exact ⟨y, hy, hconn.mono (openSub_mono _ hab)⟩

/-- For `q = 2`, `φ¹_{Λ_(n+1)}(0 ↔ ∂Λ_n) ≤ φ¹_{Λ_n}(0 ↔ ∂Λ_n)`. -/
lemma wiredFiniteMeasure_succ_le_boxBdryConnEvent (n : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d (n + 1) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      ≤ (wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  have hS : IsIncreasing {ω : ConfigSpace (Sym2 (boxVerts d n)) |
      ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)} :=
    isIncreasing_connToBdryEvent n
  have hmeas : MeasurableSet (boxBdryConnEvent d n) := measurableSet_boxBdryConnEvent d n
  have hdom := wiredFiniteMeasure_succ_le_smallerBox n hp hp1 hS hmeas
  rw [wiredFiniteMeasure_real_boxBdryConnEvent_sum d n hp hp1]
  exact hdom

/-- An open edge of `Λ_n` is an open edge of `Λ_(n+1)`. -/
lemma openSub_succ_adj_inner (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x y : boxVerts d n) :
    (openSub (boxGraph d (n + 1)) (boxRestrict d (n + 1) ω)).Adj
        (boxVertIncl d n x) (boxVertIncl d n y)
      ↔ (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y := by
  rw [openSub_adj, openSub_adj, boxGraph_adj_boxVertIncl]
  have he : s(boxVertIncl d n x, boxVertIncl d n y) = innerEdge d n s(x, y) := by
    rw [innerEdge, Sym2.map_mk]
  rw [he,
    show boxRestrict d (n + 1) ω (innerEdge d n s(x, y))
        = ω (edgeIncl d (n + 1) (innerEdge d n s(x, y))) from rfl,
    edgeIncl_innerEdge]
  rfl

/-- A vertex of `Λ_n` adjacent to a vertex of `Λ_(n+1) \ Λ_n` lies on `∂Λ_n`. -/
lemma boxBoundary_of_openSub_succ_adj_outer (n : ℕ) (hn : 1 ≤ n)
    (ω : ConfigSpace (Sym2 (Site d)))
    {x : boxVerts d n} {z : boxVerts d (n + 1)} (hz : ¬ IsInnerVert d n z)
    (h : (openSub (boxGraph d (n + 1)) (boxRestrict d (n + 1) ω)).Adj (boxVertIncl d n x) z) :
    boxBoundary d n x := by
  rw [openSub_adj] at h
  obtain ⟨hadj, _⟩ := h
  have hnn : StatMech.Lattice.NearestNeighbour d (x : Site d) (z : Site d) := by
    have hcp := hadj; rw [boxGraph, SimpleGraph.comap_adj] at hcp; exact hcp
  exact ⟨x.2, notMem_box_pred_of_adj_outer hn x.2 hnn hz⟩

/-- The inclusion `Λ_n → Λ_(n+1)` maps the origin to the origin. -/
lemma boxVertIncl_boxOrigin (n : ℕ) :
    boxVertIncl d n (IsingFK.boxOrigin d n) = IsingFK.boxOrigin d (n + 1) :=
  Subtype.ext rfl

/-- A connection from the origin to `∂Λ_(n+1)` inside `Λ_(n+1)` passes through `∂Λ_n`. -/
lemma connToBdry_succ_of_connToBdry (n : ℕ) (hn : 1 ≤ n) (ω : ConfigSpace (Sym2 (Site d)))
    {v : boxVerts d (n + 1)} (hv : boxBoundary d (n + 1) v)
    (h : (openSub (boxGraph d (n + 1)) (boxRestrict d (n + 1) ω)).Reachable
        (IsingFK.boxOrigin d (n + 1)) v) :
    ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω) (IsingFK.boxOrigin d n) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  set OS := openSub (boxGraph d (n + 1)) (boxRestrict d (n + 1) ω)
  set os := openSub (boxGraph d n) (boxRestrict d n ω)
  suffices H : ∀ w : boxVerts d (n + 1),
      Relation.ReflTransGen OS.Adj (IsingFK.boxOrigin d (n + 1)) w →
      (ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω) (IsingFK.boxOrigin d n)
        ∨ ∃ x : boxVerts d n, boxVertIncl d n x = w
            ∧ os.Reachable (IsingFK.boxOrigin d n) x) by
    rcases H v h with hdone | ⟨x, hx, hreach⟩
    · exact hdone
    · exfalso
      have hvinner : IsInnerVert d n v := by rw [← hx]; exact isInnerVert_boxVertIncl d n x
      rw [boxBoundary, mem_vertexBoundary] at hv
      exact hv.2 (by simpa [IsInnerVert, box] using hvinner)
  intro w hw
  induction hw with
  | refl => exact Or.inr ⟨IsingFK.boxOrigin d n, boxVertIncl_boxOrigin n,
      SimpleGraph.Reachable.refl _⟩
  | @tail u w hru hadj ih =>
      rcases ih with hdone | ⟨x, hx, hreach⟩
      · exact Or.inl hdone
      · subst hx
        by_cases hw_inner : IsInnerVert d n w
        · obtain ⟨x', rfl⟩ := (isInnerVert_iff_range d n w).mp hw_inner
          exact Or.inr ⟨x', rfl,
            hreach.trans ((openSub_succ_adj_inner n ω x x').mp hadj).reachable⟩
        · exact Or.inl ⟨x, boxBoundary_of_openSub_succ_adj_outer n hn ω hw_inner hadj, hreach⟩

/-- The events `0 ↔ ∂Λ_n` decrease in `n`. -/
lemma boxBdryConnEvent_succ_subset (n : ℕ) (hn : 1 ≤ n) :
    boxBdryConnEvent d (n + 1) ⊆ boxBdryConnEvent d n := by
  intro ω hω
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_ofPred_eq, ConnToBdry] at hω ⊢
  obtain ⟨v, hv, hconn⟩ := hω
  exact connToBdry_succ_of_connToBdry n hn ω hv hconn

/-- For `q = 2`, `φ¹_{Λ_(n+1)}(0 ↔ ∂Λ_(n+1)) ≤ φ¹_{Λ_n}(0 ↔ ∂Λ_n)`. -/
lemma wiredFiniteMeasure_boxBdryConnEvent_antitone (n : ℕ) (hn : 1 ≤ n) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d (n + 1) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d (n + 1))
      ≤ (wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  refine le_trans ?_ (wiredFiniteMeasure_succ_le_boxBdryConnEvent n hp hp1)
  exact measureReal_mono (boxBdryConnEvent_succ_subset n hn)

/-! ## D. Restriction between nested boxes -/

/-- The inclusion `Λ_n → Λ_m` for `n ≤ m`. -/
def boxVertInclLE (d : ℕ) {n m : ℕ} (h : n ≤ m) (x : boxVerts d n) : boxVerts d m :=
  ⟨(x : Site d), box_mono d h x.2⟩

/-- The inclusion of edges of `Λ_n` into edges of `Λ_m` for `n ≤ m`. -/
def innerEdgeLE (d : ℕ) {n m : ℕ} (h : n ≤ m) : Sym2 (boxVerts d n) → Sym2 (boxVerts d m) :=
  Sym2.map (boxVertInclLE d h)

/-- Including an edge into `Λ_m` and then into `ℤ^d` is including it into `ℤ^d`. -/
lemma edgeIncl_innerEdgeLE (d : ℕ) {n m : ℕ} (h : n ≤ m) (e : Sym2 (boxVerts d n)) :
    edgeIncl d m (innerEdgeLE d h e) = edgeIncl d n e := by
  unfold edgeIncl innerEdgeLE boxVertInclLE
  rw [Sym2.map_map]
  rfl

/-- Restrict a configuration on `Λ_m` to `Λ_n` for `n ≤ m`. -/
noncomputable def boxRestrictLE (d : ℕ) {n m : ℕ} (h : n ≤ m)
    (η : ConfigSpace (Sym2 (boxVerts d m))) : ConfigSpace (Sym2 (boxVerts d n)) :=
  fun eb => η (innerEdgeLE d h eb)

/-- Restricting to `Λ_m` and then to `Λ_n` is restricting to `Λ_n`. -/
lemma boxRestrictLE_boxRestrict (d : ℕ) {n m : ℕ} (h : n ≤ m)
    (ω : ConfigSpace (Sym2 (Site d))) :
    boxRestrictLE d h (boxRestrict d m ω) = boxRestrict d n ω := by
  funext eb
  change ω (edgeIncl d m (innerEdgeLE d h eb)) = ω (edgeIncl d n eb)
  rw [edgeIncl_innerEdgeLE]

/-- Restriction between boxes is monotone. -/
lemma boxRestrictLE_monotone (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    Monotone (boxRestrictLE d h) :=
  fun _ _ hab eb => hab (innerEdgeLE d h eb)

/-- The event `0 ↔ ∂Λ_n` inside `Λ_n`, as an event on `Λ_m` for `n ≤ m`. -/
noncomputable def connToBdryEventLE (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    Set (ConfigSpace (Sym2 (boxVerts d m))) :=
  boxRestrictLE d h ⁻¹' {ω : ConfigSpace (Sym2 (boxVerts d n)) |
    ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)}

/-- The event `connToBdryEventLE` is increasing. -/
lemma isIncreasing_connToBdryEventLE (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    IsIncreasing (connToBdryEventLE d h) := by
  intro a b hab ha
  simp only [connToBdryEventLE, Set.mem_preimage, Set.mem_ofPred_eq] at ha ⊢
  obtain ⟨y, hy, hconn⟩ := ha
  exact ⟨y, hy, hconn.mono (openSub_mono _ (boxRestrictLE_monotone d h hab))⟩

/-- The event `0 ↔ ∂Λ_n` is a `Λ_m` cylinder event for every `m ≥ n`. -/
lemma boxBdryConnEvent_eq_boxRestrict_preimage (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    boxBdryConnEvent d n = boxRestrict d m ⁻¹' (connToBdryEventLE d h) := by
  ext ω
  simp only [boxBdryConnEvent, connToBdryEventLE, Set.mem_preimage, Set.mem_ofPred_eq,
    boxRestrictLE_boxRestrict]

/-- The cylinder form of `0 ↔ ∂Λ_n` is measurable. -/
lemma measurableSet_boxRestrict_connToBdryEventLE (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    MeasurableSet (boxRestrict d m ⁻¹' (connToBdryEventLE d h)) := by
  rw [← boxBdryConnEvent_eq_boxRestrict_preimage d h]
  exact measurableSet_boxBdryConnEvent d n

/-- The wired `Λ_m` measure of a `Λ_m` cylinder event, as a finite sum. -/
lemma wiredFiniteMeasure_real_boxRestrictEvent (m : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (S : Set (ConfigSpace (Sym2 (boxVerts d m))))
    (hmeas : MeasurableSet (boxRestrict d m ⁻¹' S)) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d m)),
          S.indicator (fun _ =>
              (1 : ℝ)) ω * wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω := by
  have hw : (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _).real
        (boxRestrict d m ⁻¹' S)
      = ((wiredFkPMF (boxGraph d m) (boxBoundary d m) hp hp1
            (by norm_num : (0 : ℝ) < 2)).toMeasure
          (extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d m) hmeas]
  have hpre : extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S) = S := by
    ext ω
    simp only [Set.mem_preimage, boxRestrict_extendEdge]
  rw [hw, hpre, wiredFkPMF_toMeasure_toReal d m hp hp1 (by norm_num : (0 : ℝ) < 2)]

/-- For `q = 2` and `n ≤ m`, `φ¹_{Λ_(m+1)}(0 ↔ ∂Λ_n) ≤ φ¹_{Λ_m}(0 ↔ ∂Λ_n)`. -/
lemma wiredFiniteMeasure_succ_le_boxBdryConnEvent_le (n m : ℕ) (h : n ≤ m) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d (m + 1) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  have hmeas := measurableSet_boxRestrict_connToBdryEventLE d h
  have hstep := wiredFiniteMeasure_succ_le_smallerBox m hp hp1
    (isIncreasing_connToBdryEventLE d h) hmeas
  rw [boxBdryConnEvent_eq_boxRestrict_preimage d h (n := n),
    wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 (connToBdryEventLE d h) hmeas]
  exact hstep

/-- For `q = 2`, `φ¹_{Λ_(n+k+1)}(0 ↔ ∂Λ_n) ≤ φ¹_{Λ_(n+k)}(0 ↔ ∂Λ_n)`. -/
lemma wiredFiniteMeasure_boxBdryConnEvent_antitone_radius (n k : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d (n+k+1) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      ≤ (wiredFiniteMeasure d (n+k) hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) :=
  wiredFiniteMeasure_succ_le_boxBdryConnEvent_le n (n+k) (Nat.le_add_right n k) hp hp1

/-! ## E. Convergence of box-boundary connection probabilities -/

/-- An open edge of the box is an open edge of `ℤ^d`. -/
lemma openSubgraph_adj_of_boxGraph (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {x y : boxVerts d n} (h : (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y) :
    (openSubgraph d ω).Adj (x : Site d) (y : Site d) := by
  rw [openSub_adj] at h
  obtain ⟨hadj, hopen⟩ := h
  rw [boxGraph, SimpleGraph.comap_adj] at hadj
  refine ⟨hadj, ?_⟩
  have hev : boxRestrict d n ω s(x, y) = ω s((x:Site d), (y:Site d)) := by
    change ω (edgeIncl d n s(x, y)) = ω s((x : Site d), (y : Site d))
    unfold edgeIncl
    rw [Sym2.map_mk]
  rw [hev] at hopen
  exact hopen

/-- An open connection inside the box is an open connection in `ℤ^d`. -/
lemma connected_of_boxConnected (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {x y : boxVerts d n}
    (h : (openSub (boxGraph d n) (boxRestrict d n ω)).Reachable x y) :
    StatMech.Lattice.Connected d ω (x : Site d) (y : Site d) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  unfold StatMech.Lattice.Connected
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u w _ hadj ih => exact ih.tail (openSubgraph_adj_of_boxGraph n ω hadj)

/-- A connection from the origin to `∂Λ_n` inside `Λ_n` reaches the complement of `Λ_(n-1)`. -/
lemma boxBdryConnEvent_subset_crossingEvent (n : ℕ) :
    boxBdryConnEvent d n ⊆ crossingEvent d n := by
  intro ω hω
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_ofPred_eq, ConnToBdry] at hω
  obtain ⟨v, hv, hconn⟩ := hω
  rw [mem_crossingEvent]
  refine ⟨(v : Site d), connected_of_boxConnected n ω hconn, ?_⟩
  rw [boxBoundary, mem_vertexBoundary] at hv
  exact hv.2

/-- An open edge of `ℤ^d` between box vertices is an open edge of the box. -/
lemma boxGraph_open_of_openSubgraph (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {x y : boxVerts d n} (h : (openSubgraph d ω).Adj (x : Site d) (y : Site d)) :
    (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y := by
  rw [openSubgraph_adj] at h
  obtain ⟨hadj, hopen⟩ := h
  rw [openSub_adj]
  refine ⟨by rw [boxGraph, SimpleGraph.comap_adj]; exact hadj, ?_⟩
  change ω (edgeIncl d n s(x, y)) = true
  unfold edgeIncl
  rw [Sym2.map_mk]
  exact hopen

/-- A connection from the origin to a site outside `Λ_n` gives a connection to `∂Λ_n` inside `Λ_n`.
-/
lemma boxBdryConn_of_crossing (n : ℕ) (hn : 1 ≤ n) (ω : ConfigSpace (Sym2 (Site d)))
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

/-- Reaching the complement of `Λ_n` implies `0 ↔ ∂Λ_n`. -/
lemma crossingEvent_succ_subset_boxBdryConnEvent (n : ℕ) (hn : 1 ≤ n) :
    crossingEvent d (n + 1) ⊆ boxBdryConnEvent d n := by
  intro ω hω
  rw [mem_crossingEvent] at hω
  obtain ⟨v, hconn, hv⟩ := hω
  simp only [Nat.add_sub_cancel] at hv
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_ofPred_eq]
  exact boxBdryConn_of_crossing n hn ω hv hconn

/-- Under the wired infinite-volume measure, `P(0 ↔ ∂Λ_n) → θ¹(p, q)`. -/
lemma wiredIv_boxBdryConnEvent_tendsto {p q : ℝ}
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
  have htail_shift : Tendsto (fun n => μ.real (crossingEvent d (n + 1))) atTop
      (𝓝 (fkTheta d hp hp1 hq (q := q))) := htail.comp (tendsto_add_atTop_nat 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' htail_shift htail ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact measureReal_mono (crossingEvent_succ_subset_boxBdryConnEvent n hn)
  · filter_upwards with n
    exact measureReal_mono (boxBdryConnEvent_subset_crossingEvent n)

/-- The events `0 ↔ ∂Λ_n` decrease in `n ≥ 1`. -/
lemma boxBdryConnEvent_subset_le (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    boxBdryConnEvent d n ⊆ boxBdryConnEvent d k := by
  induction n with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hlt | _
      · exact (boxBdryConnEvent_succ_subset m (by omega)).trans (ih (by omega))
      · rw [show k = m+1 by omega]

/-- For `q = 2`, `j ↦ φ¹_{Λ_(k+j)}(0 ↔ ∂Λ_k)` is antitone. -/
lemma radius_antitone (k : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Antitone (fun j => (wiredFiniteMeasure d (k+j) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k)) := by
  apply antitone_nat_of_succ_le
  intro j
  have := wiredFiniteMeasure_succ_le_boxBdryConnEvent_le (d := d) k (k+j)
    (Nat.le_add_right k j) hp hp1
  simpa [Nat.add_assoc] using this

/-- A bounded-below antitone real sequence converges to the limit of any of its subsequences. -/
lemma tendsto_of_antitone_of_subseq {a : ℕ → ℝ} {L : ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hanti : Antitone a) (hbdd : BddBelow (Set.range a))
    (hsub : Tendsto (fun m => a (φ m)) atTop (𝓝 L)) :
    Tendsto a atTop (𝓝 L) := by
  have hinf : Tendsto a atTop (𝓝 (⨅ n, a n)) := tendsto_atTop_ciInf hanti hbdd
  rw [tendsto_nhds_unique hsub (hinf.comp hφ.tendsto_atTop)]
  exact hinf

/-- For `q = 2`, `φ¹_{Λ_(k+j)}(0 ↔ ∂Λ_k)` converges as `j → ∞` to the wired infinite-volume
probability of `0 ↔ ∂Λ_k`. -/
lemma wiredFiniteMeasure_radius_tendsto (k : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun j => (wiredFiniteMeasure d (k+j) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k))
      atTop (𝓝 (((wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
          Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k))) := by
  classical
  have hq : (0 : ℝ) < 2 := by norm_num
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

/-- For `q = 2`, `φ¹_{Λ_n}(0 ↔ ∂Λ_n) → θ¹(p, 2)`. -/
lemma boxBdryConnEvent_diag_tendsto {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => (wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n))
      atTop (𝓝 (fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))) := by
  classical
  have hq : (0 : ℝ) < 2 := by norm_num
  set μ := fun m =>
    (wiredFiniteMeasure d m hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) with hμ
  set ν := ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))) with hν
  set aN := fun n => (μ n).real (boxBdryConnEvent d n) with haN
  set bN := fun k => ν.real (boxBdryConnEvent d k) with hbN
  set fk := fkTheta d hp hp1 hq (q := 2) with hfk
  have haprime : ∀ k, Tendsto (fun j => (μ (k+j)).real (boxBdryConnEvent d k)) atTop (𝓝 (bN k)) :=
    fun k => wiredFiniteMeasure_radius_tendsto k hp hp1
  set a1 := fun j => aN (j + 1) with ha1
  have ha1_anti : Antitone a1 := by
    apply antitone_nat_of_succ_le
    intro j
    exact wiredFiniteMeasure_boxBdryConnEvent_antitone (j + 1) (by omega) hp hp1
  have ha1_bdd : BddBelow (Set.range a1) := ⟨0, by rintro x ⟨j, rfl⟩; exact measureReal_nonneg⟩
  have haN_tendsto : Tendsto aN atTop (𝓝 (⨅ j, a1 j)) :=
    (tendsto_add_atTop_iff_nat (f := aN) 1).mp (tendsto_atTop_ciInf ha1_anti ha1_bdd)
  set L := ⨅ j, a1 j with hL
  suffices hLfk : L = fk by rw [hLfk] at haN_tendsto; exact haN_tendsto
  have hbN_tendsto : Tendsto bN atTop (𝓝 fk) := wiredIv_boxBdryConnEvent_tendsto hp hp1 hq
  apply le_antisymm
  · have hLle : ∀ k, 1 ≤ k → L ≤ bN k := by
      intro k hk
      have hbound : ∀ j, aN (k+j) ≤ (μ (k+j)).real (boxBdryConnEvent d k) := fun j =>
        measureReal_mono (boxBdryConnEvent_subset_le k (k+j) hk (Nat.le_add_right k j))
      have hktop : Tendsto (fun j => k + j) atTop atTop :=
        tendsto_atTop_mono (fun j => Nat.le_add_left j k) tendsto_id
      have hL1 : Tendsto (fun j => aN (k+j)) atTop (𝓝 L) := haN_tendsto.comp hktop
      exact le_of_tendsto_of_tendsto' hL1 (haprime k) hbound
    refine ge_of_tendsto hbN_tendsto ?_
    filter_upwards [eventually_ge_atTop 1] with k hk using hLle k hk
  · have hbk_le : ∀ k, bN k ≤ aN k := by
      intro k
      have hanti_k := radius_antitone (d := d) k hp hp1
      have hle : bN k ≤ (μ (k + 0)).real (boxBdryConnEvent d k) := by
        refine le_of_tendsto (haprime k) ?_
        filter_upwards [eventually_ge_atTop 0] with j _ using hanti_k (Nat.zero_le j)
      have hk0 : aN k = (μ (k + 0)).real (boxBdryConnEvent d k) := by simp [haN]
      rw [hk0]; exact hle
    exact le_of_tendsto_of_tendsto' hbN_tendsto haN_tendsto hbk_le

/-- The box-boundary connection profile of the Ising FK representation converges to `θ¹(p, 2)`. -/
lemma boxBoundaryConnProfile_tendsto {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n)
      atTop (𝓝 (fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))) :=
  boxBoundaryConnProfile_tendsto_of_diag d hp hp1 (boxBdryConnEvent_diag_tendsto hp hp1)

end FK

end StatMech
