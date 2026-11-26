/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeTranslationInvariance
public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredErgodicity
public import PhyslibExt.StatisticalMechanics.RandomCluster.DlrInfiniteSandwich
public import MathlibExt.Probability.Configuration.MonotoneLimit

/-!
# The free infinite-volume random-cluster measure satisfies the FK-DLR property

The free infinite-volume random-cluster measure on `ℤ^d` (`1 ≤ q`) is an FK-DLR measure: its
marginal on each finite box is a mixture of boundary-condition measures whose boundary wirings
are supported on the boundary clique.

## i. Overview

Fix an inner box inside a larger outer box. Conditioning the free outer measure on the edges
outside the inner box induces a wiring (which boundary vertices are connected outside), and the
inner marginal is the mixture over wirings of the finite-volume measures with that boundary
condition. This file packages the wiring distribution as a probability measure on graphs on the
inner vertices, shows that each wiring lies below the boundary clique, and passes to the limit
along the subsequence defining the free infinite-volume measure, using compactness of the finite
space of wirings and convergence on clopen sets. `freeInfiniteVolume_isFKDLR` and
`freeFiniteBox_marginal_specification` are proved unconditionally (only `0 < p < 1`, `1 ≤ q`).

## ii. Key results

- `freeNestedMarginal_eq_wiringMixture` : the inner marginal of the outer free measure is the
  wiring mixture of boundary-condition measures.
- `freeFiniteBox_marginal_specification` : the finite-box version, with wirings supported below
  the boundary clique.
- `freeInfiniteVolume_isFKDLR` : the free infinite-volume measure satisfies the FK-DLR property.

## iii. Table of contents

- A. The wiring distribution of the free outer measure
- B. Marginals as wiring mixtures
- C. Finite boxes
- D. The FK-DLR property in infinite volume

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

open MeasureTheory Set SimpleGraph Filter Topology
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice

variable {Vin Vout : Type*} [Fintype Vin] [DecidableEq Vin]
  [Fintype Vout] [DecidableEq Vout]

/-! ## A. The wiring distribution of the free outer measure -/

/-- The discrete measurable structure on graphs on the inner vertex set. -/
local instance (priority := 10000) : MeasurableSpace (SimpleGraph Vin) := ⊤
/-- Every set of graphs is measurable for the discrete measurable structure. -/
local instance : DiscreteMeasurableSpace (SimpleGraph Vin) := ⟨fun _ => trivial⟩
/-- The discrete topology on graphs on the inner vertex set. -/
local instance : TopologicalSpace (SimpleGraph Vin) := ⊥
/-- The topology on graphs on the inner vertex set is discrete. -/
local instance : DiscreteTopology (SimpleGraph Vin) := ⟨rfl⟩

/-- The free outer measure of the outer configurations whose induced wiring on the inner vertices
is the graph `C`. -/
noncomputable def freeNestedWiringWeight
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (p q : ℝ) (C : SimpleGraph Vin) : ℝ := by
  classical
  exact ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
      if ocd_inducedWiring Gout ιV (bdp_noBdry (Vout := Vout)) ψ = C then
        ∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
          fkProb Gout p q σ
      else 0
/-- The wiring weights are nonnegative. -/
lemma freeNestedWiringWeight_nonneg
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (C : SimpleGraph Vin) :
    0 ≤ freeNestedWiringWeight Gout ιV p q C := by
  classical
  unfold freeNestedWiringWeight
  exact Finset.sum_nonneg fun ψ _ => by
    split
    · exact Finset.sum_nonneg fun σ _ => fkProb_nonneg Gout hp hp1 hq σ
    · exact le_rfl
/-- The wiring weights sum to one. -/
lemma freeNestedWiringWeight_sum_eq_one
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (hι : Function.Injective ιV) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ C : SimpleGraph Vin, freeNestedWiringWeight Gout ιV p q C = 1 := by
  classical
  rw [show (∑ C : SimpleGraph Vin, freeNestedWiringWeight Gout ιV p q C) =
      ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
        ∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
          fkProb Gout p q σ by
    unfold freeNestedWiringWeight
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ψ _
    simp]
  have hsum := ocd_sum_fibreMass_eq_one
    (Gout := Gout) (bdryOut := bdp_noBdry (Vout := Vout)) hι hp hp1 hq
  simpa only [bdp_bcProb_noBdry_eq_fkProb] using hsum
/-- The wiring distribution as a probability mass function on inner graphs. -/
noncomputable def freeNestedWiringPMF
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (hι : Function.Injective ιV) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : PMF (SimpleGraph Vin) :=
  PMF.ofFintype
    (fun C => ENNReal.ofReal (freeNestedWiringWeight Gout ιV p q C)) <| by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun C _ => freeNestedWiringWeight_nonneg Gout ιV hp hp1 hq C),
        freeNestedWiringWeight_sum_eq_one Gout ιV hι hp hp1 hq]
      norm_num
/-- The wiring distribution as a probability measure on inner graphs. -/
noncomputable def freeNestedWiringMeasure
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (hι : Function.Injective ιV) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (SimpleGraph Vin) :=
  ⟨(freeNestedWiringPMF Gout ιV hι hp hp1 hq).toMeasure, inferInstance⟩
/-- The wiring measure of a single graph is its wiring weight. -/
lemma freeNestedWiringMeasure_real_singleton
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (hι : Function.Injective ιV) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (C : SimpleGraph Vin) :
    (freeNestedWiringMeasure Gout ιV hι hp hp1 hq : Measure _).real {C} =
      freeNestedWiringWeight Gout ιV p q C := by
  rw [Measure.real, show
      (freeNestedWiringMeasure Gout ιV hι hp hp1 hq : Measure _) =
        (freeNestedWiringPMF Gout ιV hι hp hp1 hq).toMeasure from rfl,
    PMF.toMeasure_apply_singleton _ C MeasurableSet.of_discrete,
    freeNestedWiringPMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (freeNestedWiringWeight_nonneg Gout ιV hp hp1 hq C)]
/-! ## B. Marginals as wiring mixtures -/

/-- Weak convergence of probability measures gives convergence of the real measure of a clopen
set. -/
lemma tendsto_probabilityMeasure_real_of_isClopen
    {α ι : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] [HasOuterApproxClosed α]
    {L : Filter ι} {μ : ProbabilityMeasure α} {μs : ι → ProbabilityMeasure α}
    (hμ : Tendsto μs L (𝓝 μ)) {A : Set α} (hA : IsClopen A) :
    Tendsto (fun i => (μs i : Measure α).real A) L
      (𝓝 ((μ : Measure α).real A)) := by
  have hnn := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hA
  have hcoe := (NNReal.continuous_coe.tendsto _).comp hnn
  have hreal : ∀ ν : ProbabilityMeasure α,
      ((ν A : NNReal) : ℝ) = (ν : Measure α).real A := by
    intro ν
    rw [Measure.real, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  simpa only [Function.comp_def, hreal] using hcoe
/-- The marginal of the free outer measure on the inner edges is the mixture, over induced
wirings `C`, of the inner boundary-condition measures with wiring `C`. -/
lemma freeNestedMarginal_eq_wiringMixture
    (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 Vin))) : by
    classical
    exact
      (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1 : ℝ)) ρ *
          fkProb Gout p q ρ) =
        ∑ C : SimpleGraph Vin,
          freeNestedWiringWeight Gout ιV p q C * dlrBcEventMass Gin C p q A := by
  classical
  have hdecomp := ocd_bcProb_decompose
    (Gout := Gout) (bdryOut := bdp_noBdry (Vout := Vout)) hι hp hp1 hq
    (ocd_innerRestrict ιV ⁻¹' A)
  simp only [bdp_bcProb_noBdry_eq_fkProb] at hdecomp
  rw [hdecomp]
  rw [show (∑ C : SimpleGraph Vin,
        freeNestedWiringWeight Gout ιV p q C * dlrBcEventMass Gin C p q A) =
      ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
        (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
          fkProb Gout p q σ) *
        dlrBcEventMass Gin
          (ocd_inducedWiring Gout ιV (bdp_noBdry (Vout := Vout)) ψ) p q A by
    unfold freeNestedWiringWeight
    calc
      ∑ C : SimpleGraph Vin,
          (∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
              if ocd_inducedWiring Gout ιV (bdp_noBdry (Vout := Vout)) ψ = C then
                ∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
                  fkProb Gout p q σ
              else 0) * dlrBcEventMass Gin C p q A =
        ∑ C : SimpleGraph Vin,
          ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
            (if ocd_inducedWiring Gout ιV (bdp_noBdry (Vout := Vout)) ψ = C then
              ∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
                fkProb Gout p q σ
            else 0) * dlrBcEventMass Gin C p q A := by
              apply Finset.sum_congr rfl
              intro C _
              rw [Finset.sum_mul]
      _ = ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
          ∑ C : SimpleGraph Vin,
            (if ocd_inducedWiring Gout ιV (bdp_noBdry (Vout := Vout)) ψ = C then
              ∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
                fkProb Gout p q σ
            else 0) * dlrBcEventMass Gin C p q A := by
              rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ψ _
        simp]
  apply Finset.sum_congr rfl
  intro ψ _
  congr 1
  rw [ocd_condBcProb_psiExt_sum_eq_inducedBox hι hadjm hp hp1 hq ψ
    (ocd_innerRestrict ιV ⁻¹' A)]
  have hpre : ocd_psiExt ιV ψ ⁻¹' (ocd_innerRestrict ιV ⁻¹' A) = A := by
    ext ω
    simp only [Set.mem_preimage, ocd_innerRestrict_psiExt hι]
  rw [hpre]
  rfl

variable {d : ℕ}

/-! ## C. Finite boxes -/

/-- For `1 ≤ N`, the wiring induced on the box of radius `N` lies below the boundary clique. -/
lemma freeNestedInducedWiring_le_boundary {N m : ℕ}
    (hN : 1 ≤ N) (hNm : N < m)
    (ψ : ConfigSpace (Sym2 (boxVerts d m))) :
    ocd_inducedWiring (boxGraph d m) (boxVertInclLE d (le_of_lt hNm))
        (bdp_noBdry (Vout := boxVerts d m)) ψ ≤
      StatMech.Lattice.boundaryCliqueGraph (boxBoundary d N) := by
  exact ocd_latticeInducedWiring_le
    (boxVertInclLE d (le_of_lt hNm)) (cbk_boxVertInclLE_val _)
    (dfi_boxVertInclLE_injective d _) (bdp_noBdry (Vout := boxVerts d m))
    (boxBoundary d N) (fun _ h => h) (fun x z => flc_hbdryIn_box hN x z) ψ
/-- The wiring induced on the box of radius `N` lies below the boundary clique, for every `N`. -/
lemma freeNestedInducedWiring_le_boundary_all {N m : ℕ}
    (hNm : N < m) (ψ : ConfigSpace (Sym2 (boxVerts d m))) :
    ocd_inducedWiring (boxGraph d m) (boxVertInclLE d (le_of_lt hNm))
        (bdp_noBdry (Vout := boxVerts d m)) ψ ≤
      StatMech.Lattice.boundaryCliqueGraph (boxBoundary d N) := by
  cases N with
  | zero =>
      intro x y hxy
      have heq : x = y := by
        apply Subtype.ext
        funext i
        have hx : (x : Site d) i = 0 := Int.natAbs_eq_zero.mp (Nat.le_zero.mp (x.2 i))
        have hy : (y : Site d) i = 0 := Int.natAbs_eq_zero.mp (Nat.le_zero.mp (y.2 i))
        rw [hx, hy]
      exact (hxy.1 heq).elim
  | succ N =>
      exact freeNestedInducedWiring_le_boundary (Nat.succ_le_succ (Nat.zero_le N)) hNm ψ
/-- For `1 ≤ N`, a wiring of positive weight lies below the boundary clique. -/
lemma freeNestedWiringWeight_support {N m : ℕ}
    (hN : 1 ≤ N) (hNm : N < m) {p q : ℝ}
    (C : SimpleGraph (boxVerts d N))
    (hC : freeNestedWiringWeight (boxGraph d m)
      (boxVertInclLE d (le_of_lt hNm)) p q C ≠ 0) :
    C ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d N) := by
  classical
  by_contra hle
  apply hC
  unfold freeNestedWiringWeight
  apply Finset.sum_eq_zero
  intro ψ _
  rw [ite_eq_right]
  intro heq
  apply hle
  rw [← heq]
  exact freeNestedInducedWiring_le_boundary hN hNm ψ
/-- A wiring of positive weight lies below the boundary clique, for every `N`. -/
lemma freeNestedWiringWeight_support_all {N m : ℕ}
    (hNm : N < m) {p q : ℝ} (C : SimpleGraph (boxVerts d N))
    (hC : freeNestedWiringWeight (boxGraph d m)
      (boxVertInclLE d (le_of_lt hNm)) p q C ≠ 0) :
    C ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d N) := by
  classical
  by_contra hle
  apply hC
  unfold freeNestedWiringWeight
  apply Finset.sum_eq_zero
  intro ψ _
  rw [ite_eq_right]
  intro heq
  apply hle
  rw [← heq]
  exact freeNestedInducedWiring_le_boundary_all hNm ψ
/-- The marginal on the box of radius `N` of the free measure on a larger box is a wiring
mixture of boundary-condition measures. -/
lemma freeFiniteBox_marginal_eq_wiringMixture {N m : ℕ}
    (hNm : N < m) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q)
    (A : Set (ConfigSpace (Sym2 (boxVerts d N)))) : by
    classical
    exact
      (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A) =
        ∑ C : SimpleGraph (boxVerts d N),
          freeNestedWiringWeight (boxGraph d m)
            (boxVertInclLE d (le_of_lt hNm)) p q C *
            dlrBcEventMass (boxGraph d N) C p q A := by
  classical
  let T : Set (ConfigSpace (Sym2 (boxVerts d m))) :=
    boxRestrictLE d (le_of_lt hNm) ⁻¹' A
  have hevent : boxRestrict d N ⁻¹' A = boxRestrict d m ⁻¹' T := by
    ext ω
    simp only [T, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [hevent, freeFiniteMeasure_real_boxRestrictEvent m hp hp1
    (zero_lt_one.trans_le hq) T hmeas]
  have hrestrict :
      ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm)) =
        boxRestrictLE d (le_of_lt hNm) := rfl
  have hT : T = ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm)) ⁻¹' A := by
    change boxRestrictLE d (le_of_lt hNm) ⁻¹' A = _
    rw [← hrestrict]
  rw [hT]
  exact freeNestedMarginal_eq_wiringMixture (boxGraph d N) (boxGraph d m)
    (boxVertInclLE d (le_of_lt hNm)) (dfi_boxVertInclLE_injective d _)
    (cbk_adjMatch _) hp hp1 (zero_lt_one.trans_le hq) A
/-- The marginal on the box of radius `N` of the free measure on a larger box is a mixture of
boundary-condition measures whose wirings lie below the boundary clique. -/
theorem freeFiniteBox_marginal_specification {N m : ℕ}
    (hNm : N < m) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) : by
    classical
    exact ∃ weight : SimpleGraph (boxVerts d N) → ℝ,
        (∀ C, 0 ≤ weight C) ∧
        (∑ C, weight C = 1) ∧
        (∀ C, weight C ≠ 0 →
          C ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d N)) ∧
        ∀ A : Set (ConfigSpace (Sym2 (boxVerts d N))),
          (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
              (boxRestrict d N ⁻¹' A) =
            ∑ C, weight C * dlrBcEventMass (boxGraph d N) C p q A := by
  classical
  let weight : SimpleGraph (boxVerts d N) → ℝ :=
    freeNestedWiringWeight (boxGraph d m) (boxVertInclLE d (le_of_lt hNm)) p q
  refine ⟨weight, ?_, ?_, ?_, ?_⟩
  · intro C
    exact freeNestedWiringWeight_nonneg (boxGraph d m)
      (boxVertInclLE d (le_of_lt hNm)) hp hp1
        (zero_lt_one.trans_le hq) C
  · exact freeNestedWiringWeight_sum_eq_one (boxGraph d m)
      (boxVertInclLE d (le_of_lt hNm)) (dfi_boxVertInclLE_injective d _)
      hp hp1 (zero_lt_one.trans_le hq)
  · intro C hC
    exact freeNestedWiringWeight_support_all hNm C hC
  · intro A
    let T : Set (ConfigSpace (Sym2 (boxVerts d m))) :=
      boxRestrictLE d (le_of_lt hNm) ⁻¹' A
    have hevent : boxRestrict d N ⁻¹' A = boxRestrict d m ⁻¹' T := by
      ext ω
      simp only [T, Set.mem_preimage, boxRestrictLE_boxRestrict]
    have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
      (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
    rw [hevent, freeFiniteMeasure_real_boxRestrictEvent m hp hp1
      (zero_lt_one.trans_le hq) T hmeas]
    have hrestrict :
        ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm)) =
          boxRestrictLE d (le_of_lt hNm) := rfl
    have hT : T =
        ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm)) ⁻¹' A := by
      change boxRestrictLE d (le_of_lt hNm) ⁻¹' A = _
      rw [← hrestrict]
    rw [hT]
    simpa only [weight] using
      freeNestedMarginal_eq_wiringMixture (boxGraph d N) (boxGraph d m)
      (boxVertInclLE d (le_of_lt hNm)) (dfi_boxVertInclLE_injective d _)
      (cbk_adjMatch _) hp hp1 (zero_lt_one.trans_le hq) A

/-! ## D. The FK-DLR property in infinite volume -/

/-- For `q ≥ 1`, the free infinite-volume random-cluster measure on `ℤ^d` satisfies the FK-DLR
property. -/
theorem freeInfiniteVolume_isFKDLR {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) :
    IsFKDLR d p q
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)) := by
  classical
  intro N
  obtain ⟨φ, hφ, hconv⟩ :=
    freeInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  let radius : ℕ → ℕ := fun k => φ (N + 1 + k)
  have hradius : ∀ k, N < radius k := by
    intro k
    exact lt_of_lt_of_le (Nat.lt_add_one N)
      ((Nat.le_add_right (N + 1) k).trans (hφ.id_le (N + 1 + k)))
  let wiringSeq : ℕ → ProbabilityMeasure (SimpleGraph (boxVerts d N)) := fun k =>
    freeNestedWiringMeasure (boxGraph d (radius k))
      (boxVertInclLE d (le_of_lt (hradius k)))
      (dfi_boxVertInclLE_injective d _) hp hp1 (zero_lt_one.trans_le hq)
  obtain ⟨ν, τ, hτ, hwiring⟩ := CompactSpace.tendsto_subseq wiringSeq
  let weight : SimpleGraph (boxVerts d N) → ℝ :=
    fun C => (ν : Measure (SimpleGraph (boxVerts d N))).real {C}
  have hweight_tendsto (C : SimpleGraph (boxVerts d N)) :
      Tendsto (fun k => freeNestedWiringWeight (boxGraph d (radius (τ k)))
        (boxVertInclLE d (le_of_lt (hradius (τ k)))) p q C) atTop
        (𝓝 (weight C)) := by
    have hsingle := tendsto_probabilityMeasure_real_of_isClopen hwiring
      (isClopen_discrete ({C} : Set (SimpleGraph (boxVerts d N))))
    simpa only [wiringSeq, Function.comp_apply, weight,
      freeNestedWiringMeasure_real_singleton] using hsingle
  refine ⟨weight, ?_, ?_, ?_, ?_⟩
  · intro C
    exact measureReal_nonneg
  · change ∑ C : SimpleGraph (boxVerts d N),
        (ν : Measure (SimpleGraph (boxVerts d N))).real {C} = 1
    simpa using
      (sum_measureReal_singleton
        (μ := (ν : Measure (SimpleGraph (boxVerts d N))))
        (Finset.univ : Finset (SimpleGraph (boxVerts d N))))
  · intro C hC
    by_contra hle
    have hzero : ∀ k,
        freeNestedWiringWeight (boxGraph d (radius (τ k)))
          (boxVertInclLE d (le_of_lt (hradius (τ k)))) p q C = 0 := by
      intro k
      by_contra hnz
      exact hle (freeNestedWiringWeight_support_all (hradius (τ k)) C hnz)
    have hzero_tendsto : Tendsto (fun k => freeNestedWiringWeight
        (boxGraph d (radius (τ k)))
        (boxVertInclLE d (le_of_lt (hradius (τ k)))) p q C) atTop (𝓝 0) := by
      convert tendsto_const_nhds using 1
      funext k
      exact hzero k
    exact hC (tendsto_nhds_unique (hweight_tendsto C) hzero_tendsto)
  · intro A
    have hclopen : IsClopen (boxRestrict d N ⁻¹' A) :=
      isClopen_boxRestrict_preimage N A
    have houter0 := hconv.tendsto_real_of_isClopen hclopen
    have houter : Tendsto
        (fun k => (freeFiniteMeasure d (radius (τ k)) hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (boxRestrict d N ⁻¹' A)) atTop
        (𝓝 ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A))) := by
      have htail := houter0.comp (Filter.tendsto_add_atTop_nat (N + 1))
      have hsub := htail.comp hτ.tendsto_atTop
      refine hsub.congr fun k => ?_
      simp only [radius, Function.comp_apply, Nat.add_comm (τ k) (N + 1)]
    have hmix_tendsto : Tendsto
        (fun k => ∑ C : SimpleGraph (boxVerts d N),
          freeNestedWiringWeight (boxGraph d (radius (τ k)))
            (boxVertInclLE d (le_of_lt (hradius (τ k)))) p q C *
            dlrBcEventMass (boxGraph d N) C p q A) atTop
        (𝓝 (∑ C : SimpleGraph (boxVerts d N),
          weight C * dlrBcEventMass (boxGraph d N) C p q A)) := by
      simpa using
        (tendsto_finsetSum Finset.univ fun C _ =>
          (hweight_tendsto C).mul_const (dlrBcEventMass (boxGraph d N) C p q A))
    have heq : ∀ k,
        (freeFiniteMeasure d (radius (τ k)) hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (boxRestrict d N ⁻¹' A) =
          ∑ C : SimpleGraph (boxVerts d N),
            freeNestedWiringWeight (boxGraph d (radius (τ k)))
              (boxVertInclLE d (le_of_lt (hradius (τ k)))) p q C *
              dlrBcEventMass (boxGraph d N) C p q A := by
      intro k
      exact freeFiniteBox_marginal_eq_wiringMixture
        (hradius (τ k)) hp hp1 hq A
    exact tendsto_nhds_unique houter
      (hmix_tendsto.congr' (Eventually.of_forall fun k => (heq k).symm))

end FK

end StatMech
