/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolume
public import PhyslibExt.StatisticalMechanics.RandomCluster.TwoPoint
public import PhyslibExt.StatisticalMechanics.RandomCluster.Limits
public import MathlibExt.Probability.Configuration.MonotoneLimit
/-!
# Two-point functions of infinite-volume FK measures

Monotone limits of probabilities of increasing clopen events, restriction to a box, and
infinite-volume two-point functions as limits of box two-point functions.

## i. Overview

For a sequence of probability measures on a countable product of `Bool`, `ivTwoPointSup` and
`ivTwoPointInf` are the supremum and infimum of the masses of an event. If the sequence is
stochastically increasing (respectively decreasing) and the event is clopen and increasing, the
masses converge to the supremum (respectively infimum).

`boxRestrict d N` restricts a configuration of `ℤ^d` to the box `Λ_N`, and `boxConnEvent d N x y`
is the event that `x` and `y` are connected inside `Λ_N`. Its probability under the box measures
is the finite-volume two-point function. `freeIvTwoPoint` and `wiredIvTwoPoint` are the
supremum over free box measures and the infimum over wired box measures; they are limits under
the explicit hypothesis that the free (respectively wired) box measures form a stochastically
increasing (respectively decreasing) chain.

## ii. Key results

- `ivTwoPointInf_isLimit` : monotone limits along decreasing chains of measures (the increasing
  case is `tendsto_NNReal_of_monotone_isIncreasing`).
- `freeFiniteMeasure_real_boxConnEvent` : the box measure of `boxConnEvent` is `twoPointFun`.
- `freeIvTwoPoint`, `wiredIvTwoPoint` : infinite-volume two-point functions in `Λ_N`, with
  positivity (`freeIvTwoPoint_pos`) and limit statements (`freeIvTwoPoint_isLimit`,
  `wiredIvTwoPoint_isLimit`).

## iii. Table of contents

- A. Monotone limits along chains of measures
- B. Restriction to a box and box connection events
- C. Connection probabilities of the box measures
- D. Infinite-volume two-point functions

## iv. References

- G. R. Grimmett, *The Random-Cluster Model*, Springer, 2006.
-/

@[expose] public section

open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators NNReal Topology

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open StatMech.Lattice

variable {E : Type*} [Countable E]

/-!
## A. Monotone limits along chains of measures
-/

lemma bddAbove_range_apply (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) : BddAbove (Set.range (fun n => (μ n) A)) :=
  ⟨1, by rintro x ⟨n, rfl⟩; exact MeasureTheory.ProbabilityMeasure.apply_le_one _ _⟩

/-- The supremum over `n` of the masses `μ n A` of an event `A`. -/
noncomputable def ivTwoPointSup (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) : NNReal :=
  ⨆ n, (μ n) A

/-- The infimum over `n` of the masses `μ n A` of an event `A`. -/
noncomputable def ivTwoPointInf (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) : NNReal :=
  ⨅ n, (μ n) A

lemma le_ivTwoPointSup (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) (n : ℕ) : (μ n) A ≤ ivTwoPointSup μ A :=
  le_ciSup (bddAbove_range_apply μ A) n

lemma ivTwoPointInf_le (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) (n : ℕ) : ivTwoPointInf μ A ≤ (μ n) A :=
  ciInf_le (OrderBot.bddBelow _) n

lemma ivTwoPointSup_pos (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) {n : ℕ} (hn : 0 < (μ n) A) : 0 < ivTwoPointSup μ A :=
  lt_of_lt_of_le hn (le_ivTwoPointSup μ A n)

lemma ivTwoPointInf_pos_of_uniform (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) {c : NNReal} (hc : 0 < c) (hbound : ∀ n, c ≤ (μ n) A) :
    0 < ivTwoPointInf μ A :=
  lt_of_lt_of_le hc (le_ciInf hbound)

/-- Along a stochastically decreasing sequence of measures, the mass of a clopen increasing event
converges to its infimum. -/
lemma ivTwoPointInf_isLimit (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (hchain : ∀ n, (μ (n + 1) : Measure (ConfigSpace E)) ≼ (μ n : Measure (ConfigSpace E)))
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) :
    Tendsto (fun n => (μ n) A) atTop (𝓝 (ivTwoPointInf μ A)) := by
  have hAmeas := hAclopen.isOpen.measurableSet
  have hanti : Antitone (fun n => (μ n) A) := by
    apply antitone_nat_of_succ_le
    intro n
    have hreal : (μ (n + 1) : Measure (ConfigSpace E)).real A
        ≤ (μ n : Measure (ConfigSpace E)).real A := hchain n A hAmeas hAinc
    rw [MeasureTheory.ProbabilityMeasure.measureReal_eq_coe_coeFn,
      MeasureTheory.ProbabilityMeasure.measureReal_eq_coe_coeFn] at hreal
    exact_mod_cast hreal
  exact tendsto_atTop_ciInf hanti (OrderBot.bddBelow _)

/-!
## B. Restriction to a box and box connection events
-/

/-- Restriction of a configuration of `ℤ^d` to the edges of the box `Λ_n`. -/
def boxRestrict (d n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) :
    ConfigSpace (Sym2 (boxVerts d n)) :=
  fun eb => ω (edgeIncl d n eb)

lemma continuous_boxRestrict (d n : ℕ) : Continuous (boxRestrict d n) :=
  continuous_pi (fun eb => continuous_apply (edgeIncl d n eb))

lemma monotone_boxRestrict (d n : ℕ) : Monotone (boxRestrict d n) :=
  fun _ _ hab eb => hab (edgeIncl d n eb)

/-- Cylinder events of the box `Λ_N` are clopen. -/
lemma isClopen_boxRestrict_preimage {d : ℕ} (N : ℕ)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) : IsClopen (boxRestrict d N ⁻¹' S) :=
  IsClopen.preimage ⟨isClosed_discrete _, isOpen_discrete _⟩ (continuous_boxRestrict d N)

/-- Cylinder events of the box `Λ_N` are measurable. -/
lemma measurableSet_boxRestrict_preimage {d : ℕ} (N : ℕ)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) : MeasurableSet (boxRestrict d N ⁻¹' S) :=
  (isClopen_boxRestrict_preimage N S).isOpen.measurableSet

/-- The preimage of an increasing event under box restriction is increasing. -/
lemma isIncreasing_boxRestrict_preimage {d : ℕ} (N : ℕ)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    IsIncreasing (boxRestrict d N ⁻¹' S) :=
  fun _ _ hab ha => hS (monotone_boxRestrict d N hab) ha

/-- The event that `x` and `y` are joined by open edges inside the box `Λ_n`. -/
def boxConnEvent (d n : ℕ) (x y : boxVerts d n) : Set (ConfigSpace (Sym2 (Site d))) :=
  boxRestrict d n ⁻¹' (connEvent (boxGraph d n) x y)

lemma isClopen_boxConnEvent (d n : ℕ) (x y : boxVerts d n) :
    IsClopen (boxConnEvent d n x y) :=
  IsClopen.preimage ⟨isClosed_discrete _, isOpen_discrete _⟩ (continuous_boxRestrict d n)

lemma measurableSet_boxConnEvent (d n : ℕ) (x y : boxVerts d n) :
    MeasurableSet (boxConnEvent d n x y) :=
  (isClopen_boxConnEvent d n x y).isOpen.measurableSet

lemma isIncreasing_boxConnEvent (d n : ℕ) (x y : boxVerts d n) :
    IsIncreasing (boxConnEvent d n x y) :=
  fun _ _ hab ha => connEvent_isIncreasing (boxGraph d n) x y (monotone_boxRestrict d n hab) ha

lemma boxRestrict_extendEdge (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    boxRestrict d n (extendEdge d n ω) = ω := by
  funext eb
  unfold boxRestrict extendEdge
  have hmem : edgeIncl d n eb ∈ Set.range (edgeIncl d n) := ⟨eb, rfl⟩
  rw [dite_eq_left hmem]
  congr 1
  exact edgeIncl_injective d n hmem.choose_spec

lemma extendEdge_preimage_boxConnEvent (d n : ℕ) (x y : boxVerts d n) :
    extendEdge d n ⁻¹' (boxConnEvent d n x y) = connEvent (boxGraph d n) x y := by
  ext ω
  simp only [boxConnEvent, Set.mem_preimage, boxRestrict_extendEdge]

/-!
## C. Connection probabilities of the box measures
-/

/-- The free box measure of the connection event in `Λ_n` is the finite-volume two-point function.
-/
lemma freeFiniteMeasure_real_boxConnEvent (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x y : boxVerts d n) :
    (freeFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxConnEvent d n x y)
      = twoPointFun (boxGraph d n) p q x y := by
  have hA : MeasurableSet (boxConnEvent d n x y) := measurableSet_boxConnEvent d n x y
  have hfree : (freeFiniteMeasure d n hp hp1 hq : Measure _).real (boxConnEvent d n x y)
      = ((fkPMF (boxGraph d n) hp hp1 hq).toMeasure
          (extendEdge d n ⁻¹' (boxConnEvent d n x y))).toReal := by
    unfold freeFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d n) hA]
  rw [hfree, extendEdge_preimage_boxConnEvent, fkPMF_toMeasure_toReal]
  unfold twoPointFun
  exact Finset.sum_congr rfl fun ω _ => mul_comm _ _

/-- Every configuration has positive wired random-cluster probability. -/
lemma wiredFkProb_pos {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (bdry : V → Prop) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (ω : ConfigSpace (Sym2 V)) :
    0 < wiredFkProb G bdry p q ω := by
  classical
  exact div_pos (wiredFkWeight_pos G bdry hp hp1 hq ω) (wiredFkZ_pos G bdry hp hp1 hq)

lemma wiredFiniteMeasure_real_boxConnEvent (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x y : boxVerts d n) :
    (wiredFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxConnEvent d n x y)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (connEvent (boxGraph d n) x y).indicator (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  have hA : MeasurableSet (boxConnEvent d n x y) := measurableSet_boxConnEvent d n x y
  have hw : (wiredFiniteMeasure d n hp hp1 hq : Measure _).real (boxConnEvent d n x y)
      = ((wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq).toMeasure
          (extendEdge d n ⁻¹' (boxConnEvent d n x y))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d n) hA]
  rw [hw, extendEdge_preimage_boxConnEvent, wiredFkPMF_toMeasure_toReal]

lemma freeFiniteMeasure_apply_boxConnEvent_pos (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {x y : boxVerts d n}
    (h : (boxGraph d n).Reachable x y) :
    0 < (freeFiniteMeasure d n hp hp1 hq) (boxConnEvent d n x y) := by
  have hreal : 0 < (freeFiniteMeasure d n hp hp1 hq : Measure _).real (boxConnEvent d n x y) := by
    rw [freeFiniteMeasure_real_boxConnEvent]
    exact twoPointFun_pos_of_reachable (boxGraph d n) hp hp1 hq h
  rw [MeasureTheory.ProbabilityMeasure.measureReal_eq_coe_coeFn] at hreal
  exact_mod_cast hreal

lemma wiredFiniteMeasure_apply_boxConnEvent_pos (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {x y : boxVerts d n}
    (h : (boxGraph d n).Reachable x y) :
    0 < (wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d n x y) := by
  have hreal : 0 < (wiredFiniteMeasure d n hp hp1 hq : Measure _).real (boxConnEvent d n x y) := by
    rw [wiredFiniteMeasure_real_boxConnEvent]
    apply Finset.sum_pos'
    · intro ω _
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
        (wiredFkProb_pos (boxGraph d n) (boxBoundary d n) hp hp1 hq ω).le
    · refine ⟨fun _ => true, Finset.mem_univ _, ?_⟩
      rw [Set.indicator_of_mem (allOpen_mem_connEvent (boxGraph d n) h), one_mul]
      exact wiredFkProb_pos (boxGraph d n) (boxBoundary d n) hp hp1 hq _
  rw [MeasureTheory.ProbabilityMeasure.measureReal_eq_coe_coeFn] at hreal
  exact_mod_cast hreal

/-!
## D. Infinite-volume two-point functions
-/

/-- The free infinite-volume two-point function in `Λ_N`: the supremum over `n` of `φ⁰_n(x ↔ y in
Λ_N)`. -/
noncomputable def freeIvTwoPoint (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x y : boxVerts d N) : NNReal :=
  ivTwoPointSup (fun n => freeFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)

/-- The wired infinite-volume two-point function in `Λ_N`: the infimum over `n` of `φ¹_n(x ↔ y in
Λ_N)`. -/
noncomputable def wiredIvTwoPoint (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x y : boxVerts d N) : NNReal :=
  ivTwoPointInf (fun n => wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)

lemma freeIvTwoPoint_pos (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {x y : boxVerts d N}
    (h : (boxGraph d N).Reachable x y) :
    0 < freeIvTwoPoint d N hp hp1 hq x y :=
  ivTwoPointSup_pos _ _ (freeFiniteMeasure_apply_boxConnEvent_pos d N hp hp1 hq h)

lemma freeIvTwoPoint_self_pos (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x : boxVerts d N) :
    0 < freeIvTwoPoint d N hp hp1 hq x x :=
  freeIvTwoPoint_pos d N hp hp1 hq (SimpleGraph.Reachable.refl x)

lemma wiredIvTwoPoint_pos_of_uniform (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {x y : boxVerts d N} {c : NNReal} (hc : 0 < c)
    (hbound : ∀ n, c ≤ (wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)) :
    0 < wiredIvTwoPoint d N hp hp1 hq x y :=
  ivTwoPointInf_pos_of_uniform _ _ hc hbound

/-- If the free box measures increase stochastically in `n`, then `φ⁰_n(x ↔ y in Λ_N)` converges to
`freeIvTwoPoint`. -/
lemma freeIvTwoPoint_isLimit (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hchain : ∀ n, (freeFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
        ≼ (freeFiniteMeasure d (n + 1) hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))))
    (x y : boxVerts d N) :
    Tendsto (fun n => (freeFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)) atTop
      (𝓝 (freeIvTwoPoint d N hp hp1 hq x y)) :=
  tendsto_NNReal_of_monotone_isIncreasing hchain (isClopen_boxConnEvent d N x y)
    (isIncreasing_boxConnEvent d N x y)

/-- If the wired box measures decrease stochastically in `n`, then `φ¹_n(x ↔ y in Λ_N)` converges to
`wiredIvTwoPoint`. -/
lemma wiredIvTwoPoint_isLimit (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hchain : ∀ n, (wiredFiniteMeasure d (n + 1) hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
        ≼ (wiredFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))))
    (x y : boxVerts d N) :
    Tendsto (fun n => (wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)) atTop
      (𝓝 (wiredIvTwoPoint d N hp hp1 hq x y)) :=
  ivTwoPointInf_isLimit _ hchain (isClopen_boxConnEvent d N x y) (isIncreasing_boxConnEvent d N x y)

end FK

end StatMech
