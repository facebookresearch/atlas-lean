/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Exploration
public import MathlibExt.Probability.Percolation.OffClusterIndep
public import MathlibExt.Probability.Percolation.SurfaceReassembly
public import MathlibExt.Probability.Percolation.RSW.Defs
public import MathlibExt.Probability.CorrelationInequalities.Harris
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanExteriorClosure
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ClosedContourSeparation
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StraightWalk
public import MathlibExt.Probability.Percolation.Universality.CrossingTranslationInvariance
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LeftFillInteriorArc
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-!
# Lowest crossings and the RSW gluing at p = 1/2

The lowest-crossing exploration for critical bond percolation on `ℤ²`, the diagonal crossing events
of two adjacent rectangles, and the connector events that glue them into a horizontal crossing; it
proves the square-crossing bound `P(H) ≥ 1/2` and the diagonal bounds `≥ 1/32`.

## i. Overview

Crossing paths of a rectangle are finite, so open crossings are decomposed by first witnesses and by
lowest (highest) open diagonal paths, ranked by the size of the explored region. Reflections and the
rotation by `π` relate right and left diagonal events. The connector events of section F join a
right and a left diagonal path through the vertical axis; a dual reflection of the face-dual
configuration shows each has probability at least `1/2`, given the self-duality hypothesis `hdual`
of the `*_of_dual_reflection` lemmas. `rlc_square_half` and `rlc_half_rightDiagonal_unconditional` /
`rlc_half_leftDiagonal_unconditional` are unconditional. The `Rlc*Property` / `Rlc*Reachability`
predicates are hypotheses of intermediate lemmas, not proved here.

## ii. Key results

- `rlc_square_half`: `1/2 ≤ P(horizontal crossing of [0, m]²)` at `p = 1/2` (unconditional).
- `rlc_half_rightDiagonal_unconditional`: `1/32 ≤ P(right diagonal event)` (unconditional).
- `rlc_mixedWiredConnector_half_of_dual_reflection`: connector probability `≥ 1/2`, conditional on
  the dual-reflection hypothesis `hdual`.
- `rlc_mixedWiredConnector_glues_horizontal`: open diagonal paths plus a connector give a horizontal
  crossing of `[-2n, 2n] × [-n, n]`.

## iii. Table of contents

- A. Crossing paths and restricted events
- B. Reflections and diagonal events
- C. Diagonal paths and their regions
- D. Lowest and highest open paths
- E. Trace graphs of two paths
- F. Connectors across the axis
- G. Dual reflection

## iv. References

* L. Russo, *A note on percolation*, Z. Wahrsch. Verw. Gebiete 43 (1978); P. D. Seymour, D. J. A.
  Welsh, *Percolation probabilities on the square lattice*, Ann. Discrete Math. 3 (1978).
* V. Tassion, *Crossing probabilities for Voronoi percolation*, Ann. Probab. 44 (2016).
* H. Kesten, *The critical probability of bond percolation on the square lattice equals 1/2*, Comm.
  Math. Phys. 74 (1980).
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StatMech

namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box

variable {E : Type*}

/-! ## A. Crossing paths and restricted events -/

/-- An explicit lattice walk from a right-side site `z` back to a top-side site `x` of the rectangle
  `[0, 2n] × [-n, n]`, along its boundary. -/
noncomputable def rlc_cornerReturn {n : ℤ}
    (x : topSide 0 (2 * n) (-n) n)
    (z : rightSide 0 (2 * n) (-n) n) :
    (hypercubicLattice 2).Walk (z : Site 2) (x : Site 2) := by
  have hz0 : (z : Site 2) 0 = 2 * n := z.2.2
  have hx1 : (x : Site 2) 1 = n := x.2.2
  have hz1le : (z : Site 2) 1 ≤ n := by
    have hzSide := z.2
    rw [mem_rightSide, mem_rect] at hzSide
    exact hzSide.1.2.2.2
  have hx0le : (x : Site 2) 0 ≤ 2 * n := by
    have hxSide := x.2
    rw [mem_topSide, mem_rect] at hxSide
    exact hxSide.1.2.1
  have hzNat : ((n + 1 - (z : Site 2) 1).toNat : ℤ) =
      n + 1 - (z : Site 2) 1 := by
    rw [Int.toNat_of_nonneg (by omega)]
  have hxNat : ((2 * n + 1 - (x : Site 2) 0).toNat : ℤ) =
      2 * n + 1 - (x : Site 2) 0 := by
    rw [Int.toNat_of_nonneg (by omega)]
  let s1 : (hypercubicLattice 2).Walk (z : Site 2)
      ![2 * n + 1, (z : Site 2) 1] :=
    (jec_hsegRight ((z : Site 2) 1) (2 * n) 1).copy
      (by ext i; fin_cases i <;> simp [hz0])
      (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk
      ![2 * n + 1, (z : Site 2) 1] ![2 * n + 1, n + 1] :=
    (jec_vsegUp (2 * n + 1) ((z : Site 2) 1)
      (n + 1 - (z : Site 2) 1).toNat).copy rfl
      (by
        ext i
        fin_cases i
        · simp
        · simp [hzNat])
  let s3 : (hypercubicLattice 2).Walk
      ![(x : Site 2) 0, n + 1] ![2 * n + 1, n + 1] :=
    (jec_hsegRight (n + 1) ((x : Site 2) 0)
      (2 * n + 1 - (x : Site 2) 0).toNat).copy rfl
      (by
        ext i
        fin_cases i
        · simp [hxNat]
        · simp)
  let s4 : (hypercubicLattice 2).Walk
      ![(x : Site 2) 0, n] ![(x : Site 2) 0, n + 1] :=
    (jec_vsegUp ((x : Site 2) 0) n 1).copy rfl
      (by ext i; fin_cases i <;> simp)
  exact s1.append (s2.append (s3.reverse.append
    (s4.reverse.copy rfl (by
      ext i
      fin_cases i
      · simp
      · simpa using hx1.symm))))

lemma rlc_cornerReturn_support_inside {n : ℤ}
    (x : topSide 0 (2 * n) (-n) n)
    (z : rightSide 0 (2 * n) (-n) n) {p : Site 2}
    (hp : p ∈ (rlc_cornerReturn x z).support)
    (hpR : p ∈ rect 0 (2 * n) (-n) n) :
    p = (z : Site 2) ∨ p = (x : Site 2) := by
  have hz0 : (z : Site 2) 0 = 2 * n := z.2.2
  have hx1 : (x : Site 2) 1 = n := x.2.2
  have hz1le : (z : Site 2) 1 ≤ n := by
    have hzSide := z.2
    rw [mem_rightSide, mem_rect] at hzSide
    exact hzSide.1.2.2.2
  have hx0le : (x : Site 2) 0 ≤ 2 * n := by
    have hxSide := x.2
    rw [mem_topSide, mem_rect] at hxSide
    exact hxSide.1.2.1
  simp only [rlc_cornerReturn, SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse] at hp
  rcases hp with hp | hp | hp | hp
  · obtain ⟨hp1, hp0lo, hp0hi⟩ :=
      jec_hsegRight_support ((z : Site 2) 1) (2 * n) 1 hp
    rw [mem_rect] at hpR
    by_cases heq : p 0 = 2 * n
    · left
      funext i
      fin_cases i
      · simpa [hz0] using heq
      · simpa using hp1
    · omega
  · obtain ⟨hp0, _hp1lo, _hp1hi⟩ :=
      jec_vsegUp_support (2 * n + 1) ((z : Site 2) 1)
        (n + 1 - (z : Site 2) 1).toNat hp
    rw [mem_rect] at hpR
    omega
  · obtain ⟨hp1, _hp0lo, _hp0hi⟩ :=
      jec_hsegRight_support (n + 1) ((x : Site 2) 0)
        (2 * n + 1 - (x : Site 2) 0).toNat (by simpa using hp)
    rw [mem_rect] at hpR
    omega
  · obtain ⟨hp0, hp1lo, hp1hi⟩ :=
      jec_vsegUp_support ((x : Site 2) 0) n 1 (by simpa using hp)
    rw [mem_rect] at hpR
    right
    funext i
    fin_cases i
    · simpa using hp0
    · have hp1 : p 1 = n := by omega
      simpa [hx1] using hp1

lemma rlc_cornerReturn_rayCount_zero {n : ℤ}
    (x : topSide 0 (2 * n) (-n) n)
    (z : rightSide 0 (2 * n) (-n) n)
    (p : Site 2) (hpR : p ∈ rect 0 (2 * n) (-n) n) :
    jec_rayCount p (rlc_cornerReturn x z) = 0 := by
  have hz1le : (z : Site 2) 1 ≤ n := by
    have hzSide := z.2
    rw [mem_rightSide, mem_rect] at hzSide
    exact hzSide.1.2.2.2
  have hx0le : (x : Site 2) 0 ≤ 2 * n := by
    have hxSide := x.2
    rw [mem_topSide, mem_rect] at hxSide
    exact hxSide.1.2.1
  rw [mem_rect] at hpR
  simp only [rlc_cornerReturn, jec_rayCount_append, jec_rayCount_copy,
    jec_rayCount_reverse, jec_rayCount_hsegRight, jec_rayCount_vsegUp]
  split_ifs <;> omega

lemma rlc_ray_eq_below_right_of_avoids {n : ℤ}
    (t : rightSide 0 (2 * n) (-n) n) {a b : Site 2}
    (w : (hypercubicLattice 2).Walk a b)
    (hbox : ∀ p ∈ w.support, p ∈ rect 0 (2 * n) (-n) n)
    (havoid : (t : Site 2) ∉ w.support) :
    jec_rayCount (t : Site 2) w =
      crossCount (jec_belowSet ((t : Site 2) 1)) w := by
  classical
  rw [jec_rayCount, crossCount]
  refine List.countP_congr ?_
  intro e he
  obtain ⟨u, v⟩ := e
  have hadj : (hypercubicLattice 2).Adj u v := w.adj_of_mem_edges he
  have huSupp : u ∈ w.support := w.fst_mem_support_of_mem_edges he
  have hvSupp : v ∈ w.support := w.snd_mem_support_of_mem_edges he
  have huR := hbox u huSupp
  have hvR := hbox v hvSupp
  have ht0 : (t : Site 2) 0 = 2 * n := t.2.2
  simp only [decide_eq_true_eq]
  change jec_rayEdge (t : Site 2) s(u, v) ↔
    bdEdge (jec_belowSet ((t : Site 2) 1)) s(u, v)
  rw [jec_rayEdge_mk,
    jec_belowSet_bdEdge ((t : Site 2) 1) u v hadj]
  constructor
  · rintro ⟨⟨hcol, _hle⟩, hrow⟩
    exact ⟨hcol, hrow⟩
  · rintro ⟨hcol, hrow⟩
    refine ⟨⟨hcol, ?_⟩, hrow⟩
    rw [mem_rect] at huR hvR
    by_contra hle
    have hcolEq : u 0 = 2 * n := by omega
    rcases hrow with hrow | hrow
    · have hvEq : v = (t : Site 2) := by
        funext i
        fin_cases i
        · have hv0 : v 0 = 2 * n := by omega
          exact hv0.trans ht0.symm
        · exact hrow.2
      exact havoid (hvEq ▸ hvSupp)
    · have huEq : u = (t : Site 2) := by
        funext i
        fin_cases i
        · exact hcolEq.trans ht0.symm
        · exact hrow.2
      exact havoid (huEq ▸ huSupp)

-- The unused instance binder is part of the signature; removing it changes the statement.
set_option linter.unusedDecidableInType false in
lemma rlc_harris_cylinder {E : Type*} [Countable E] [DecidableEq E]
    (p : ℝ≥0) (hp : p ≤ 1) {A B : Set (ConfigSpace E)}
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B)
    (T U : Finset E)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (T : Set E))
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set E)) :
    (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B
      ≤ (bernoulliProductMeasure (E := E) p hp).real (A ∩ B) := by
  classical
  let F := T ∪ U
  have hAF : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E) :=
    hA.mono (by simp [F])
  have hBF : DependsOn (B.indicator (fun _ => (1 : ℝ))) (F : Set E) :=
    hB.mono (by simp [F])
  have hcylA : A = cylinder F (F.restrict '' A) :=
    eq_cylinder_restrict_image A F hAF
  have hcylB : B = cylinder F (F.restrict '' B) :=
    eq_cylinder_restrict_image B F hBF
  have hPA : (bernoulliProductMeasure (E := E) p hp).real A =
      (bernoulliProductMeasure (E := ↥F) p hp).real (F.restrict '' A) := by
    conv_lhs => rw [hcylA]
    rw [realProb_cylinder]
  have hPB : (bernoulliProductMeasure (E := E) p hp).real B =
      (bernoulliProductMeasure (E := ↥F) p hp).real (F.restrict '' B) := by
    conv_lhs => rw [hcylB]
    rw [realProb_cylinder]
  have hPAB : (bernoulliProductMeasure (E := E) p hp).real (A ∩ B) =
      (bernoulliProductMeasure (E := ↥F) p hp).real
        ((F.restrict '' A) ∩ (F.restrict '' B)) := by
    conv_lhs => rw [hcylA, hcylB, inter_cylinder_same]
    rw [realProb_cylinder]
  rw [hPA, hPB, hPAB]
  exact harris_inequality hp
    (isIncreasing_restrict_image A hAinc F)
    (isIncreasing_restrict_image B hBinc F)

-- The unused instance binder is part of the signature; removing it changes the statement.
set_option linter.unusedDecidableInType false in
lemma rlc_harris_three_cylinder {E : Type*} [Countable E] [DecidableEq E]
    (p : ℝ≥0) (hp : p ≤ 1) {A B C : Set (ConfigSpace E)}
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B) (hCinc : IsIncreasing C)
    (T U V : Finset E)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (T : Set E))
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set E))
    (hC : DependsOn (C.indicator (fun _ => (1 : ℝ))) (V : Set E)) :
    (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B
        * (bernoulliProductMeasure (E := E) p hp).real C
      ≤ (bernoulliProductMeasure (E := E) p hp).real (A ∩ B ∩ C) := by
  let μ := bernoulliProductMeasure (E := E) p hp
  have hAB : μ.real A * μ.real B ≤ μ.real (A ∩ B) :=
    rlc_harris_cylinder p hp hAinc hBinc T U hA hB
  have hABdep : DependsOn ((A ∩ B).indicator (fun _ => (1 : ℝ)))
      ((T ∪ U : Finset E) : Set E) := by
    simpa only [Finset.coe_union] using dependsOn_inter hA hB
  have hABC : μ.real (A ∩ B) * μ.real C ≤ μ.real (A ∩ B ∩ C) :=
    rlc_harris_cylinder p hp (hAinc.inter hBinc) hCinc (T ∪ U) V hABdep hC
  calc
    μ.real A * μ.real B * μ.real C
        ≤ μ.real (A ∩ B) * μ.real C :=
          mul_le_mul_of_nonneg_right hAB measureReal_nonneg
    _ ≤ μ.real (A ∩ B ∩ C) := hABC

-- The unused instance binder is part of the signature; removing it changes the statement.
set_option linter.unusedDecidableInType false in
lemma rlc_diagonal_event_lower_bound {E : Type*} [Countable E] [DecidableEq E]
    (p : ℝ≥0) (hp : p ≤ 1) (α : ℝ) (hα : 0 ≤ α)
    (A B C Diag : Set (ConfigSpace E))
    (T U V : Finset E)
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B) (hCinc : IsIncreasing C)
    (hAdep : DependsOn (A.indicator (fun _ => (1 : ℝ))) (T : Set E))
    (hBdep : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set E))
    (hCdep : DependsOn (C.indicator (fun _ => (1 : ℝ))) (V : Set E))
    (hAprob : α / 2 ≤ (bernoulliProductMeasure (E := E) p hp).real A)
    (hBprob : α / 2 ≤ (bernoulliProductMeasure (E := E) p hp).real B)
    (hCprob : α ≤ (bernoulliProductMeasure (E := E) p hp).real C)
    (hforce : A ∩ B ∩ C ⊆ Diag) :
    α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real Diag := by
  let μ := bernoulliProductMeasure (E := E) p hp
  have hfkg : μ.real A * μ.real B * μ.real C ≤ μ.real (A ∩ B ∩ C) :=
    rlc_harris_three_cylinder p hp hAinc hBinc hCinc T U V hAdep hBdep hCdep
  have hlower : (α / 2) * (α / 2) * α ≤ μ.real A * μ.real B * μ.real C := by
    have hAB : (α / 2) * (α / 2) ≤ μ.real A * μ.real B := by
      exact mul_le_mul hAprob hBprob (by positivity) measureReal_nonneg
    exact mul_le_mul hAB hCprob hα
      (mul_nonneg measureReal_nonneg measureReal_nonneg)
  calc
    α ^ 3 / 4 = (α / 2) * (α / 2) * α := by ring
    _ ≤ μ.real A * μ.real B * μ.real C := hlower
    _ ≤ μ.real (A ∩ B ∩ C) := hfkg
    _ ≤ μ.real Diag := measureReal_mono hforce

lemma rlc_connector_half_of_dual_reflection {E : Type*}
    (mu : Measure (ConfigSpace E)) [IsProbabilityMeasure mu]
    (sigma : ConfigSpace E → ConfigSpace E)
    (hsigma : MeasurePreserving sigma mu mu)
    (Connect : Set (ConfigSpace E)) (hConnect : MeasurableSet Connect)
    (hdual : Connectᶜ ⊆ sigma ⁻¹' Connect) :
    (1 : ℝ) / 2 ≤ mu.real Connect := by
  have hmono : mu.real Connectᶜ ≤ mu.real (sigma ⁻¹' Connect) :=
    measureReal_mono hdual
  have hpres : mu.real (sigma ⁻¹' Connect) = mu.real Connect :=
    hsigma.measureReal_preimage hConnect.nullMeasurableSet
  have hcompl : mu.real Connectᶜ = 1 - mu.real Connect := by
    rw [measureReal_compl hConnect, probReal_univ]
  rw [hpres, hcompl] at hmono
  linarith

lemma rlc_connector_half_of_dual_comparison {E : Type*}
    (mu : Measure (ConfigSpace E)) [IsProbabilityMeasure mu]
    (sigma : ConfigSpace E → ConfigSpace E)
    (hsigma : MeasurePreserving sigma mu mu)
    (Connect DualConnect : Set (ConfigSpace E))
    (hConnect : MeasurableSet Connect)
    (hDualConnect : MeasurableSet DualConnect)
    (hdual : Connectᶜ ⊆ sigma ⁻¹' DualConnect)
    (hcompare : mu.real DualConnect ≤ mu.real Connect) :
    (1 : ℝ) / 2 ≤ mu.real Connect := by
  have hmono : mu.real Connectᶜ ≤
      mu.real (sigma ⁻¹' DualConnect) :=
    measureReal_mono hdual
  have hpres : mu.real (sigma ⁻¹' DualConnect) =
      mu.real DualConnect :=
    hsigma.measureReal_preimage hDualConnect.nullMeasurableSet
  have hcompl : mu.real Connectᶜ = 1 - mu.real Connect := by
    rw [measureReal_compl hConnect, probReal_univ]
  rw [hpres, hcompl] at hmono
  linarith

/-- The first-witness decomposition: configurations in `W i` but in no `W j` with `j < i`. -/
def rlc_firstWitness {N : ℕ} (W : Fin N → Set (ConfigSpace E)) (i : Fin N) :
    Set (ConfigSpace E) :=
  W i \ ⋃ j : Fin N, ⋃ (_hji : j < i), W j

lemma rlc_mem_firstWitness_iff {N : ℕ} {W : Fin N → Set (ConfigSpace E)}
    {i : Fin N} {omega : ConfigSpace E} :
    omega ∈ rlc_firstWitness W i ↔
      omega ∈ W i ∧ ∀ j : Fin N, j < i → omega ∉ W j := by
  simp [rlc_firstWitness]

lemma rlc_firstWitness_pairwiseDisjoint {N : ℕ}
    (W : Fin N → Set (ConfigSpace E)) :
    Pairwise (Disjoint on rlc_firstWitness W) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · change Disjoint (rlc_firstWitness W i) (rlc_firstWitness W j)
    rw [Set.disjoint_left]
    intro omega hi hj
    exact (rlc_mem_firstWitness_iff.mp hj).2 i hij'
      (rlc_mem_firstWitness_iff.mp hi).1
  · change Disjoint (rlc_firstWitness W i) (rlc_firstWitness W j)
    rw [Set.disjoint_left]
    intro omega hi hj
    exact (rlc_mem_firstWitness_iff.mp hi).2 j hji'
      (rlc_mem_firstWitness_iff.mp hj).1

lemma rlc_iUnion_firstWitness {N : ℕ} (W : Fin N → Set (ConfigSpace E)) :
    (⋃ i, rlc_firstWitness W i) = ⋃ i, W i := by
  classical
  apply Set.Subset.antisymm
  · exact Set.iUnion_mono fun i => sdiff_subset
  · intro omega homega
    simp only [Set.mem_iUnion] at homega ⊢
    obtain ⟨i, hi⟩ := homega
    let P : ℕ → Prop := fun k => ∃ hk : k < N, omega ∈ W ⟨k, hk⟩
    have hP : ∃ k, P k := ⟨i, i.isLt, hi⟩
    let k := Nat.find hP
    have hk : P k := Nat.find_spec hP
    refine ⟨⟨k, hk.1⟩, rlc_mem_firstWitness_iff.mpr ⟨hk.2, ?_⟩⟩
    intro j hji hj
    have hmin : k ≤ j := Nat.find_min' hP ⟨j.isLt, hj⟩
    exact (not_le_of_gt hji) hmin

/-- The union of the supports `T j` over `j ≤ i`. -/
noncomputable def rlc_exploredSupport {N : ℕ} [DecidableEq E]
    (T : Fin N → Finset E) (i : Fin N) : Finset E :=
  (Finset.univ.filter fun j : Fin N => j ≤ i).biUnion T

lemma rlc_mem_exploredSupport {N : ℕ} [DecidableEq E]
    {T : Fin N → Finset E} {i j : Fin N} (hji : j ≤ i) {e : E} (he : e ∈ T j) :
    e ∈ rlc_exploredSupport T i := by
  classical
  simp only [rlc_exploredSupport, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨j, hji, he⟩

lemma rlc_firstWitness_dependsOn {N : ℕ} [DecidableEq E]
    (W : Fin N → Set (ConfigSpace E)) (T : Fin N → Finset E)
    (hW : ∀ i, DependsOn ((W i).indicator (fun _ => (1 : ℝ))) (T i : Set E))
    (i : Fin N) :
    DependsOn ((rlc_firstWitness W i).indicator (fun _ => (1 : ℝ)))
      (rlc_exploredSupport T i : Set E) := by
  intro omega omega' hagree
  have hwiff : ∀ j : Fin N, j ≤ i → (omega ∈ W j ↔ omega' ∈ W j) := by
    intro j hji
    apply indic_iff
    apply hW j
    intro e he
    exact hagree e (rlc_mem_exploredSupport hji he)
  have hfirst : omega ∈ rlc_firstWitness W i ↔ omega' ∈ rlc_firstWitness W i := by
    rw [rlc_mem_firstWitness_iff, rlc_mem_firstWitness_iff]
    constructor
    · rintro ⟨hi, hmin⟩
      refine ⟨(hwiff i le_rfl).mp hi, ?_⟩
      intro j hji hj'
      exact hmin j hji ((hwiff j hji.le).mpr hj')
    · rintro ⟨hi, hmin⟩
      refine ⟨(hwiff i le_rfl).mpr hi, ?_⟩
      intro j hji hj
      exact hmin j hji ((hwiff j hji.le).mp hj)
  by_cases hmem : omega ∈ rlc_firstWitness W i
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hfirst.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hfirst.mpr h))]

lemma rlc_firstWitness_inter_pairwiseDisjoint {N : ℕ}
    (W X : Fin N → Set (ConfigSpace E)) :
    Pairwise (Disjoint on fun i => rlc_firstWitness W i ∩ X i) := by
  intro i j hij
  exact (rlc_firstWitness_pairwiseDisjoint W hij).mono inter_subset_left inter_subset_left

lemma rlc_exploration_lower_bound {N : ℕ} [Countable E] [DecidableEq E]
    (p : ℝ≥0) (hp : p ≤ 1)
    (W X : Fin N → Set (ConfigSpace E))
    (T U : Fin N → Finset E) (Goal : Set (ConfigSpace E)) (c : ℝ)
    (_hc : 0 ≤ c)
    (hW : ∀ i, DependsOn ((W i).indicator (fun _ => (1 : ℝ))) (T i : Set E))
    (hX : ∀ i, DependsOn ((X i).indicator (fun _ => (1 : ℝ))) (U i : Set E))
    (hdisj : ∀ i, Disjoint (rlc_exploredSupport T i) (U i))
    (hprob : ∀ i, c ≤ (bernoulliProductMeasure (E := E) p hp).real (X i))
    (hglue : ∀ i, rlc_firstWitness W i ∩ X i ⊆ Goal) :
    c * (bernoulliProductMeasure (E := E) p hp).real (⋃ i, W i)
      ≤ (bernoulliProductMeasure (E := E) p hp).real Goal := by
  classical
  let mu := bernoulliProductMeasure (E := E) p hp
  let F : Fin N → Set (ConfigSpace E) := fun i => rlc_firstWitness W i ∩ X i
  have hfirstDep : ∀ i, DependsOn
      ((rlc_firstWitness W i).indicator (fun _ => (1 : ℝ)))
      (rlc_exploredSupport T i : Set E) :=
    fun i => rlc_firstWitness_dependsOn W T hW i
  have hfirstMeas : ∀ i, MeasurableSet (rlc_firstWitness W i) :=
    fun i => measurableSet_of_dependsOn (hfirstDep i)
  have hFMeas : ∀ i, MeasurableSet (F i) := by
    intro i
    exact (hfirstMeas i).inter (measurableSet_of_dependsOn (hX i))
  have hfactor : ∀ i, mu.real (F i) =
      mu.real (rlc_firstWitness W i) * mu.real (X i) := by
    intro i
    exact indep_cylinder_inf p hp _ _ _ _ (hdisj i) (hfirstDep i) (hX i)
  have hterm : ∀ i, c * mu.real (rlc_firstWitness W i) ≤ mu.real (F i) := by
    intro i
    rw [hfactor i, mul_comm c]
    exact mul_le_mul_of_nonneg_left (hprob i) measureReal_nonneg
  have hFsub : (⋃ i, F i) ⊆ Goal := by
    intro omega homega
    simp only [Set.mem_iUnion] at homega
    obtain ⟨i, hi⟩ := homega
    exact hglue i hi
  calc
    c * mu.real (⋃ i, W i)
        = c * ∑ i, mu.real (rlc_firstWitness W i) := by
          rw [← rlc_iUnion_firstWitness W,
            measureReal_iUnion_fintype (rlc_firstWitness_pairwiseDisjoint W) hfirstMeas]
    _ = ∑ i, c * mu.real (rlc_firstWitness W i) := by rw [Finset.mul_sum]
    _ ≤ ∑ i, mu.real (F i) := Finset.sum_le_sum fun i _ => hterm i
    _ = mu.real (⋃ i, F i) :=
      (measureReal_iUnion_fintype (rlc_firstWitness_inter_pairwiseDisjoint W X) hFMeas).symm
    _ ≤ mu.real Goal := measureReal_mono hFsub (measure_ne_top mu Goal)

-- The unused instance binder is part of the signature; removing it changes the statement.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
lemma rlc_stoppingPartition_lower_bound {I : Type*} [Fintype I]
    [Countable E] [DecidableEq E]
    (p : ℝ≥0) (hp : p ≤ 1)
    (H Goal : Set (ConfigSpace E))
    (Part X : I → Set (ConfigSpace E))
    (T U : I → Finset E) (c : ℝ) (_hc : 0 ≤ c)
    (hpart : (⋃ i, Part i) = H)
    (hpair : Pairwise (Disjoint on Part))
    (hPart : ∀ i, DependsOn ((Part i).indicator (fun _ => (1 : ℝ))) (T i : Set E))
    (hX : ∀ i, DependsOn ((X i).indicator (fun _ => (1 : ℝ))) (U i : Set E))
    (hdisj : ∀ i, Disjoint (T i) (U i))
    (hprob : ∀ i, c ≤ (bernoulliProductMeasure (E := E) p hp).real (X i))
    (hglue : ∀ i, Part i ∩ X i ⊆ Goal) :
    c * (bernoulliProductMeasure (E := E) p hp).real H
      ≤ (bernoulliProductMeasure (E := E) p hp).real Goal := by
  classical
  let mu := bernoulliProductMeasure (E := E) p hp
  let F : I → Set (ConfigSpace E) := fun i => Part i ∩ X i
  have hPartMeas : ∀ i, MeasurableSet (Part i) :=
    fun i => measurableSet_of_dependsOn (hPart i)
  have hXMeas : ∀ i, MeasurableSet (X i) :=
    fun i => measurableSet_of_dependsOn (hX i)
  have hFMeas : ∀ i, MeasurableSet (F i) :=
    fun i => (hPartMeas i).inter (hXMeas i)
  have hFpair : Pairwise (Disjoint on F) := by
    intro i j hij
    exact (hpair hij).mono inter_subset_left inter_subset_left
  have hfactor : ∀ i,
      mu.real (F i) = mu.real (Part i) * mu.real (X i) := by
    intro i
    exact indep_cylinder_inf p hp _ _ _ _ (hdisj i) (hPart i) (hX i)
  have hterm : ∀ i, c * mu.real (Part i) ≤ mu.real (F i) := by
    intro i
    rw [hfactor i, mul_comm c]
    exact mul_le_mul_of_nonneg_left (hprob i) measureReal_nonneg
  have hFsub : (⋃ i, F i) ⊆ Goal := by
    intro omega homega
    simp only [Set.mem_iUnion] at homega
    obtain ⟨i, hi⟩ := homega
    exact hglue i hi
  calc
    c * mu.real H = c * ∑ i, mu.real (Part i) := by
      rw [← hpart, measureReal_iUnion_fintype hpair hPartMeas]
    _ = ∑ i, c * mu.real (Part i) := by rw [Finset.mul_sum]
    _ ≤ ∑ i, mu.real (F i) := Finset.sum_le_sum fun i _ => hterm i
    _ = mu.real (⋃ i, F i) :=
      (measureReal_iUnion_fintype hFpair hFMeas).symm
    _ ≤ mu.real Goal := measureReal_mono hFsub (measure_ne_top mu Goal)

-- The unused instance binder is part of the signature; removing it changes the statement.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
lemma rlc_bernoulli_rsw_stopping_sixth_power
    {I : Type*} [Fintype I] [Countable E] [DecidableEq E]
    (p : ℝ≥0) (hp : p ≤ 1) (α : ℝ) (hα : 0 ≤ α)
    (E₀ E₁ Goal : Set (ConfigSpace E))
    (S₀ S₁ : Finset E)
    (hE₀inc : IsIncreasing E₀) (hE₁inc : IsIncreasing E₁)
    (hE₀dep : DependsOn (E₀.indicator (fun _ => (1 : ℝ))) (S₀ : Set E))
    (hE₁dep : DependsOn (E₁.indicator (fun _ => (1 : ℝ))) (S₁ : Set E))
    (hE₀prob : α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real E₀)
    (hE₁prob : α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real E₁)
    (Part X : I → Set (ConfigSpace E))
    (T U : I → Finset E)
    (hpart : (⋃ i, Part i) = E₀ ∩ E₁)
    (hpair : Pairwise (Disjoint on Part))
    (hPart : ∀ i, DependsOn ((Part i).indicator (fun _ => (1 : ℝ))) (T i : Set E))
    (hX : ∀ i, DependsOn ((X i).indicator (fun _ => (1 : ℝ))) (U i : Set E))
    (hdisj : ∀ i, Disjoint (T i) (U i))
    (hconnector : ∀ i, (1 : ℝ) / 2 ≤
      (bernoulliProductMeasure (E := E) p hp).real (X i))
    (hglue : ∀ i, Part i ∩ X i ⊆ Goal) :
    α ^ 6 / 32 ≤ (bernoulliProductMeasure (E := E) p hp).real Goal := by
  let μ := bernoulliProductMeasure (E := E) p hp
  have hdiag : μ.real E₀ * μ.real E₁ ≤ μ.real (E₀ ∩ E₁) :=
    rlc_harris_cylinder p hp hE₀inc hE₁inc S₀ S₁ hE₀dep hE₁dep
  have hdiagLower : (α ^ 3 / 4) * (α ^ 3 / 4) ≤ μ.real E₀ * μ.real E₁ := by
    exact mul_le_mul hE₀prob hE₁prob (by positivity) measureReal_nonneg
  have hexplore : (1 : ℝ) / 2 * μ.real (E₀ ∩ E₁) ≤ μ.real Goal :=
    rlc_stoppingPartition_lower_bound p hp (E₀ ∩ E₁) Goal Part X T U (1 / 2)
      (by norm_num) hpart hpair hPart hX hdisj hconnector hglue
  calc
    α ^ 6 / 32 = (1 : ℝ) / 2 * ((α ^ 3 / 4) * (α ^ 3 / 4)) := by ring
    _ ≤ (1 : ℝ) / 2 * (μ.real E₀ * μ.real E₁) :=
      mul_le_mul_of_nonneg_left hdiagLower (by norm_num)
    _ ≤ (1 : ℝ) / 2 * μ.real (E₀ ∩ E₁) :=
      mul_le_mul_of_nonneg_left hdiag (by norm_num)
    _ ≤ μ.real Goal := hexplore

lemma rlc_bernoulli_rsw_sixth_power {N : ℕ} [Countable E] [DecidableEq E]
    (p : ℝ≥0) (hp : p ≤ 1) (α : ℝ) (hα : 0 ≤ α)
    (E₀ E₁ Goal : Set (ConfigSpace E))
    (S₀ S₁ : Finset E)
    (hE₀inc : IsIncreasing E₀) (hE₁inc : IsIncreasing E₁)
    (hE₀dep : DependsOn (E₀.indicator (fun _ => (1 : ℝ))) (S₀ : Set E))
    (hE₁dep : DependsOn (E₁.indicator (fun _ => (1 : ℝ))) (S₁ : Set E))
    (hE₀prob : α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real E₀)
    (hE₁prob : α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real E₁)
    (W X : Fin N → Set (ConfigSpace E))
    (T U : Fin N → Finset E)
    (hpartition : (⋃ i, W i) = E₀ ∩ E₁)
    (hW : ∀ i, DependsOn ((W i).indicator (fun _ => (1 : ℝ))) (T i : Set E))
    (hX : ∀ i, DependsOn ((X i).indicator (fun _ => (1 : ℝ))) (U i : Set E))
    (hdisj : ∀ i, Disjoint (rlc_exploredSupport T i) (U i))
    (hconnector : ∀ i, (1 : ℝ) / 2 ≤
      (bernoulliProductMeasure (E := E) p hp).real (X i))
    (hglue : ∀ i, rlc_firstWitness W i ∩ X i ⊆ Goal) :
    α ^ 6 / 32 ≤ (bernoulliProductMeasure (E := E) p hp).real Goal := by
  let μ := bernoulliProductMeasure (E := E) p hp
  have hdiag : μ.real E₀ * μ.real E₁ ≤ μ.real (E₀ ∩ E₁) :=
    rlc_harris_cylinder p hp hE₀inc hE₁inc S₀ S₁ hE₀dep hE₁dep
  have hdiagLower : (α ^ 3 / 4) * (α ^ 3 / 4) ≤ μ.real E₀ * μ.real E₁ := by
    exact mul_le_mul hE₀prob hE₁prob (by positivity) measureReal_nonneg
  have hexplore : (1 : ℝ) / 2 * μ.real (E₀ ∩ E₁) ≤ μ.real Goal := by
    rw [← hpartition]
    exact rlc_exploration_lower_bound p hp W X T U Goal (1 / 2)
      (by norm_num) hW hX hdisj hconnector hglue
  calc
    α ^ 6 / 32 = (1 : ℝ) / 2 * ((α ^ 3 / 4) * (α ^ 3 / 4)) := by ring
    _ ≤ (1 : ℝ) / 2 * (μ.real E₀ * μ.real E₁) := by
      exact mul_le_mul_of_nonneg_left hdiagLower (by norm_num)
    _ ≤ (1 : ℝ) / 2 * μ.real (E₀ ∩ E₁) := by
      exact mul_le_mul_of_nonneg_left hdiag (by norm_num)
    _ ≤ μ.real Goal := hexplore

/-- The finite rectangle `rect a b c d` as a `Fintype`. -/
noncomputable instance rlc_rectFintype (a b c d : ℤ) : Fintype (rect a b c d) :=
  (rect_finite a b c d).fintype

/-- The finite rectangle `rect a b c d` as a `Finset` of sites. -/
noncomputable def rlc_rectFinset (a b c d : ℤ) : Finset (Site 2) :=
  (rect_finite a b c d).toFinset

@[simp] lemma rlc_mem_rectFinset {a b c d : ℤ} {x : Site 2} :
    x ∈ rlc_rectFinset a b c d ↔ x ∈ rect a b c d := by
  simp [rlc_rectFinset]

/-- The sites of the rectangle on the vertical line `x = x₀` with height in `[lo, hi]`. -/
noncomputable def rlc_verticalSegment (a b c d x₀ lo hi : ℤ) :
    Finset (rect a b c d) :=
  Finset.univ.filter fun z : rect a b c d =>
    (z : Site 2) 0 = x₀ ∧ lo ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ hi

@[simp] lemma rlc_mem_verticalSegment {a b c d x₀ lo hi : ℤ}
    {z : rect a b c d} :
    z ∈ rlc_verticalSegment a b c d x₀ lo hi ↔
      (z : Site 2) 0 = x₀ ∧ lo ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ hi := by
  simp [rlc_verticalSegment]

/-- The event that some site of `P` is connected to some site of `Q` by an open path inside the
  rectangle. -/
def rlc_betweenEvent {a b c d : ℤ} (P Q : Finset (rect a b c d)) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x : ↥P, ∃ y : ↥Q,
    ConnectedWithin 2 omega (rect a b c d) x.1 y.1}

lemma rlc_betweenEvent_isIncreasing {a b c d : ℤ}
    (P Q : Finset (rect a b c d)) : IsIncreasing (rlc_betweenEvent P Q) := by
  intro omega omega' homega
  rintro ⟨x, y, hxy⟩
  exact ⟨x, y, StatMech.TwoDim.connectedWithin_mono homega hxy⟩

lemma rlc_betweenEvent_dependsOn {a b c d : ℤ}
    (P Q : Finset (rect a b c d)) :
    DependsOn ((rlc_betweenEvent P Q).indicator (fun _ => (1 : ℝ)))
      (StatMech.Percolation.edgesWithinFinset (rlc_rectFinset a b c d) :
        Set (Sym2 (Site 2))) := by
  intro omega omega' hagree
  have hcoord : ∀ u v : Site 2, u ∈ rect a b c d → v ∈ rect a b c d →
      omega s(u, v) = omega' s(u, v) := by
    intro u v hu hv
    apply hagree
    change s(u, v) ∈ StatMech.Percolation.edgesWithinFinset (rlc_rectFinset a b c d)
    rw [StatMech.Percolation.mem_edgesWithinFinset]
    exact ⟨u, by simpa using hu, v, by simpa using hv, rfl⟩
  have hG : openSubgraphInduce 2 omega (rect a b c d) =
      openSubgraphInduce 2 omega' (rect a b c d) := by
    apply SimpleGraph.ext
    ext u v
    simp only [openSubgraphInduce_adj, openSubgraph_adj]
    rw [hcoord u v u.2 v.2]
  have hiff : omega ∈ rlc_betweenEvent P Q ↔ omega' ∈ rlc_betweenEvent P Q := by
    simp only [rlc_betweenEvent, Set.mem_ofPred_eq, ConnectedWithin, hG]
  by_cases hmem : omega ∈ rlc_betweenEvent P Q
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hiff.mpr h))]

lemma rlc_betweenEvent_measurableSet {a b c d : ℤ}
    (P Q : Finset (rect a b c d)) : MeasurableSet (rlc_betweenEvent P Q) :=
  measurableSet_of_dependsOn (rlc_betweenEvent_dependsOn P Q)

/-- Self-avoiding lattice paths inside the rectangle from a site of `P` to a site of `Q`. -/
abbrev RlcBetweenPath {a b c d : ℤ} (P Q : Finset (rect a b c d)) :=
  Σ x : ↥P, Σ y : ↥Q,
    ((hypercubicLattice 2).induce (rect a b c d)).Path x.1 y.1

/-- There are finitely many paths between `P` and `Q` inside the rectangle. -/
noncomputable instance rlc_betweenPathFintype {a b c d : ℤ}
    (P Q : Finset (rect a b c d)) : Fintype (RlcBetweenPath P Q) := by
  classical
  unfold RlcBetweenPath
  infer_instance

/-- The edges of a path between `P` and `Q`, as edges of `ℤ²`. -/
noncomputable def rlc_betweenPathEdges {a b c d : ℤ}
    {P Q : Finset (rect a b c d)} (gamma : RlcBetweenPath P Q) :
    Finset (Sym2 (Site 2)) :=
  gamma.2.2.1.edges.toFinset.image (Sym2.map Subtype.val)

/-- The event that every edge of the given path is open. -/
def rlc_betweenPathOpen {a b c d : ℤ} {P Q : Finset (rect a b c d)}
    (gamma : RlcBetweenPath P Q) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∀ e ∈ rlc_betweenPathEdges gamma, omega e = true}

lemma rlc_betweenPathOpen_dependsOn {a b c d : ℤ}
    {P Q : Finset (rect a b c d)} (gamma : RlcBetweenPath P Q) :
    DependsOn ((rlc_betweenPathOpen gamma).indicator (fun _ => (1 : ℝ)))
      (rlc_betweenPathEdges gamma : Set (Sym2 (Site 2))) := by
  intro omega omega' hagree
  have hiff : omega ∈ rlc_betweenPathOpen gamma ↔
      omega' ∈ rlc_betweenPathOpen gamma := by
    constructor
    · intro h e he
      rw [← hagree e he]
      exact h e he
    · intro h e he
      rw [hagree e he]
      exact h e he
  by_cases hmem : omega ∈ rlc_betweenPathOpen gamma
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hiff.mpr h))]

/-- The left side of a rectangle is finite. -/
noncomputable instance rlc_leftSideFintype (a b c d : ℤ) :
    Fintype (leftSide a b c d) :=
  ((rect_finite a b c d).subset leftSide_subset).fintype

/-- The right side of a rectangle is finite. -/
noncomputable instance rlc_rightSideFintype (a b c d : ℤ) :
    Fintype (rightSide a b c d) :=
  ((rect_finite a b c d).subset rightSide_subset).fintype

/-- Self-avoiding lattice paths inside the rectangle from its left side to its right side. -/
abbrev RlcCrossingPath (a b c d : ℤ) :=
  Σ x : leftSide a b c d, Σ y : rightSide a b c d,
    ((hypercubicLattice 2).induce (rect a b c d)).Path
      ⟨(x : Site 2), leftSide_subset x.2⟩
      ⟨(y : Site 2), rightSide_subset y.2⟩

/-- There are finitely many left-right crossing paths of a rectangle. -/
noncomputable instance rlc_crossingPathFintype (a b c d : ℤ) :
    Fintype (RlcCrossingPath a b c d) := by
  classical
  unfold RlcCrossingPath
  infer_instance

/-- The edges of a crossing path, as edges of `ℤ²`. -/
noncomputable def rlc_pathEdges {a b c d : ℤ} (gamma : RlcCrossingPath a b c d) :
    Finset (Sym2 (Site 2)) :=
  gamma.2.2.1.edges.toFinset.image (Sym2.map Subtype.val)

/-- The event that every edge of the crossing path is open. -/
def rlc_pathOpen {a b c d : ℤ} (gamma : RlcCrossingPath a b c d) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∀ e ∈ rlc_pathEdges gamma, omega e = true}

lemma rlc_pathOpen_dependsOn {a b c d : ℤ} (gamma : RlcCrossingPath a b c d) :
    DependsOn ((rlc_pathOpen gamma).indicator (fun _ => (1 : ℝ)))
      (rlc_pathEdges gamma : Set (Sym2 (Site 2))) := by
  intro omega omega' hagree
  have hiff : omega ∈ rlc_pathOpen gamma ↔ omega' ∈ rlc_pathOpen gamma := by
    constructor
    · intro h e he
      rw [← hagree e he]
      exact h e he
    · intro h e he
      rw [hagree e he]
      exact h e he
  by_cases hmem : omega ∈ rlc_pathOpen gamma
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hiff.mpr h))]

lemma rlc_pathOpen_measurableSet {a b c d : ℤ} (gamma : RlcCrossingPath a b c d) :
    MeasurableSet (rlc_pathOpen gamma) :=
  measurableSet_of_dependsOn (rlc_pathOpen_dependsOn gamma)

/-- A walk in the induced rectangle graph all of whose edges are open, viewed as a walk in the open
  subgraph. -/
noncomputable def rlc_openWalkOfEdges {a b c d : ℤ}
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : rect a b c d}
    (w : ((hypercubicLattice 2).induce (rect a b c d)).Walk u v)
    (hopen : ∀ e ∈ w.edges.toFinset.image (Sym2.map Subtype.val),
      omega e = true) :
    (openSubgraphInduce 2 omega (rect a b c d)).Walk u v := by
  induction w with
  | nil => exact .nil
  | @cons u v z huv w ih =>
    apply SimpleGraph.Walk.cons
    · rw [openSubgraphInduce_adj, openSubgraph_adj]
      constructor
      · exact huv
      · apply hopen
        simp
    · apply ih
      intro e he
      apply hopen
      simp only [SimpleGraph.Walk.edges_cons, List.toFinset_cons,
        Finset.image_insert, Finset.mem_insert]
      exact Or.inr he

lemma rlc_iUnion_pathOpen (a b c d : ℤ) :
    (⋃ gamma : RlcCrossingPath a b c d, rlc_pathOpen gamma) =
      horizontalCrossingEvent a b c d := by
  ext omega
  constructor
  · intro h
    simp only [Set.mem_iUnion] at h
    obtain ⟨gamma, hgamma⟩ := h
    refine ⟨gamma.1, gamma.2.1, ⟨rlc_openWalkOfEdges omega gamma.2.2.1 ?_⟩⟩
    change ∀ e ∈ gamma.2.2.1.edges.toFinset.image (Sym2.map Subtype.val),
      omega e = true at hgamma
    exact hgamma
  · rintro ⟨x, y, hxy⟩
    let q0 := hxy.some
    have hle : openSubgraphInduce 2 omega (rect a b c d) ≤
        (hypercubicLattice 2).induce (rect a b c d) := by
      intro u v huv
      rw [openSubgraphInduce_adj, openSubgraph_adj] at huv
      exact huv.1
    let q := q0.mapLe hle
    let gamma : RlcCrossingPath a b c d := ⟨x, y, q.toPath⟩
    simp only [Set.mem_iUnion]
    refine ⟨gamma, ?_⟩
    intro e he
    simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset] at he
    obtain ⟨z, hz, rfl⟩ := he
    have hzq : z ∈ q.edges := q.edges_toPath_subset_edges hz
    have hedge : q.edges = q0.edges := SimpleGraph.Walk.edges_mapLe_eq_edges hle q0
    have hzq0 : z ∈ q0.edges := hedge ▸ hzq
    induction z using Sym2.inductionOn with
    | _ u v =>
      have hadj := q0.adj_of_mem_edges hzq0
      rw [openSubgraphInduce_adj, openSubgraph_adj] at hadj
      simpa using hadj.2

lemma rlc_iUnion_betweenPathOpen {a b c d : ℤ}
    (P Q : Finset (rect a b c d)) :
    (⋃ gamma : RlcBetweenPath P Q, rlc_betweenPathOpen gamma) =
      rlc_betweenEvent P Q := by
  ext omega
  constructor
  · intro h
    simp only [Set.mem_iUnion] at h
    obtain ⟨gamma, hgamma⟩ := h
    refine ⟨gamma.1, gamma.2.1, ⟨rlc_openWalkOfEdges omega gamma.2.2.1 ?_⟩⟩
    change ∀ e ∈ gamma.2.2.1.edges.toFinset.image (Sym2.map Subtype.val),
      omega e = true at hgamma
    exact hgamma
  · rintro ⟨x, y, hxy⟩
    let q0 := hxy.some
    have hle : openSubgraphInduce 2 omega (rect a b c d) ≤
        (hypercubicLattice 2).induce (rect a b c d) := by
      intro u v huv
      rw [openSubgraphInduce_adj, openSubgraph_adj] at huv
      exact huv.1
    let q := q0.mapLe hle
    let gamma : RlcBetweenPath P Q := ⟨x, y, q.toPath⟩
    simp only [Set.mem_iUnion]
    refine ⟨gamma, ?_⟩
    intro e he
    simp only [rlc_betweenPathEdges, Finset.mem_image, List.mem_toFinset] at he
    obtain ⟨z, hz, rfl⟩ := he
    have hzq : z ∈ q.edges := q.edges_toPath_subset_edges hz
    have hedge : q.edges = q0.edges := SimpleGraph.Walk.edges_mapLe_eq_edges hle q0
    have hzq0 : z ∈ q0.edges := hedge ▸ hzq
    induction z using Sym2.inductionOn with
    | _ u v =>
      have hadj := q0.adj_of_mem_edges hzq0
      rw [openSubgraphInduce_adj, openSubgraph_adj] at hadj
      simpa using hadj.2

lemma rlc_verticalCrossingEvent_dependsOn (a b c d : ℤ) :
    DependsOn ((verticalCrossingEvent a b c d).indicator (fun _ => (1 : ℝ)))
      (edgesWithinFinset (rect_finite a b c d).toFinset : Set (Sym2 (Site 2))) := by
  let S := (rect_finite a b c d).toFinset
  have hSco : (S : Set (Site 2)) = rect a b c d := by
    ext z
    simp [S]
  intro omega omega' hagree
  have hconn : ∀ (x y : Site 2),
      (∃ (hx : x ∈ rect a b c d) (hy : y ∈ rect a b c d),
        ConnectedWithin 2 omega (rect a b c d) ⟨x, hx⟩ ⟨y, hy⟩) ↔
      (∃ (hx : x ∈ rect a b c d) (hy : y ∈ rect a b c d),
        ConnectedWithin 2 omega' (rect a b c d) ⟨x, hx⟩ ⟨y, hy⟩) := by
    intro x y
    rw [← hSco]
    exact withinConn_congr S x y hagree
  have hevent : omega ∈ verticalCrossingEvent a b c d ↔
      omega' ∈ verticalCrossingEvent a b c d := by
    constructor
    · rintro ⟨x, y, hxy⟩
      have hc : ∃ (hx' : (x : Site 2) ∈ rect a b c d)
          (hy' : (y : Site 2) ∈ rect a b c d),
          ConnectedWithin 2 omega (rect a b c d) ⟨x, hx'⟩ ⟨y, hy'⟩ :=
        ⟨bottomSide_subset x.2, topSide_subset y.2, hxy⟩
      obtain ⟨_, _, hc'⟩ := (hconn x y).mp hc
      exact ⟨x, y, hc'⟩
    · rintro ⟨x, y, hxy⟩
      have hc : ∃ (hx' : (x : Site 2) ∈ rect a b c d)
          (hy' : (y : Site 2) ∈ rect a b c d),
          ConnectedWithin 2 omega' (rect a b c d) ⟨x, hx'⟩ ⟨y, hy'⟩ :=
        ⟨bottomSide_subset x.2, topSide_subset y.2, hxy⟩
      obtain ⟨_, _, hc'⟩ := (hconn x y).mpr hc
      exact ⟨x, y, hc'⟩
  by_cases hmem : omega ∈ verticalCrossingEvent a b c d
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]

/-- The event of an open left-right crossing of the rectangle that starts in `L` and ends in `R`. -/
def rlc_lrRestrictedEvent (a b c d : ℤ) (L R : Set (Site 2)) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ (x : leftSide a b c d) (y : rightSide a b c d),
    (x : Site 2) ∈ L ∧ (y : Site 2) ∈ R ∧
    ConnectedWithin 2 omega (rect a b c d)
      ⟨(x : Site 2), leftSide_subset x.2⟩
      ⟨(y : Site 2), rightSide_subset y.2⟩}

lemma rlc_lrRestrictedEvent_isIncreasing (a b c d : ℤ) (L R : Set (Site 2)) :
    IsIncreasing (rlc_lrRestrictedEvent a b c d L R) := by
  intro omega omega' homega hle
  obtain ⟨x, y, hx, hy, hxy⟩ := hle
  exact ⟨x, y, hx, hy, StatMech.TwoDim.connectedWithin_mono homega hxy⟩

lemma rlc_lrRestrictedEvent_dependsOn (a b c d : ℤ) (L R : Set (Site 2)) :
    DependsOn ((rlc_lrRestrictedEvent a b c d L R).indicator
      (fun _ => (1 : ℝ)))
      (edgesWithinFinset (rect_finite a b c d).toFinset : Set (Sym2 (Site 2))) := by
  let S := (rect_finite a b c d).toFinset
  have hSco : (S : Set (Site 2)) = rect a b c d := by
    ext z
    simp [S]
  intro omega omega' hagree
  have hconn : ∀ (x y : Site 2),
      (∃ (hx : x ∈ rect a b c d) (hy : y ∈ rect a b c d),
        ConnectedWithin 2 omega (rect a b c d) ⟨x, hx⟩ ⟨y, hy⟩) ↔
      (∃ (hx : x ∈ rect a b c d) (hy : y ∈ rect a b c d),
        ConnectedWithin 2 omega' (rect a b c d) ⟨x, hx⟩ ⟨y, hy⟩) := by
    intro x y
    rw [← hSco]
    exact withinConn_congr S x y hagree
  have hevent : omega ∈ rlc_lrRestrictedEvent a b c d L R ↔
      omega' ∈ rlc_lrRestrictedEvent a b c d L R := by
    constructor
    · rintro ⟨x, y, hx, hy, hxy⟩
      have hc : ∃ (hx' : (x : Site 2) ∈ rect a b c d)
          (hy' : (y : Site 2) ∈ rect a b c d),
          ConnectedWithin 2 omega (rect a b c d) ⟨x, hx'⟩ ⟨y, hy'⟩ :=
        ⟨leftSide_subset x.2, rightSide_subset y.2, hxy⟩
      obtain ⟨_, _, hc'⟩ := (hconn x y).mp hc
      exact ⟨x, y, hx, hy, hc'⟩
    · rintro ⟨x, y, hx, hy, hxy⟩
      have hc : ∃ (hx' : (x : Site 2) ∈ rect a b c d)
          (hy' : (y : Site 2) ∈ rect a b c d),
          ConnectedWithin 2 omega' (rect a b c d) ⟨x, hx'⟩ ⟨y, hy'⟩ :=
        ⟨leftSide_subset x.2, rightSide_subset y.2, hxy⟩
      obtain ⟨_, _, hc'⟩ := (hconn x y).mpr hc
      exact ⟨x, y, hx, hy, hc'⟩
  by_cases hmem : omega ∈ rlc_lrRestrictedEvent a b c d L R
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]

/-- The closed lower half-plane `{z | z 1 ≤ 0}`. -/
def rlc_lowerHalf : Set (Site 2) := {z | z 1 ≤ 0}
/-- The closed upper half-plane `{z | 0 ≤ z 1}`. -/
def rlc_upperHalf : Set (Site 2) := {z | 0 ≤ z 1}

/-- The right diagonal event: a crossing of `[0, 2n] × [-n, n]` from the lower half of its left side
  to the upper half of its right side. -/
def rlc_rightDiagonal (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_lrRestrictedEvent 0 (2 * n) (-n) n rlc_lowerHalf rlc_upperHalf

/-- A crossing of `[0, 2n] × [-n, n]` ending in the upper half of the right side. -/
def rlc_rightToUpper (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_lrRestrictedEvent 0 (2 * n) (-n) n Set.univ rlc_upperHalf

/-- A crossing of `[0, 2n] × [-n, n]` starting in the lower half of the left side. -/
def rlc_lowerToRight (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_lrRestrictedEvent 0 (2 * n) (-n) n rlc_lowerHalf Set.univ

/-- The left diagonal event: a crossing of `[-2n, 0] × [-n, n]` from the lower half of its left side
  to the upper half of its right side. -/
def rlc_leftDiagonal (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_lrRestrictedEvent (-2 * n) 0 (-n) n rlc_lowerHalf rlc_upperHalf

lemma rlc_rightDiagonal_of_three (n : ℤ) (hn : 0 < n) :
    rlc_rightToUpper n ∩ rlc_lowerToRight n ∩
        verticalCrossingEvent 0 (2 * n) (-n) n ⊆ rlc_rightDiagonal n := by
  intro omega homega
  obtain ⟨⟨hupper, hlower⟩, hvertical⟩ := homega
  obtain ⟨xu, yu, _hxu, hyu, hcu⟩ := hupper
  obtain ⟨xl, yl, hxl, _hyl, hcl⟩ := hlower
  obtain ⟨xb, yt, hcv⟩ := hvertical
  have hsep : CrossingSeparatesH omega 0 (2 * n) 0 (2 * n) (-n) n :=
    crossingSeparatesH_of_crossingArcSides omega 0 (2 * n) 0 (2 * n) (-n) n
      (StatMech.Lattice.jec_crossingArcSides omega (by omega) (by omega))
  have hmeet : HVMeetProperty omega 0 (2 * n) 0 (2 * n) (-n) n :=
    hvMeet_of_crossingSeparatesH omega 0 (2 * n) 0 (2 * n) (-n) n hsep
  have h00 : (0 : ℤ) ≤ 0 := le_rfl
  have h02 : (0 : ℤ) ≤ 2 * n := by omega
  have h22 : (2 * n : ℤ) ≤ 2 * n := le_rfl
  obtain ⟨zu, hzuO, hzuH, hcuzu, hcvzu⟩ :=
    hmeet h00 h02 h22 xu yu hcu xb yt hcv
  obtain ⟨zl, hzlO, hzlH, hclzl, hcvzl⟩ :=
    hmeet h00 h02 h22 xl yl hcl xb yt hcv
  have hzlzu : ConnectedWithin 2 omega (rect 0 (2 * n) (-n) n)
      ⟨zl, hzlH⟩ ⟨zu, hzuH⟩ := by
    simpa only using hcvzl.symm.trans hcvzu
  have hconn : ConnectedWithin 2 omega (rect 0 (2 * n) (-n) n)
      ⟨(xl : Site 2), leftSide_subset xl.2⟩
      ⟨(yu : Site 2), rightSide_subset yu.2⟩ :=
    hclzl.trans (hzlzu.trans (hcuzu.symm.trans hcu))
  exact ⟨xl, yu, hxl, hyu, hconn⟩

/-! ## B. Reflections and diagonal events -/

/-- Reflection in the horizontal axis: `(x, y) ↦ (x, -y)`. -/
def rlc_flipYFun (x : Site 2) : Site 2 := ![x 0, -x 1]

/-- Reflection in the horizontal axis, as an equivalence of sites. -/
def rlc_flipY : Site 2 ≃ Site 2 where
  toFun := rlc_flipYFun
  invFun := rlc_flipYFun
  left_inv x := by funext i; fin_cases i <;> simp [rlc_flipYFun]
  right_inv x := by funext i; fin_cases i <;> simp [rlc_flipYFun]

@[simp] lemma rlc_flipY_zero (x : Site 2) : rlc_flipY x 0 = x 0 := by
  simp [rlc_flipY, rlc_flipYFun]

@[simp] lemma rlc_flipY_one (x : Site 2) : rlc_flipY x 1 = -x 1 := by
  simp [rlc_flipY, rlc_flipYFun]

@[simp] lemma rlc_flipY_involutive (x : Site 2) : rlc_flipY (rlc_flipY x) = x := by
  funext i
  fin_cases i <;> simp

lemma rlc_adj_flipY (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔
      (hypercubicLattice 2).Adj (rlc_flipY x) (rlc_flipY y) := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [rlc_flipY_zero, rlc_flipY_one]
  rw [show -x 1 - -y 1 = -(x 1 - y 1) by ring, Int.natAbs_neg]

/-- Reflection in the horizontal axis, acting on edges. -/
noncomputable def rlc_flipYEdge : Sym2 (Site 2) ≃ Sym2 (Site 2) :=
  sym2Congr rlc_flipY

lemma rlc_flipYEdge_symm_apply (e : Sym2 (Site 2)) :
    rlc_flipYEdge.symm e = e.map rlc_flipY := by
  simp [rlc_flipYEdge, sym2Congr, rlc_flipY]

/-- Reflection in the horizontal axis, acting on configurations. -/
noncomputable def rlc_flipYConfig :
    ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)) :=
  Equiv.piCongrLeft (fun _ => Bool) rlc_flipYEdge

lemma rlc_flipYConfig_apply (omega : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) :
    rlc_flipYConfig omega e = omega (e.map rlc_flipY) := by
  rw [rlc_flipYConfig, Equiv.piCongrLeft_apply, eq_rec_constant,
    rlc_flipYEdge_symm_apply]

lemma rlc_measurable_flipYConfig : Measurable rlc_flipYConfig :=
  (MeasurableEquiv.piCongrLeft (fun _ => Bool) rlc_flipYEdge).measurable

lemma rlc_flipY_measurePreserving (p : ℝ≥0) (hp : p ≤ 1) :
    MeasurePreserving rlc_flipYConfig
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp)
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) := by
  refine ⟨rlc_measurable_flipYConfig, ?_⟩
  rw [rlc_flipYConfig]
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure p hp) rlc_flipYEdge

lemma rlc_mem_centeredRect_flipY (a b n : ℤ) (x : Site 2) :
    x ∈ rect a b (-n) n ↔ rlc_flipY x ∈ rect a b (-n) n := by
  simp only [mem_rect, rlc_flipY_zero, rlc_flipY_one]
  omega

lemma rlc_mem_leftSide_flipY (a b n : ℤ) (x : Site 2) :
    x ∈ leftSide a b (-n) n ↔ rlc_flipY x ∈ leftSide a b (-n) n := by
  rw [mem_leftSide, mem_leftSide]
  exact and_congr (rlc_mem_centeredRect_flipY a b n x) (by simp)

lemma rlc_mem_rightSide_flipY (a b n : ℤ) (x : Site 2) :
    x ∈ rightSide a b (-n) n ↔ rlc_flipY x ∈ rightSide a b (-n) n := by
  rw [mem_rightSide, mem_rightSide]
  exact and_congr (rlc_mem_centeredRect_flipY a b n x) (by simp)

lemma rlc_isOpenEdge_flipY (omega : ConfigSpace (Sym2 (Site 2))) (x y : Site 2) :
    IsOpenEdge 2 (rlc_flipYConfig omega) x y ↔
      IsOpenEdge 2 omega (rlc_flipY x) (rlc_flipY y) := by
  unfold IsOpenEdge
  rw [rlc_adj_flipY]
  have hedge : (s(x, y) : Sym2 (Site 2)).map rlc_flipY =
      s(rlc_flipY x, rlc_flipY y) := Sym2.map_mk _ _ _
  rw [rlc_flipYConfig_apply, hedge]

/-- Reflection in the horizontal axis as a homomorphism of open subgraphs induced on the centred
  rectangle. -/
noncomputable def rlc_flipYInducedHom (a b n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraphInduce 2 omega (rect a b (-n) n) →g
      openSubgraphInduce 2 (rlc_flipYConfig omega) (rect a b (-n) n) where
  toFun := fun x =>
    ⟨rlc_flipY (x : Site 2), (rlc_mem_centeredRect_flipY a b n x).mp x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    change IsOpenEdge 2 (rlc_flipYConfig omega)
      (rlc_flipY (x : Site 2)) (rlc_flipY (y : Site 2))
    rw [rlc_isOpenEdge_flipY, rlc_flipY_involutive, rlc_flipY_involutive]
    exact hxy

lemma rlc_flipY_lrRestricted_iff (a b n : ℤ) (L R : Set (Site 2))
    (omega : ConfigSpace (Sym2 (Site 2))) :
    omega ∈ rlc_lrRestrictedEvent a b (-n) n L R →
      rlc_flipYConfig omega ∈ rlc_lrRestrictedEvent a b (-n) n
        (rlc_flipY '' L) (rlc_flipY '' R) := by
  rintro ⟨x, y, hxL, hyR, hxy⟩
  let xf : leftSide a b (-n) n :=
    ⟨rlc_flipY (x : Site 2), (rlc_mem_leftSide_flipY a b n x).mp x.2⟩
  let yf : rightSide a b (-n) n :=
    ⟨rlc_flipY (y : Site 2), (rlc_mem_rightSide_flipY a b n y).mp y.2⟩
  refine ⟨xf, yf, ⟨x, hxL, rfl⟩, ⟨y, hyR, rfl⟩, ?_⟩
  exact hxy.map (rlc_flipYInducedHom a b n omega)

lemma rlc_flipY_image_univ : rlc_flipY '' (Set.univ : Set (Site 2)) = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨rlc_flipY x, Set.mem_univ _, rlc_flipY_involutive x⟩

lemma rlc_flipY_image_upper : rlc_flipY '' rlc_upperHalf = rlc_lowerHalf := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change 0 ≤ y 1 at hy
    change -(y 1) ≤ 0
    omega
  · intro hx
    change x 1 ≤ 0 at hx
    refine ⟨rlc_flipY x, ?_, rlc_flipY_involutive x⟩
    change 0 ≤ -(x 1)
    omega

lemma rlc_flipY_image_lower : rlc_flipY '' rlc_lowerHalf = rlc_upperHalf := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y 1 ≤ 0 at hy
    change 0 ≤ -(y 1)
    omega
  · intro hx
    change 0 ≤ x 1 at hx
    refine ⟨rlc_flipY x, ?_, rlc_flipY_involutive x⟩
    change -(x 1) ≤ 0
    omega

/-- A crossing of `[0, 2n] × [-n, n]` ending in the lower half of the right side. -/
def rlc_rightToLower (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_lrRestrictedEvent 0 (2 * n) (-n) n Set.univ rlc_lowerHalf

/-- A crossing of `[0, 2n] × [-n, n]` starting in the upper half of the left side. -/
def rlc_upperToRight (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_lrRestrictedEvent 0 (2 * n) (-n) n rlc_upperHalf Set.univ

lemma rlc_flipYConfig_involutive (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_flipYConfig (rlc_flipYConfig omega) = omega := by
  funext e
  rw [rlc_flipYConfig_apply, rlc_flipYConfig_apply]
  induction e using Sym2.inductionOn with
  | _ x y => simp

lemma rlc_flip_rightToUpper (n : ℤ)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (h : omega ∈ rlc_rightToUpper n) :
    rlc_flipYConfig omega ∈ rlc_rightToLower n := by
  have ht := rlc_flipY_lrRestricted_iff 0 (2 * n) n Set.univ rlc_upperHalf omega h
  simpa [rlc_rightToUpper, rlc_rightToLower, rlc_flipY_image_univ,
    rlc_flipY_image_upper] using ht

lemma rlc_flip_rightToLower (n : ℤ)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (h : omega ∈ rlc_rightToLower n) :
    rlc_flipYConfig omega ∈ rlc_rightToUpper n := by
  have ht := rlc_flipY_lrRestricted_iff 0 (2 * n) n Set.univ rlc_lowerHalf omega h
  simpa [rlc_rightToUpper, rlc_rightToLower, rlc_flipY_image_univ,
    rlc_flipY_image_lower] using ht

lemma rlc_flip_lowerToRight (n : ℤ)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (h : omega ∈ rlc_lowerToRight n) :
    rlc_flipYConfig omega ∈ rlc_upperToRight n := by
  have ht := rlc_flipY_lrRestricted_iff 0 (2 * n) n rlc_lowerHalf Set.univ omega h
  simpa [rlc_lowerToRight, rlc_upperToRight, rlc_flipY_image_univ,
    rlc_flipY_image_lower] using ht

lemma rlc_flip_upperToRight (n : ℤ)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (h : omega ∈ rlc_upperToRight n) :
    rlc_flipYConfig omega ∈ rlc_lowerToRight n := by
  have ht := rlc_flipY_lrRestricted_iff 0 (2 * n) n rlc_upperHalf Set.univ omega h
  simpa [rlc_lowerToRight, rlc_upperToRight, rlc_flipY_image_univ,
    rlc_flipY_image_upper] using ht

lemma rlc_rightToUpper_reflection_prob (p : ℝ≥0) (hp : p ≤ 1) (n : ℤ) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_rightToUpper n) =
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_rightToLower n) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  have hpre : rlc_flipYConfig ⁻¹' rlc_rightToUpper n = rlc_rightToLower n := by
    ext omega
    constructor
    · intro h
      have := rlc_flip_rightToUpper n h
      rwa [rlc_flipYConfig_involutive] at this
    · exact rlc_flip_rightToLower n
  calc
    mu.real (rlc_rightToUpper n) =
        mu.real (rlc_flipYConfig ⁻¹' rlc_rightToUpper n) :=
      ((rlc_flipY_measurePreserving p hp).measureReal_preimage
        (measurableSet_of_dependsOn
          (rlc_lrRestrictedEvent_dependsOn 0 (2 * n) (-n) n
            Set.univ rlc_upperHalf)).nullMeasurableSet).symm
    _ = mu.real (rlc_rightToLower n) := by rw [hpre]

lemma rlc_lowerToRight_reflection_prob (p : ℝ≥0) (hp : p ≤ 1) (n : ℤ) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_lowerToRight n) =
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_upperToRight n) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  have hpre : rlc_flipYConfig ⁻¹' rlc_lowerToRight n = rlc_upperToRight n := by
    ext omega
    constructor
    · intro h
      have := rlc_flip_lowerToRight n h
      rwa [rlc_flipYConfig_involutive] at this
    · exact rlc_flip_upperToRight n
  calc
    mu.real (rlc_lowerToRight n) =
        mu.real (rlc_flipYConfig ⁻¹' rlc_lowerToRight n) :=
      ((rlc_flipY_measurePreserving p hp).measureReal_preimage
        (measurableSet_of_dependsOn
          (rlc_lrRestrictedEvent_dependsOn 0 (2 * n) (-n) n
            rlc_lowerHalf Set.univ)).nullMeasurableSet).symm
    _ = mu.real (rlc_upperToRight n) := by rw [hpre]

lemma rlc_horizontal_subset_right_halves (n : ℤ) :
    horizontalCrossingEvent 0 (2 * n) (-n) n ⊆
      rlc_rightToUpper n ∪ rlc_rightToLower n := by
  rintro omega ⟨x, y, hxy⟩
  rcases le_total 0 ((y : Site 2) 1) with hy | hy
  · exact Or.inl ⟨x, y, Set.mem_univ _, hy, hxy⟩
  · exact Or.inr ⟨x, y, Set.mem_univ _, hy, hxy⟩

lemma rlc_horizontal_subset_left_halves (n : ℤ) :
    horizontalCrossingEvent 0 (2 * n) (-n) n ⊆
      rlc_lowerToRight n ∪ rlc_upperToRight n := by
  rintro omega ⟨x, y, hxy⟩
  rcases le_total 0 ((x : Site 2) 1) with hx | hx
  · exact Or.inr ⟨x, y, hx, Set.mem_univ _, hxy⟩
  · exact Or.inl ⟨x, y, hx, Set.mem_univ _, hxy⟩

lemma rlc_rightToUpper_half_localization (p : ℝ≥0) (hp : p ≤ 1)
    (n : ℤ) (alpha : ℝ)
    (hcross : alpha ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (horizontalCrossingEvent 0 (2 * n) (-n) n)) :
    alpha / 2 ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (rlc_rightToUpper n) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  have hmono : mu.real (horizontalCrossingEvent 0 (2 * n) (-n) n) ≤
      mu.real (rlc_rightToUpper n ∪ rlc_rightToLower n) :=
    measureReal_mono (rlc_horizontal_subset_right_halves n) (measure_ne_top _ _)
  have hunion := measureReal_union_le (μ := mu) (rlc_rightToUpper n) (rlc_rightToLower n)
  rw [← rlc_rightToUpper_reflection_prob p hp n] at hunion
  linarith

lemma rlc_lowerToRight_half_localization (p : ℝ≥0) (hp : p ≤ 1)
    (n : ℤ) (alpha : ℝ)
    (hcross : alpha ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (horizontalCrossingEvent 0 (2 * n) (-n) n)) :
    alpha / 2 ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (rlc_lowerToRight n) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  have hmono : mu.real (horizontalCrossingEvent 0 (2 * n) (-n) n) ≤
      mu.real (rlc_lowerToRight n ∪ rlc_upperToRight n) :=
    measureReal_mono (rlc_horizontal_subset_left_halves n) (measure_ne_top _ _)
  have hunion := measureReal_union_le (μ := mu) (rlc_lowerToRight n) (rlc_upperToRight n)
  rw [← rlc_lowerToRight_reflection_prob p hp n] at hunion
  linarith

lemma rlc_rightDiagonal_lower_bound (p : ℝ≥0) (hp : p ≤ 1)
    (n : ℤ) (hn : 0 < n) (alpha : ℝ) (halpha : 0 ≤ alpha)
    (hH : alpha ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (horizontalCrossingEvent 0 (2 * n) (-n) n))
    (hV : alpha ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (verticalCrossingEvent 0 (2 * n) (-n) n)) :
    alpha ^ 3 / 4 ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
      (rlc_rightDiagonal n) := by
  let F := (rect_finite 0 (2 * n) (-n) n).toFinset
  apply rlc_diagonal_event_lower_bound p hp alpha halpha
    (rlc_rightToUpper n) (rlc_lowerToRight n)
    (verticalCrossingEvent 0 (2 * n) (-n) n) (rlc_rightDiagonal n)
    (edgesWithinFinset F) (edgesWithinFinset F) (edgesWithinFinset F)
  · exact rlc_lrRestrictedEvent_isIncreasing _ _ _ _ _ _
  · exact rlc_lrRestrictedEvent_isIncreasing _ _ _ _ _ _
  · exact StatMech.RSW.Strip.verticalCrossingEvent_isIncreasing _ _ _ _
  · simpa [F, rlc_rightToUpper] using
      rlc_lrRestrictedEvent_dependsOn 0 (2 * n) (-n) n Set.univ rlc_upperHalf
  · simpa [F, rlc_lowerToRight] using
      rlc_lrRestrictedEvent_dependsOn 0 (2 * n) (-n) n rlc_lowerHalf Set.univ
  · simpa [F] using StatMech.Universality.rlc_verticalCrossingEvent_dependsOn 0 (2 * n) (-n) n
  · exact rlc_rightToUpper_half_localization p hp n alpha hH
  · exact rlc_lowerToRight_half_localization p hp n alpha hH
  · exact hV
  · exact rlc_rightDiagonal_of_three n hn

/-- The translation vector `(-2n, 0)`. -/
def rlc_leftShift (n : ℤ) : Site 2 := ![-2 * n, 0]

@[simp] lemma rlc_leftShift_zero (n : ℤ) : rlc_leftShift n 0 = -2 * n := rfl
@[simp] lemma rlc_leftShift_one (n : ℤ) : rlc_leftShift n 1 = 0 := rfl

lemma rlc_leftShift_rect (n : ℤ) :
    rect (0 + rlc_leftShift n 0) (2 * n + rlc_leftShift n 0)
        (-n + rlc_leftShift n 1) (n + rlc_leftShift n 1) =
      rect (-2 * n) 0 (-n) n := by
  congr 1 <;> simp

/-- The left translation by `2n` as a homomorphism of induced open subgraphs. -/
noncomputable def rlc_leftShiftHom (n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraphInduce 2 (translateConfig (rlc_leftShift n) omega)
        (rect 0 (2 * n) (-n) n) →g
      openSubgraphInduce 2 omega (rect (-2 * n) 0 (-n) n) where
  toFun := fun x => ⟨(x : Site 2) + rlc_leftShift n, by
    have := (cti_mem_rect_translate 0 (2 * n) (-n) n (rlc_leftShift n) x).mp x.2
    simpa using this⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy ⊢
    exact (cti_isOpenEdge_translate (rlc_leftShift n) omega x y).mp hxy

/-- The inverse of the left translation, as a homomorphism of induced open subgraphs. -/
noncomputable def rlc_leftShiftHomInv (n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraphInduce 2 omega (rect (-2 * n) 0 (-n) n) →g
      openSubgraphInduce 2 (translateConfig (rlc_leftShift n) omega)
        (rect 0 (2 * n) (-n) n) where
  toFun := fun x => ⟨(x : Site 2) - rlc_leftShift n, by
    rw [cti_mem_rect_translate 0 (2 * n) (-n) n (rlc_leftShift n)]
    simpa using x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy ⊢
    have key := (cti_isOpenEdge_translate (rlc_leftShift n) omega
      ((x : Site 2) - rlc_leftShift n) ((y : Site 2) - rlc_leftShift n)).2
    simp only [sub_add_cancel] at key
    exact key hxy

lemma rlc_translate_rightDiagonal_to_left (n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : translateConfig (rlc_leftShift n) omega ∈ rlc_rightDiagonal n) :
    omega ∈ rlc_leftDiagonal n := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  let xl : leftSide (-2 * n) 0 (-n) n :=
    ⟨(x : Site 2) + rlc_leftShift n,
      by simpa using
        (cti_mem_leftSide_translate 0 (2 * n) (-n) n (rlc_leftShift n) x).mp x.2⟩
  let yl : rightSide (-2 * n) 0 (-n) n :=
    ⟨(y : Site 2) + rlc_leftShift n,
      by simpa using
        (cti_mem_rightSide_translate 0 (2 * n) (-n) n (rlc_leftShift n) y).mp y.2⟩
  refine ⟨xl, yl, ?_, ?_, ?_⟩
  · simpa [xl, rlc_lowerHalf] using hx
  · simpa [yl, rlc_upperHalf] using hy
  · exact hxy.map (rlc_leftShiftHom n omega)

lemma rlc_translate_leftDiagonal_to_right (n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : omega ∈ rlc_leftDiagonal n) :
    translateConfig (rlc_leftShift n) omega ∈ rlc_rightDiagonal n := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  let xr : leftSide 0 (2 * n) (-n) n :=
    ⟨(x : Site 2) - rlc_leftShift n, by
      rw [cti_mem_leftSide_translate 0 (2 * n) (-n) n (rlc_leftShift n)]
      simpa using x.2⟩
  let yr : rightSide 0 (2 * n) (-n) n :=
    ⟨(y : Site 2) - rlc_leftShift n, by
      rw [cti_mem_rightSide_translate 0 (2 * n) (-n) n (rlc_leftShift n)]
      simpa using y.2⟩
  refine ⟨xr, yr, ?_, ?_, ?_⟩
  · simpa [xr, rlc_lowerHalf] using hx
  · simpa [yr, rlc_upperHalf] using hy
  · exact hxy.map (rlc_leftShiftHomInv n omega)

lemma rlc_leftDiagonal_preimage (n : ℤ) :
    translateConfig (rlc_leftShift n) ⁻¹' rlc_rightDiagonal n =
      rlc_leftDiagonal n := by
  ext omega
  exact ⟨rlc_translate_rightDiagonal_to_left n omega,
    rlc_translate_leftDiagonal_to_right n omega⟩

lemma rlc_leftDiagonal_prob_eq_right (n : ℤ) :
    halfMeasure.real (rlc_leftDiagonal n) =
      halfMeasure.real (rlc_rightDiagonal n) := by
  rw [← rlc_leftDiagonal_preimage n]
  exact (cti_selfDual_shift_invariant (rlc_leftShift n)).measureReal_preimage
    (measurableSet_of_dependsOn
      (rlc_lrRestrictedEvent_dependsOn 0 (2 * n) (-n) n
        rlc_lowerHalf rlc_upperHalf)).nullMeasurableSet

/-! ## C. Diagonal paths and their regions -/

/-- Crossing paths of the rectangle that start in `L` and end in `R`. -/
abbrev RlcRestrictedCrossingPath (a b c d : ℤ) (L R : Set (Site 2)) :=
  {gamma : RlcCrossingPath a b c d //
    (gamma.1 : Site 2) ∈ L ∧ (gamma.2.1 : Site 2) ∈ R}

/-- There are finitely many restricted crossing paths. -/
noncomputable instance rlc_restrictedCrossingPathFintype
    (a b c d : ℤ) (L R : Set (Site 2)) :
    Fintype (RlcRestrictedCrossingPath a b c d L R) := by
  classical
  unfold RlcRestrictedCrossingPath
  infer_instance

lemma rlc_iUnion_restrictedPathOpen (a b c d : ℤ) (L R : Set (Site 2)) :
    (⋃ gamma : RlcRestrictedCrossingPath a b c d L R,
      rlc_pathOpen gamma.1) = rlc_lrRestrictedEvent a b c d L R := by
  ext omega
  constructor
  · intro h
    simp only [Set.mem_iUnion] at h
    obtain ⟨gamma, hgamma⟩ := h
    refine ⟨gamma.1.1, gamma.1.2.1, gamma.2.1, gamma.2.2,
      ⟨rlc_openWalkOfEdges omega gamma.1.2.2.1 ?_⟩⟩
    change ∀ e ∈ gamma.1.2.2.1.edges.toFinset.image (Sym2.map Subtype.val),
      omega e = true at hgamma
    exact hgamma
  · rintro ⟨x, y, hx, hy, hxy⟩
    let q0 := hxy.some
    have hle : openSubgraphInduce 2 omega (rect a b c d) ≤
        (hypercubicLattice 2).induce (rect a b c d) := by
      intro u v huv
      rw [openSubgraphInduce_adj, openSubgraph_adj] at huv
      exact huv.1
    let q := q0.mapLe hle
    let gamma0 : RlcCrossingPath a b c d := ⟨x, y, q.toPath⟩
    let gamma : RlcRestrictedCrossingPath a b c d L R :=
      ⟨gamma0, hx, hy⟩
    simp only [Set.mem_iUnion]
    refine ⟨gamma, ?_⟩
    intro e he
    simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset] at he
    obtain ⟨z, hz, rfl⟩ := he
    have hzq : z ∈ q.edges := q.edges_toPath_subset_edges hz
    have hedge : q.edges = q0.edges := SimpleGraph.Walk.edges_mapLe_eq_edges hle q0
    have hzq0 : z ∈ q0.edges := hedge ▸ hzq
    induction z using Sym2.inductionOn with
    | _ u v =>
      have hadj := q0.adj_of_mem_edges hzq0
      rw [openSubgraphInduce_adj, openSubgraph_adj] at hadj
      simpa using hadj.2

/-- Diagonal crossing paths of `[0, 2n] × [-n, n]`: from the lower half of the left side to the
  upper half of the right side. -/
abbrev RlcRightDiagonalPath (n : ℤ) :=
  RlcRestrictedCrossingPath 0 (2 * n) (-n) n rlc_lowerHalf rlc_upperHalf

/-- Diagonal crossing paths of `[-2n, 0] × [-n, n]`: from the lower half of the left side to the
  upper half of the right side. -/
abbrev RlcLeftDiagonalPath (n : ℤ) :=
  RlcRestrictedCrossingPath (-2 * n) 0 (-n) n rlc_lowerHalf rlc_upperHalf

/-- Rotation by `π`: `(x, y) ↦ (-x, -y)`. -/
def rlc_rot180Fun (x : Site 2) : Site 2 := ![-x 0, -x 1]

/-- Rotation by `π`, as an equivalence of sites. -/
def rlc_rot180 : Site 2 ≃ Site 2 where
  toFun := rlc_rot180Fun
  invFun := rlc_rot180Fun
  left_inv x := by funext i; fin_cases i <;> simp [rlc_rot180Fun]
  right_inv x := by funext i; fin_cases i <;> simp [rlc_rot180Fun]

@[simp] lemma rlc_rot180_zero (x : Site 2) : rlc_rot180 x 0 = -x 0 := by
  simp [rlc_rot180, rlc_rot180Fun]

@[simp] lemma rlc_rot180_one (x : Site 2) : rlc_rot180 x 1 = -x 1 := by
  simp [rlc_rot180, rlc_rot180Fun]

@[simp] lemma rlc_rot180_involutive (x : Site 2) :
    rlc_rot180 (rlc_rot180 x) = x := rlc_rot180.left_inv x

@[simp] lemma rlc_rot180Edge_involutive (e : Sym2 (Site 2)) :
    Sym2.map rlc_rot180 (Sym2.map rlc_rot180 e) = e := by
  induction e using Sym2.inductionOn with
  | _ u v => simp

lemma rlc_adj_rot180 (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔
      (hypercubicLattice 2).Adj (rlc_rot180 x) (rlc_rot180 y) := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, rlc_rot180_zero,
    rlc_rot180_one]
  have h0 : (-x 0 - -y 0).natAbs = (x 0 - y 0).natAbs := by
    rw [show -x 0 - -y 0 = -(x 0 - y 0) by ring, Int.natAbs_neg]
  have h1 : (-x 1 - -y 1).natAbs = (x 1 - y 1).natAbs := by
    rw [show -x 1 - -y 1 = -(x 1 - y 1) by ring, Int.natAbs_neg]
  rw [h0, h1]

lemma rlc_rot180_mem_rightRect_iff_leftRect (n : ℤ) (x : Site 2) :
    x ∈ rect 0 (2 * n) (-n) n ↔
      rlc_rot180 x ∈ rect (-2 * n) 0 (-n) n := by
  simp only [mem_rect, rlc_rot180_zero, rlc_rot180_one]
  omega

/-- Rotation by `π` from the right rectangle to the left rectangle, as a homomorphism of induced
  graphs. -/
noncomputable def rlc_rot180RightInducedHom (n : ℤ) :
    ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)) →g
      ((hypercubicLattice 2).induce (rect (-2 * n) 0 (-n) n)) where
  toFun z := ⟨rlc_rot180 (z : Site 2),
    (rlc_rot180_mem_rightRect_iff_leftRect n z).mp z.2⟩
  map_rel' := by
    intro x y hxy
    exact (rlc_adj_rot180 (x : Site 2) (y : Site 2)).mp hxy

lemma rlc_rot180RightInducedHom_injective (n : ℤ) :
    Function.Injective (rlc_rot180RightInducedHom n) := by
  intro x y hxy
  apply Subtype.ext
  exact rlc_rot180.injective (congrArg Subtype.val hxy)

/-- The image of a right diagonal path under rotation by `π`, as a left diagonal path. -/
noncomputable def rlc_rot180RightPath {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : RlcLeftDiagonalPath n := by
  let x : leftSide (-2 * n) 0 (-n) n :=
    ⟨rlc_rot180 (gamma.1.2.1 : Site 2), by
      rw [mem_leftSide]
      have hy := gamma.1.2.1.2
      rw [mem_rightSide] at hy
      refine ⟨(rlc_rot180_mem_rightRect_iff_leftRect n _).mp hy.1, ?_⟩
      simpa using congrArg Neg.neg hy.2⟩
  let y : rightSide (-2 * n) 0 (-n) n :=
    ⟨rlc_rot180 (gamma.1.1 : Site 2), by
      rw [mem_rightSide]
      have hx := gamma.1.1.2
      rw [mem_leftSide] at hx
      refine ⟨(rlc_rot180_mem_rightRect_iff_leftRect n _).mp hx.1, ?_⟩
      simpa using congrArg Neg.neg hx.2⟩
  let w := gamma.1.2.2.1.reverse.map (rlc_rot180RightInducedHom n)
  have hw : w.IsPath := by
    exact SimpleGraph.Walk.IsPath.map
      (rlc_rot180RightInducedHom_injective n) gamma.1.2.2.2.reverse
  refine ⟨⟨x, y, ⟨w, hw⟩⟩, ?_, ?_⟩
  · change -(gamma.1.2.1 : Site 2) 1 ≤ 0
    exact neg_nonpos.mpr gamma.2.2
  · change 0 ≤ -(gamma.1.1 : Site 2) 1
    simpa [rlc_lowerHalf] using gamma.2.1

lemma rlc_rot180_mem_leftRect_iff_rightRect (n : ℤ) (x : Site 2) :
    x ∈ rect (-2 * n) 0 (-n) n ↔
      rlc_rot180 x ∈ rect 0 (2 * n) (-n) n := by
  have h := rlc_rot180_mem_rightRect_iff_leftRect n (rlc_rot180 x)
  simpa using h.symm

/-- Rotation by `π` from the left rectangle to the right rectangle, as a homomorphism of induced
  graphs. -/
noncomputable def rlc_rot180LeftInducedHom (n : ℤ) :
    ((hypercubicLattice 2).induce (rect (-2 * n) 0 (-n) n)) →g
      ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)) where
  toFun z := ⟨rlc_rot180 (z : Site 2),
    (rlc_rot180_mem_leftRect_iff_rightRect n z).mp z.2⟩
  map_rel' := by
    intro x y hxy
    exact (rlc_adj_rot180 (x : Site 2) (y : Site 2)).mp hxy

lemma rlc_rot180LeftInducedHom_injective (n : ℤ) :
    Function.Injective (rlc_rot180LeftInducedHom n) := by
  intro x y hxy
  apply Subtype.ext
  exact rlc_rot180.injective (congrArg Subtype.val hxy)

/-- The image of a left diagonal path under rotation by `π`, as a right diagonal path. -/
noncomputable def rlc_rot180LeftPath {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : RlcRightDiagonalPath n := by
  let x : leftSide 0 (2 * n) (-n) n :=
    ⟨rlc_rot180 (gamma.1.2.1 : Site 2), by
      rw [mem_leftSide]
      have hy := gamma.1.2.1.2
      rw [mem_rightSide] at hy
      refine ⟨(rlc_rot180_mem_leftRect_iff_rightRect n _).mp hy.1, ?_⟩
      simpa using congrArg Neg.neg hy.2⟩
  let y : rightSide 0 (2 * n) (-n) n :=
    ⟨rlc_rot180 (gamma.1.1 : Site 2), by
      rw [mem_rightSide]
      have hx := gamma.1.1.2
      rw [mem_leftSide] at hx
      refine ⟨(rlc_rot180_mem_leftRect_iff_rightRect n _).mp hx.1, ?_⟩
      simpa using congrArg Neg.neg hx.2⟩
  let w := gamma.1.2.2.1.reverse.map (rlc_rot180LeftInducedHom n)
  have hw : w.IsPath := by
    exact SimpleGraph.Walk.IsPath.map
      (rlc_rot180LeftInducedHom_injective n) gamma.1.2.2.2.reverse
  refine ⟨⟨x, y, ⟨w, hw⟩⟩, ?_, ?_⟩
  · change -(gamma.1.2.1 : Site 2) 1 ≤ 0
    exact neg_nonpos.mpr gamma.2.2
  · change 0 ≤ -(gamma.1.1 : Site 2) 1
    simpa [rlc_lowerHalf] using gamma.2.1

lemma rlc_iUnion_rightDiagonalPath (n : ℤ) :
    (⋃ gamma : RlcRightDiagonalPath n, rlc_pathOpen gamma.1) =
      rlc_rightDiagonal n :=
  rlc_iUnion_restrictedPathOpen 0 (2 * n) (-n) n rlc_lowerHalf rlc_upperHalf

lemma rlc_iUnion_leftDiagonalPath (n : ℤ) :
    (⋃ gamma : RlcLeftDiagonalPath n, rlc_pathOpen gamma.1) =
      rlc_leftDiagonal n :=
  rlc_iUnion_restrictedPathOpen (-2 * n) 0 (-n) n rlc_lowerHalf rlc_upperHalf

/-- A pair of a right and a left diagonal path. -/
abbrev RlcDiagonalPathPair (n : ℤ) :=
  RlcRightDiagonalPath n × RlcLeftDiagonalPath n

/-- There are finitely many pairs of diagonal paths. -/
noncomputable instance rlc_diagonalPathPairFintype (n : ℤ) :
    Fintype (RlcDiagonalPathPair n) := by
  unfold RlcDiagonalPathPair
  infer_instance

/-- The event that both paths of the pair are open. -/
def rlc_pathPairOpen {n : ℤ} (pair : RlcDiagonalPathPair n) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_pathOpen pair.1.1 ∩ rlc_pathOpen pair.2.1

/-- The union of the edges of the two paths of the pair. -/
noncomputable def rlc_pathPairEdges {n : ℤ}
    (pair : RlcDiagonalPathPair n) : Finset (Sym2 (Site 2)) :=
  rlc_pathEdges pair.1.1 ∪ rlc_pathEdges pair.2.1

lemma rlc_pathPairOpen_dependsOn {n : ℤ}
    (pair : RlcDiagonalPathPair n) :
    DependsOn ((rlc_pathPairOpen pair).indicator (fun _ => (1 : ℝ)))
      (rlc_pathPairEdges pair : Set (Sym2 (Site 2))) := by
  simpa only [rlc_pathPairOpen, rlc_pathPairEdges, Finset.coe_union] using
    dependsOn_inter (rlc_pathOpen_dependsOn pair.1.1)
      (rlc_pathOpen_dependsOn pair.2.1)

lemma rlc_iUnion_pathPairOpen (n : ℤ) :
    (⋃ pair : RlcDiagonalPathPair n, rlc_pathPairOpen pair) =
      rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
  ext omega
  constructor
  · intro h
    obtain ⟨pair, hright, hleft⟩ := Set.mem_iUnion.mp h
    exact ⟨by
      rw [← rlc_iUnion_rightDiagonalPath]
      exact Set.mem_iUnion.mpr ⟨pair.1, hright⟩,
      by
        rw [← rlc_iUnion_leftDiagonalPath]
        exact Set.mem_iUnion.mpr ⟨pair.2, hleft⟩⟩
  · rintro ⟨hright, hleft⟩
    rw [← rlc_iUnion_rightDiagonalPath] at hright
    rw [← rlc_iUnion_leftDiagonalPath] at hleft
    obtain ⟨gamma, hgamma⟩ := Set.mem_iUnion.mp hright
    obtain ⟨gamma', hgamma'⟩ := Set.mem_iUnion.mp hleft
    exact Set.mem_iUnion.mpr ⟨(gamma, gamma'), hgamma, hgamma'⟩

/-- The coordinate swap `(x, y) ↦ (y, x)` on the right rectangle, as a homomorphism of induced
  graphs. -/
noncomputable def rlc_swapRightInducedHom (n : ℤ) :
    ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)) →g
      hypercubicLattice 2 where
  toFun z := crf_swap (z : Site 2)
  map_rel' := by
    intro x y hxy
    exact (crf_adj_swap (x : Site 2) (y : Site 2)).mp hxy

/-- The walk obtained by swapping the coordinates of a right diagonal path. -/
noncomputable def rlc_swappedRightPathWalk {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    (hypercubicLattice 2).Walk
      (crf_swap (gamma.1.1 : Site 2))
      (crf_swap (gamma.1.2.1 : Site 2)) :=
  gamma.1.2.2.1.map (rlc_swapRightInducedHom n)

/-- The sites of the swapped right diagonal path. -/
def rlc_swappedRightPathSupport {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : Set (Site 2) :=
  {p | ∃ z ∈ gamma.1.2.2.1.support,
    p = crf_swap (z : Site 2)}

lemma rlc_rightPath_arcSeparatingSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) :
    ArcSeparatingSet (rlc_swappedRightPathSupport gamma)
      (-n) n 0 (2 * n) := by
  let a0 : ℤ := (gamma.1.1 : Site 2) 1
  let b0 : ℤ := (gamma.1.2.1 : Site 2) 1
  have hstart : crf_swap (gamma.1.1 : Site 2) = ![a0, 0] := by
    have hs := gamma.1.1.2
    rw [mem_leftSide] at hs
    ext i
    fin_cases i <;> simp [a0, hs.2]
  have hend : crf_swap (gamma.1.2.1 : Site 2) = ![b0, 2 * n] := by
    have he := gamma.1.2.1.2
    rw [mem_rightSide] at he
    ext i
    fin_cases i <;> simp [b0, he.2]
  let V : (hypercubicLattice 2).Walk ![a0, 0] ![b0, 2 * n] :=
    (rlc_swappedRightPathWalk gamma).copy hstart hend
  have hs := gamma.1.1.2
  have he := gamma.1.2.1.2
  rw [mem_leftSide, mem_rect] at hs
  rw [mem_rightSide, mem_rect] at he
  have hVbox : ∀ p ∈ V.support, p ∈ rect (-n) n 0 (2 * n) := by
    intro p hp
    dsimp only [V] at hp
    rw [SimpleGraph.Walk.support_copy] at hp
    change p ∈ (SimpleGraph.Walk.map (rlc_swapRightInducedHom n)
      gamma.1.2.2.1).support at hp
    have hsupp := SimpleGraph.Walk.support_map
      (rlc_swapRightInducedHom n)
      (show ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)).Walk _ _
        from gamma.1.2.2.1)
    rw [hsupp, List.mem_map] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact (crf_mem_rect_swap 0 (2 * n) (-n) n (z : Site 2)).mp z.2
  have hVP : ∀ p ∈ V.support,
      p ∈ rlc_swappedRightPathSupport gamma := by
    intro p hp
    dsimp only [V] at hp
    rw [SimpleGraph.Walk.support_copy] at hp
    change p ∈ (SimpleGraph.Walk.map (rlc_swapRightInducedHom n)
      gamma.1.2.2.1).support at hp
    have hsupp := SimpleGraph.Walk.support_map
      (rlc_swapRightInducedHom n)
      (show ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)).Walk _ _
        from gamma.1.2.2.1)
    rw [hsupp, List.mem_map] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact ⟨z, hz, rfl⟩
  exact jec_arcSeparatingSet (-n) n 0 (2 * n) a0 b0
    (by omega) (by omega)
    hs.1.2.2.1 hs.1.2.2.2 he.1.2.2.1 he.1.2.2.2
    V hVbox _ hVP

/-- A set of sites separating the swapped right diagonal path from its other side (chosen by the
  arc-separation lemma). -/
noncomputable def rlc_swappedBelowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) : Set (Site 2) :=
  Classical.choose (rlc_rightPath_arcSeparatingSet hn gamma)

lemma rlc_swappedBelowSet_spec {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) :
    (∀ z : Site 2, z ∈ rect (-n) n 0 (2 * n) → z 0 = -n →
      z ∈ rlc_swappedBelowSet hn gamma) ∧
    (∀ z : Site 2, z ∈ rect (-n) n 0 (2 * n) → z 0 = n →
      z ∉ rlc_swappedBelowSet hn gamma) ∧
    (∀ u v : Site 2, u ∈ rect (-n) n 0 (2 * n) →
      v ∈ rect (-n) n 0 (2 * n) →
      (hypercubicLattice 2).Adj u v →
      bdEdge (rlc_swappedBelowSet hn gamma) s(u, v) →
      u ∈ rlc_swappedRightPathSupport gamma ∨
        v ∈ rlc_swappedRightPathSupport gamma) :=
  Classical.choose_spec (rlc_rightPath_arcSeparatingSet hn gamma)

/-- The sites below a right diagonal path: the swap-preimage of the swapped separating set. -/
noncomputable def rlc_belowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) : Set (Site 2) :=
  crf_swap ⁻¹' rlc_swappedBelowSet hn gamma

lemma rlc_bottomSide_subset_belowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) :
    bottomSide 0 (2 * n) (-n) n ⊆ rlc_belowSet hn gamma := by
  intro z hz
  apply (rlc_swappedBelowSet_spec hn gamma).1 (crf_swap z)
  · exact (crf_mem_rect_swap 0 (2 * n) (-n) n z).mp hz.1
  · simpa using hz.2

lemma rlc_topSide_disjoint_belowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) :
    Disjoint (topSide 0 (2 * n) (-n) n) (rlc_belowSet hn gamma) := by
  rw [Set.disjoint_left]
  intro z hzTop hzBelow
  exact (rlc_swappedBelowSet_spec hn gamma).2.1 (crf_swap z)
    ((crf_mem_rect_swap 0 (2 * n) (-n) n z).mp hzTop.1)
    (by simpa using hzTop.2) hzBelow

/-- The coordinate swap on the left rectangle, as a homomorphism of induced graphs. -/
noncomputable def rlc_swapLeftInducedHom (n : ℤ) :
    ((hypercubicLattice 2).induce (rect (-2 * n) 0 (-n) n)) →g
      hypercubicLattice 2 where
  toFun z := crf_swap (z : Site 2)
  map_rel' := by
    intro x y hxy
    exact (crf_adj_swap (x : Site 2) (y : Site 2)).mp hxy

/-- The walk obtained by swapping the coordinates of a left diagonal path. -/
noncomputable def rlc_swappedLeftPathWalk {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    (hypercubicLattice 2).Walk
      (crf_swap (gamma.1.1 : Site 2))
      (crf_swap (gamma.1.2.1 : Site 2)) :=
  gamma.1.2.2.1.map (rlc_swapLeftInducedHom n)

/-- The sites of the swapped left diagonal path. -/
def rlc_swappedLeftPathSupport {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : Set (Site 2) :=
  {p | ∃ z ∈ gamma.1.2.2.1.support,
    p = crf_swap (z : Site 2)}

lemma rlc_leftPath_arcSeparatingSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    ArcSeparatingSet (rlc_swappedLeftPathSupport gamma)
      (-n) n (-2 * n) 0 := by
  let a0 : ℤ := (gamma.1.1 : Site 2) 1
  let b0 : ℤ := (gamma.1.2.1 : Site 2) 1
  have hstart : crf_swap (gamma.1.1 : Site 2) = ![a0, -2 * n] := by
    have hs := gamma.1.1.2
    rw [mem_leftSide] at hs
    ext i
    fin_cases i <;> simp [a0, hs.2]
  have hend : crf_swap (gamma.1.2.1 : Site 2) = ![b0, 0] := by
    have he := gamma.1.2.1.2
    rw [mem_rightSide] at he
    ext i
    fin_cases i <;> simp [b0, he.2]
  let V : (hypercubicLattice 2).Walk ![a0, -2 * n] ![b0, 0] :=
    (rlc_swappedLeftPathWalk gamma).copy hstart hend
  have hs := gamma.1.1.2
  have he := gamma.1.2.1.2
  rw [mem_leftSide, mem_rect] at hs
  rw [mem_rightSide, mem_rect] at he
  have hVbox : ∀ p ∈ V.support, p ∈ rect (-n) n (-2 * n) 0 := by
    intro p hp
    dsimp only [V] at hp
    rw [SimpleGraph.Walk.support_copy] at hp
    change p ∈ (SimpleGraph.Walk.map (rlc_swapLeftInducedHom n)
      gamma.1.2.2.1).support at hp
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact (crf_mem_rect_swap (-2 * n) 0 (-n) n (z : Site 2)).mp z.2
  have hVP : ∀ p ∈ V.support,
      p ∈ rlc_swappedLeftPathSupport gamma := by
    intro p hp
    dsimp only [V] at hp
    rw [SimpleGraph.Walk.support_copy] at hp
    change p ∈ (SimpleGraph.Walk.map (rlc_swapLeftInducedHom n)
      gamma.1.2.2.1).support at hp
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact ⟨z, hz, rfl⟩
  exact jec_arcSeparatingSet (-n) n (-2 * n) 0 a0 b0
    (by omega) (by omega)
    hs.1.2.2.1 hs.1.2.2.2 he.1.2.2.1 he.1.2.2.2
    V hVbox _ hVP

/-- A set of sites separating the swapped left diagonal path from its other side. -/
noncomputable def rlc_swappedLeftBelowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) : Set (Site 2) :=
  Classical.choose (rlc_leftPath_arcSeparatingSet hn gamma)

lemma rlc_swappedLeftBelowSet_spec {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    (∀ z : Site 2, z ∈ rect (-n) n (-2 * n) 0 → z 0 = -n →
      z ∈ rlc_swappedLeftBelowSet hn gamma) ∧
    (∀ z : Site 2, z ∈ rect (-n) n (-2 * n) 0 → z 0 = n →
      z ∉ rlc_swappedLeftBelowSet hn gamma) ∧
    (∀ u v : Site 2, u ∈ rect (-n) n (-2 * n) 0 →
      v ∈ rect (-n) n (-2 * n) 0 →
      (hypercubicLattice 2).Adj u v →
      bdEdge (rlc_swappedLeftBelowSet hn gamma) s(u, v) →
      u ∈ rlc_swappedLeftPathSupport gamma ∨
        v ∈ rlc_swappedLeftPathSupport gamma) :=
  Classical.choose_spec (rlc_leftPath_arcSeparatingSet hn gamma)

/-- The sites above a left diagonal path. -/
noncomputable def rlc_aboveSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) : Set (Site 2) :=
  crf_swap ⁻¹' (rlc_swappedLeftBelowSet hn gamma)ᶜ

lemma rlc_leftTopSide_subset_aboveSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    topSide (-2 * n) 0 (-n) n ⊆ rlc_aboveSet hn gamma := by
  intro z hz
  exact (rlc_swappedLeftBelowSet_spec hn gamma).2.1 (crf_swap z)
    ((crf_mem_rect_swap (-2 * n) 0 (-n) n z).mp hz.1)
    (by simpa using hz.2)

lemma rlc_leftBottomSide_disjoint_aboveSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    Disjoint (bottomSide (-2 * n) 0 (-n) n) (rlc_aboveSet hn gamma) := by
  rw [Set.disjoint_left]
  intro z hzBottom hzAbove
  exact hzAbove ((rlc_swappedLeftBelowSet_spec hn gamma).1 (crf_swap z)
    ((crf_mem_rect_swap (-2 * n) 0 (-n) n z).mp hzBottom.1)
    (by simpa using hzBottom.2))

lemma rlc_half_rightDiagonal_lower_bound (n : ℤ) (hn : 0 < n)
    (hH : (1 : ℝ) / 2 ≤ halfMeasure.real
      (horizontalCrossingEvent 0 (2 * n) (-n) n))
    (hV : (1 : ℝ) / 2 ≤ halfMeasure.real
      (verticalCrossingEvent 0 (2 * n) (-n) n)) :
    (1 : ℝ) / 32 ≤ halfMeasure.real (rlc_rightDiagonal n) := by
  have h := rlc_rightDiagonal_lower_bound (2⁻¹ : ℝ≥0) half_le_one n hn
    ((1 : ℝ) / 2) (by norm_num) hH hV
  norm_num at h
  simpa [halfMeasure] using h

lemma rlc_half_leftDiagonal_lower_bound (n : ℤ) (hn : 0 < n)
    (hH : (1 : ℝ) / 2 ≤ halfMeasure.real
      (horizontalCrossingEvent 0 (2 * n) (-n) n))
    (hV : (1 : ℝ) / 2 ≤ halfMeasure.real
      (verticalCrossingEvent 0 (2 * n) (-n) n)) :
    (1 : ℝ) / 32 ≤ halfMeasure.real (rlc_leftDiagonal n) := by
  rw [rlc_leftDiagonal_prob_eq_right]
  exact rlc_half_rightDiagonal_lower_bound n hn hH hV

lemma rlc_lrRestricted_univ (a b c d : ℤ) :
    rlc_lrRestrictedEvent a b c d Set.univ Set.univ =
      horizontalCrossingEvent a b c d := by
  ext omega
  simp only [rlc_lrRestrictedEvent, Set.mem_ofPred_eq, Set.mem_univ, true_and,
    mem_horizontalCrossingEvent, HorizontalCrossing]

lemma rlc_horizontalCrossing_dependsOn (a b c d : ℤ) :
    DependsOn ((horizontalCrossingEvent a b c d).indicator (fun _ => (1 : ℝ)))
      (edgesWithinFinset (rect_finite a b c d).toFinset : Set (Sym2 (Site 2))) := by
  rw [← rlc_lrRestricted_univ]
  exact rlc_lrRestrictedEvent_dependsOn a b c d Set.univ Set.univ

/-- `1/2 ≤ P(horizontal crossing of [0, m]²)` at `p = 1/2` (unconditional). -/
theorem rlc_square_half (m : ℤ) (hm : 0 < m) :
    (1 : ℝ) / 2 ≤ halfMeasure.real
      (horizontalCrossingEvent 0 m 0 m) := by
  exact crr_square_half m hm
    (StatMech.Universality.measurableSet_horizontalCrossingEvent 0 m 0 m)
    (by
      change MeasurableSet (verticalCrossingEvent 0 (m - 1) (-1) m)
      exact StatMech.Universality.measurableSet_verticalCrossingEvent 0 (m - 1) (-1) m)
    (StatMech.Universality.measurableSet_horizontalCrossingEvent (-1) m 0 (m - 1))

lemma rlc_centered_square_horizontal_half (n : ℤ) (hn : 0 < n) :
    (1 : ℝ) / 2 ≤ halfMeasure.real
      (horizontalCrossingEvent 0 (2 * n) (-n) n) := by
  have hbase := rlc_square_half (2 * n) (by omega)
  have htrans := cti_horizontalCrossing_translation_invariant
    0 (2 * n) 0 (2 * n) (![0, -n] : Site 2)
    (StatMech.Universality.measurableSet_horizontalCrossingEvent 0 (2 * n) 0 (2 * n))
  have heq : halfMeasure.real
      (horizontalCrossingEvent 0 (2 * n) (-n) n) =
      halfMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 (2 * n)) := by
    simpa [show 2 * n + -n = n by ring] using htrans
  rwa [heq]

lemma rlc_centered_square_vertical_half (n : ℤ) (hn : 0 < n) :
    (1 : ℝ) / 2 ≤ halfMeasure.real
      (verticalCrossingEvent 0 (2 * n) (-n) n) := by
  have hH := rlc_centered_square_horizontal_half n hn
  have hswap := crf_verticalCrossing_eq_horizontal_swap 0 (2 * n) (-n) n
    (StatMech.Universality.measurableSet_horizontalCrossingEvent (-n) n 0 (2 * n))
  have htrans := cti_horizontalCrossing_translation_invariant
    (-n) n 0 (2 * n) (![n, -n] : Site 2)
    (StatMech.Universality.measurableSet_horizontalCrossingEvent (-n) n 0 (2 * n))
  have heq : halfMeasure.real
      (verticalCrossingEvent 0 (2 * n) (-n) n) =
      halfMeasure.real (horizontalCrossingEvent 0 (2 * n) (-n) n) := by
    rw [hswap]
    simpa [show -n + n = 0 by ring, show n + n = 2 * n by ring,
      show 2 * n + -n = n by ring] using htrans.symm
  rwa [heq]

/-- `1/32 ≤ P(right diagonal event)` (unconditional). -/
theorem rlc_half_rightDiagonal_unconditional (n : ℤ) (hn : 0 < n) :
    (1 : ℝ) / 32 ≤ halfMeasure.real (rlc_rightDiagonal n) :=
  rlc_half_rightDiagonal_lower_bound n hn
    (rlc_centered_square_horizontal_half n hn)
    (rlc_centered_square_vertical_half n hn)

/-- `1/32 ≤ P(left diagonal event)` at `p = 1/2` (unconditional). -/
theorem rlc_half_leftDiagonal_unconditional (n : ℤ) (hn : 0 < n) :
    (1 : ℝ) / 32 ≤ halfMeasure.real (rlc_leftDiagonal n) := by
  rw [rlc_leftDiagonal_prob_eq_right]
  exact rlc_half_rightDiagonal_unconditional n hn

/-- The sites visited by a crossing path. -/
noncomputable def rlc_pathVertices {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) : Finset (Site 2) :=
  gamma.2.2.1.support.toFinset.image Subtype.val

lemma rlc_pathVertices_rot180RightPath {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_pathVertices (rlc_rot180RightPath gamma).1 =
      (rlc_pathVertices gamma.1).image rlc_rot180 := by
  classical
  let w := gamma.1.2.2.1.reverse.map (rlc_rot180RightInducedHom n)
  change w.support.toFinset.image Subtype.val =
    (gamma.1.2.2.1.support.toFinset.image Subtype.val).image rlc_rot180
  ext z
  simp only [Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : u ∈ List.map (rlc_rot180RightInducedHom n)
        gamma.1.2.2.1.reverse.support := by
      rw [← SimpleGraph.Walk.support_map]
      exact hu
    rw [List.mem_map, SimpleGraph.Walk.support_reverse] at hu'
    obtain ⟨v, hv, huv⟩ := hu'
    refine ⟨(v : Site 2), ⟨v, by simpa using hv, rfl⟩, ?_⟩
    exact congrArg Subtype.val huv
  · rintro ⟨v, ⟨u, hu, huv⟩, hvz⟩
    subst v
    refine ⟨rlc_rot180RightInducedHom n u, ?_, ?_⟩
    · have humap : rlc_rot180RightInducedHom n u ∈
          (gamma.1.2.2.1.reverse.map
            (rlc_rot180RightInducedHom n)).support := by
        rw [SimpleGraph.Walk.support_map, List.mem_map,
          SimpleGraph.Walk.support_reverse]
        exact ⟨u, by simpa using hu, rfl⟩
      exact humap
    · exact hvz

lemma rlc_pathVertices_rot180LeftPath {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_pathVertices (rlc_rot180LeftPath gamma).1 =
      (rlc_pathVertices gamma.1).image rlc_rot180 := by
  classical
  let w := gamma.1.2.2.1.reverse.map (rlc_rot180LeftInducedHom n)
  change w.support.toFinset.image Subtype.val =
    (gamma.1.2.2.1.support.toFinset.image Subtype.val).image rlc_rot180
  ext z
  simp only [Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : u ∈ List.map (rlc_rot180LeftInducedHom n)
        gamma.1.2.2.1.reverse.support := by
      rw [← SimpleGraph.Walk.support_map]
      exact hu
    rw [List.mem_map, SimpleGraph.Walk.support_reverse] at hu'
    obtain ⟨v, hv, huv⟩ := hu'
    refine ⟨(v : Site 2), ⟨v, by simpa using hv, rfl⟩, ?_⟩
    exact congrArg Subtype.val huv
  · rintro ⟨v, ⟨u, hu, huv⟩, hvz⟩
    subst v
    refine ⟨rlc_rot180LeftInducedHom n u, ?_, ?_⟩
    · have humap : rlc_rot180LeftInducedHom n u ∈
          (gamma.1.2.2.1.reverse.map
            (rlc_rot180LeftInducedHom n)).support := by
        rw [SimpleGraph.Walk.support_map, List.mem_map,
          SimpleGraph.Walk.support_reverse]
        exact ⟨u, by simpa using hu, rfl⟩
      exact humap
    · exact hvz

lemma rlc_pathVertices_rot180_roundtrip_left {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_pathVertices (rlc_rot180RightPath
      (rlc_rot180LeftPath gamma)).1 = rlc_pathVertices gamma.1 := by
  rw [rlc_pathVertices_rot180RightPath,
    rlc_pathVertices_rot180LeftPath, Finset.image_image]
  simp [Function.comp_def, rlc_rot180_involutive]

lemma rlc_pathVertices_rot180_roundtrip_right {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_pathVertices (rlc_rot180LeftPath
      (rlc_rot180RightPath gamma)).1 = rlc_pathVertices gamma.1 := by
  rw [rlc_pathVertices_rot180LeftPath,
    rlc_pathVertices_rot180RightPath, Finset.image_image]
  simp [Function.comp_def, rlc_rot180_involutive]

lemma rlc_pathEdges_rot180RightPath {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_pathEdges (rlc_rot180RightPath gamma).1 =
      (rlc_pathEdges gamma.1).image (Sym2.map rlc_rot180) := by
  classical
  let hom := rlc_rot180RightInducedHom n
  let w := gamma.1.2.2.1.reverse.map hom
  change w.edges.toFinset.image (Sym2.map Subtype.val) =
    (gamma.1.2.2.1.edges.toFinset.image
      (Sym2.map Subtype.val)).image (Sym2.map rlc_rot180)
  have hcomp (d : Sym2 (rect 0 (2 * n) (-n) n)) :
      Sym2.map Subtype.val (Sym2.map hom d) =
        Sym2.map rlc_rot180 (Sym2.map Subtype.val d) := by
    induction d using Sym2.inductionOn with
    | _ u v => rfl
  ext e
  simp only [Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨e0, he0, heq⟩
    have he0' : e0 ∈ List.map (Sym2.map hom)
        gamma.1.2.2.1.reverse.edges := by
      rw [← SimpleGraph.Walk.edges_map]
      exact he0
    rw [List.mem_map, SimpleGraph.Walk.edges_reverse] at he0'
    obtain ⟨d, hd, hde⟩ := he0'
    refine ⟨Sym2.map Subtype.val d,
      ⟨d, by simpa using hd, rfl⟩, ?_⟩
    calc
      Sym2.map rlc_rot180 (Sym2.map Subtype.val d) =
          Sym2.map Subtype.val (Sym2.map hom d) := (hcomp d).symm
      _ = Sym2.map Subtype.val e0 := congrArg (Sym2.map Subtype.val) hde
      _ = e := heq
  · rintro ⟨a, ⟨d, hd, hda⟩, hae⟩
    refine ⟨Sym2.map hom d, ?_, ?_⟩
    · have hdmap : Sym2.map hom d ∈
          (gamma.1.2.2.1.reverse.map hom).edges := by
        rw [SimpleGraph.Walk.edges_map, List.mem_map,
          SimpleGraph.Walk.edges_reverse]
        exact ⟨d, by simpa using hd, rfl⟩
      exact hdmap
    · calc
        Sym2.map Subtype.val (Sym2.map hom d) =
            Sym2.map rlc_rot180 (Sym2.map Subtype.val d) := hcomp d
        _ = Sym2.map rlc_rot180 a := congrArg (Sym2.map rlc_rot180) hda
        _ = e := hae

lemma rlc_pathEdges_rot180LeftPath {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_pathEdges (rlc_rot180LeftPath gamma).1 =
      (rlc_pathEdges gamma.1).image (Sym2.map rlc_rot180) := by
  classical
  let hom := rlc_rot180LeftInducedHom n
  let w := gamma.1.2.2.1.reverse.map hom
  change w.edges.toFinset.image (Sym2.map Subtype.val) =
    (gamma.1.2.2.1.edges.toFinset.image
      (Sym2.map Subtype.val)).image (Sym2.map rlc_rot180)
  have hcomp (d : Sym2 (rect (-2 * n) 0 (-n) n)) :
      Sym2.map Subtype.val (Sym2.map hom d) =
        Sym2.map rlc_rot180 (Sym2.map Subtype.val d) := by
    induction d using Sym2.inductionOn with
    | _ u v => rfl
  ext e
  simp only [Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨e0, he0, heq⟩
    have he0' : e0 ∈ List.map (Sym2.map hom)
        gamma.1.2.2.1.reverse.edges := by
      rw [← SimpleGraph.Walk.edges_map]
      exact he0
    rw [List.mem_map, SimpleGraph.Walk.edges_reverse] at he0'
    obtain ⟨d, hd, hde⟩ := he0'
    refine ⟨Sym2.map Subtype.val d,
      ⟨d, by simpa using hd, rfl⟩, ?_⟩
    calc
      Sym2.map rlc_rot180 (Sym2.map Subtype.val d) =
          Sym2.map Subtype.val (Sym2.map hom d) := (hcomp d).symm
      _ = Sym2.map Subtype.val e0 := congrArg (Sym2.map Subtype.val) hde
      _ = e := heq
  · rintro ⟨a, ⟨d, hd, hda⟩, hae⟩
    refine ⟨Sym2.map hom d, ?_, ?_⟩
    · have hdmap : Sym2.map hom d ∈
          (gamma.1.2.2.1.reverse.map hom).edges := by
        rw [SimpleGraph.Walk.edges_map, List.mem_map,
          SimpleGraph.Walk.edges_reverse]
        exact ⟨d, by simpa using hd, rfl⟩
      exact hdmap
    · calc
        Sym2.map Subtype.val (Sym2.map hom d) =
            Sym2.map rlc_rot180 (Sym2.map Subtype.val d) := hcomp d
        _ = Sym2.map rlc_rot180 a := congrArg (Sym2.map rlc_rot180) hda
        _ = e := hae

lemma rlc_pathEdges_rot180_roundtrip_left {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_pathEdges (rlc_rot180RightPath
      (rlc_rot180LeftPath gamma)).1 = rlc_pathEdges gamma.1 := by
  rw [rlc_pathEdges_rot180RightPath, rlc_pathEdges_rot180LeftPath,
    Finset.image_image]
  have hinvol : (Sym2.map rlc_rot180 ∘ Sym2.map rlc_rot180) = id := by
    funext e
    induction e using Sym2.inductionOn with
    | _ u v => simp
  rw [hinvol, Finset.image_id]

lemma rlc_swappedRightPathSupport_eq {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_swappedRightPathSupport gamma =
      crf_swap '' (rlc_pathVertices gamma.1 : Set (Site 2)) := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(z : Site 2), ?_, rfl⟩
    simp only [rlc_pathVertices, Finset.mem_coe, Finset.mem_image,
      List.mem_toFinset]
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    simp only [rlc_pathVertices, Finset.mem_coe, Finset.mem_image,
      List.mem_toFinset] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact ⟨u, hu, rfl⟩

lemma rlc_swappedLeftPathSupport_eq {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_swappedLeftPathSupport gamma =
      crf_swap '' (rlc_pathVertices gamma.1 : Set (Site 2)) := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(z : Site 2), ?_, rfl⟩
    simp only [rlc_pathVertices, Finset.mem_coe, Finset.mem_image,
      List.mem_toFinset]
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    simp only [rlc_pathVertices, Finset.mem_coe, Finset.mem_image,
      List.mem_toFinset] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact ⟨u, hu, rfl⟩

lemma rlc_belowSet_boundary_path {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rect 0 (2 * n) (-n) n)
    (hv : v ∈ rect 0 (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_belowSet hn gamma) s(u, v)) :
    u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
  have hbdSwap : bdEdge (rlc_swappedBelowSet hn gamma)
      s(crf_swap u, crf_swap v) := by
    rw [bdEdge_mk] at hbd ⊢
    simpa [rlc_belowSet] using hbd
  have h := (rlc_swappedBelowSet_spec hn gamma).2.2
    (crf_swap u) (crf_swap v)
    ((crf_mem_rect_swap 0 (2 * n) (-n) n u).mp hu)
    ((crf_mem_rect_swap 0 (2 * n) (-n) n v).mp hv)
    ((crf_adj_swap u v).mp hadj) hbdSwap
  rw [rlc_swappedRightPathSupport_eq] at h
  rcases h with ⟨z, hz, hzu⟩ | ⟨z, hz, hzv⟩
  · left
    exact crf_swap.injective hzu |>.symm ▸ hz
  · right
    exact crf_swap.injective hzv |>.symm ▸ hz

lemma rlc_aboveSet_boundary_path {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rect (-2 * n) 0 (-n) n)
    (hv : v ∈ rect (-2 * n) 0 (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_aboveSet hn gamma) s(u, v)) :
    u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
  have hbdSwap : bdEdge (rlc_swappedLeftBelowSet hn gamma)
      s(crf_swap u, crf_swap v) := by
    rw [bdEdge_mk] at hbd ⊢
    simp only [rlc_aboveSet, Set.mem_preimage, Set.mem_compl_iff] at hbd
    tauto
  have h := (rlc_swappedLeftBelowSet_spec hn gamma).2.2
    (crf_swap u) (crf_swap v)
    ((crf_mem_rect_swap (-2 * n) 0 (-n) n u).mp hu)
    ((crf_mem_rect_swap (-2 * n) 0 (-n) n v).mp hv)
    ((crf_adj_swap u v).mp hadj) hbdSwap
  rw [rlc_swappedLeftPathSupport_eq] at h
  rcases h with ⟨z, hz, hzu⟩ | ⟨z, hz, hzv⟩
  · left
    exact crf_swap.injective hzu |>.symm ▸ hz
  · right
    exact crf_swap.injective hzv |>.symm ▸ hz

/-- The lattice graph on the right rectangle with the sites of the given path removed. -/
def rlc_rightPathAvoidGraph {n : ℤ} (gamma : RlcRightDiagonalPath n) :
    SimpleGraph (Site 2) where
  Adj u v := (hypercubicLattice 2).Adj u v ∧
    u ∈ rect 0 (2 * n) (-n) n ∧ v ∈ rect 0 (2 * n) (-n) n ∧
    u ∉ rlc_pathVertices gamma.1 ∧ v ∉ rlc_pathVertices gamma.1
  symm := by
    refine ⟨?_⟩
    intro u v h
    exact ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩
  loopless := ⟨fun u h => (hypercubicLattice 2).irrefl h.1⟩

lemma rlc_rightPathAvoidGraph_walk_dest {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {x z : Site 2}
    (hxR : x ∈ rect 0 (2 * n) (-n) n)
    (hxP : x ∉ rlc_pathVertices gamma.1)
    (w : (rlc_rightPathAvoidGraph gamma).Walk x z) :
    z ∈ rect 0 (2 * n) (-n) n ∧ z ∉ rlc_pathVertices gamma.1 := by
  induction w with
  | nil => exact ⟨hxR, hxP⟩
  | @cons a b c hab w ih =>
      exact ih hab.2.2.1 hab.2.2.2.2

/-- The sites reachable from the top side while avoiding the path: the strict region above a right
  diagonal path. -/
def rlc_strictTopSet {n : ℤ} (gamma : RlcRightDiagonalPath n) :
    Set (Site 2) :=
  {z | ∃ x : Site 2, x ∈ topSide 0 (2 * n) (-n) n ∧
    x ∉ rlc_pathVertices gamma.1 ∧
    (rlc_rightPathAvoidGraph gamma).Reachable x z}

lemma rlc_strictTopSet_subset_box {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_strictTopSet gamma ⊆ rect 0 (2 * n) (-n) n := by
  rintro z ⟨x, hxTop, hxP, hreach⟩
  obtain ⟨w⟩ := hreach
  exact (rlc_rightPathAvoidGraph_walk_dest gamma hxTop.1 hxP w).1

lemma rlc_strictTopSet_disjoint_path {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    Disjoint (rlc_strictTopSet gamma)
      (rlc_pathVertices gamma.1 : Set (Site 2)) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hxTop, hxP, hreach⟩ hzPath
  obtain ⟨w⟩ := hreach
  exact (rlc_rightPathAvoidGraph_walk_dest gamma hxTop.1 hxP w).2 hzPath

lemma rlc_strictTopSet_step {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_strictTopSet gamma)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hvp : v ∉ rlc_pathVertices gamma.1)
    (hadj : (hypercubicLattice 2).Adj u v) :
    v ∈ rlc_strictTopSet gamma := by
  obtain ⟨x, hxTop, hxPath, huv⟩ := hu
  obtain ⟨w⟩ := huv
  have huData := rlc_rightPathAvoidGraph_walk_dest gamma hxTop.1 hxPath w
  have hstep : (rlc_rightPathAvoidGraph gamma).Adj u v :=
    ⟨hadj, huData.1, hvR, huData.2, hvp⟩
  exact ⟨x, hxTop, hxPath, ⟨w.concat hstep⟩⟩

lemma rlc_strictTopSet_boundary_path {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {u v : Site 2}
    (huR : u ∈ rect 0 (2 * n) (-n) n)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_strictTopSet gamma) s(u, v)) :
    u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
  rw [bdEdge_mk] at hbd
  by_cases hu : u ∈ rlc_strictTopSet gamma
  · right
    by_contra hvp
    exact (hbd.mp hu) (rlc_strictTopSet_step gamma hu hvR hvp hadj)
  · left
    by_contra hup
    have hv : v ∈ rlc_strictTopSet gamma := by
      by_contra hv
      exact hu (hbd.mpr hv)
    exact hu (rlc_strictTopSet_step gamma hv huR hup hadj.symm)

lemma rlc_strictTopSet_mono_of_disjoint_path {n : ℤ}
    (gamma lambda : RlcRightDiagonalPath n)
    (hdisj : Disjoint (rlc_strictTopSet gamma)
      (rlc_pathVertices lambda.1 : Set (Site 2))) :
    rlc_strictTopSet gamma ⊆ rlc_strictTopSet lambda := by
  rintro z hz
  obtain ⟨x, hxTop, hxGamma, hreach⟩ := hz
  have hxMem : x ∈ rlc_strictTopSet gamma :=
    ⟨x, hxTop, hxGamma, SimpleGraph.Reachable.refl x⟩
  have hxLambda : x ∉ rlc_pathVertices lambda.1 := fun hx =>
    (Set.disjoint_left.mp hdisj) hxMem hx
  obtain ⟨w⟩ := hreach
  have lift_walk : ∀ {a b : Site 2}
      (q : (rlc_rightPathAvoidGraph gamma).Walk a b),
      a ∈ rlc_strictTopSet gamma →
      (rlc_rightPathAvoidGraph lambda).Walk a b := by
    intro a b q haTop
    induction q with
    | nil => exact .nil
    | @cons a b c hab q ih =>
        have hbTop := rlc_strictTopSet_step gamma haTop hab.2.2.1
          hab.2.2.2.2 hab.1
        have haLambda : a ∉ rlc_pathVertices lambda.1 := fun ha =>
          (Set.disjoint_left.mp hdisj) haTop ha
        have hbLambda : b ∉ rlc_pathVertices lambda.1 := fun hb =>
          (Set.disjoint_left.mp hdisj) hbTop hb
        exact .cons
          ⟨hab.1, (rlc_strictTopSet_subset_box gamma haTop), hab.2.2.1,
            haLambda, hbLambda⟩
          (ih hbTop)
  exact ⟨x, hxTop, hxLambda, ⟨lift_walk w hxMem⟩⟩

/-- The sites reachable from the bottom side while avoiding the path: the strict region below a
  right diagonal path. -/
def rlc_strictBelowSet {n : ℤ} (gamma : RlcRightDiagonalPath n) :
    Set (Site 2) :=
  {z | ∃ x : Site 2, x ∈ bottomSide 0 (2 * n) (-n) n ∧
    x ∉ rlc_pathVertices gamma.1 ∧
    (rlc_rightPathAvoidGraph gamma).Reachable x z}

lemma rlc_strictBelowSet_subset_box {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_strictBelowSet gamma ⊆ rect 0 (2 * n) (-n) n := by
  rintro z ⟨x, hxBottom, hxP, hreach⟩
  obtain ⟨w⟩ := hreach
  exact (rlc_rightPathAvoidGraph_walk_dest gamma hxBottom.1 hxP w).1

lemma rlc_strictBelowSet_disjoint_path {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    Disjoint (rlc_strictBelowSet gamma) (rlc_pathVertices gamma.1 : Set (Site 2)) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hxBottom, hxP, hreach⟩ hzPath
  obtain ⟨w⟩ := hreach
  exact (rlc_rightPathAvoidGraph_walk_dest gamma hxBottom.1 hxP w).2 hzPath

lemma rlc_strictBelowSet_step {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_strictBelowSet gamma)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hvp : v ∉ rlc_pathVertices gamma.1)
    (hadj : (hypercubicLattice 2).Adj u v) :
    v ∈ rlc_strictBelowSet gamma := by
  obtain ⟨x, hxBottom, hxPath, huv⟩ := hu
  obtain ⟨w⟩ := huv
  have huData := rlc_rightPathAvoidGraph_walk_dest gamma
    hxBottom.1 hxPath w
  have hstep : (rlc_rightPathAvoidGraph gamma).Adj u v :=
    ⟨hadj, huData.1, hvR, huData.2, hvp⟩
  exact ⟨x, hxBottom, hxPath, ⟨w.concat hstep⟩⟩

lemma rlc_strictBelowSet_mono_of_disjoint_path {n : ℤ}
    (gamma lambda : RlcRightDiagonalPath n)
    (hdisj : Disjoint (rlc_strictBelowSet gamma)
      (rlc_pathVertices lambda.1 : Set (Site 2))) :
    rlc_strictBelowSet gamma ⊆ rlc_strictBelowSet lambda := by
  rintro z hz
  obtain ⟨x, hxBottom, hxGamma, hreach⟩ := hz
  have hxMem : x ∈ rlc_strictBelowSet gamma :=
    ⟨x, hxBottom, hxGamma, SimpleGraph.Reachable.refl x⟩
  have hxLambda : x ∉ rlc_pathVertices lambda.1 := fun hx =>
    (Set.disjoint_left.mp hdisj) hxMem hx
  obtain ⟨w⟩ := hreach
  have lift_walk : ∀ {a b : Site 2}
      (q : (rlc_rightPathAvoidGraph gamma).Walk a b),
      a ∈ rlc_strictBelowSet gamma →
      (rlc_rightPathAvoidGraph lambda).Walk a b := by
    intro a b q haBelow
    induction q with
    | nil => exact .nil
    | @cons a b c hab q ih =>
        have hbBelow := rlc_strictBelowSet_step gamma haBelow hab.2.2.1
          hab.2.2.2.2 hab.1
        have haLambda : a ∉ rlc_pathVertices lambda.1 := fun ha =>
          (Set.disjoint_left.mp hdisj) haBelow ha
        have hbLambda : b ∉ rlc_pathVertices lambda.1 := fun hb =>
          (Set.disjoint_left.mp hdisj) hbBelow hb
        exact .cons
          ⟨hab.1, (rlc_strictBelowSet_subset_box gamma haBelow), hab.2.2.1,
            haLambda, hbLambda⟩
          (ih hbBelow)
  exact ⟨x, hxBottom, hxLambda, ⟨lift_walk w hxMem⟩⟩

lemma rlc_strictBelowSet_boundary_path {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {u v : Site 2}
    (huR : u ∈ rect 0 (2 * n) (-n) n)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_strictBelowSet gamma) s(u, v)) :
    u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
  rw [bdEdge_mk] at hbd
  by_cases hu : u ∈ rlc_strictBelowSet gamma
  · right
    by_contra hvp
    exact (hbd.mp hu) (rlc_strictBelowSet_step gamma hu hvR hvp hadj)
  · left
    by_contra hup
    have hv : v ∈ rlc_strictBelowSet gamma := by
      by_contra hv
      exact hu (hbd.mpr hv)
    exact hu (rlc_strictBelowSet_step gamma hv huR hup hadj.symm)

/-- The coordinate swap restricted to the graph avoiding a right diagonal path. -/
noncomputable def rlc_swapRightAvoidHom {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_rightPathAvoidGraph gamma →g hypercubicLattice 2 where
  toFun := crf_swap
  map_rel' := by
    intro u v huv
    exact (crf_adj_swap u v).mp huv.1

lemma rlc_topSide_disjoint_strictBelowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) :
    Disjoint (topSide 0 (2 * n) (-n) n) (rlc_strictBelowSet gamma) := by
  rw [Set.disjoint_left]
  intro z hzTop hzBelow
  obtain ⟨x, hxBottom, hxPath, hreach⟩ := hzBelow
  obtain ⟨w⟩ := hreach
  let ws : (hypercubicLattice 2).Walk (crf_swap x) (crf_swap z) :=
    w.map (rlc_swapRightAvoidHom gamma)
  have hwsBox : ∀ p ∈ ws.support, p ∈ rect (-n) n 0 (2 * n) := by
    intro p hp
    dsimp only [ws] at hp
    have hsupp := SimpleGraph.Walk.support_map
      (rlc_swapRightAvoidHom gamma) w
    have hp' : p ∈ List.map (⇑(rlc_swapRightAvoidHom gamma)) w.support := by
      rw [← hsupp]
      exact hp
    rw [List.mem_map] at hp'
    obtain ⟨q, hq, rfl⟩ := hp'
    have hqData := rlc_rightPathAvoidGraph_walk_dest gamma
      hxBottom.1 hxPath (w.takeUntil q hq)
    exact (crf_mem_rect_swap 0 (2 * n) (-n) n q).mp hqData.1
  obtain ⟨p, hpws, hpPath⟩ := tpc_two_paths_cross_of_sep
    (rlc_rightPath_arcSeparatingSet hn gamma)
    ((crf_mem_rect_swap 0 (2 * n) (-n) n x).mp hxBottom.1)
    ((crf_mem_rect_swap 0 (2 * n) (-n) n z).mp hzTop.1)
    (by simpa using hxBottom.2) (by simpa using hzTop.2) ws hwsBox
  dsimp only [ws] at hpws
  have hsupp := SimpleGraph.Walk.support_map
    (rlc_swapRightAvoidHom gamma) w
  have hpws' : p ∈ List.map (⇑(rlc_swapRightAvoidHom gamma)) w.support := by
    rw [← hsupp]
    exact hpws
  rw [List.mem_map] at hpws'
  obtain ⟨q, hq, hqp⟩ := hpws'
  rw [rlc_swappedRightPathSupport_eq] at hpPath
  obtain ⟨r, hrPath, hrp⟩ := hpPath
  have hqr : (q : Site 2) = r := by
    apply crf_swap.injective
    exact hqp.trans hrp.symm
  have hqData := rlc_rightPathAvoidGraph_walk_dest gamma
    hxBottom.1 hxPath (w.takeUntil q hq)
  exact hqData.2 (hqr ▸ hrPath)

lemma rlc_strictBelowSet_subset_belowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) :
    rlc_strictBelowSet gamma ⊆ rlc_belowSet hn gamma := by
  rintro z ⟨x, hxBottom, hxPath, hreach⟩
  obtain ⟨w⟩ := hreach
  have hxBelow : x ∈ rlc_belowSet hn gamma :=
    rlc_bottomSide_subset_belowSet hn gamma hxBottom
  have walk_stays : ∀ {a c : Site 2}
      (q : (rlc_rightPathAvoidGraph gamma).Walk a c),
      a ∈ rlc_belowSet hn gamma → c ∈ rlc_belowSet hn gamma := by
    intro a c q haBelow
    induction q with
    | nil => exact haBelow
    | @cons a b c hab q ih =>
      have hbBelow : b ∈ rlc_belowSet hn gamma := by
        by_contra hbBelow
        have hbd : bdEdge (rlc_belowSet hn gamma) s(a, b) := by
          rw [bdEdge_mk]
          exact iff_of_true haBelow hbBelow
        rcases rlc_belowSet_boundary_path hn gamma hab.2.1 hab.2.2.1
            hab.1 hbd with haPath | hbPath
        · exact hab.2.2.2.1 haPath
        · exact hab.2.2.2.2 hbPath
      exact ih hbBelow
  exact walk_stays w hxBelow

lemma rlc_strictTopSet_disjoint_belowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) :
    Disjoint (rlc_strictTopSet gamma) (rlc_belowSet hn gamma) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hxTop, hxPath, hreach⟩ hzBelow
  obtain ⟨w⟩ := hreach
  have hxOutside : x ∉ rlc_belowSet hn gamma :=
    (Set.disjoint_left.mp (rlc_topSide_disjoint_belowSet hn gamma)) hxTop
  have walk_stays : ∀ {a c : Site 2}
      (q : (rlc_rightPathAvoidGraph gamma).Walk a c),
      a ∉ rlc_belowSet hn gamma → c ∉ rlc_belowSet hn gamma := by
    intro a c q haOutside
    induction q with
    | nil => exact haOutside
    | @cons a b c hab q ih =>
      have hbOutside : b ∉ rlc_belowSet hn gamma := by
        intro hbBelow
        have hbd : bdEdge (rlc_belowSet hn gamma) s(a, b) := by
          rw [bdEdge_mk]
          exact iff_of_false haOutside (not_not.mpr hbBelow)
        rcases rlc_belowSet_boundary_path hn gamma hab.2.1 hab.2.2.1
            hab.1 hbd with haPath | hbPath
        · exact hab.2.2.2.1 haPath
        · exact hab.2.2.2.2 hbPath
      exact ih hbOutside
  exact (walk_stays w hxOutside) hzBelow

lemma rlc_strictTopSet_disjoint_strictBelowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) :
    Disjoint (rlc_strictTopSet gamma) (rlc_strictBelowSet gamma) :=
  (rlc_strictTopSet_disjoint_belowSet hn gamma).mono_right
    (rlc_strictBelowSet_subset_belowSet hn gamma)

lemma rlc_disjointRightPaths_not_mutually_top {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1)) :
    ¬ ((rlc_pathVertices gamma.1 : Set (Site 2)) ⊆
          rlc_strictTopSet delta ∧
        (rlc_pathVertices delta.1 : Set (Site 2)) ⊆
          rlc_strictTopSet gamma) := by
  rintro ⟨hgammaTop, hdeltaTop⟩
  let x : Site 2 := ![0, -n]
  have hxBottom : x ∈ bottomSide 0 (2 * n) (-n) n := by
    rw [mem_bottomSide, mem_rect]
    simp [x]
    omega
  by_cases hxDelta : x ∈ rlc_pathVertices delta.1
  · have hxNotGamma : x ∉ rlc_pathVertices gamma.1 := fun hxGamma =>
      (Finset.disjoint_left.mp hdisj) hxGamma hxDelta
    have hxBelowGamma : x ∈ rlc_strictBelowSet gamma :=
      ⟨x, hxBottom, hxNotGamma, SimpleGraph.Reachable.refl x⟩
    exact (Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_strictBelowSet hn gamma))
        (hdeltaTop hxDelta) hxBelowGamma
  · have hxBelowDelta : x ∈ rlc_strictBelowSet delta :=
      ⟨x, hxBottom, hxDelta, SimpleGraph.Reachable.refl x⟩
    have hbelowDisjGamma : Disjoint (rlc_strictBelowSet delta)
        (rlc_pathVertices gamma.1 : Set (Site 2)) := by
      rw [Set.disjoint_left]
      intro z hzBelow hzGamma
      exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_strictBelowSet hn delta))
          (hgammaTop hzGamma) hzBelow
    have hbelowMono : rlc_strictBelowSet delta ⊆
        rlc_strictBelowSet gamma :=
      rlc_strictBelowSet_mono_of_disjoint_path
        delta gamma hbelowDisjGamma
    let y : Site 2 := ![0, n]
    have hyTop : y ∈ topSide 0 (2 * n) (-n) n := by
      rw [mem_topSide, mem_rect]
      simp [y]
      omega
    have hyNotBelow : y ∉ rlc_strictBelowSet delta := fun hy =>
      (Set.disjoint_left.mp
        (rlc_topSide_disjoint_strictBelowSet hn delta)) hyTop hy
    let w : (hypercubicLattice 2).Walk x y := sw_vertSeg 0 (-n) n
    have hwRect : ∀ z ∈ w.support, z ∈ rect 0 (2 * n) (-n) n := by
      intro z hz
      have hz' := sw_vertSeg_support_subset 0 (-n) n hz
      obtain ⟨t, ht, rfl⟩ := hz'
      rw [Set.uIcc_of_le (by omega)] at ht
      change -n ≤ t ∧ t ≤ n at ht
      rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    obtain ⟨a, b, hab, haBelow, hbNotBelow, haRect, hbRect⟩ :=
      crr_walk_exit_set_in_box (rlc_strictBelowSet delta)
        (rect 0 (2 * n) (-n) n) w hwRect hxBelowDelta hyNotBelow
    have hbd : bdEdge (rlc_strictBelowSet delta) s(a, b) := by
      rw [bdEdge_mk]
      exact iff_of_true haBelow hbNotBelow
    have hbDelta : b ∈ rlc_pathVertices delta.1 := by
      rcases rlc_strictBelowSet_boundary_path delta haRect hbRect hab hbd with
        haDelta | hbDelta
      · exact False.elim ((Set.disjoint_left.mp
          (rlc_strictBelowSet_disjoint_path delta)) haBelow haDelta)
      · exact hbDelta
    have hbNotGamma : b ∉ rlc_pathVertices gamma.1 := fun hbGamma =>
      (Finset.disjoint_left.mp hdisj) hbGamma hbDelta
    have haBelowGamma : a ∈ rlc_strictBelowSet gamma := hbelowMono haBelow
    have hbBelowGamma : b ∈ rlc_strictBelowSet gamma :=
      rlc_strictBelowSet_step gamma haBelowGamma hbRect hbNotGamma hab
    exact (Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_strictBelowSet hn gamma))
        (hdeltaTop hbDelta) hbBelowGamma

/-- The lattice graph on the left rectangle with the sites of the given path removed. -/
def rlc_leftPathAvoidGraph {n : ℤ} (gamma : RlcLeftDiagonalPath n) :
    SimpleGraph (Site 2) where
  Adj u v := (hypercubicLattice 2).Adj u v ∧
    u ∈ rect (-2 * n) 0 (-n) n ∧ v ∈ rect (-2 * n) 0 (-n) n ∧
    u ∉ rlc_pathVertices gamma.1 ∧ v ∉ rlc_pathVertices gamma.1
  symm := by
    refine ⟨?_⟩
    intro u v h
    exact ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩
  loopless := ⟨fun u h => (hypercubicLattice 2).irrefl h.1⟩

lemma rlc_leftPathAvoidGraph_walk_dest {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) {x z : Site 2}
    (hxR : x ∈ rect (-2 * n) 0 (-n) n)
    (hxP : x ∉ rlc_pathVertices gamma.1)
    (w : (rlc_leftPathAvoidGraph gamma).Walk x z) :
    z ∈ rect (-2 * n) 0 (-n) n ∧ z ∉ rlc_pathVertices gamma.1 := by
  induction w with
  | nil => exact ⟨hxR, hxP⟩
  | @cons a b c hab w ih =>
      exact ih hab.2.2.1 hab.2.2.2.2

/-- The strict region below a left diagonal path: sites reachable from the bottom side while
  avoiding it. -/
def rlc_strictBottomSet {n : ℤ} (gamma : RlcLeftDiagonalPath n) :
    Set (Site 2) :=
  {z | ∃ x : Site 2, x ∈ bottomSide (-2 * n) 0 (-n) n ∧
    x ∉ rlc_pathVertices gamma.1 ∧
    (rlc_leftPathAvoidGraph gamma).Reachable x z}

lemma rlc_strictBottomSet_subset_box {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_strictBottomSet gamma ⊆ rect (-2 * n) 0 (-n) n := by
  rintro z ⟨x, hxBottom, hxP, hreach⟩
  obtain ⟨w⟩ := hreach
  exact (rlc_leftPathAvoidGraph_walk_dest gamma hxBottom.1 hxP w).1

lemma rlc_strictBottomSet_disjoint_path {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    Disjoint (rlc_strictBottomSet gamma)
      (rlc_pathVertices gamma.1 : Set (Site 2)) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hxBottom, hxP, hreach⟩ hzPath
  obtain ⟨w⟩ := hreach
  exact (rlc_leftPathAvoidGraph_walk_dest gamma hxBottom.1 hxP w).2 hzPath

lemma rlc_strictBottomSet_step {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_strictBottomSet gamma)
    (hvR : v ∈ rect (-2 * n) 0 (-n) n)
    (hvp : v ∉ rlc_pathVertices gamma.1)
    (hadj : (hypercubicLattice 2).Adj u v) :
    v ∈ rlc_strictBottomSet gamma := by
  obtain ⟨x, hxBottom, hxPath, huv⟩ := hu
  obtain ⟨w⟩ := huv
  have huData := rlc_leftPathAvoidGraph_walk_dest gamma hxBottom.1 hxPath w
  have hstep : (rlc_leftPathAvoidGraph gamma).Adj u v :=
    ⟨hadj, huData.1, hvR, huData.2, hvp⟩
  exact ⟨x, hxBottom, hxPath, ⟨w.concat hstep⟩⟩

lemma rlc_strictBottomSet_boundary_path {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) {u v : Site 2}
    (huR : u ∈ rect (-2 * n) 0 (-n) n)
    (hvR : v ∈ rect (-2 * n) 0 (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_strictBottomSet gamma) s(u, v)) :
    u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
  rw [bdEdge_mk] at hbd
  by_cases hu : u ∈ rlc_strictBottomSet gamma
  · right
    by_contra hvp
    exact (hbd.mp hu) (rlc_strictBottomSet_step gamma hu hvR hvp hadj)
  · left
    by_contra hup
    have hv : v ∈ rlc_strictBottomSet gamma := by
      by_contra hv
      exact hu (hbd.mpr hv)
    exact hu (rlc_strictBottomSet_step gamma hv huR hup hadj.symm)

lemma rlc_strictTopSet_eq_of_pathVertices_eq {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hverts : rlc_pathVertices gamma.1 = rlc_pathVertices delta.1) :
    rlc_strictTopSet gamma = rlc_strictTopSet delta := by
  have hgraph : rlc_rightPathAvoidGraph gamma =
      rlc_rightPathAvoidGraph delta := by
    ext u v
    simp only [rlc_rightPathAvoidGraph]
    rw [hverts]
  ext z
  simp only [rlc_strictTopSet, Set.mem_ofPred_eq]
  rw [hgraph, hverts]

lemma rlc_strictBottomSet_eq_of_pathVertices_eq {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n)
    (hverts : rlc_pathVertices gamma.1 = rlc_pathVertices delta.1) :
    rlc_strictBottomSet gamma = rlc_strictBottomSet delta := by
  have hgraph : rlc_leftPathAvoidGraph gamma =
      rlc_leftPathAvoidGraph delta := by
    ext u v
    simp only [rlc_leftPathAvoidGraph]
    rw [hverts]
  ext z
  simp only [rlc_strictBottomSet, Set.mem_ofPred_eq]
  rw [hgraph, hverts]

/-- Rotation by `π` between the avoid-graphs of a right path and its rotated left path. -/
noncomputable def rlc_rot180RightAvoidHom {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_rightPathAvoidGraph gamma →g
      rlc_leftPathAvoidGraph (rlc_rot180RightPath gamma) where
  toFun := rlc_rot180
  map_rel' := by
    intro u v h
    refine ⟨(rlc_adj_rot180 u v).mp h.1,
      (rlc_rot180_mem_rightRect_iff_leftRect n u).mp h.2.1,
      (rlc_rot180_mem_rightRect_iff_leftRect n v).mp h.2.2.1, ?_, ?_⟩
    · intro hu
      rw [rlc_pathVertices_rot180RightPath, Finset.mem_image] at hu
      obtain ⟨z, hz, hzu⟩ := hu
      have hzu' : z = u := rlc_rot180.injective (by
        simpa using hzu)
      exact h.2.2.2.1 (hzu' ▸ hz)
    · intro hv
      rw [rlc_pathVertices_rot180RightPath, Finset.mem_image] at hv
      obtain ⟨z, hz, hzv⟩ := hv
      have hzv' : z = v := rlc_rot180.injective (by
        simpa using hzv)
      exact h.2.2.2.2 (hzv' ▸ hz)

lemma rlc_rot180_mem_strictBottom_of_mem_strictTop {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {z : Site 2}
    (hz : z ∈ rlc_strictTopSet gamma) :
    rlc_rot180 z ∈ rlc_strictBottomSet (rlc_rot180RightPath gamma) := by
  obtain ⟨x, hxTop, hxPath, hreach⟩ := hz
  obtain ⟨w⟩ := hreach
  have hxBottom : rlc_rot180 x ∈ bottomSide (-2 * n) 0 (-n) n := by
    rw [mem_bottomSide]
    rw [mem_topSide] at hxTop
    refine ⟨(rlc_rot180_mem_rightRect_iff_leftRect n x).mp hxTop.1, ?_⟩
    simp only [rlc_rot180_one, hxTop.2]
  have hxNot : rlc_rot180 x ∉
      rlc_pathVertices (rlc_rot180RightPath gamma).1 := by
    intro hx
    rw [rlc_pathVertices_rot180RightPath, Finset.mem_image] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := rlc_rot180.injective (by simpa using hyx)
    exact hxPath (this ▸ hy)
  exact ⟨rlc_rot180 x, hxBottom, hxNot,
    ⟨w.map (rlc_rot180RightAvoidHom gamma)⟩⟩

/-- Rotation by `π` between the avoid-graphs of a left path and its rotated right path. -/
noncomputable def rlc_rot180LeftAvoidHom {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_leftPathAvoidGraph gamma →g
      rlc_rightPathAvoidGraph (rlc_rot180LeftPath gamma) where
  toFun := rlc_rot180
  map_rel' := by
    intro u v h
    refine ⟨(rlc_adj_rot180 u v).mp h.1,
      (rlc_rot180_mem_leftRect_iff_rightRect n u).mp h.2.1,
      (rlc_rot180_mem_leftRect_iff_rightRect n v).mp h.2.2.1, ?_, ?_⟩
    · intro hu
      rw [rlc_pathVertices_rot180LeftPath, Finset.mem_image] at hu
      obtain ⟨z, hz, hzu⟩ := hu
      have hzu' : z = u := rlc_rot180.injective (by simpa using hzu)
      exact h.2.2.2.1 (hzu' ▸ hz)
    · intro hv
      rw [rlc_pathVertices_rot180LeftPath, Finset.mem_image] at hv
      obtain ⟨z, hz, hzv⟩ := hv
      have hzv' : z = v := rlc_rot180.injective (by simpa using hzv)
      exact h.2.2.2.2 (hzv' ▸ hz)

lemma rlc_rot180_mem_strictTop_of_mem_strictBottom {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) {z : Site 2}
    (hz : z ∈ rlc_strictBottomSet gamma) :
    rlc_rot180 z ∈ rlc_strictTopSet (rlc_rot180LeftPath gamma) := by
  obtain ⟨x, hxBottom, hxPath, hreach⟩ := hz
  obtain ⟨w⟩ := hreach
  have hxTop : rlc_rot180 x ∈ topSide 0 (2 * n) (-n) n := by
    rw [mem_topSide]
    rw [mem_bottomSide] at hxBottom
    refine ⟨(rlc_rot180_mem_leftRect_iff_rightRect n x).mp hxBottom.1, ?_⟩
    simp only [rlc_rot180_one, hxBottom.2]
    omega
  have hxNot : rlc_rot180 x ∉
      rlc_pathVertices (rlc_rot180LeftPath gamma).1 := by
    intro hx
    rw [rlc_pathVertices_rot180LeftPath, Finset.mem_image] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := rlc_rot180.injective (by simpa using hyx)
    exact hxPath (this ▸ hy)
  exact ⟨rlc_rot180 x, hxTop, hxNot,
    ⟨w.map (rlc_rot180LeftAvoidHom gamma)⟩⟩

lemma rlc_rot180_mem_strictBottom_iff_mem_strictTop {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (z : Site 2) :
    rlc_rot180 z ∈ rlc_strictBottomSet (rlc_rot180RightPath gamma) ↔
      z ∈ rlc_strictTopSet gamma := by
  constructor
  · intro hz
    have hdouble := rlc_rot180_mem_strictTop_of_mem_strictBottom
      (rlc_rot180RightPath gamma) hz
    have heq := rlc_strictTopSet_eq_of_pathVertices_eq
      (rlc_rot180LeftPath (rlc_rot180RightPath gamma)) gamma
      (rlc_pathVertices_rot180_roundtrip_right gamma)
    rw [heq] at hdouble
    simpa using hdouble
  · exact rlc_rot180_mem_strictBottom_of_mem_strictTop gamma

lemma rlc_rot180_mem_strictTop_iff_mem_strictBottom {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) (z : Site 2) :
    rlc_rot180 z ∈ rlc_strictTopSet (rlc_rot180LeftPath gamma) ↔
      z ∈ rlc_strictBottomSet gamma := by
  constructor
  · intro hz
    have hdouble := rlc_rot180_mem_strictBottom_of_mem_strictTop
      (rlc_rot180LeftPath gamma) hz
    have heq := rlc_strictBottomSet_eq_of_pathVertices_eq
      (rlc_rot180RightPath (rlc_rot180LeftPath gamma)) gamma
      (rlc_pathVertices_rot180_roundtrip_left gamma)
    rw [heq] at hdouble
    simpa using hdouble
  · exact rlc_rot180_mem_strictTop_of_mem_strictBottom gamma

lemma rlc_strictBottomSet_mono_of_disjoint_path {n : ℤ}
    (gamma lambda : RlcLeftDiagonalPath n)
    (hdisj : Disjoint (rlc_strictBottomSet gamma)
      (rlc_pathVertices lambda.1 : Set (Site 2))) :
    rlc_strictBottomSet gamma ⊆ rlc_strictBottomSet lambda := by
  rintro z hz
  obtain ⟨x, hxBottom, hxGamma, hreach⟩ := hz
  have hxMem : x ∈ rlc_strictBottomSet gamma :=
    ⟨x, hxBottom, hxGamma, SimpleGraph.Reachable.refl x⟩
  have hxLambda : x ∉ rlc_pathVertices lambda.1 := fun hx =>
    (Set.disjoint_left.mp hdisj) hxMem hx
  obtain ⟨w⟩ := hreach
  have lift_walk : ∀ {a b : Site 2}
      (q : (rlc_leftPathAvoidGraph gamma).Walk a b),
      a ∈ rlc_strictBottomSet gamma →
      (rlc_leftPathAvoidGraph lambda).Walk a b := by
    intro a b q haBottom
    induction q with
    | nil => exact .nil
    | @cons a b c hab q ih =>
        have hbBottom := rlc_strictBottomSet_step gamma haBottom hab.2.2.1
          hab.2.2.2.2 hab.1
        have haLambda : a ∉ rlc_pathVertices lambda.1 := fun ha =>
          (Set.disjoint_left.mp hdisj) haBottom ha
        have hbLambda : b ∉ rlc_pathVertices lambda.1 := fun hb =>
          (Set.disjoint_left.mp hdisj) hbBottom hb
        exact .cons
          ⟨hab.1, (rlc_strictBottomSet_subset_box gamma haBottom), hab.2.2.1,
            haLambda, hbLambda⟩
          (ih hbBottom)
  exact ⟨x, hxBottom, hxLambda, ⟨lift_walk w hxMem⟩⟩

/-- The strict region above a left diagonal path: sites reachable from the top side while avoiding
  it. -/
def rlc_strictAboveSet {n : ℤ} (gamma : RlcLeftDiagonalPath n) :
    Set (Site 2) :=
  {z | ∃ x : Site 2, x ∈ topSide (-2 * n) 0 (-n) n ∧
    x ∉ rlc_pathVertices gamma.1 ∧
    (rlc_leftPathAvoidGraph gamma).Reachable x z}

lemma rlc_strictAboveSet_subset_box {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_strictAboveSet gamma ⊆ rect (-2 * n) 0 (-n) n := by
  rintro z ⟨x, hxTop, hxP, hreach⟩
  obtain ⟨w⟩ := hreach
  exact (rlc_leftPathAvoidGraph_walk_dest gamma hxTop.1 hxP w).1

lemma rlc_strictAboveSet_disjoint_path {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    Disjoint (rlc_strictAboveSet gamma) (rlc_pathVertices gamma.1 : Set (Site 2)) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hxTop, hxP, hreach⟩ hzPath
  obtain ⟨w⟩ := hreach
  exact (rlc_leftPathAvoidGraph_walk_dest gamma hxTop.1 hxP w).2 hzPath

lemma rlc_strictAboveSet_step {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_strictAboveSet gamma)
    (hvR : v ∈ rect (-2 * n) 0 (-n) n)
    (hvp : v ∉ rlc_pathVertices gamma.1)
    (hadj : (hypercubicLattice 2).Adj u v) :
    v ∈ rlc_strictAboveSet gamma := by
  obtain ⟨x, hxTop, hxPath, huv⟩ := hu
  obtain ⟨w⟩ := huv
  have huData := rlc_leftPathAvoidGraph_walk_dest gamma hxTop.1 hxPath w
  have hstep : (rlc_leftPathAvoidGraph gamma).Adj u v :=
    ⟨hadj, huData.1, hvR, huData.2, hvp⟩
  exact ⟨x, hxTop, hxPath, ⟨w.concat hstep⟩⟩

lemma rlc_strictAboveSet_boundary_path {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) {u v : Site 2}
    (huR : u ∈ rect (-2 * n) 0 (-n) n)
    (hvR : v ∈ rect (-2 * n) 0 (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_strictAboveSet gamma) s(u, v)) :
    u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
  rw [bdEdge_mk] at hbd
  by_cases hu : u ∈ rlc_strictAboveSet gamma
  · right
    by_contra hvp
    exact (hbd.mp hu) (rlc_strictAboveSet_step gamma hu hvR hvp hadj)
  · left
    by_contra hup
    have hv : v ∈ rlc_strictAboveSet gamma := by
      by_contra hv
      exact hu (hbd.mpr hv)
    exact hu (rlc_strictAboveSet_step gamma hv huR hup hadj.symm)

/-- The coordinate swap restricted to the graph avoiding a left diagonal path. -/
noncomputable def rlc_swapLeftAvoidHom {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_leftPathAvoidGraph gamma →g hypercubicLattice 2 where
  toFun := crf_swap
  map_rel' := by
    intro u v huv
    exact (crf_adj_swap u v).mp huv.1

lemma rlc_leftBottomSide_disjoint_strictAboveSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    Disjoint (bottomSide (-2 * n) 0 (-n) n)
      (rlc_strictAboveSet gamma) := by
  rw [Set.disjoint_left]
  intro z hzBottom hzAbove
  obtain ⟨x, hxTop, hxPath, hreach⟩ := hzAbove
  obtain ⟨w⟩ := hreach
  let ws : (hypercubicLattice 2).Walk (crf_swap z) (crf_swap x) :=
    w.reverse.map (rlc_swapLeftAvoidHom gamma)
  have hwsBox : ∀ p ∈ ws.support, p ∈ rect (-n) n (-2 * n) 0 := by
    intro p hp
    dsimp only [ws] at hp
    have hsupp := SimpleGraph.Walk.support_map
      (rlc_swapLeftAvoidHom gamma) w.reverse
    have hp' : p ∈ List.map (⇑(rlc_swapLeftAvoidHom gamma))
        w.reverse.support := by
      rw [← hsupp]
      exact hp
    rw [List.mem_map] at hp'
    obtain ⟨q, hq, rfl⟩ := hp'
    have hq' : q ∈ w.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hq
    have hqData := rlc_leftPathAvoidGraph_walk_dest gamma
      hxTop.1 hxPath (w.takeUntil q hq')
    exact (crf_mem_rect_swap (-2 * n) 0 (-n) n q).mp hqData.1
  obtain ⟨p, hpws, hpPath⟩ := tpc_two_paths_cross_of_sep
    (rlc_leftPath_arcSeparatingSet hn gamma)
    ((crf_mem_rect_swap (-2 * n) 0 (-n) n z).mp hzBottom.1)
    ((crf_mem_rect_swap (-2 * n) 0 (-n) n x).mp hxTop.1)
    (by simpa using hzBottom.2) (by simpa using hxTop.2) ws hwsBox
  dsimp only [ws] at hpws
  have hsupp := SimpleGraph.Walk.support_map
    (rlc_swapLeftAvoidHom gamma) w.reverse
  have hpws' : p ∈ List.map (⇑(rlc_swapLeftAvoidHom gamma))
      w.reverse.support := by
    rw [← hsupp]
    exact hpws
  rw [List.mem_map] at hpws'
  obtain ⟨q, hq, hqp⟩ := hpws'
  have hq' : q ∈ w.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hq
  rw [rlc_swappedLeftPathSupport_eq] at hpPath
  obtain ⟨r, hrPath, hrp⟩ := hpPath
  have hqr : (q : Site 2) = r := by
    apply crf_swap.injective
    exact hqp.trans hrp.symm
  have hqData := rlc_leftPathAvoidGraph_walk_dest gamma
    hxTop.1 hxPath (w.takeUntil q hq')
  exact hqData.2 (hqr ▸ hrPath)

lemma rlc_strictAboveSet_subset_aboveSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    rlc_strictAboveSet gamma ⊆ rlc_aboveSet hn gamma := by
  rintro z ⟨x, hxTop, hxPath, hreach⟩
  obtain ⟨w⟩ := hreach
  have hxAbove : x ∈ rlc_aboveSet hn gamma :=
    rlc_leftTopSide_subset_aboveSet hn gamma hxTop
  have walk_stays : ∀ {a c : Site 2}
      (q : (rlc_leftPathAvoidGraph gamma).Walk a c),
      a ∈ rlc_aboveSet hn gamma → c ∈ rlc_aboveSet hn gamma := by
    intro a c q haAbove
    induction q with
    | nil => exact haAbove
    | @cons a b c hab q ih =>
      have hbAbove : b ∈ rlc_aboveSet hn gamma := by
        by_contra hbAbove
        have hbd : bdEdge (rlc_aboveSet hn gamma) s(a, b) := by
          rw [bdEdge_mk]
          exact iff_of_true haAbove hbAbove
        rcases rlc_aboveSet_boundary_path hn gamma hab.2.1 hab.2.2.1
            hab.1 hbd with haPath | hbPath
        · exact hab.2.2.2.1 haPath
        · exact hab.2.2.2.2 hbPath
      exact ih hbAbove
  exact walk_stays w hxAbove

lemma rlc_strictBottomSet_disjoint_aboveSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    Disjoint (rlc_strictBottomSet gamma) (rlc_aboveSet hn gamma) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hxBottom, hxPath, hreach⟩ hzAbove
  obtain ⟨w⟩ := hreach
  have hxOutside : x ∉ rlc_aboveSet hn gamma :=
    (Set.disjoint_left.mp
      (rlc_leftBottomSide_disjoint_aboveSet hn gamma)) hxBottom
  have walk_stays : ∀ {a c : Site 2}
      (q : (rlc_leftPathAvoidGraph gamma).Walk a c),
      a ∉ rlc_aboveSet hn gamma → c ∉ rlc_aboveSet hn gamma := by
    intro a c q haOutside
    induction q with
    | nil => exact haOutside
    | @cons a b c hab q ih =>
      have hbOutside : b ∉ rlc_aboveSet hn gamma := by
        intro hbAbove
        have hbd : bdEdge (rlc_aboveSet hn gamma) s(a, b) := by
          rw [bdEdge_mk]
          exact iff_of_false haOutside (not_not.mpr hbAbove)
        rcases rlc_aboveSet_boundary_path hn gamma hab.2.1 hab.2.2.1
            hab.1 hbd with haPath | hbPath
        · exact hab.2.2.2.1 haPath
        · exact hab.2.2.2.2 hbPath
      exact ih hbOutside
  exact (walk_stays w hxOutside) hzAbove

lemma rlc_strictBottomSet_disjoint_strictAboveSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) :
    Disjoint (rlc_strictBottomSet gamma) (rlc_strictAboveSet gamma) :=
  (rlc_strictBottomSet_disjoint_aboveSet hn gamma).mono_right
    (rlc_strictAboveSet_subset_aboveSet hn gamma)

lemma rlc_strictBelowSet_finite {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    (rlc_strictBelowSet gamma).Finite :=
  (rect_finite 0 (2 * n) (-n) n).subset
    (rlc_strictBelowSet_subset_box gamma)

lemma rlc_strictAboveSet_finite {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    (rlc_strictAboveSet gamma).Finite :=
  (rect_finite (-2 * n) 0 (-n) n).subset
    (rlc_strictAboveSet_subset_box gamma)

lemma rlc_strictTopSet_finite {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    (rlc_strictTopSet gamma).Finite :=
  (rect_finite 0 (2 * n) (-n) n).subset
    (rlc_strictTopSet_subset_box gamma)

lemma rlc_strictBottomSet_finite {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    (rlc_strictBottomSet gamma).Finite :=
  (rect_finite (-2 * n) 0 (-n) n).subset
    (rlc_strictBottomSet_subset_box gamma)

lemma rlc_bdEdge_inter {S T : Set (Site 2)} {e : Sym2 (Site 2)}
    (h : bdEdge (S ∩ T) e) : bdEdge S e ∨ bdEdge T e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [bdEdge_mk, Set.mem_inter_iff] at h ⊢
      tauto

lemma rlc_bdEdge_union {S T : Set (Site 2)} {e : Sym2 (Site 2)}
    (h : bdEdge (S ∪ T) e) : bdEdge S e ∨ bdEdge T e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [bdEdge_mk, Set.mem_union] at h ⊢
      tauto

/-- The union of the strict regions above two right diagonal paths. -/
def rlc_rightUpperUnionSet {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) : Set (Site 2) :=
  rlc_strictTopSet gamma ∪ rlc_strictTopSet delta

lemma rlc_rightUpperUnionSet_finite {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_rightUpperUnionSet gamma delta).Finite :=
  (rlc_strictTopSet_finite gamma).union
    (rlc_strictTopSet_finite delta)

lemma rlc_rightUpperUnionSet_boundary_paths {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (huR : u ∈ rect 0 (2 * n) (-n) n)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_rightUpperUnionSet gamma delta) s(u, v)) :
    (u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1) ∨
      (u ∈ rlc_pathVertices delta.1 ∨ v ∈ rlc_pathVertices delta.1) := by
  rcases rlc_bdEdge_union hbd with hgamma | hdelta
  · exact Or.inl (rlc_strictTopSet_boundary_path gamma huR hvR hadj hgamma)
  · exact Or.inr (rlc_strictTopSet_boundary_path delta huR hvR hadj hdelta)

lemma rlc_rightUpperUnionSet_exit_mem_paths {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_rightUpperUnionSet gamma delta)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hv : v ∉ rlc_rightUpperUnionSet gamma delta)
    (hadj : (hypercubicLattice 2).Adj u v) :
    v ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices delta.1 := by
  rcases hu with huGamma | huDelta
  · have hvGamma : v ∉ rlc_strictTopSet gamma := fun h => hv (Or.inl h)
    have hbd : bdEdge (rlc_strictTopSet gamma) s(u, v) := by
      rw [bdEdge_mk]
      exact iff_of_true huGamma hvGamma
    rcases rlc_strictTopSet_boundary_path gamma
        (rlc_strictTopSet_subset_box gamma huGamma) hvR hadj hbd with huP | hvP
    · exact False.elim ((Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path gamma)) huGamma huP)
    · exact Or.inl hvP
  · have hvDelta : v ∉ rlc_strictTopSet delta := fun h => hv (Or.inr h)
    have hbd : bdEdge (rlc_strictTopSet delta) s(u, v) := by
      rw [bdEdge_mk]
      exact iff_of_true huDelta hvDelta
    rcases rlc_strictTopSet_boundary_path delta
        (rlc_strictTopSet_subset_box delta huDelta) hvR hadj hbd with huP | hvP
    · exact False.elim ((Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path delta)) huDelta huP)
    · exact Or.inr hvP

/-- The union of the strict regions below two left diagonal paths. -/
def rlc_leftLowerUnionSet {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) : Set (Site 2) :=
  rlc_strictBottomSet gamma ∪ rlc_strictBottomSet delta

lemma rlc_leftLowerUnionSet_finite {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) :
    (rlc_leftLowerUnionSet gamma delta).Finite :=
  (rlc_strictBottomSet_finite gamma).union
    (rlc_strictBottomSet_finite delta)

lemma rlc_leftLowerUnionSet_boundary_paths {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) {u v : Site 2}
    (huR : u ∈ rect (-2 * n) 0 (-n) n)
    (hvR : v ∈ rect (-2 * n) 0 (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_leftLowerUnionSet gamma delta) s(u, v)) :
    (u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1) ∨
      (u ∈ rlc_pathVertices delta.1 ∨ v ∈ rlc_pathVertices delta.1) := by
  rcases rlc_bdEdge_union hbd with hgamma | hdelta
  · exact Or.inl (rlc_strictBottomSet_boundary_path gamma huR hvR hadj hgamma)
  · exact Or.inr (rlc_strictBottomSet_boundary_path delta huR hvR hadj hdelta)

lemma rlc_leftLowerUnionSet_exit_mem_paths {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_leftLowerUnionSet gamma delta)
    (hvR : v ∈ rect (-2 * n) 0 (-n) n)
    (hv : v ∉ rlc_leftLowerUnionSet gamma delta)
    (hadj : (hypercubicLattice 2).Adj u v) :
    v ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices delta.1 := by
  rcases hu with huGamma | huDelta
  · have hvGamma : v ∉ rlc_strictBottomSet gamma := fun h => hv (Or.inl h)
    have hbd : bdEdge (rlc_strictBottomSet gamma) s(u, v) := by
      rw [bdEdge_mk]
      exact iff_of_true huGamma hvGamma
    rcases rlc_strictBottomSet_boundary_path gamma
        (rlc_strictBottomSet_subset_box gamma huGamma) hvR hadj hbd with huP | hvP
    · exact False.elim ((Set.disjoint_left.mp
        (rlc_strictBottomSet_disjoint_path gamma)) huGamma huP)
    · exact Or.inl hvP
  · have hvDelta : v ∉ rlc_strictBottomSet delta := fun h => hv (Or.inr h)
    have hbd : bdEdge (rlc_strictBottomSet delta) s(u, v) := by
      rw [bdEdge_mk]
      exact iff_of_true huDelta hvDelta
    rcases rlc_strictBottomSet_boundary_path delta
        (rlc_strictBottomSet_subset_box delta huDelta) hvR hadj hbd with huP | hvP
    · exact False.elim ((Set.disjoint_left.mp
        (rlc_strictBottomSet_disjoint_path delta)) huDelta huP)
    · exact Or.inr hvP

/-- The intersection of the strict regions below two right diagonal paths. -/
def rlc_commonStrictBelowSet {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) : Set (Site 2) :=
  rlc_strictBelowSet gamma ∩ rlc_strictBelowSet delta

lemma rlc_commonStrictBelowSet_finite {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_commonStrictBelowSet gamma delta).Finite :=
  (rlc_strictBelowSet_finite gamma).inter_of_left
    (rlc_strictBelowSet delta)

lemma rlc_bottom_mem_commonStrictBelowSet {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {z : Site 2}
    (hz : z ∈ bottomSide 0 (2 * n) (-n) n)
    (hgamma : z ∉ rlc_pathVertices gamma.1)
    (hdelta : z ∉ rlc_pathVertices delta.1) :
    z ∈ rlc_commonStrictBelowSet gamma delta := by
  exact ⟨⟨z, hz, hgamma, SimpleGraph.Reachable.refl z⟩,
    ⟨z, hz, hdelta, SimpleGraph.Reachable.refl z⟩⟩

lemma rlc_topSide_disjoint_commonStrictBelowSet {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) :
    Disjoint (topSide 0 (2 * n) (-n) n)
      (rlc_commonStrictBelowSet gamma delta) := by
  rw [Set.disjoint_left]
  intro z hzTop hzCommon
  exact (Set.disjoint_left.mp (rlc_topSide_disjoint_strictBelowSet hn gamma))
    hzTop hzCommon.1

lemma rlc_commonStrictBelowSet_boundary_paths {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (huR : u ∈ rect 0 (2 * n) (-n) n)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_commonStrictBelowSet gamma delta) s(u, v)) :
    (u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1) ∨
      (u ∈ rlc_pathVertices delta.1 ∨ v ∈ rlc_pathVertices delta.1) := by
  rcases rlc_bdEdge_inter hbd with hgamma | hdelta
  · exact Or.inl (rlc_strictBelowSet_boundary_path gamma huR hvR hadj hgamma)
  · exact Or.inr (rlc_strictBelowSet_boundary_path delta huR hvR hadj hdelta)

/-- The lattice graph on the right rectangle with the sites of both paths removed. -/
def rlc_rightPairAvoidGraph {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) : SimpleGraph (Site 2) where
  Adj u v := (hypercubicLattice 2).Adj u v ∧
    u ∈ rect 0 (2 * n) (-n) n ∧ v ∈ rect 0 (2 * n) (-n) n ∧
    u ∉ rlc_pathVertices gamma.1 ∧ v ∉ rlc_pathVertices gamma.1 ∧
    u ∉ rlc_pathVertices delta.1 ∧ v ∉ rlc_pathVertices delta.1
  symm := by
    refine ⟨?_⟩
    intro u v h
    exact ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2.1,
      h.2.2.2.1, h.2.2.2.2.2.2, h.2.2.2.2.2.1⟩
  loopless := ⟨fun u h => (hypercubicLattice 2).irrefl h.1⟩

lemma rlc_rightPairAvoidGraph_walk_dest {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {x z : Site 2}
    (hxR : x ∈ rect 0 (2 * n) (-n) n)
    (hxGamma : x ∉ rlc_pathVertices gamma.1)
    (hxDelta : x ∉ rlc_pathVertices delta.1)
    (w : (rlc_rightPairAvoidGraph gamma delta).Walk x z) :
    z ∈ rect 0 (2 * n) (-n) n ∧
      z ∉ rlc_pathVertices gamma.1 ∧
      z ∉ rlc_pathVertices delta.1 := by
  induction w with
  | nil => exact ⟨hxR, hxGamma, hxDelta⟩
  | @cons a b c hab w ih =>
      exact ih hab.2.2.1 hab.2.2.2.2.1 hab.2.2.2.2.2.2

/-- The sites reachable from the bottom side while avoiding both right diagonal paths. -/
def rlc_jointBottomSet {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) : Set (Site 2) :=
  {z | ∃ x : Site 2, x ∈ bottomSide 0 (2 * n) (-n) n ∧
    x ∉ rlc_pathVertices gamma.1 ∧
    x ∉ rlc_pathVertices delta.1 ∧
    (rlc_rightPairAvoidGraph gamma delta).Reachable x z}

lemma rlc_jointBottomSet_subset_box {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_jointBottomSet gamma delta ⊆ rect 0 (2 * n) (-n) n := by
  rintro z ⟨x, hxBottom, hxGamma, hxDelta, hreach⟩
  obtain ⟨w⟩ := hreach
  exact (rlc_rightPairAvoidGraph_walk_dest gamma delta
    hxBottom.1 hxGamma hxDelta w).1

lemma rlc_jointBottomSet_finite {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_jointBottomSet gamma delta).Finite :=
  (rect_finite 0 (2 * n) (-n) n).subset
    (rlc_jointBottomSet_subset_box gamma delta)

lemma rlc_jointBottomSet_disjoint_paths {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    Disjoint (rlc_jointBottomSet gamma delta)
      ((rlc_pathVertices gamma.1 : Set (Site 2)) ∪
        rlc_pathVertices delta.1) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hxBottom, hxGamma, hxDelta, hreach⟩ hzPath
  obtain ⟨w⟩ := hreach
  have hz := rlc_rightPairAvoidGraph_walk_dest gamma delta
    hxBottom.1 hxGamma hxDelta w
  exact hzPath.elim hz.2.1 hz.2.2

lemma rlc_jointBottomSet_subset_commonStrictBelowSet {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_jointBottomSet gamma delta ⊆
      rlc_commonStrictBelowSet gamma delta := by
  rintro z ⟨x, hxBottom, hxGamma, hxDelta, hreach⟩
  obtain ⟨w⟩ := hreach
  have wg : (rlc_rightPathAvoidGraph gamma).Walk x z := by
    apply w.transfer (rlc_rightPathAvoidGraph gamma)
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have huv := w.adj_of_mem_edges he
        exact ⟨huv.1, huv.2.1, huv.2.2.1,
          huv.2.2.2.1, huv.2.2.2.2.1⟩
  have wd : (rlc_rightPathAvoidGraph delta).Walk x z := by
    apply w.transfer (rlc_rightPathAvoidGraph delta)
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have huv := w.adj_of_mem_edges he
        exact ⟨huv.1, huv.2.1, huv.2.2.1,
          huv.2.2.2.2.2.1, huv.2.2.2.2.2.2⟩
  exact ⟨⟨x, hxBottom, hxGamma, ⟨wg⟩⟩,
    ⟨x, hxBottom, hxDelta, ⟨wd⟩⟩⟩

lemma rlc_jointBottomSet_exit_mem_paths {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_jointBottomSet gamma delta)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hv : v ∉ rlc_jointBottomSet gamma delta) :
    v ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices delta.1 := by
  rcases hu with ⟨x, hxBottom, hxGamma, hxDelta, ⟨w⟩⟩
  have huData := rlc_rightPairAvoidGraph_walk_dest gamma delta
    hxBottom.1 hxGamma hxDelta w
  by_contra hvPath
  rw [not_or] at hvPath
  have hstep : (rlc_rightPairAvoidGraph gamma delta).Adj u v :=
    ⟨hadj, huData.1, hvR, huData.2.1, hvPath.1,
      huData.2.2, hvPath.2⟩
  exact hv ⟨x, hxBottom, hxGamma, hxDelta, ⟨w.concat hstep⟩⟩

lemma rlc_jointBottomSet_boundary_trace_safe {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_jointBottomSet gamma delta)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hvPath : v ∈ rlc_pathVertices gamma.1 ∨
      v ∈ rlc_pathVertices delta.1) :
    v ∉ rlc_rightUpperUnionSet gamma delta := by
  have huBelow := rlc_jointBottomSet_subset_commonStrictBelowSet
    gamma delta hu
  intro hvTop
  rcases hvTop with hvTopGamma | hvTopDelta
  · rcases hvPath with hvGamma | hvDelta
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path gamma)) hvTopGamma hvGamma
    · have hvNotGamma : v ∉ rlc_pathVertices gamma.1 := by
        intro hvGamma
        exact (Set.disjoint_left.mp
          (rlc_strictTopSet_disjoint_path gamma)) hvTopGamma hvGamma
      have hvBelowGamma := rlc_strictBelowSet_step gamma huBelow.1
        hvR hvNotGamma hadj
      exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_strictBelowSet hn gamma))
          hvTopGamma hvBelowGamma
  · rcases hvPath with hvGamma | hvDelta
    · have hvNotDelta : v ∉ rlc_pathVertices delta.1 := by
        intro hvDelta
        exact (Set.disjoint_left.mp
          (rlc_strictTopSet_disjoint_path delta)) hvTopDelta hvDelta
      have hvBelowDelta := rlc_strictBelowSet_step delta huBelow.2
        hvR hvNotDelta hadj
      exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_strictBelowSet hn delta))
          hvTopDelta hvBelowDelta
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path delta)) hvTopDelta hvDelta

lemma rlc_jointBottomSet_exit_mem_paths_and_safe {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_jointBottomSet gamma delta)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hv : v ∉ rlc_jointBottomSet gamma delta) :
    (v ∈ rlc_pathVertices gamma.1 ∨
      v ∈ rlc_pathVertices delta.1) ∧
      v ∉ rlc_rightUpperUnionSet gamma delta := by
  have hvPath := rlc_jointBottomSet_exit_mem_paths
    gamma delta hu hvR hadj hv
  exact ⟨hvPath, rlc_jointBottomSet_boundary_trace_safe
    hn gamma delta hu hvR hadj hvPath⟩

/-- The path sites adjacent to the joint bottom region. -/
def rlc_jointBottomTraceBoundary {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) : Set (Site 2) :=
  {v | v ∈ rect 0 (2 * n) (-n) n ∧
    (v ∈ rlc_pathVertices gamma.1 ∨
      v ∈ rlc_pathVertices delta.1) ∧
    ∃ u, u ∈ rlc_jointBottomSet gamma delta ∧
      (hypercubicLattice 2).Adj u v}

lemma rlc_jointBottomTraceBoundary_subset_paths {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_jointBottomTraceBoundary gamma delta ⊆
      (rlc_pathVertices gamma.1 : Set (Site 2)) ∪
        rlc_pathVertices delta.1 := by
  rintro v ⟨_vR, hvPath, _u, _hu, _hadj⟩
  exact hvPath

lemma rlc_jointBottomTraceBoundary_finite {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_jointBottomTraceBoundary gamma delta).Finite :=
  ((rlc_pathVertices gamma.1 ∪ rlc_pathVertices delta.1).finite_toSet).subset (by
    intro v hv
    simpa using rlc_jointBottomTraceBoundary_subset_paths gamma delta hv)

lemma rlc_jointBottomTraceBoundary_safe {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) {v : Site 2}
    (hv : v ∈ rlc_jointBottomTraceBoundary gamma delta) :
    v ∉ rlc_rightUpperUnionSet gamma delta := by
  rcases hv with ⟨hvR, hvPath, u, hu, hadj⟩
  exact rlc_jointBottomSet_boundary_trace_safe
    hn gamma delta hu hvR hadj hvPath

lemma rlc_bottomTraceVertex_safe {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) {v : Site 2}
    (hvBottom : v ∈ bottomSide 0 (2 * n) (-n) n)
    (_hvPath : v ∈ rlc_pathVertices gamma.1 ∨
      v ∈ rlc_pathVertices delta.1) :
    v ∉ rlc_rightUpperUnionSet gamma delta := by
  intro hvTop
  rcases hvTop with hvTopGamma | hvTopDelta
  · by_cases hvGamma : v ∈ rlc_pathVertices gamma.1
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path gamma)) hvTopGamma hvGamma
    · have hvBelowGamma : v ∈ rlc_strictBelowSet gamma :=
        ⟨v, hvBottom, hvGamma, SimpleGraph.Reachable.refl v⟩
      exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_strictBelowSet hn gamma))
          hvTopGamma hvBelowGamma
  · by_cases hvDelta : v ∈ rlc_pathVertices delta.1
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path delta)) hvTopDelta hvDelta
    · have hvBelowDelta : v ∈ rlc_strictBelowSet delta :=
        ⟨v, hvBottom, hvDelta, SimpleGraph.Reachable.refl v⟩
      exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_strictBelowSet hn delta))
          hvTopDelta hvBelowDelta

/-- The frontier of the joint bottom region along the union of the two paths. -/
def rlc_jointBottomTraceFrontier {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) : Set (Site 2) :=
  rlc_jointBottomTraceBoundary gamma delta ∪
    (bottomSide 0 (2 * n) (-n) n ∩
      ((rlc_pathVertices gamma.1 : Set (Site 2)) ∪
        rlc_pathVertices delta.1))

lemma rlc_jointBottomTraceFrontier_subset_paths {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_jointBottomTraceFrontier gamma delta ⊆
      (rlc_pathVertices gamma.1 : Set (Site 2)) ∪
        rlc_pathVertices delta.1 := by
  rintro v (hvBoundary | ⟨_hvBottom, hvPath⟩)
  · exact rlc_jointBottomTraceBoundary_subset_paths gamma delta hvBoundary
  · exact hvPath

lemma rlc_jointBottomTraceFrontier_finite {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_jointBottomTraceFrontier gamma delta).Finite :=
  ((rlc_pathVertices gamma.1 ∪ rlc_pathVertices delta.1).finite_toSet).subset (by
    intro v hv
    simpa using rlc_jointBottomTraceFrontier_subset_paths gamma delta hv)

lemma rlc_jointBottomTraceFrontier_safe {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) {v : Site 2}
    (hv : v ∈ rlc_jointBottomTraceFrontier gamma delta) :
    v ∉ rlc_rightUpperUnionSet gamma delta := by
  rcases hv with hvBoundary | ⟨hvBottom, hvPath⟩
  · exact rlc_jointBottomTraceBoundary_safe hn gamma delta hvBoundary
  · exact rlc_bottomTraceVertex_safe hn gamma delta hvBottom hvPath

/-- The intersection of the strict regions above two left diagonal paths. -/
def rlc_commonStrictAboveSet {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) : Set (Site 2) :=
  rlc_strictAboveSet gamma ∩ rlc_strictAboveSet delta

lemma rlc_commonStrictAboveSet_finite {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) :
    (rlc_commonStrictAboveSet gamma delta).Finite :=
  (rlc_strictAboveSet_finite gamma).inter_of_left
    (rlc_strictAboveSet delta)

lemma rlc_top_mem_commonStrictAboveSet {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) {z : Site 2}
    (hz : z ∈ topSide (-2 * n) 0 (-n) n)
    (hgamma : z ∉ rlc_pathVertices gamma.1)
    (hdelta : z ∉ rlc_pathVertices delta.1) :
    z ∈ rlc_commonStrictAboveSet gamma delta := by
  exact ⟨⟨z, hz, hgamma, SimpleGraph.Reachable.refl z⟩,
    ⟨z, hz, hdelta, SimpleGraph.Reachable.refl z⟩⟩

lemma rlc_leftBottomSide_disjoint_commonStrictAboveSet {n : ℤ}
    (hn : 0 < n) (gamma delta : RlcLeftDiagonalPath n) :
    Disjoint (bottomSide (-2 * n) 0 (-n) n)
      (rlc_commonStrictAboveSet gamma delta) := by
  rw [Set.disjoint_left]
  intro z hzBottom hzCommon
  exact (Set.disjoint_left.mp
    (rlc_leftBottomSide_disjoint_strictAboveSet hn gamma)) hzBottom hzCommon.1

lemma rlc_commonStrictAboveSet_boundary_paths {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) {u v : Site 2}
    (huR : u ∈ rect (-2 * n) 0 (-n) n)
    (hvR : v ∈ rect (-2 * n) 0 (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_commonStrictAboveSet gamma delta) s(u, v)) :
    (u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1) ∨
      (u ∈ rlc_pathVertices delta.1 ∨ v ∈ rlc_pathVertices delta.1) := by
  rcases rlc_bdEdge_inter hbd with hgamma | hdelta
  · exact Or.inl (rlc_strictAboveSet_boundary_path gamma huR hvR hadj hgamma)
  · exact Or.inr (rlc_strictAboveSet_boundary_path delta huR hvR hadj hdelta)

/-- The strict region below a right diagonal path, as a `Finset`. -/
noncomputable def rlc_strictBelowVertices {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : Finset (Site 2) :=
  (rlc_strictBelowSet_finite gamma).toFinset

/-- The strict region above a left diagonal path, as a `Finset`. -/
noncomputable def rlc_strictAboveVertices {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : Finset (Site 2) :=
  (rlc_strictAboveSet_finite gamma).toFinset

/-- The strict region above a right diagonal path, as a `Finset`. -/
noncomputable def rlc_strictTopVertices {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : Finset (Site 2) :=
  (rlc_strictTopSet_finite gamma).toFinset

/-- The strict region below a left diagonal path, as a `Finset`. -/
noncomputable def rlc_strictBottomVertices {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : Finset (Site 2) :=
  (rlc_strictBottomSet_finite gamma).toFinset

@[simp] lemma rlc_mem_strictBelowVertices {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {z : Site 2} :
    z ∈ rlc_strictBelowVertices gamma ↔ z ∈ rlc_strictBelowSet gamma := by
  simp [rlc_strictBelowVertices]

@[simp] lemma rlc_mem_strictAboveVertices {n : ℤ}
    {gamma : RlcLeftDiagonalPath n} {z : Site 2} :
    z ∈ rlc_strictAboveVertices gamma ↔ z ∈ rlc_strictAboveSet gamma := by
  simp [rlc_strictAboveVertices]

@[simp] lemma rlc_mem_strictTopVertices {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {z : Site 2} :
    z ∈ rlc_strictTopVertices gamma ↔ z ∈ rlc_strictTopSet gamma := by
  simp [rlc_strictTopVertices]

@[simp] lemma rlc_mem_strictBottomVertices {n : ℤ}
    {gamma : RlcLeftDiagonalPath n} {z : Site 2} :
    z ∈ rlc_strictBottomVertices gamma ↔ z ∈ rlc_strictBottomSet gamma := by
  simp [rlc_strictBottomVertices]

/-- Path `delta` lies in the strict region below path `gamma`. -/
def rlc_rightPathStrictlyBelow {n : ℤ}
    (delta gamma : RlcRightDiagonalPath n) : Prop :=
  (rlc_pathVertices delta.1 : Set (Site 2)) ⊆ rlc_strictBelowSet gamma

/-- Path `delta` lies in the strict region above path `gamma`. -/
def rlc_leftPathStrictlyAbove {n : ℤ}
    (delta gamma : RlcLeftDiagonalPath n) : Prop :=
  (rlc_pathVertices delta.1 : Set (Site 2)) ⊆ rlc_strictAboveSet gamma

lemma rlc_path_start_mem_vertices {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) :
    (gamma.1 : Site 2) ∈ rlc_pathVertices gamma := by
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
  exact ⟨⟨(gamma.1 : Site 2), leftSide_subset gamma.1.2⟩,
    gamma.2.2.1.start_mem_support, rfl⟩

lemma rlc_rightPathStrictlyBelow_irrefl {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    ¬ rlc_rightPathStrictlyBelow gamma gamma := by
  intro h
  have hstart := rlc_path_start_mem_vertices gamma.1
  exact (Set.disjoint_left.mp (rlc_strictBelowSet_disjoint_path gamma))
    (h hstart) hstart

lemma rlc_leftPathStrictlyAbove_irrefl {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    ¬ rlc_leftPathStrictlyAbove gamma gamma := by
  intro h
  have hstart := rlc_path_start_mem_vertices gamma.1
  exact (Set.disjoint_left.mp (rlc_strictAboveSet_disjoint_path gamma))
    (h hstart) hstart

/-! ## D. Lowest and highest open paths -/

/-- The sites of the right rectangle on or below a right diagonal path (the explored region of a
  lowest-path exploration). -/
noncomputable def rlc_rightExploredVertices {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : Finset (Site 2) :=
  rlc_rectFinset 0 (2 * n) (-n) n \ rlc_strictTopVertices gamma

/-- The sites of the left rectangle on or above a left diagonal path. -/
noncomputable def rlc_leftExploredVertices {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : Finset (Site 2) :=
  rlc_rectFinset (-2 * n) 0 (-n) n \ rlc_strictBottomVertices gamma

lemma rlc_rightPathVertex_mem_explored {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1) :
    z ∈ rlc_rightExploredVertices gamma := by
  rw [rlc_rightExploredVertices, Finset.mem_sdiff]
  constructor
  · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hz
    obtain ⟨u, _hu, rfl⟩ := hz
    simp
  · intro hzTop
    exact (Set.disjoint_left.mp (rlc_strictTopSet_disjoint_path gamma))
      (by simpa using hzTop) hz

lemma rlc_leftPathVertex_mem_explored {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1) :
    z ∈ rlc_leftExploredVertices gamma := by
  rw [rlc_leftExploredVertices, Finset.mem_sdiff]
  constructor
  · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hz
    obtain ⟨u, _hu, rfl⟩ := hz
    simpa using u.2
  · intro hzBottom
    exact (Set.disjoint_left.mp (rlc_strictBottomSet_disjoint_path gamma))
      (by simpa using hzBottom) hz

/-- An enumeration index of right diagonal paths, used to break ties. -/
noncomputable def rlc_rightPathIndex {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : ℕ :=
  (Fintype.equivFin (RlcRightDiagonalPath n) gamma).val

/-- An enumeration index of left diagonal paths, used to break ties. -/
noncomputable def rlc_leftPathIndex {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : ℕ :=
  (Fintype.equivFin (RlcLeftDiagonalPath n) gamma).val

/-- The rank of a right diagonal path: size of its explored region, with the index as tie-
  breaker. -/
noncomputable def rlc_rightPathRank {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : ℕ :=
  (rlc_rightExploredVertices gamma).card *
      Fintype.card (RlcRightDiagonalPath n) + rlc_rightPathIndex gamma

/-- The rank of a left diagonal path: size of its explored region, with the index as tie-breaker. -/
noncomputable def rlc_leftPathRank {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : ℕ :=
  (rlc_leftExploredVertices gamma).card *
      Fintype.card (RlcLeftDiagonalPath n) + rlc_leftPathIndex gamma

/-- Path `delta` is below path `gamma`: its explored region is a strict subset. -/
def rlc_rightPathBelow {n : ℤ}
    (delta gamma : RlcRightDiagonalPath n) : Prop :=
  rlc_rightExploredVertices delta ⊂ rlc_rightExploredVertices gamma ∨
    (rlc_rightExploredVertices delta = rlc_rightExploredVertices gamma ∧
      rlc_rightPathIndex delta < rlc_rightPathIndex gamma)

/-- Path `delta` is above path `gamma`: its explored region is a strict subset. -/
def rlc_leftPathAbove {n : ℤ}
    (delta gamma : RlcLeftDiagonalPath n) : Prop :=
  rlc_leftExploredVertices delta ⊂ rlc_leftExploredVertices gamma ∨
    (rlc_leftExploredVertices delta = rlc_leftExploredVertices gamma ∧
      rlc_leftPathIndex delta < rlc_leftPathIndex gamma)

lemma rlc_rightPathBelow_irrefl {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : ¬ rlc_rightPathBelow gamma gamma := by
  rintro (h | h)
  · exact (Finset.ssubset_iff_subset_ne.mp h).2 rfl
  · exact (lt_irrefl _ h.2)

lemma rlc_leftPathAbove_irrefl {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : ¬ rlc_leftPathAbove gamma gamma := by
  rintro (h | h)
  · exact (Finset.ssubset_iff_subset_ne.mp h).2 rfl
  · exact (lt_irrefl _ h.2)

lemma rlc_rightPathBelow_rank_lt {n : ℤ}
    {delta gamma : RlcRightDiagonalPath n}
    (h : rlc_rightPathBelow delta gamma) :
    rlc_rightPathRank delta < rlc_rightPathRank gamma := by
  let N := Fintype.card (RlcRightDiagonalPath n)
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨gamma⟩
  have hindex : rlc_rightPathIndex delta < N :=
    (Fintype.equivFin (RlcRightDiagonalPath n) delta).isLt
  rcases h with hstrict | heq
  · have hcard : (rlc_rightExploredVertices delta).card <
        (rlc_rightExploredVertices gamma).card :=
      Finset.card_lt_card hstrict
    have hmul : (rlc_rightExploredVertices delta).card * N + N ≤
        (rlc_rightExploredVertices gamma).card * N := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right N (Nat.succ_le_iff.mpr hcard)
    dsimp only [rlc_rightPathRank]
    change _ * N + rlc_rightPathIndex delta <
      _ * N + rlc_rightPathIndex gamma
    calc
      _ * N + rlc_rightPathIndex delta < _ * N + N :=
        Nat.add_lt_add_left hindex _
      _ ≤ _ * N := hmul
      _ ≤ _ * N + rlc_rightPathIndex gamma := Nat.le_add_right _ _
  · dsimp only [rlc_rightPathRank]
    rw [heq.1]
    exact Nat.add_lt_add_left heq.2 _

lemma rlc_leftPathAbove_rank_lt {n : ℤ}
    {delta gamma : RlcLeftDiagonalPath n}
    (h : rlc_leftPathAbove delta gamma) :
    rlc_leftPathRank delta < rlc_leftPathRank gamma := by
  let N := Fintype.card (RlcLeftDiagonalPath n)
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨gamma⟩
  have hindex : rlc_leftPathIndex delta < N :=
    (Fintype.equivFin (RlcLeftDiagonalPath n) delta).isLt
  rcases h with hstrict | heq
  · have hcard : (rlc_leftExploredVertices delta).card <
        (rlc_leftExploredVertices gamma).card :=
      Finset.card_lt_card hstrict
    have hmul : (rlc_leftExploredVertices delta).card * N + N ≤
        (rlc_leftExploredVertices gamma).card * N := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right N (Nat.succ_le_iff.mpr hcard)
    dsimp only [rlc_leftPathRank]
    change _ * N + rlc_leftPathIndex delta <
      _ * N + rlc_leftPathIndex gamma
    calc
      _ * N + rlc_leftPathIndex delta < _ * N + N :=
        Nat.add_lt_add_left hindex _
      _ ≤ _ * N := hmul
      _ ≤ _ * N + rlc_leftPathIndex gamma := Nat.le_add_right _ _
  · dsimp only [rlc_leftPathRank]
    rw [heq.1]
    exact Nat.add_lt_add_left heq.2 _

lemma rlc_pathEdge_endpoints_mem_vertices {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) {x y : Site 2}
    (he : s(x, y) ∈ rlc_pathEdges gamma) :
    x ∈ rlc_pathVertices gamma ∧ y ∈ rlc_pathVertices gamma := by
  simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset] at he
  obtain ⟨e, he, heq⟩ := he
  induction e using Sym2.inductionOn with
  | _ u v =>
    have heq' : s(x, y) = s((u : Site 2), (v : Site 2)) := by
      simpa using heq.symm
    rw [Sym2.eq_iff] at heq'
    rcases heq' with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
    · subst x; subst y
      constructor
      · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        exact ⟨u, gamma.2.2.1.fst_mem_support_of_mem_edges he, rfl⟩
      · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        exact ⟨v, gamma.2.2.1.snd_mem_support_of_mem_edges he, rfl⟩
    · subst x; subst y
      constructor
      · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        exact ⟨v, gamma.2.2.1.snd_mem_support_of_mem_edges he, rfl⟩
      · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        exact ⟨u, gamma.2.2.1.fst_mem_support_of_mem_edges he, rfl⟩

lemma rlc_pathVertex_mem_rect {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma) : z ∈ rect a b c d := by
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  exact u.2

lemma rlc_rightSide_strictTop_height_gt {n : ℤ} (_hn : 0 < n)
    (gamma : RlcRightDiagonalPath n)
    (z : rightSide 0 (2 * n) (-n) n)
    (hzTop : (z : Site 2) ∈ rlc_strictTopSet gamma) :
    (gamma.1.2.1 : Site 2) 1 < (z : Site 2) 1 := by
  classical
  by_contra hnot
  have hzle : (z : Site 2) 1 ≤ (gamma.1.2.1 : Site 2) 1 :=
    le_of_not_gt hnot
  have hEndPath : (gamma.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩,
      gamma.1.2.2.1.end_mem_support, rfl⟩
  have hzNeEnd : (z : Site 2) ≠ (gamma.1.2.1 : Site 2) := by
    intro h
    exact (Set.disjoint_left.mp (rlc_strictTopSet_disjoint_path gamma))
      hzTop (h ▸ hEndPath)
  have hlt : (z : Site 2) 1 < (gamma.1.2.1 : Site 2) 1 := by
    apply lt_of_le_of_ne hzle
    intro h
    apply hzNeEnd
    funext i
    fin_cases i
    · exact z.2.2.trans gamma.1.2.1.2.2.symm
    · exact h
  obtain ⟨x0, hxTop, hxPath, hreach⟩ := hzTop
  let x : topSide 0 (2 * n) (-n) n := ⟨x0, hxTop⟩
  obtain ⟨wAvoid⟩ := hreach
  let hle : rlc_rightPathAvoidGraph gamma ≤ hypercubicLattice 2 :=
    fun _ _ h => h.1
  let W : (hypercubicLattice 2).Walk (x : Site 2) (z : Site 2) :=
    wAvoid.mapLe hle
  have hWbox : ∀ q ∈ W.support,
      q ∈ rect 0 (2 * n) (-n) n := by
    intro q hq
    have hq' : q ∈ wAvoid.support := by
      simpa [W, SimpleGraph.Walk.support_mapLe_eq_support] using hq
    exact (rlc_rightPathAvoidGraph_walk_dest gamma hxTop.1 hxPath
      (wAvoid.takeUntil q hq')).1
  have hWavoid : ∀ q ∈ W.support,
      q ∉ rlc_pathVertices gamma.1 := by
    intro q hq
    have hq' : q ∈ wAvoid.support := by
      simpa [W, SimpleGraph.Walk.support_mapLe_eq_support] using hq
    exact (rlc_rightPathAvoidGraph_walk_dest gamma hxTop.1 hxPath
      (wAvoid.takeUntil q hq')).2
  have hEndNotW : (gamma.1.2.1 : Site 2) ∉ W.support := by
    intro h
    exact (hWavoid _ h) hEndPath
  let R := rlc_cornerReturn x z
  let C : (hypercubicLattice 2).Walk (x : Site 2) (x : Site 2) :=
    W.append R
  have hRayReturn (p : Site 2)
      (hp : p ∈ rect 0 (2 * n) (-n) n) :
      jec_rayCount p R = 0 := by
    exact rlc_cornerReturn_rayCount_zero x z p hp
  have hStartRect : (gamma.1.1 : Site 2) ∈
      rect 0 (2 * n) (-n) n := leftSide_subset gamma.1.1.2
  have hEndRect : (gamma.1.2.1 : Site 2) ∈
      rect 0 (2 * n) (-n) n := rightSide_subset gamma.1.2.1.2
  have hRayStartW : jec_rayCount (gamma.1.1 : Site 2) W = 0 := by
    apply jec_rayCount_eq_zero_of_right
    intro q hq
    have hqR := hWbox q hq
    have hstartSide := gamma.1.1.2
    rw [mem_leftSide] at hstartSide
    rw [mem_rect] at hqR
    simpa [hstartSide.2] using hqR.1
  have hRayStart : Even (jec_rayCount (gamma.1.1 : Site 2) C) := by
    rw [show jec_rayCount (gamma.1.1 : Site 2) C =
      jec_rayCount (gamma.1.1 : Site 2) W +
        jec_rayCount (gamma.1.1 : Site 2) R by
          exact jec_rayCount_append _ W R,
      hRayStartW, hRayReturn _ hStartRect]
    exact Even.zero
  let y : rightSide 0 (2 * n) (-n) n := gamma.1.2.1
  have hRayEndEq : jec_rayCount (y : Site 2) W =
      crossCount (jec_belowSet ((y : Site 2) 1)) W :=
    rlc_ray_eq_below_right_of_avoids y W hWbox hEndNotW
  have hCrossOdd : ¬ Even
      (crossCount (jec_belowSet ((y : Site 2) 1)) W) := by
    rw [crossCount_parity]
    simp only [jec_mem_belowSet]
    have hx1 : (x : Site 2) 1 = n := x.2.2
    have hy1le : (y : Site 2) 1 ≤ n := by
      have hySide := y.2
      rw [mem_rightSide, mem_rect] at hySide
      exact hySide.1.2.2.2
    have hxNot : ¬ (x : Site 2) 1 ≤ (y : Site 2) 1 - 1 := by
      omega
    have hzIn : (z : Site 2) 1 ≤ (y : Site 2) 1 - 1 := by
      dsimp only [y]
      omega
    exact fun hiff => hxNot (hiff.mpr hzIn)
  have hRayEnd : ¬ Even (jec_rayCount (y : Site 2) C) := by
    rw [show jec_rayCount (y : Site 2) C =
      jec_rayCount (y : Site 2) W + jec_rayCount (y : Site 2) R by
        exact jec_rayCount_append _ W R,
      hRayEndEq, hRayReturn _ hEndRect, add_zero]
    exact hCrossOdd
  let hom : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)) →g hypercubicLattice 2 :=
    (SimpleGraph.Embedding.induce (G := hypercubicLattice 2)
      (rect 0 (2 * n) (-n) n)).toHom
  let gW : (hypercubicLattice 2).Walk
      (gamma.1.1 : Site 2) (gamma.1.2.1 : Site 2) :=
    gamma.1.2.2.1.map hom
  obtain ⟨q, hqGammaRev, hqC⟩ :=
    ccs_closedLoop_separatingSide_forces_cross C
      ({(y : Site 2)} : Set (Site 2))
      ({(gamma.1.1 : Site 2)} : Set (Site 2))
      (by
        intro q hq
        rw [Set.mem_singleton_iff] at hq
        subst q
        exact hRayEnd)
      (by
        intro q hq
        rw [Set.mem_singleton_iff] at hq
        subst q
        exact hRayStart)
      (by simp [y]) (by simp) gW.reverse
  have hqGamma : q ∈ gW.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hqGammaRev
  have hqPath : q ∈ rlc_pathVertices gamma.1 := by
    dsimp only [gW] at hqGamma
    have hqMapped : q ∈ List.map hom gamma.1.2.2.1.support := by
      have hsupp := SimpleGraph.Walk.support_map hom gamma.1.2.2.1
      have hm := congrArg (fun l => q ∈ l) hsupp
      exact Eq.mp hm hqGamma
    rw [List.mem_map] at hqMapped
    obtain ⟨u, hu, huq⟩ := hqMapped
    change (u : Site 2) = q at huq
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨u, hu, huq⟩
  have hqRect := rlc_pathVertex_mem_rect gamma.1 hqPath
  dsimp only [C] at hqC
  rw [SimpleGraph.Walk.mem_support_append_iff] at hqC
  rcases hqC with hqW | hqR
  · exact (hWavoid q hqW) hqPath
  · rcases rlc_cornerReturn_support_inside x z hqR hqRect with hqz | hqx
    · exact (hWavoid _ W.end_mem_support) (hqz ▸ hqPath)
    · apply hxPath
      have hxPath' : (x : Site 2) ∈ rlc_pathVertices gamma.1 :=
        hqx ▸ hqPath
      simpa [x] using hxPath'

lemma rlc_right_endpoints_not_both_unsafe {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) :
    ¬ ((gamma.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta ∧
      (delta.1.2.1 : Site 2) ∈ rlc_rightUpperUnionSet gamma delta) := by
  rintro ⟨hgamma, hdelta⟩
  have hgammaPath : (gamma.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩,
      gamma.1.2.2.1.end_mem_support, rfl⟩
  have hdeltaPath : (delta.1.2.1 : Site 2) ∈
      rlc_pathVertices delta.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩,
      delta.1.2.2.1.end_mem_support, rfl⟩
  have hgammaTopDelta : (gamma.1.2.1 : Site 2) ∈
      rlc_strictTopSet delta := by
    rcases hgamma with hgammaTop | hgammaTop
    · exact False.elim ((Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path gamma)) hgammaTop hgammaPath)
    · exact hgammaTop
  have hdeltaTopGamma : (delta.1.2.1 : Site 2) ∈
      rlc_strictTopSet gamma := by
    rcases hdelta with hdeltaTop | hdeltaTop
    · exact hdeltaTop
    · exact False.elim ((Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path delta)) hdeltaTop hdeltaPath)
  have hgd := rlc_rightSide_strictTop_height_gt hn delta
    gamma.1.2.1 hgammaTopDelta
  have hdg := rlc_rightSide_strictTop_height_gt hn gamma
    delta.1.2.1 hdeltaTopGamma
  omega

lemma rlc_exists_safe_right_endpoint {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) :
    (gamma.1.2.1 : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∨
      (delta.1.2.1 : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
  by_contra h
  push Not at h
  exact rlc_right_endpoints_not_both_unsafe hn gamma delta h

lemma rlc_pathEdge_lattice {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) {x y : Site 2}
    (he : s(x, y) ∈ rlc_pathEdges gamma) :
    (hypercubicLattice 2).Adj x y := by
  simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset] at he
  obtain ⟨e, he, heq⟩ := he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hadj := gamma.2.2.1.adj_of_mem_edges he
      have heq' : s(x, y) = s((u : Site 2), (v : Site 2)) := by
        simpa using heq.symm
      rw [Sym2.eq_iff] at heq'
      rcases heq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj
      · exact hadj.symm

lemma rlc_walk_pred_constant {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (P : V → Prop)
    (hstep : ∀ {u v : V}, s(u, v) ∈ p.edges → (P u ↔ P v))
    {z : V} (hz : z ∈ p.support) : P z ↔ P a := by
  induction p with
  | nil =>
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      exact hz ▸ Iff.rfl
  | @cons a b c hab p ih =>
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Iff.rfl
      · have htail : ∀ {u v : V}, s(u, v) ∈ p.edges → (P u ↔ P v) := by
          intro u v he
          apply hstep
          simpa using Or.inr he
        exact (ih htail hz).trans (hstep (by simp)).symm

lemma rlc_strictTopSet_mem_iff_walk_start_of_avoids {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {a b : Site 2}
    (p : (hypercubicLattice 2).Walk a b)
    (hbox : ∀ z ∈ p.support, z ∈ rect 0 (2 * n) (-n) n)
    (havoid : ∀ z ∈ p.support, z ∉ rlc_pathVertices gamma.1)
    {z : Site 2} (hz : z ∈ p.support) :
    z ∈ rlc_strictTopSet gamma ↔ a ∈ rlc_strictTopSet gamma := by
  apply rlc_walk_pred_constant p (fun u => u ∈ rlc_strictTopSet gamma)
  · intro u v he
    have hu : u ∈ p.support := p.fst_mem_support_of_mem_edges he
    have hv : v ∈ p.support := p.snd_mem_support_of_mem_edges he
    constructor
    · intro huTop
      exact rlc_strictTopSet_step gamma huTop (hbox v hv) (havoid v hv)
        (p.adj_of_mem_edges he)
    · intro hvTop
      exact rlc_strictTopSet_step gamma hvTop (hbox u hu) (havoid u hu)
        (p.adj_of_mem_edges he).symm
  · exact hz

lemma rlc_strictBelowSet_mem_iff_walk_start_of_avoids {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {a b : Site 2}
    (p : (hypercubicLattice 2).Walk a b)
    (hbox : ∀ z ∈ p.support, z ∈ rect 0 (2 * n) (-n) n)
    (havoid : ∀ z ∈ p.support, z ∉ rlc_pathVertices gamma.1)
    {z : Site 2} (hz : z ∈ p.support) :
    z ∈ rlc_strictBelowSet gamma ↔ a ∈ rlc_strictBelowSet gamma := by
  apply rlc_walk_pred_constant p (fun u => u ∈ rlc_strictBelowSet gamma)
  · intro u v he
    have hu : u ∈ p.support := p.fst_mem_support_of_mem_edges he
    have hv : v ∈ p.support := p.snd_mem_support_of_mem_edges he
    constructor
    · intro huBelow
      exact rlc_strictBelowSet_step gamma huBelow (hbox v hv) (havoid v hv)
        (p.adj_of_mem_edges he)
    · intro hvBelow
      exact rlc_strictBelowSet_step gamma hvBelow (hbox u hu) (havoid u hu)
        (p.adj_of_mem_edges he).symm
  · exact hz

lemma rlc_strictTopSet_mem_iff_rectWalk_start_of_avoids {n : ℤ}
    (gamma : RlcRightDiagonalPath n)
    {a b : rect 0 (2 * n) (-n) n}
    (p : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Walk a b)
    (havoid : ∀ z ∈ p.support,
      (z : Site 2) ∉ rlc_pathVertices gamma.1)
    {z : rect 0 (2 * n) (-n) n} (hz : z ∈ p.support) :
    (z : Site 2) ∈ rlc_strictTopSet gamma ↔
      (a : Site 2) ∈ rlc_strictTopSet gamma := by
  apply rlc_walk_pred_constant p
    (fun u => (u : Site 2) ∈ rlc_strictTopSet gamma)
  · intro u v he
    have hu : u ∈ p.support := p.fst_mem_support_of_mem_edges he
    have hv : v ∈ p.support := p.snd_mem_support_of_mem_edges he
    constructor
    · intro huTop
      exact rlc_strictTopSet_step gamma huTop v.2 (havoid v hv)
        (p.adj_of_mem_edges he)
    · intro hvTop
      exact rlc_strictTopSet_step gamma hvTop u.2 (havoid u hu)
        (p.adj_of_mem_edges he).symm
  · exact hz

lemma rlc_strictBelowSet_mem_iff_rectWalk_start_of_avoids {n : ℤ}
    (gamma : RlcRightDiagonalPath n)
    {a b : rect 0 (2 * n) (-n) n}
    (p : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Walk a b)
    (havoid : ∀ z ∈ p.support,
      (z : Site 2) ∉ rlc_pathVertices gamma.1)
    {z : rect 0 (2 * n) (-n) n} (hz : z ∈ p.support) :
    (z : Site 2) ∈ rlc_strictBelowSet gamma ↔
      (a : Site 2) ∈ rlc_strictBelowSet gamma := by
  apply rlc_walk_pred_constant p
    (fun u => (u : Site 2) ∈ rlc_strictBelowSet gamma)
  · intro u v he
    have hu : u ∈ p.support := p.fst_mem_support_of_mem_edges he
    have hv : v ∈ p.support := p.snd_mem_support_of_mem_edges he
    constructor
    · intro huBelow
      exact rlc_strictBelowSet_step gamma huBelow v.2 (havoid v hv)
        (p.adj_of_mem_edges he)
    · intro hvBelow
      exact rlc_strictBelowSet_step gamma hvBelow u.2 (havoid u hu)
        (p.adj_of_mem_edges he).symm
  · exact hz

lemma rlc_strictTopSet_mem_iff_path_start_of_disjoint {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    {z : Site 2} (hz : z ∈ rlc_pathVertices delta.1) :
    z ∈ rlc_strictTopSet gamma ↔
      (delta.1.1 : Site 2) ∈ rlc_strictTopSet gamma := by
  classical
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hz
  obtain ⟨zs, hzs, rfl⟩ := hz
  let p := delta.1.2.2.1
  have hconst := rlc_walk_pred_constant p
    (fun u => (u : Site 2) ∈ rlc_strictTopSet gamma) (z := zs) ?_ hzs
  · simpa [p] using hconst
  · intro u v he
    have heAmb : s((u : Site 2), (v : Site 2)) ∈
        rlc_pathEdges delta.1 := by
      simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
      exact ⟨s(u, v), he, by simp⟩
    have hends := rlc_pathEdge_endpoints_mem_vertices delta.1 heAmb
    have huNot : (u : Site 2) ∉ rlc_pathVertices gamma.1 :=
      fun hu => (Finset.disjoint_left.mp hdisj) hu hends.1
    have hvNot : (v : Site 2) ∉ rlc_pathVertices gamma.1 :=
      fun hv => (Finset.disjoint_left.mp hdisj) hv hends.2
    constructor
    · intro huTop
      exact rlc_strictTopSet_step gamma huTop v.2 hvNot
        (rlc_pathEdge_lattice delta.1 heAmb)
    · intro hvTop
      exact rlc_strictTopSet_step gamma hvTop u.2 huNot
        (rlc_pathEdge_lattice delta.1 heAmb).symm

lemma rlc_strictBottomSet_mem_iff_path_start_of_disjoint {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    {z : Site 2} (hz : z ∈ rlc_pathVertices delta.1) :
    z ∈ rlc_strictBottomSet gamma ↔
      (delta.1.1 : Site 2) ∈ rlc_strictBottomSet gamma := by
  classical
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hz
  obtain ⟨zs, hzs, rfl⟩ := hz
  let p := delta.1.2.2.1
  have hconst := rlc_walk_pred_constant p
    (fun u => (u : Site 2) ∈ rlc_strictBottomSet gamma) (z := zs) ?_ hzs
  · simpa [p] using hconst
  · intro u v he
    have heAmb : s((u : Site 2), (v : Site 2)) ∈
        rlc_pathEdges delta.1 := by
      simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
      exact ⟨s(u, v), he, by simp⟩
    have hends := rlc_pathEdge_endpoints_mem_vertices delta.1 heAmb
    have huNot : (u : Site 2) ∉ rlc_pathVertices gamma.1 :=
      fun hu => (Finset.disjoint_left.mp hdisj) hu hends.1
    have hvNot : (v : Site 2) ∉ rlc_pathVertices gamma.1 :=
      fun hv => (Finset.disjoint_left.mp hdisj) hv hends.2
    constructor
    · intro huBottom
      exact rlc_strictBottomSet_step gamma huBottom v.2 hvNot
        (rlc_pathEdge_lattice delta.1 heAmb)
    · intro hvBottom
      exact rlc_strictBottomSet_step gamma hvBottom u.2 huNot
        (rlc_pathEdge_lattice delta.1 heAmb).symm

lemma rlc_rightPathEdge_enter_strictTop_common {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (he : s(u, v) ∈ rlc_pathEdges gamma.1)
    (hu : u ∉ rlc_strictTopSet delta)
    (hv : v ∈ rlc_strictTopSet delta) :
    u ∈ rlc_pathVertices delta.1 := by
  have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he
  have hbd : bdEdge (rlc_strictTopSet delta) s(u, v) := by
    rw [bdEdge_mk]
    exact iff_of_false hu (not_not.mpr hv)
  rcases rlc_strictTopSet_boundary_path delta
      (rlc_pathVertex_mem_rect gamma.1 hends.1)
      (rlc_pathVertex_mem_rect gamma.1 hends.2)
      (rlc_pathEdge_lattice gamma.1 he) hbd with huDelta | hvDelta
  · exact huDelta
  · exact False.elim ((Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_path delta)) hv hvDelta)

lemma rlc_rightPathEdge_exit_strictTop_common {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (he : s(u, v) ∈ rlc_pathEdges gamma.1)
    (hu : u ∈ rlc_strictTopSet delta)
    (hv : v ∉ rlc_strictTopSet delta) :
    v ∈ rlc_pathVertices delta.1 := by
  have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he
  have hbd : bdEdge (rlc_strictTopSet delta) s(u, v) := by
    rw [bdEdge_mk]
    exact iff_of_true hu hv
  rcases rlc_strictTopSet_boundary_path delta
      (rlc_pathVertex_mem_rect gamma.1 hends.1)
      (rlc_pathVertex_mem_rect gamma.1 hends.2)
      (rlc_pathEdge_lattice gamma.1 he) hbd with huDelta | hvDelta
  · exact False.elim ((Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_path delta)) hu huDelta)
  · exact hvDelta

lemma rlc_leftPathEdge_enter_strictBottom_common {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) {u v : Site 2}
    (he : s(u, v) ∈ rlc_pathEdges gamma.1)
    (hu : u ∉ rlc_strictBottomSet delta)
    (hv : v ∈ rlc_strictBottomSet delta) :
    u ∈ rlc_pathVertices delta.1 := by
  have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he
  have hbd : bdEdge (rlc_strictBottomSet delta) s(u, v) := by
    rw [bdEdge_mk]
    exact iff_of_false hu (not_not.mpr hv)
  rcases rlc_strictBottomSet_boundary_path delta
      (rlc_pathVertex_mem_rect gamma.1 hends.1)
      (rlc_pathVertex_mem_rect gamma.1 hends.2)
      (rlc_pathEdge_lattice gamma.1 he) hbd with huDelta | hvDelta
  · exact huDelta
  · exact False.elim ((Set.disjoint_left.mp
      (rlc_strictBottomSet_disjoint_path delta)) hv hvDelta)

lemma rlc_leftPathEdge_exit_strictBottom_common {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) {u v : Site 2}
    (he : s(u, v) ∈ rlc_pathEdges gamma.1)
    (hu : u ∈ rlc_strictBottomSet delta)
    (hv : v ∉ rlc_strictBottomSet delta) :
    v ∈ rlc_pathVertices delta.1 := by
  have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he
  have hbd : bdEdge (rlc_strictBottomSet delta) s(u, v) := by
    rw [bdEdge_mk]
    exact iff_of_true hu hv
  rcases rlc_strictBottomSet_boundary_path delta
      (rlc_pathVertex_mem_rect gamma.1 hends.1)
      (rlc_pathVertex_mem_rect gamma.1 hends.2)
      (rlc_pathEdge_lattice gamma.1 he) hbd with huDelta | hvDelta
  · exact False.elim ((Set.disjoint_left.mp
      (rlc_strictBottomSet_disjoint_path delta)) hu huDelta)
  · exact hvDelta

/-- Configurations in `W i` but in no `W j` with `j` preceding `i`: the minimal-candidate
  decomposition. -/
noncomputable def rlc_rankedMinimalCandidate {I : Type*}
    (W : I → Set (ConfigSpace E)) (prec : I → I → Prop) (i : I) :
    Set (ConfigSpace E) := by
  classical
  exact W i \ ⋃ j : I, if prec j i then W j else ∅

-- The unused instance binder is part of the signature; removing it changes the statement.
set_option linter.unusedFintypeInType false in
lemma rlc_iUnion_rankedMinimalCandidate {I : Type*} [Fintype I]
    (W : I → Set (ConfigSpace E)) (prec : I → I → Prop) (rank : I → ℕ)
    (hrank : ∀ {j i}, prec j i → rank j < rank i) :
    (⋃ i, rlc_rankedMinimalCandidate W prec i) = ⋃ i, W i := by
  classical
  apply Set.Subset.antisymm
  · intro omega homega
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp homega
    exact Set.mem_iUnion.mpr ⟨i, hi.1⟩
  · intro omega homega
    obtain ⟨i0, hi0⟩ := Set.mem_iUnion.mp homega
    let Open : Finset I := Finset.univ.filter fun i => omega ∈ W i
    have hOpen : Open.Nonempty := ⟨i0, by simp [Open, hi0]⟩
    let R : Finset ℕ := Open.image rank
    have hR : R.Nonempty := hOpen.image rank
    let r := R.min' hR
    have hrmem : r ∈ R := R.min'_mem hR
    obtain ⟨i, hiOpen, hirank⟩ := Finset.mem_image.mp hrmem
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change omega ∈ W i ∧
      omega ∉ ⋃ j : I, if prec j i then W j else ∅
    refine ⟨(Finset.mem_filter.mp hiOpen).2, ?_⟩
    intro hlower
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hlower
    by_cases hji : prec j i
    · have hjW : omega ∈ W j := by simpa [hji] using hj
      have hjOpen : j ∈ Open := by simp [Open, hjW]
      have hjR : rank j ∈ R := Finset.mem_image.mpr ⟨j, hjOpen, rfl⟩
      have hmin : r ≤ rank j := R.min'_le _ hjR
      have hlt := hrank hji
      rw [hirank] at hlt
      exact (not_lt_of_ge hmin) hlt
    · simp [hji] at hj

/-- The edges of all right diagonal paths below the given one. -/
noncomputable def rlc_rightLowerPathEdges {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : Finset (Sym2 (Site 2)) := by
  classical
  exact (Finset.univ.filter fun delta : RlcRightDiagonalPath n =>
      rlc_rightPathBelow delta gamma).biUnion
        (fun delta => rlc_pathEdges delta.1)

lemma rlc_mem_rightLowerPathEdges {n : ℤ}
    {gamma delta : RlcRightDiagonalPath n} {e : Sym2 (Site 2)}
    (hbelow : rlc_rightPathBelow delta gamma)
    (he : e ∈ rlc_pathEdges delta.1) :
    e ∈ rlc_rightLowerPathEdges gamma := by
  classical
  simp only [rlc_rightLowerPathEdges, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨delta, hbelow, he⟩

/-- The event that `gamma` is open and no right diagonal path below it is open: `gamma` is the
  lowest open path. -/
noncomputable def rlc_rightLowestCandidate {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    Set (ConfigSpace (Sym2 (Site 2))) := by
  classical
  exact rlc_pathOpen gamma.1 \ ⋃ delta : RlcRightDiagonalPath n,
    if rlc_rightPathBelow delta gamma then rlc_pathOpen delta.1 else ∅

/-- The edges determining the lowest-candidate event of `gamma`. -/
noncomputable def rlc_rightLowestCandidateEdges {n : ℤ}
    (gamma : RlcRightDiagonalPath n) : Finset (Sym2 (Site 2)) :=
  rlc_pathEdges gamma.1 ∪ rlc_rightLowerPathEdges gamma

lemma rlc_rightLowestCandidateEdges_subset {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_rightLowestCandidateEdges gamma ⊆
      edgesWithinFinset (rlc_rightExploredVertices gamma) := by
  classical
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [mem_edgesWithinFinset]
      have hxy : x ∈ rlc_rightExploredVertices gamma ∧
          y ∈ rlc_rightExploredVertices gamma := by
        rw [rlc_rightLowestCandidateEdges, Finset.mem_union] at he
        rcases he with hePath | heLower
        · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hePath
          exact ⟨rlc_rightPathVertex_mem_explored gamma hends.1,
            rlc_rightPathVertex_mem_explored gamma hends.2⟩
        · simp only [rlc_rightLowerPathEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_univ, true_and] at heLower
          obtain ⟨delta, hbelow, heDelta⟩ := heLower
          have hends := rlc_pathEdge_endpoints_mem_vertices delta.1 heDelta
          have hsub : rlc_rightExploredVertices delta ⊆
              rlc_rightExploredVertices gamma := by
            rcases hbelow with hstrict | heq
            · exact (Finset.ssubset_iff_subset_ne.mp hstrict).1
            · simp [heq.1]
          constructor
          · exact hsub (rlc_rightPathVertex_mem_explored delta hends.1)
          · exact hsub (rlc_rightPathVertex_mem_explored delta hends.2)
      exact ⟨x, hxy.1, y, hxy.2, rfl⟩

lemma rlc_rightLowestCandidate_dependsOn {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    DependsOn ((rlc_rightLowestCandidate gamma).indicator (fun _ => (1 : ℝ)))
      (rlc_rightLowestCandidateEdges gamma : Set (Sym2 (Site 2))) := by
  classical
  intro omega omega' hagree
  have hgamma : omega ∈ rlc_pathOpen gamma.1 ↔
      omega' ∈ rlc_pathOpen gamma.1 := by
    apply indic_iff
    apply rlc_pathOpen_dependsOn gamma.1
    intro e he
    exact hagree e (by
      simp only [rlc_rightLowestCandidateEdges, Finset.mem_coe,
        Finset.mem_union]
      exact Or.inl he)
  have hdelta : ∀ (delta : RlcRightDiagonalPath n),
      rlc_rightPathBelow delta gamma →
      (omega ∈ rlc_pathOpen delta.1 ↔ omega' ∈ rlc_pathOpen delta.1) := by
    intro delta hbelow
    apply indic_iff
    apply rlc_pathOpen_dependsOn delta.1
    intro e he
    exact hagree e (by
      simp only [rlc_rightLowestCandidateEdges, Finset.mem_coe,
        Finset.mem_union]
      exact Or.inr (rlc_mem_rightLowerPathEdges hbelow he))
  have hlower :
      (omega ∈ ⋃ delta : RlcRightDiagonalPath n,
          if rlc_rightPathBelow delta gamma then
            rlc_pathOpen delta.1 else ∅) ↔
      (omega' ∈ ⋃ delta : RlcRightDiagonalPath n,
          if rlc_rightPathBelow delta gamma then
            rlc_pathOpen delta.1 else ∅) := by
    simp only [Set.mem_iUnion]
    apply exists_congr
    intro delta
    by_cases hbelow : rlc_rightPathBelow delta gamma
    · simpa [hbelow] using hdelta delta hbelow
    · simp [hbelow]
  have hevent : omega ∈ rlc_rightLowestCandidate gamma ↔
      omega' ∈ rlc_rightLowestCandidate gamma := by
    change (_ ∧ ¬ _) ↔ (_ ∧ ¬ _)
    rw [hgamma, hlower]
  by_cases hmem : omega ∈ rlc_rightLowestCandidate gamma
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]

lemma rlc_iUnion_rightLowestCandidate (n : ℤ) :
    (⋃ gamma : RlcRightDiagonalPath n, rlc_rightLowestCandidate gamma) =
      rlc_rightDiagonal n := by
  calc
    _ = ⋃ gamma : RlcRightDiagonalPath n, rlc_pathOpen gamma.1 := by
      simpa only [rlc_rightLowestCandidate, rlc_rankedMinimalCandidate] using
        (rlc_iUnion_rankedMinimalCandidate
          (W := fun gamma : RlcRightDiagonalPath n => rlc_pathOpen gamma.1)
          rlc_rightPathBelow rlc_rightPathRank
          (fun h => rlc_rightPathBelow_rank_lt h))
    _ = rlc_rightDiagonal n := rlc_iUnion_rightDiagonalPath n

/-- The edges of all left diagonal paths above the given one. -/
noncomputable def rlc_leftUpperPathEdges {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : Finset (Sym2 (Site 2)) := by
  classical
  exact (Finset.univ.filter fun delta : RlcLeftDiagonalPath n =>
      rlc_leftPathAbove delta gamma).biUnion
        (fun delta => rlc_pathEdges delta.1)

lemma rlc_mem_leftUpperPathEdges {n : ℤ}
    {gamma delta : RlcLeftDiagonalPath n} {e : Sym2 (Site 2)}
    (habove : rlc_leftPathAbove delta gamma)
    (he : e ∈ rlc_pathEdges delta.1) :
    e ∈ rlc_leftUpperPathEdges gamma := by
  classical
  simp only [rlc_leftUpperPathEdges, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨delta, habove, he⟩

/-- The event that `gamma` is open and no left diagonal path above it is open: `gamma` is the
  highest open path. -/
noncomputable def rlc_leftHighestCandidate {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (Site 2))) := by
  classical
  exact rlc_pathOpen gamma.1 \ ⋃ delta : RlcLeftDiagonalPath n,
    if rlc_leftPathAbove delta gamma then rlc_pathOpen delta.1 else ∅

/-- The edges determining the highest-candidate event of `gamma`. -/
noncomputable def rlc_leftHighestCandidateEdges {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) : Finset (Sym2 (Site 2)) :=
  rlc_pathEdges gamma.1 ∪ rlc_leftUpperPathEdges gamma

lemma rlc_leftHighestCandidateEdges_subset {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_leftHighestCandidateEdges gamma ⊆
      edgesWithinFinset (rlc_leftExploredVertices gamma) := by
  classical
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [mem_edgesWithinFinset]
      have hxy : x ∈ rlc_leftExploredVertices gamma ∧
          y ∈ rlc_leftExploredVertices gamma := by
        rw [rlc_leftHighestCandidateEdges, Finset.mem_union] at he
        rcases he with hePath | heUpper
        · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hePath
          exact ⟨rlc_leftPathVertex_mem_explored gamma hends.1,
            rlc_leftPathVertex_mem_explored gamma hends.2⟩
        · simp only [rlc_leftUpperPathEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_univ, true_and] at heUpper
          obtain ⟨delta, habove, heDelta⟩ := heUpper
          have hends := rlc_pathEdge_endpoints_mem_vertices delta.1 heDelta
          have hsub : rlc_leftExploredVertices delta ⊆
              rlc_leftExploredVertices gamma := by
            rcases habove with hstrict | heq
            · exact (Finset.ssubset_iff_subset_ne.mp hstrict).1
            · simp [heq.1]
          constructor
          · exact hsub (rlc_leftPathVertex_mem_explored delta hends.1)
          · exact hsub (rlc_leftPathVertex_mem_explored delta hends.2)
      change ∃ x' ∈ rlc_leftExploredVertices gamma,
        ∃ y' ∈ rlc_leftExploredVertices gamma, s(x, y) = s(x', y')
      exact ⟨x, hxy.1, y, hxy.2, rfl⟩

lemma rlc_leftHighestCandidate_dependsOn {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    DependsOn ((rlc_leftHighestCandidate gamma).indicator (fun _ => (1 : ℝ)))
      (rlc_leftHighestCandidateEdges gamma : Set (Sym2 (Site 2))) := by
  classical
  intro omega omega' hagree
  have hgamma : omega ∈ rlc_pathOpen gamma.1 ↔
      omega' ∈ rlc_pathOpen gamma.1 := by
    apply indic_iff
    apply rlc_pathOpen_dependsOn gamma.1
    intro e he
    exact hagree e (by
      simp only [rlc_leftHighestCandidateEdges, Finset.mem_coe,
        Finset.mem_union]
      exact Or.inl he)
  have hdelta : ∀ (delta : RlcLeftDiagonalPath n),
      rlc_leftPathAbove delta gamma →
      (omega ∈ rlc_pathOpen delta.1 ↔ omega' ∈ rlc_pathOpen delta.1) := by
    intro delta habove
    apply indic_iff
    apply rlc_pathOpen_dependsOn delta.1
    intro e he
    exact hagree e (by
      simp only [rlc_leftHighestCandidateEdges, Finset.mem_coe,
        Finset.mem_union]
      exact Or.inr (rlc_mem_leftUpperPathEdges habove he))
  have hupper :
      (omega ∈ ⋃ delta : RlcLeftDiagonalPath n,
          if rlc_leftPathAbove delta gamma then
            rlc_pathOpen delta.1 else ∅) ↔
      (omega' ∈ ⋃ delta : RlcLeftDiagonalPath n,
          if rlc_leftPathAbove delta gamma then
            rlc_pathOpen delta.1 else ∅) := by
    simp only [Set.mem_iUnion]
    apply exists_congr
    intro delta
    by_cases habove : rlc_leftPathAbove delta gamma
    · simpa [habove] using hdelta delta habove
    · simp [habove]
  have hevent : omega ∈ rlc_leftHighestCandidate gamma ↔
      omega' ∈ rlc_leftHighestCandidate gamma := by
    change (_ ∧ ¬ _) ↔ (_ ∧ ¬ _)
    rw [hgamma, hupper]
  by_cases hmem : omega ∈ rlc_leftHighestCandidate gamma
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]

lemma rlc_iUnion_leftHighestCandidate (n : ℤ) :
    (⋃ gamma : RlcLeftDiagonalPath n, rlc_leftHighestCandidate gamma) =
      rlc_leftDiagonal n := by
  calc
    _ = ⋃ gamma : RlcLeftDiagonalPath n, rlc_pathOpen gamma.1 := by
      simpa only [rlc_leftHighestCandidate, rlc_rankedMinimalCandidate] using
        (rlc_iUnion_rankedMinimalCandidate
          (W := fun gamma : RlcLeftDiagonalPath n => rlc_pathOpen gamma.1)
          rlc_leftPathAbove rlc_leftPathRank
          (fun h => rlc_leftPathAbove_rank_lt h))
    _ = rlc_leftDiagonal n := rlc_iUnion_leftDiagonalPath n

/-- The event that the pair is the lowest right and highest left open diagonal path. -/
noncomputable def rlc_extremalPairCandidate {n : ℤ}
    (pair : RlcDiagonalPathPair n) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_rightLowestCandidate pair.1 ∩ rlc_leftHighestCandidate pair.2

/-- The edges determining the extremal-pair event. -/
noncomputable def rlc_extremalPairCandidateEdges {n : ℤ}
    (pair : RlcDiagonalPathPair n) : Finset (Sym2 (Site 2)) :=
  rlc_rightLowestCandidateEdges pair.1 ∪
    rlc_leftHighestCandidateEdges pair.2

lemma rlc_extremalPairCandidate_dependsOn {n : ℤ}
    (pair : RlcDiagonalPathPair n) :
    DependsOn ((rlc_extremalPairCandidate pair).indicator (fun _ => (1 : ℝ)))
      (rlc_extremalPairCandidateEdges pair : Set (Sym2 (Site 2))) := by
  simpa only [rlc_extremalPairCandidate, rlc_extremalPairCandidateEdges,
    Finset.coe_union] using
      dependsOn_inter (rlc_rightLowestCandidate_dependsOn pair.1)
        (rlc_leftHighestCandidate_dependsOn pair.2)

lemma rlc_extremalPairCandidate_subset_pathPairOpen {n : ℤ}
    (pair : RlcDiagonalPathPair n) :
    rlc_extremalPairCandidate pair ⊆ rlc_pathPairOpen pair := by
  rintro omega ⟨hright, hleft⟩
  exact ⟨hright.1, hleft.1⟩

lemma rlc_iUnion_extremalPairCandidate (n : ℤ) :
    (⋃ pair : RlcDiagonalPathPair n, rlc_extremalPairCandidate pair) =
      rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
  ext omega
  constructor
  · intro h
    obtain ⟨pair, hright, hleft⟩ := Set.mem_iUnion.mp h
    constructor
    · rw [← rlc_iUnion_rightLowestCandidate]
      exact Set.mem_iUnion.mpr ⟨pair.1, hright⟩
    · rw [← rlc_iUnion_leftHighestCandidate]
      exact Set.mem_iUnion.mpr ⟨pair.2, hleft⟩
  · rintro ⟨hright, hleft⟩
    rw [← rlc_iUnion_rightLowestCandidate] at hright
    rw [← rlc_iUnion_leftHighestCandidate] at hleft
    obtain ⟨gamma, hgamma⟩ := Set.mem_iUnion.mp hright
    obtain ⟨delta, hdelta⟩ := Set.mem_iUnion.mp hleft
    exact Set.mem_iUnion.mpr ⟨(gamma, delta), hgamma, hdelta⟩

lemma rlc_rightLowestCandidate_not_open_of_below {n : ℤ}
    {gamma delta : RlcRightDiagonalPath n}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hgamma : omega ∈ rlc_rightLowestCandidate gamma)
    (hbelow : rlc_rightPathBelow delta gamma) :
    omega ∉ rlc_pathOpen delta.1 := by
  intro hdelta
  apply hgamma.2
  exact Set.mem_iUnion.mpr ⟨delta, by simp [hbelow, hdelta]⟩

lemma rlc_leftHighestCandidate_not_open_of_above {n : ℤ}
    {gamma delta : RlcLeftDiagonalPath n}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hgamma : omega ∈ rlc_leftHighestCandidate gamma)
    (habove : rlc_leftPathAbove delta gamma) :
    omega ∉ rlc_pathOpen delta.1 := by
  intro hdelta
  apply hgamma.2
  exact Set.mem_iUnion.mpr ⟨delta, by simp [habove, hdelta]⟩

/-! ## E. Trace graphs of two paths -/

/-- The graph on the right rectangle whose edges are the edges of two right diagonal paths. -/
def rlc_rightTraceGraph {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    SimpleGraph (rect 0 (2 * n) (-n) n) where
  Adj u v :=
    ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Adj u v ∧
      s((u : Site 2), (v : Site 2)) ∈
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1
  symm := by
    refine ⟨?_⟩
    intro u v h
    exact ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- The walk along `gamma` in the trace graph of `gamma` and `delta`. -/
noncomputable def rlc_rightTraceGraph_walk_left {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_rightTraceGraph gamma delta).Walk
      ⟨gamma.1.1, leftSide_subset gamma.1.1.2⟩
      ⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ := by
  apply gamma.1.2.2.1.transfer (rlc_rightTraceGraph gamma delta)
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have heAmb : s((u : Site 2), (v : Site 2)) ∈
          rlc_pathEdges gamma.1 := by
        simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
        exact ⟨s(u, v), he, by simp⟩
      exact ⟨gamma.1.2.2.1.adj_of_mem_edges he,
        Finset.mem_union_left _ heAmb⟩

/-- The walk along `delta` in the trace graph of `gamma` and `delta`. -/
noncomputable def rlc_rightTraceGraph_walk_right {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_rightTraceGraph gamma delta).Walk
      ⟨delta.1.1, leftSide_subset delta.1.1.2⟩
      ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩ := by
  apply delta.1.2.2.1.transfer (rlc_rightTraceGraph gamma delta)
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have heAmb : s((u : Site 2), (v : Site 2)) ∈
          rlc_pathEdges delta.1 := by
        simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
        exact ⟨s(u, v), he, by simp⟩
      exact ⟨delta.1.2.2.1.adj_of_mem_edges he,
        Finset.mem_union_right _ heAmb⟩

lemma rlc_rightTraceGraph_reachable_of_common {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    {z u v : rect 0 (2 * n) (-n) n}
    (hzGamma : z ∈ gamma.1.2.2.1.support)
    (hzDelta : z ∈ delta.1.2.2.1.support)
    (hu : u ∈ gamma.1.2.2.1.support)
    (hv : v ∈ delta.1.2.2.1.support) :
    (rlc_rightTraceGraph gamma delta).Reachable u v := by
  let pg := rlc_rightTraceGraph_walk_left gamma delta
  let pd := rlc_rightTraceGraph_walk_right gamma delta
  have huPg : u ∈ pg.support := by
    simpa only [pg, rlc_rightTraceGraph_walk_left,
      SimpleGraph.Walk.support_transfer] using hu
  have hzPg : z ∈ pg.support := by
    simpa only [pg, rlc_rightTraceGraph_walk_left,
      SimpleGraph.Walk.support_transfer] using hzGamma
  have hzPd : z ∈ pd.support := by
    simpa only [pd, rlc_rightTraceGraph_walk_right,
      SimpleGraph.Walk.support_transfer] using hzDelta
  have hvPd : v ∈ pd.support := by
    simpa only [pd, rlc_rightTraceGraph_walk_right,
      SimpleGraph.Walk.support_transfer] using hv
  have huz : (rlc_rightTraceGraph gamma delta).Reachable u z :=
    ⟨(pg.takeUntil u huPg).reverse.append (pg.takeUntil z hzPg)⟩
  have hzv : (rlc_rightTraceGraph gamma delta).Reachable z v :=
    ⟨(pd.takeUntil z hzPd).reverse.append (pd.takeUntil v hvPd)⟩
  exact huz.trans hzv

/-- The trace graph restricted to sites outside the strict regions above the two paths. -/
def rlc_rightSafeTraceGraph {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    SimpleGraph (rect 0 (2 * n) (-n) n) where
  Adj u v :=
    ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)).Adj u v ∧
      s((u : Site 2), (v : Site 2)) ∈
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1 ∧
      (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (v : Site 2) ∉ rlc_rightUpperUnionSet gamma delta
  symm := by
    refine ⟨?_⟩
    intro u v h
    exact ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2.1,
      h.2.2.2, h.2.2.1⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

lemma rlc_rightSafeTraceGraph_le_traceGraph {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_rightSafeTraceGraph gamma delta ≤
      rlc_rightTraceGraph gamma delta := by
  intro u v huv
  exact ⟨huv.1, huv.2.1⟩

lemma rlc_jointBottomTraceBoundary_adj_safeTraceGraph {n : ℤ}
    (hn : 0 < n) (gamma delta : RlcRightDiagonalPath n)
    {u v : rect 0 (2 * n) (-n) n}
    (hu : (u : Site 2) ∈ rlc_jointBottomTraceBoundary gamma delta)
    (hv : (v : Site 2) ∈ rlc_jointBottomTraceBoundary gamma delta)
    (he : s((u : Site 2), (v : Site 2)) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1)
    (hadj : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Adj u v) :
    (rlc_rightSafeTraceGraph gamma delta).Adj u v :=
  ⟨hadj, he, rlc_jointBottomTraceBoundary_safe hn gamma delta hu,
    rlc_jointBottomTraceBoundary_safe hn gamma delta hv⟩

lemma rlc_jointBottomTraceBoundary_walk_safe {n : ℤ}
    (hn : 0 < n) (gamma delta : RlcRightDiagonalPath n)
    {x y : rect 0 (2 * n) (-n) n}
    (w : (rlc_rightTraceGraph gamma delta).Walk x y)
    (hboundary : ∀ z ∈ w.support,
      (z : Site 2) ∈ rlc_jointBottomTraceBoundary gamma delta) :
    (rlc_rightSafeTraceGraph gamma delta).Reachable x y := by
  refine ⟨w.transfer (rlc_rightSafeTraceGraph gamma delta) ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv := w.adj_of_mem_edges he
      exact rlc_jointBottomTraceBoundary_adj_safeTraceGraph hn gamma delta
        (hboundary u (w.fst_mem_support_of_mem_edges he))
        (hboundary v (w.snd_mem_support_of_mem_edges he)) huv.2 huv.1

lemma rlc_jointBottomTraceFrontier_adj_safeTraceGraph {n : ℤ}
    (hn : 0 < n) (gamma delta : RlcRightDiagonalPath n)
    {u v : rect 0 (2 * n) (-n) n}
    (hu : (u : Site 2) ∈ rlc_jointBottomTraceFrontier gamma delta)
    (hv : (v : Site 2) ∈ rlc_jointBottomTraceFrontier gamma delta)
    (he : s((u : Site 2), (v : Site 2)) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1)
    (hadj : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Adj u v) :
    (rlc_rightSafeTraceGraph gamma delta).Adj u v :=
  ⟨hadj, he, rlc_jointBottomTraceFrontier_safe hn gamma delta hu,
    rlc_jointBottomTraceFrontier_safe hn gamma delta hv⟩

lemma rlc_jointBottomTraceFrontier_walk_safe {n : ℤ}
    (hn : 0 < n) (gamma delta : RlcRightDiagonalPath n)
    {x y : rect 0 (2 * n) (-n) n}
    (w : (rlc_rightTraceGraph gamma delta).Walk x y)
    (hfrontier : ∀ z ∈ w.support,
      (z : Site 2) ∈ rlc_jointBottomTraceFrontier gamma delta) :
    (rlc_rightSafeTraceGraph gamma delta).Reachable x y := by
  refine ⟨w.transfer (rlc_rightSafeTraceGraph gamma delta) ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv := w.adj_of_mem_edges he
      exact rlc_jointBottomTraceFrontier_adj_safeTraceGraph hn gamma delta
        (hfrontier u (w.fst_mem_support_of_mem_edges he))
        (hfrontier v (w.snd_mem_support_of_mem_edges he)) huv.2 huv.1

lemma rlc_rightSafeTraceGraph_reachable_iff_traceWalk_safe {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    {u v : rect 0 (2 * n) (-n) n}
    (hu : (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta) :
    (rlc_rightSafeTraceGraph gamma delta).Reachable u v ↔
      ∃ p : (rlc_rightTraceGraph gamma delta).Walk u v,
        ∀ z ∈ p.support,
          (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
  constructor
  · rintro ⟨p⟩
    let q := p.mapLe (rlc_rightSafeTraceGraph_le_traceGraph gamma delta)
    have hsafe : ∀ z ∈ p.support,
        (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
      intro z hz
      induction p with
      | nil =>
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
          exact hz ▸ hu
      | @cons a b c hab p ih =>
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hab.2.2.1
          · exact ih hab.2.2.2 hz
    refine ⟨q, ?_⟩
    intro z hz
    have hz' : z ∈ p.support := by
      simpa [q, SimpleGraph.Walk.support_mapLe_eq_support] using hz
    exact hsafe z hz'
  · rintro ⟨p, hp⟩
    refine ⟨p.transfer (rlc_rightSafeTraceGraph gamma delta) ?_⟩
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
        have hab := p.adj_of_mem_edges he
        have ha : a ∈ p.support := p.fst_mem_support_of_mem_edges he
        have hb : b ∈ p.support := p.snd_mem_support_of_mem_edges he
        exact ⟨hab.1, hab.2, hp a ha, hp b hb⟩

/-- The heights of the sites of the two paths on the left side. -/
noncomputable def rlc_rightLeftTraceHeights {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) : Finset ℤ :=
  ((rlc_pathVertices gamma.1 ∪ rlc_pathVertices delta.1).filter
      (fun z => z 0 = 0)).image (fun z => z 1)

lemma rlc_rightLeftTraceHeights_nonempty {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_rightLeftTraceHeights gamma delta).Nonempty := by
  classical
  refine ⟨(gamma.1.1 : Site 2) 1, ?_⟩
  rw [rlc_rightLeftTraceHeights, Finset.mem_image]
  refine ⟨(gamma.1.1 : Site 2), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_union]
  exact ⟨Or.inl (rlc_path_start_mem_vertices gamma.1), gamma.1.1.2.2⟩

/-- The lowest height of a path site on the left side. -/
noncomputable def rlc_rightLeftTraceMin {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) : ℤ :=
  (rlc_rightLeftTraceHeights gamma delta).min'
    (rlc_rightLeftTraceHeights_nonempty gamma delta)

/-- The left-side site at the lowest trace height. -/
noncomputable def rlc_rightLeftTraceMinVertex {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) : Site 2 :=
  ![0, rlc_rightLeftTraceMin gamma delta]

lemma rlc_rightLeftTraceMin_mem_heights {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_rightLeftTraceMin gamma delta ∈
      rlc_rightLeftTraceHeights gamma delta := by
  exact Finset.min'_mem _ _

lemma rlc_rightLeftTraceMinVertex_mem_union {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_rightLeftTraceMinVertex gamma delta ∈
      rlc_pathVertices gamma.1 ∪ rlc_pathVertices delta.1 := by
  classical
  have hmin := rlc_rightLeftTraceMin_mem_heights gamma delta
  rw [rlc_rightLeftTraceHeights, Finset.mem_image] at hmin
  obtain ⟨z, hz, hzmin⟩ := hmin
  rw [Finset.mem_filter] at hz
  have hzeq : z = rlc_rightLeftTraceMinVertex gamma delta := by
    apply funext
    intro i
    fin_cases i
    · simpa [rlc_rightLeftTraceMinVertex] using hz.2
    · simpa [rlc_rightLeftTraceMinVertex] using hzmin
  rw [← hzeq]
  exact hz.1

lemma rlc_rightLeftTraceMinVertex_lowerHalf {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_rightLeftTraceMinVertex gamma delta ∈ rlc_lowerHalf := by
  have hstart : (gamma.1.1 : Site 2) 1 ∈
      rlc_rightLeftTraceHeights gamma delta := by
    classical
    rw [rlc_rightLeftTraceHeights, Finset.mem_image]
    refine ⟨(gamma.1.1 : Site 2), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_union]
    exact ⟨Or.inl (rlc_path_start_mem_vertices gamma.1), gamma.1.1.2.2⟩
  have hle : rlc_rightLeftTraceMin gamma delta ≤
      (gamma.1.1 : Site 2) 1 :=
    Finset.min'_le _ _ hstart
  exact hle.trans gamma.2.1

lemma rlc_rightLeftTraceMinVertex_mem_strictBelow_of_not_path {n : ℤ}
    (gamma delta eta : RlcRightDiagonalPath n)
    (heta : eta = gamma ∨ eta = delta)
    (hnot : rlc_rightLeftTraceMinVertex gamma delta ∉
      rlc_pathVertices eta.1) :
    rlc_rightLeftTraceMinVertex gamma delta ∈
      rlc_strictBelowSet eta := by
  classical
  let m := rlc_rightLeftTraceMin gamma delta
  let z : Site 2 := rlc_rightLeftTraceMinVertex gamma delta
  have hzUnion := rlc_rightLeftTraceMinVertex_mem_union gamma delta
  have hzRect : z ∈ rect 0 (2 * n) (-n) n := by
    rcases Finset.mem_union.mp hzUnion with hz | hz
    · exact rlc_pathVertex_mem_rect gamma.1 hz
    · exact rlc_pathVertex_mem_rect delta.1 hz
  have hmLower : -n ≤ m := by
    rw [mem_rect] at hzRect
    simpa [z, m, rlc_rightLeftTraceMinVertex] using hzRect.2.2.1
  have hmUpper : m ≤ n := by
    rw [mem_rect] at hzRect
    simpa [z, m, rlc_rightLeftTraceMinVertex] using hzRect.2.2.2
  let w := sw_vertSeg 0 (-n) m
  have hsupport : ∀ q ∈ w.support,
      q ∈ rect 0 (2 * n) (-n) n ∧ q ∉ rlc_pathVertices eta.1 := by
    intro q hq
    rw [sw_vertSeg_mem_support] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    rw [Set.uIcc_of_le hmLower] at ht
    rcases ht with ⟨htLower, htUpper⟩
    have hbox : (![0, t] : Site 2) ∈ rect 0 (2 * n) (-n) n := by
      rw [mem_rect]
      have hn0 : 0 ≤ 2 * n := by
        rw [mem_rect] at hzRect
        exact hzRect.2.1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    refine ⟨hbox, ?_⟩
    intro htPath
    have htHeight : t ∈ rlc_rightLeftTraceHeights gamma delta := by
      rw [rlc_rightLeftTraceHeights, Finset.mem_image]
      refine ⟨(![0, t] : Site 2), ?_, by simp⟩
      rw [Finset.mem_filter, Finset.mem_union]
      refine ⟨?_, by simp⟩
      rcases heta with rfl | rfl
      · exact Or.inl htPath
      · exact Or.inr htPath
    have hmt : m ≤ t := Finset.min'_le _ _ htHeight
    have htm : t = m := le_antisymm htUpper hmt
    apply hnot
    simpa [z, m, rlc_rightLeftTraceMinVertex, htm] using htPath
  have hw : (rlc_rightPathAvoidGraph eta).Walk ![0, -n] z := by
    apply w.transfer (rlc_rightPathAvoidGraph eta)
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
        have hab := w.adj_of_mem_edges he
        have ha := hsupport a (w.fst_mem_support_of_mem_edges he)
        have hb := hsupport b (w.snd_mem_support_of_mem_edges he)
        exact ⟨hab, ha.1, hb.1, ha.2, hb.2⟩
  have hbottom : (![0, -n] : Site 2) ∈ bottomSide 0 (2 * n) (-n) n := by
    rw [mem_bottomSide]
    have hn0 : 0 ≤ 2 * n := by
      rw [mem_rect] at hzRect
      exact hzRect.2.1
    constructor
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨le_rfl, hn0, le_rfl, hmLower.trans hmUpper⟩
    · simp
  have hstartAvoid := (hsupport ![0, -n] w.start_mem_support).2
  exact ⟨![0, -n], hbottom, hstartAvoid, ⟨hw⟩⟩

lemma rlc_rightLeftTraceMinVertex_not_upperUnion {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_rightLeftTraceMinVertex gamma delta ∉
      rlc_rightUpperUnionSet gamma delta := by
  intro htop
  rcases htop with htop | htop
  · by_cases hpath : rlc_rightLeftTraceMinVertex gamma delta ∈
        rlc_pathVertices gamma.1
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path gamma)) htop hpath
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_strictBelowSet hn gamma)) htop
          (rlc_rightLeftTraceMinVertex_mem_strictBelow_of_not_path
            gamma delta gamma (Or.inl rfl) hpath)
  · by_cases hpath : rlc_rightLeftTraceMinVertex gamma delta ∈
        rlc_pathVertices delta.1
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path delta)) htop hpath
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_strictBelowSet hn delta)) htop
          (rlc_rightLeftTraceMinVertex_mem_strictBelow_of_not_path
            gamma delta delta (Or.inr rfl) hpath)

lemma rlc_exists_safe_left_trace_anchor {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) :
    ∃ x : leftSide 0 (2 * n) (-n) n,
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (x : Site 2) ∈ rlc_pathVertices gamma.1 ∪
        rlc_pathVertices delta.1 ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
  let z := rlc_rightLeftTraceMinVertex gamma delta
  have hzUnion := rlc_rightLeftTraceMinVertex_mem_union gamma delta
  have hzRect : z ∈ rect 0 (2 * n) (-n) n := by
    rcases Finset.mem_union.mp hzUnion with hz | hz
    · exact rlc_pathVertex_mem_rect gamma.1 hz
    · exact rlc_pathVertex_mem_rect delta.1 hz
  have hzLeft : z ∈ leftSide 0 (2 * n) (-n) n := by
    exact ⟨hzRect, by simp [z, rlc_rightLeftTraceMinVertex]⟩
  exact ⟨⟨z, hzLeft⟩,
    rlc_rightLeftTraceMinVertex_lowerHalf gamma delta,
    hzUnion, rlc_rightLeftTraceMinVertex_not_upperUnion hn gamma delta⟩

/-- The lowest left-side trace site, as an element of the left side. -/
noncomputable def rlc_rightLeftTraceMinSide {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    leftSide 0 (2 * n) (-n) n := by
  let z := rlc_rightLeftTraceMinVertex gamma delta
  have hzUnion := rlc_rightLeftTraceMinVertex_mem_union gamma delta
  have hzRect : z ∈ rect 0 (2 * n) (-n) n := by
    rcases Finset.mem_union.mp hzUnion with hz | hz
    · exact rlc_pathVertex_mem_rect gamma.1 hz
    · exact rlc_pathVertex_mem_rect delta.1 hz
  exact ⟨z, hzRect, by simp [z, rlc_rightLeftTraceMinVertex]⟩

@[simp] lemma rlc_rightLeftTraceMinSide_val {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_rightLeftTraceMinSide gamma delta : Site 2) =
      rlc_rightLeftTraceMinVertex gamma delta := by
  rfl

lemma rlc_rightLeftTraceMinVertex_mem_jointBottomTraceFrontier {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_rightLeftTraceMinVertex gamma delta ∈
      rlc_jointBottomTraceFrontier gamma delta := by
  classical
  let m := rlc_rightLeftTraceMin gamma delta
  let z : Site 2 := rlc_rightLeftTraceMinVertex gamma delta
  have hzUnion := rlc_rightLeftTraceMinVertex_mem_union gamma delta
  have hzPath : z ∈ rlc_pathVertices gamma.1 ∨
      z ∈ rlc_pathVertices delta.1 := by
    simpa [z] using Finset.mem_union.mp hzUnion
  have hzRect : z ∈ rect 0 (2 * n) (-n) n := by
    rcases hzPath with hzGamma | hzDelta
    · exact rlc_pathVertex_mem_rect gamma.1 hzGamma
    · exact rlc_pathVertex_mem_rect delta.1 hzDelta
  have hmLower : -n ≤ m := by
    rw [mem_rect] at hzRect
    simpa [z, m, rlc_rightLeftTraceMinVertex] using hzRect.2.2.1
  by_cases hm : m = -n
  · right
    refine ⟨?_, ?_⟩
    · rw [mem_bottomSide]
      exact ⟨hzRect, by simp [m, rlc_rightLeftTraceMinVertex, hm]⟩
    · exact hzPath
  · left
    refine ⟨hzRect, hzPath, ?_⟩
    let x : Site 2 := ![0, -n]
    let u : Site 2 := ![0, m - 1]
    have hxm : -n ≤ m - 1 := by omega
    let w : (hypercubicLattice 2).Walk x u := sw_vertSeg 0 (-n) (m - 1)
    have hn0 : 0 ≤ 2 * n := by
      rw [mem_rect] at hzRect
      exact hzRect.2.1
    have hsupport : ∀ q ∈ w.support,
        q ∈ rect 0 (2 * n) (-n) n ∧
          q ∉ rlc_pathVertices gamma.1 ∧
          q ∉ rlc_pathVertices delta.1 := by
      intro q hq
      rw [sw_vertSeg_mem_support] at hq
      obtain ⟨t, ht, rfl⟩ := hq
      rw [Set.uIcc_of_le hxm] at ht
      rcases ht with ⟨htLower, htUpper⟩
      have hbox : (![0, t] : Site 2) ∈ rect 0 (2 * n) (-n) n := by
        rw [mem_rect]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        have hmUpper : m ≤ n := by
          rw [mem_rect] at hzRect
          simpa [z, m, rlc_rightLeftTraceMinVertex] using hzRect.2.2.2
        exact ⟨le_rfl, hn0, htLower, htUpper.trans (by omega)⟩
      have avoid : ∀ eta : RlcRightDiagonalPath n,
          (eta = gamma ∨ eta = delta) →
          (![0, t] : Site 2) ∉ rlc_pathVertices eta.1 := by
        intro eta heta htPath
        have htHeight : t ∈ rlc_rightLeftTraceHeights gamma delta := by
          rw [rlc_rightLeftTraceHeights, Finset.mem_image]
          refine ⟨(![0, t] : Site 2), ?_, by simp⟩
          rw [Finset.mem_filter, Finset.mem_union]
          refine ⟨?_, by simp⟩
          rcases heta with rfl | rfl
          · exact Or.inl htPath
          · exact Or.inr htPath
        have hmt : m ≤ t := Finset.min'_le _ _ htHeight
        exact (by omega)
      exact ⟨hbox, avoid gamma (Or.inl rfl), avoid delta (Or.inr rfl)⟩
    have hxBottom : x ∈ bottomSide 0 (2 * n) (-n) n := by
      rw [mem_bottomSide]
      constructor
      · rw [mem_rect]
        simp only [x, Matrix.cons_val_zero, Matrix.cons_val_one]
        exact ⟨le_rfl, hn0, le_rfl, by omega⟩
      · simp [x]
    have hw : (rlc_rightPairAvoidGraph gamma delta).Walk x u := by
      apply w.transfer (rlc_rightPairAvoidGraph gamma delta)
      intro e he
      induction e using Sym2.inductionOn with
      | _ a b =>
          have hab := w.adj_of_mem_edges he
          have ha := hsupport a (w.fst_mem_support_of_mem_edges he)
          have hb := hsupport b (w.snd_mem_support_of_mem_edges he)
          exact ⟨hab, ha.1, hb.1, ha.2.1, hb.2.1,
            ha.2.2, hb.2.2⟩
    have huJoint : u ∈ rlc_jointBottomSet gamma delta := by
      have hx := hsupport x w.start_mem_support
      exact ⟨x, hxBottom, hx.2.1, hx.2.2, ⟨hw⟩⟩
    have huz : (hypercubicLattice 2).Adj u z := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp only [u, z, rlc_rightLeftTraceMinVertex,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    exact ⟨u, huJoint, huz⟩

/-- For every two right diagonal paths, the safe trace graph joins a lower-left site to an upper-
  right site outside the regions above the paths. -/
def RlcRightSafeTraceReachability (n : ℤ) : Prop :=
  ∀ gamma delta : RlcRightDiagonalPath n,
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩

lemma rlc_commonRightPathVertex_not_upperUnion {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {z : Site 2}
    (hzGamma : z ∈ rlc_pathVertices gamma.1)
    (hzDelta : z ∈ rlc_pathVertices delta.1) :
    z ∉ rlc_rightUpperUnionSet gamma delta := by
  rintro (hzTopGamma | hzTopDelta)
  · exact (Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_path gamma)) hzTopGamma hzGamma
  · exact (Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_path delta)) hzTopDelta hzDelta

lemma rlc_walk_pred_first_exit {V : Type*} {G : SimpleGraph V} {x y : V}
    (w : G.Walk x y) (P : V → Prop) (hx : P x) (hy : ¬ P y) :
    ∃ u v, s(u, v) ∈ w.edges ∧ P u ∧ ¬ P v := by
  classical
  induction w with
  | nil => exact False.elim (hy hx)
  | @cons a b c hab p ih =>
      by_cases hb : P b
      · obtain ⟨u, v, huv, hu, hv⟩ := ih hb hy
        exact ⟨u, v, by simp [huv], hu, hv⟩
      · exact ⟨a, b, by simp, hx, hb⟩

lemma rlc_walk_pred_first_exit_prefix {V : Type*} {G : SimpleGraph V}
    {x y : V} (w : G.Walk x y) (P : V → Prop) (hx : P x) (hy : ¬ P y) :
    ∃ (u v : V) (q : G.Walk x u),
      G.Adj u v ∧ s(u, v) ∈ w.edges ∧
      (∀ e ∈ q.edges, e ∈ w.edges) ∧
      (∀ z ∈ q.support, P z) ∧ ¬ P v := by
  classical
  induction w with
  | nil => exact False.elim (hy hx)
  | @cons a b c hab p ih =>
      by_cases hb : P b
      · obtain ⟨u, v, q, huv, huvEdge, hqEdges, hqSafe, hv⟩ := ih hb hy
        refine ⟨u, v, .cons hab q, huv, by simp [huvEdge], ?_, ?_, hv⟩
        · intro e he
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
          rcases he with rfl | he
          · simp
          · simp [hqEdges e he]
        · intro z hz
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hx
          · exact hqSafe z hz
      · refine ⟨a, b, .nil, hab, by simp, ?_, ?_, hb⟩
        · intro e he
          simp at he
        · intro z hz
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
          exact hz ▸ hx

lemma rlc_rightTrace_switchPoint_of_enter_upperUnion {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (he : s(u, v) ∈ rlc_pathEdges gamma.1)
    (hu : u ∉ rlc_rightUpperUnionSet gamma delta)
    (hv : v ∈ rlc_rightUpperUnionSet gamma delta) :
    u ∈ rlc_pathVertices gamma.1 ∧
      u ∈ rlc_pathVertices delta.1 := by
  have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he
  refine ⟨hends.1, ?_⟩
  rcases hv with hvGamma | hvDelta
  · exact False.elim ((Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_path gamma)) hvGamma hends.2)
  · exact rlc_rightPathEdge_enter_strictTop_common
      gamma delta he (fun h => hu (Or.inr h)) hvDelta

lemma rlc_rightTrace_switchPoint_of_enter_upperUnion' {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (he : s(u, v) ∈ rlc_pathEdges delta.1)
    (hu : u ∉ rlc_rightUpperUnionSet gamma delta)
    (hv : v ∈ rlc_rightUpperUnionSet gamma delta) :
    u ∈ rlc_pathVertices gamma.1 ∧
      u ∈ rlc_pathVertices delta.1 := by
  have h := rlc_rightTrace_switchPoint_of_enter_upperUnion
    delta gamma he (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hu)
      (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hv)
  exact ⟨h.2, h.1⟩

lemma rlc_rightTrace_common_switch_before_unsafe_end {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hstart : (gamma.1.1 : Site 2) ∉
      rlc_rightUpperUnionSet gamma delta)
    (hend : (gamma.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ u v : rect 0 (2 * n) (-n) n,
      s((u : Site 2), (v : Site 2)) ∈ rlc_pathEdges gamma.1 ∧
      (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (v : Site 2) ∈ rlc_rightUpperUnionSet gamma delta ∧
      (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧
      (u : Site 2) ∈ rlc_pathVertices delta.1 := by
  classical
  let p := gamma.1.2.2.1
  obtain ⟨u, v, huv, hu, hv⟩ := rlc_walk_pred_first_exit p
    (fun z => (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
    (by simpa [p] using hstart) (by simpa [p] using hend)
  have he : s((u : Site 2), (v : Site 2)) ∈
      rlc_pathEdges gamma.1 := by
    simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
    exact ⟨s(u, v), huv, rfl⟩
  have hcommon := rlc_rightTrace_switchPoint_of_enter_upperUnion
    gamma delta he hu (not_not.mp hv)
  exact ⟨u, v, he, hu, not_not.mp hv, hcommon.1, hcommon.2⟩

lemma rlc_rightTrace_common_switch_before_unsafe_end' {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hstart : (delta.1.1 : Site 2) ∉
      rlc_rightUpperUnionSet gamma delta)
    (hend : (delta.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ u v : rect 0 (2 * n) (-n) n,
      s((u : Site 2), (v : Site 2)) ∈ rlc_pathEdges delta.1 ∧
      (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (v : Site 2) ∈ rlc_rightUpperUnionSet gamma delta ∧
      (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧
      (u : Site 2) ∈ rlc_pathVertices delta.1 := by
  obtain ⟨u, v, he, hu, hv, huDelta, huGamma⟩ :=
    rlc_rightTrace_common_switch_before_unsafe_end delta gamma
      (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hstart)
      (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hend)
  exact ⟨u, v, he,
    by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hu,
    by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hv,
    huGamma, huDelta⟩

lemma rlc_rightSafeTrace_reaches_common_before_unsafe_end {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hstart : (gamma.1.1 : Site 2) ∉
      rlc_rightUpperUnionSet gamma delta)
    (hend : (gamma.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ u : rect 0 (2 * n) (-n) n,
      (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧
      (u : Site 2) ∈ rlc_pathVertices delta.1 ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨gamma.1.1, leftSide_subset gamma.1.1.2⟩ u := by
  classical
  let p := gamma.1.2.2.1
  obtain ⟨u, v, q, _huv, huvEdge, hqEdges, hqSafe, hv⟩ :=
    rlc_walk_pred_first_exit_prefix p
      (fun z => (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
      (by simpa [p] using hstart) (by simpa [p] using hend)
  have he : s((u : Site 2), (v : Site 2)) ∈
      rlc_pathEdges gamma.1 := by
    simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
    exact ⟨s(u, v), huvEdge, rfl⟩
  have hcommon := rlc_rightTrace_switchPoint_of_enter_upperUnion
    gamma delta he (hqSafe u q.end_mem_support) (not_not.mp hv)
  refine ⟨u, hcommon.1, hcommon.2, ⟨q.transfer
    (rlc_rightSafeTraceGraph gamma delta) ?_⟩⟩
  intro e heq
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab := q.adj_of_mem_edges heq
      have habOrig : s(a, b) ∈ p.edges := hqEdges s(a, b) heq
      have habPath : s((a : Site 2), (b : Site 2)) ∈
          rlc_pathEdges gamma.1 := by
        simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
        exact ⟨s(a, b), habOrig, rfl⟩
      exact ⟨hab, Finset.mem_union_left _ habPath,
        hqSafe a (q.fst_mem_support_of_mem_edges heq),
        hqSafe b (q.snd_mem_support_of_mem_edges heq)⟩

lemma rlc_rightSafeTrace_reaches_common_from_vertex {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    {z : rect 0 (2 * n) (-n) n}
    (hz : z ∈ gamma.1.2.2.1.support)
    (hzSafe : (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
    (hend : (gamma.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ u : rect 0 (2 * n) (-n) n,
      (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧
      (u : Site 2) ∈ rlc_pathVertices delta.1 ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable z u := by
  classical
  let p := gamma.1.2.2.1
  let tail := p.dropUntil z hz
  obtain ⟨u, v, q, _huv, huvEdge, hqEdges, hqSafe, hv⟩ :=
    rlc_walk_pred_first_exit_prefix tail
      (fun w => (w : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
      (by simpa [tail] using hzSafe) (by simpa [tail, p] using hend)
  have huvOrig : s(u, v) ∈ p.edges := by
    exact (p.edges_dropUntil_subset_edges (by simpa [p] using hz)) huvEdge
  have he : s((u : Site 2), (v : Site 2)) ∈
      rlc_pathEdges gamma.1 := by
    simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
    exact ⟨s(u, v), huvOrig, rfl⟩
  have hcommon := rlc_rightTrace_switchPoint_of_enter_upperUnion
    gamma delta he (hqSafe u q.end_mem_support) (not_not.mp hv)
  refine ⟨u, hcommon.1, hcommon.2, ⟨q.transfer
    (rlc_rightSafeTraceGraph gamma delta) ?_⟩⟩
  intro e heq
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab := q.adj_of_mem_edges heq
      have habTail : s(a, b) ∈ tail.edges := hqEdges s(a, b) heq
      have habOrig : s(a, b) ∈ p.edges := by
        exact (p.edges_dropUntil_subset_edges (by simpa [p] using hz)) habTail
      have habPath : s((a : Site 2), (b : Site 2)) ∈
          rlc_pathEdges gamma.1 := by
        simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
        exact ⟨s(a, b), habOrig, rfl⟩
      exact ⟨hab, Finset.mem_union_left _ habPath,
        hqSafe a (q.fst_mem_support_of_mem_edges heq),
        hqSafe b (q.snd_mem_support_of_mem_edges heq)⟩

lemma rlc_safe_vertex_reaches_endpoint_or_common {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    {z : rect 0 (2 * n) (-n) n}
    (hz : z ∈ gamma.1.2.2.1.support)
    (hzSafe : (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta) :
    (rlc_rightSafeTraceGraph gamma delta).Reachable z
        ⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ ∨
      ∃ u : rect 0 (2 * n) (-n) n,
        (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧
        (u : Site 2) ∈ rlc_pathVertices delta.1 ∧
        (rlc_rightSafeTraceGraph gamma delta).Reachable z u := by
  classical
  let p := gamma.1.2.2.1
  let tail := p.dropUntil z hz
  by_cases hall : ∀ q ∈ tail.support,
      (q : Site 2) ∉ rlc_rightUpperUnionSet gamma delta
  · left
    refine ⟨tail.transfer (rlc_rightSafeTraceGraph gamma delta) ?_⟩
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
        have habTail := tail.adj_of_mem_edges he
        have habOrig : s(a, b) ∈ p.edges :=
          p.edges_dropUntil_subset_edges hz he
        have habPath : s((a : Site 2), (b : Site 2)) ∈
            rlc_pathEdges gamma.1 := by
          simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
          exact ⟨s(a, b), habOrig, rfl⟩
        exact ⟨habTail, Finset.mem_union_left _ habPath,
          hall a (tail.fst_mem_support_of_mem_edges he),
          hall b (tail.snd_mem_support_of_mem_edges he)⟩
  · right
    push Not at hall
    obtain ⟨v0, hv0Supp, hv0Unsafe⟩ := hall
    let initial := tail.takeUntil v0 hv0Supp
    obtain ⟨u, v, q, _huv, huvEdge, hqEdges, hqSafe, hv⟩ :=
      rlc_walk_pred_first_exit_prefix initial
        (fun w => (w : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
        (by simpa [initial, tail] using hzSafe)
        (by simpa [initial] using hv0Unsafe)
    have huvTail : s(u, v) ∈ tail.edges :=
      tail.edges_takeUntil_subset_edges hv0Supp huvEdge
    have huvOrig : s(u, v) ∈ p.edges :=
      p.edges_dropUntil_subset_edges hz huvTail
    have he : s((u : Site 2), (v : Site 2)) ∈
        rlc_pathEdges gamma.1 := by
      simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
      exact ⟨s(u, v), huvOrig, rfl⟩
    have hcommon := rlc_rightTrace_switchPoint_of_enter_upperUnion
      gamma delta he (hqSafe u q.end_mem_support) (not_not.mp hv)
    refine ⟨u, hcommon.1, hcommon.2, ⟨q.transfer
      (rlc_rightSafeTraceGraph gamma delta) ?_⟩⟩
    intro e heq
    induction e using Sym2.inductionOn with
    | _ a b =>
        have hab := q.adj_of_mem_edges heq
        have habInitial : s(a, b) ∈ initial.edges := hqEdges s(a, b) heq
        have habTail : s(a, b) ∈ tail.edges :=
          tail.edges_takeUntil_subset_edges hv0Supp habInitial
        have habOrig : s(a, b) ∈ p.edges :=
          p.edges_dropUntil_subset_edges hz habTail
        have habPath : s((a : Site 2), (b : Site 2)) ∈
            rlc_pathEdges gamma.1 := by
          simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
          exact ⟨s(a, b), habOrig, rfl⟩
        exact ⟨hab, Finset.mem_union_left _ habPath,
          hqSafe a (q.fst_mem_support_of_mem_edges heq),
          hqSafe b (q.snd_mem_support_of_mem_edges heq)⟩

lemma rlc_safe_left_anchor_reaches_common_of_unsafe_ends {n : ℤ}
    (hn : 0 < n) (gamma delta : RlcRightDiagonalPath n)
    (hgammaEnd : (gamma.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta)
    (hdeltaEnd : (delta.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ (z : leftSide 0 (2 * n) (-n) n)
      (u : rect 0 (2 * n) (-n) n),
      (z : Site 2) ∈ rlc_lowerHalf ∧
      (u : Site 2) ∈ rlc_pathVertices gamma.1 ∧
      (u : Site 2) ∈ rlc_pathVertices delta.1 ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨z, leftSide_subset z.2⟩ u := by
  classical
  obtain ⟨z, hzHalf, hzUnion, hzSafe⟩ :=
    rlc_exists_safe_left_trace_anchor hn gamma delta
  let zs : rect 0 (2 * n) (-n) n := ⟨z, leftSide_subset z.2⟩
  rcases Finset.mem_union.mp hzUnion with hzGamma | hzDelta
  · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hzGamma
    obtain ⟨zg, hzg, hzgz⟩ := hzGamma
    have hzgEq : zg = zs := by
      apply Subtype.ext
      exact hzgz
    subst zg
    obtain ⟨u, huGamma, huDelta, hreach⟩ :=
      rlc_rightSafeTrace_reaches_common_from_vertex gamma delta hzg hzSafe hgammaEnd
    exact ⟨z, u, hzHalf, huGamma, huDelta, hreach⟩
  · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hzDelta
    obtain ⟨zd, hzd, hzdz⟩ := hzDelta
    have hzdEq : zd = zs := by
      apply Subtype.ext
      exact hzdz
    subst zd
    obtain ⟨u, huDelta, huGamma, hreach⟩ :=
      rlc_rightSafeTrace_reaches_common_from_vertex delta gamma hzd
        (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hzSafe)
        (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hdeltaEnd)
    refine ⟨z, u, hzHalf, huGamma, huDelta, ?_⟩
    simpa [rlc_rightSafeTraceGraph, rlc_rightUpperUnionSet,
      Finset.union_comm, Set.union_comm] using hreach

lemma rlc_rightSafeTraceGraph_adj_of_pathEdge {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    {u v : rect 0 (2 * n) (-n) n}
    (he : s((u : Site 2), (v : Site 2)) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1)
    (hu : (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
    (hv : (v : Site 2) ∉ rlc_rightUpperUnionSet gamma delta) :
    (rlc_rightSafeTraceGraph gamma delta).Adj u v := by
  rw [Finset.mem_union] at he
  rcases he with heGamma | heDelta
  · exact ⟨rlc_pathEdge_lattice gamma.1 heGamma,
      Finset.mem_union_left _ heGamma, hu, hv⟩
  · exact ⟨rlc_pathEdge_lattice delta.1 heDelta,
      Finset.mem_union_right _ heDelta, hu, hv⟩

lemma rlc_rightSafeTraceGraph_reachable_dest_safe {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    {u v : rect 0 (2 * n) (-n) n}
    (hu : (u : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
    (hreach : (rlc_rightSafeTraceGraph gamma delta).Reachable u v) :
    (v : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
  obtain ⟨p⟩ := hreach
  induction p with
  | nil => exact hu
  | @cons a b c hab p ih =>
      exact ih hab.2.2.2

lemma rlc_rightSafeTraceReachable_of_path_safe {n : ℤ}
    (gamma delta eta : RlcRightDiagonalPath n)
    (hedges : rlc_pathEdges eta.1 ⊆
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1)
    (hsafe : Disjoint (rlc_rightUpperUnionSet gamma delta)
      (rlc_pathVertices eta.1 : Set (Site 2))) :
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
  classical
  let p := eta.1.2.2.1
  have hpStart : (eta.1.1 : Site 2) ∈ rlc_pathVertices eta.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    refine ⟨⟨eta.1.1, leftSide_subset eta.1.1.2⟩, ?_, rfl⟩
    simp
  have hpEnd : (eta.1.2.1 : Site 2) ∈ rlc_pathVertices eta.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    refine ⟨⟨eta.1.2.1, rightSide_subset eta.1.2.1.2⟩, ?_, rfl⟩
    simp
  have hstartSafe : (eta.1.1 : Site 2) ∉
      rlc_rightUpperUnionSet gamma delta :=
    fun h => (Set.disjoint_left.mp hsafe) h hpStart
  have hendSafe : (eta.1.2.1 : Site 2) ∉
      rlc_rightUpperUnionSet gamma delta :=
    fun h => (Set.disjoint_left.mp hsafe) h hpEnd
  have hp : (rlc_rightSafeTraceGraph gamma delta).Walk
      ⟨eta.1.1, leftSide_subset eta.1.1.2⟩
      ⟨eta.1.2.1, rightSide_subset eta.1.2.1.2⟩ := by
    apply p.transfer (rlc_rightSafeTraceGraph gamma delta)
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have huv : s((u : Site 2), (v : Site 2)) ∈
            rlc_pathEdges eta.1 := by
          simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
          exact ⟨s(u, v), he, by simp⟩
        have hends := rlc_pathEdge_endpoints_mem_vertices eta.1 huv
        exact ⟨p.adj_of_mem_edges he, hedges huv,
          fun hu => (Set.disjoint_left.mp hsafe) hu hends.1,
          fun hv => (Set.disjoint_left.mp hsafe) hv hends.2⟩
  exact ⟨eta.1.1, eta.1.2.1, eta.2.1, eta.2.2,
    hstartSafe, hendSafe, ⟨hp⟩⟩

lemma rlc_rightSafeTraceReachable_of_left_trace {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hcross : Disjoint (rlc_strictTopSet delta)
      (rlc_pathVertices gamma.1 : Set (Site 2))) :
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
  apply rlc_rightSafeTraceReachable_of_path_safe gamma delta gamma
  · intro e he
    exact Finset.mem_union_left _ he
  · rw [rlc_rightUpperUnionSet, Set.disjoint_union_left]
    exact ⟨rlc_strictTopSet_disjoint_path gamma, hcross⟩

lemma rlc_rightSafeTraceReachable_of_right_trace {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hcross : Disjoint (rlc_strictTopSet gamma)
      (rlc_pathVertices delta.1 : Set (Site 2))) :
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
  apply rlc_rightSafeTraceReachable_of_path_safe gamma delta delta
  · intro e he
    exact Finset.mem_union_right _ he
  · rw [rlc_rightUpperUnionSet, Set.disjoint_union_left]
    exact ⟨hcross, rlc_strictTopSet_disjoint_path delta⟩

lemma rlc_rightSafeTraceReachable_self {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma gamma ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma gamma ∧
      (rlc_rightSafeTraceGraph gamma gamma).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ :=
  rlc_rightSafeTraceReachable_of_left_trace gamma gamma
    (rlc_strictTopSet_disjoint_path gamma)

lemma rlc_rightSafeTraceReachable_of_disjoint_start_left {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices delta.1)
      (rlc_pathVertices gamma.1))
    (hstart : (gamma.1.1 : Site 2) ∉ rlc_strictTopSet delta) :
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
  apply rlc_rightSafeTraceReachable_of_left_trace gamma delta
  rw [Set.disjoint_left]
  intro z hzTop hzGamma
  have hiff := rlc_strictTopSet_mem_iff_path_start_of_disjoint
    delta gamma hdisj hzGamma
  exact hstart (hiff.mp hzTop)

lemma rlc_rightSafeTraceReachable_of_disjoint_start_right {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    (hstart : (delta.1.1 : Site 2) ∉ rlc_strictTopSet gamma) :
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
  apply rlc_rightSafeTraceReachable_of_right_trace gamma delta
  rw [Set.disjoint_left]
  intro z hzTop hzDelta
  have hiff := rlc_strictTopSet_mem_iff_path_start_of_disjoint
    gamma delta hdisj hzDelta
  exact hstart (hiff.mp hzTop)

lemma rlc_rightSafeTraceReachable_of_disjoint {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1)) :
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ := by
  by_cases hgammaStart :
      (gamma.1.1 : Site 2) ∈ rlc_strictTopSet delta
  · have hgammaTop : (rlc_pathVertices gamma.1 : Set (Site 2)) ⊆
        rlc_strictTopSet delta := by
      intro z hz
      exact (rlc_strictTopSet_mem_iff_path_start_of_disjoint
        delta gamma hdisj.symm hz).mpr hgammaStart
    have hdeltaStart :
        (delta.1.1 : Site 2) ∉ rlc_strictTopSet gamma := by
      intro hdeltaStart
      have hdeltaTop : (rlc_pathVertices delta.1 : Set (Site 2)) ⊆
          rlc_strictTopSet gamma := by
        intro z hz
        exact (rlc_strictTopSet_mem_iff_path_start_of_disjoint
          gamma delta hdisj hz).mpr hdeltaStart
      exact rlc_disjointRightPaths_not_mutually_top
        hn gamma delta hdisj ⟨hgammaTop, hdeltaTop⟩
    exact rlc_rightSafeTraceReachable_of_disjoint_start_right
      gamma delta hdisj hdeltaStart
  · exact rlc_rightSafeTraceReachable_of_disjoint_start_left
      gamma delta hdisj.symm hgammaStart

/-- The safe-trace reachability property, required only for intersecting pairs of right diagonal
  paths. -/
def RlcRightIntersectingSafeTraceReachability (n : ℤ) : Prop :=
  ∀ (gamma delta : RlcRightDiagonalPath n),
    ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices delta.1) →
    ∃ (x : leftSide 0 (2 * n) (-n) n)
      (y : rightSide 0 (2 * n) (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩

/-- The sites common to two right diagonal paths. -/
noncomputable def rlc_rightCommonSupport {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    Finset (rect 0 (2 * n) (-n) n) :=
  gamma.1.2.2.1.support.toFinset ∩ delta.1.2.2.1.support.toFinset

lemma rlc_rightCommonSupport_nonempty_of_not_disjoint {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1)) :
    (rlc_rightCommonSupport gamma delta).Nonempty := by
  classical
  obtain ⟨z, hzGamma, hzDelta⟩ := Finset.not_disjoint_iff.mp hinter
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hzGamma hzDelta
  obtain ⟨u, huGamma, huz⟩ := hzGamma
  obtain ⟨v, hvDelta, hvz⟩ := hzDelta
  have huv : u = v := by
    apply Subtype.ext
    exact huz.trans hvz.symm
  subst v
  refine ⟨u, ?_⟩
  simp [rlc_rightCommonSupport, huGamma, hvDelta]

/-- The position along `delta` of a common site of `gamma` and `delta`. -/
noncomputable def rlc_rightCommonRank {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (z : ↑(rlc_rightCommonSupport gamma delta)) : ℕ := by
  have hz : (z.1 ∈ gamma.1.2.2.1.support) ∧
      (z.1 ∈ delta.1.2.2.1.support) := by
    have hz' := Finset.mem_inter.mp z.2
    exact ⟨by simpa using hz'.1, by simpa using hz'.2⟩
  exact (gamma.1.2.2.1.takeUntil z.1 hz.1).length +
    (delta.1.2.2.1.takeUntil z.1 hz.2).length

lemma rlc_exists_min_rightCommonSupport {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1)) :
    ∃ z : ↑(rlc_rightCommonSupport gamma delta),
      ∀ q : ↑(rlc_rightCommonSupport gamma delta),
        rlc_rightCommonRank gamma delta z ≤
          rlc_rightCommonRank gamma delta q := by
  classical
  have hne := rlc_rightCommonSupport_nonempty_of_not_disjoint
    gamma delta hinter
  let : Nonempty ↑(rlc_rightCommonSupport gamma delta) :=
    ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have huniv : (Finset.univ :
      Finset ↑(rlc_rightCommonSupport gamma delta)).Nonempty :=
    ⟨⟨hne.choose, hne.choose_spec⟩, Finset.mem_univ _⟩
  obtain ⟨z, _hz, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset ↑(rlc_rightCommonSupport gamma delta))
    (rlc_rightCommonRank gamma delta) huniv
  exact ⟨z, fun q => hmin q (by simp)⟩

lemma rlc_min_rightCommon_prefixes_inter_only {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (z : ↑(rlc_rightCommonSupport gamma delta))
    (hzGamma : z.1 ∈ gamma.1.2.2.1.support)
    (hzDelta : z.1 ∈ delta.1.2.2.1.support)
    (hmin : ∀ q : ↑(rlc_rightCommonSupport gamma delta),
      rlc_rightCommonRank gamma delta z ≤
        rlc_rightCommonRank gamma delta q)
    {q : rect 0 (2 * n) (-n) n}
    (hqGamma : q ∈ (gamma.1.2.2.1.takeUntil z.1 hzGamma).support)
    (hqDelta : q ∈ (delta.1.2.2.1.takeUntil z.1 hzDelta).support) :
    q = z.1 := by
  classical
  by_contra hqz
  have hqGammaFull : q ∈ gamma.1.2.2.1.support :=
    gamma.1.2.2.1.support_takeUntil_subset_support hzGamma hqGamma
  have hqDeltaFull : q ∈ delta.1.2.2.1.support :=
    delta.1.2.2.1.support_takeUntil_subset_support hzDelta hqDelta
  have hqCommon : q ∈ rlc_rightCommonSupport gamma delta := by
    simp [rlc_rightCommonSupport, hqGammaFull, hqDeltaFull]
  let qs : ↑(rlc_rightCommonSupport gamma delta) := ⟨q, hqCommon⟩
  have hgammaLt :
      (gamma.1.2.2.1.takeUntil q hqGammaFull).length <
        (gamma.1.2.2.1.takeUntil z.1 hzGamma).length := by
    have hlen := (gamma.1.2.2.1.takeUntil z.1 hzGamma).length_takeUntil_lt_length
      hqGamma hqz
    rwa [gamma.1.2.2.1.takeUntil_takeUntil hzGamma hqGamma] at hlen
  have hdeltaLt :
      (delta.1.2.2.1.takeUntil q hqDeltaFull).length <
        (delta.1.2.2.1.takeUntil z.1 hzDelta).length := by
    have hlen := (delta.1.2.2.1.takeUntil z.1 hzDelta).length_takeUntil_lt_length
      hqDelta hqz
    rwa [delta.1.2.2.1.takeUntil_takeUntil hzDelta hqDelta] at hlen
  have hrankLt : rlc_rightCommonRank gamma delta qs <
      rlc_rightCommonRank gamma delta z := by
    change (gamma.1.2.2.1.takeUntil q hqGammaFull).length +
        (delta.1.2.2.1.takeUntil q hqDeltaFull).length <
      (gamma.1.2.2.1.takeUntil z.1 hzGamma).length +
        (delta.1.2.2.1.takeUntil z.1 hzDelta).length
    omega
  exact (not_lt_of_ge (hmin qs)) hrankLt

/-- The position from the end along `delta` of a common site of `gamma` and `delta`. -/
noncomputable def rlc_rightCommonReverseRank {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (z : ↑(rlc_rightCommonSupport gamma delta)) : ℕ := by
  have hz : (z.1 ∈ gamma.1.2.2.1.reverse.support) ∧
      (z.1 ∈ delta.1.2.2.1.reverse.support) := by
    have hz' := Finset.mem_inter.mp z.2
    constructor
    · simpa [SimpleGraph.Walk.support_reverse] using hz'.1
    · simpa [SimpleGraph.Walk.support_reverse] using hz'.2
  exact (gamma.1.2.2.1.reverse.takeUntil z.1 hz.1).length +
    (delta.1.2.2.1.reverse.takeUntil z.1 hz.2).length

/-- The position from the end along `gamma` of a common site of `gamma` and `delta`. -/
noncomputable def rlc_rightCommonGammaReverseRank {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (z : ↑(rlc_rightCommonSupport gamma delta)) : ℕ := by
  have hz : z.1 ∈ gamma.1.2.2.1.reverse.support := by
    have hz' := (Finset.mem_inter.mp z.2).1
    simpa [SimpleGraph.Walk.support_reverse] using hz'
  exact (gamma.1.2.2.1.reverse.takeUntil z.1 hz).length

lemma rlc_exists_min_gamma_reverse_rightCommonSupport {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1)) :
    ∃ z : ↑(rlc_rightCommonSupport gamma delta),
      ∀ q : ↑(rlc_rightCommonSupport gamma delta),
        rlc_rightCommonGammaReverseRank gamma delta z ≤
          rlc_rightCommonGammaReverseRank gamma delta q := by
  classical
  have hne := rlc_rightCommonSupport_nonempty_of_not_disjoint
    gamma delta hinter
  let : Nonempty ↑(rlc_rightCommonSupport gamma delta) :=
    ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have huniv : (Finset.univ :
      Finset ↑(rlc_rightCommonSupport gamma delta)).Nonempty :=
    ⟨⟨hne.choose, hne.choose_spec⟩, Finset.mem_univ _⟩
  obtain ⟨z, _hz, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset ↑(rlc_rightCommonSupport gamma delta))
    (rlc_rightCommonGammaReverseRank gamma delta) huniv
  exact ⟨z, fun q => hmin q (by simp)⟩

lemma rlc_min_gamma_reverse_rightCommon_prefix_inter_only {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (z : ↑(rlc_rightCommonSupport gamma delta))
    (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support)
    (hmin : ∀ q : ↑(rlc_rightCommonSupport gamma delta),
      rlc_rightCommonGammaReverseRank gamma delta z ≤
        rlc_rightCommonGammaReverseRank gamma delta q)
    {q : rect 0 (2 * n) (-n) n}
    (hqGamma : q ∈
      (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).support)
    (hqDelta : q ∈ delta.1.2.2.1.support) :
    q = z.1 := by
  classical
  by_contra hqz
  have hqGammaRev : q ∈ gamma.1.2.2.1.reverse.support :=
    gamma.1.2.2.1.reverse.support_takeUntil_subset_support
      hzGamma hqGamma
  have hqGammaOrig : q ∈ gamma.1.2.2.1.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hqGammaRev
  have hqCommon : q ∈ rlc_rightCommonSupport gamma delta := by
    simp [rlc_rightCommonSupport, hqGammaOrig, hqDelta]
  let qs : ↑(rlc_rightCommonSupport gamma delta) := ⟨q, hqCommon⟩
  have hrankLt : rlc_rightCommonGammaReverseRank gamma delta qs <
      rlc_rightCommonGammaReverseRank gamma delta z := by
    change (gamma.1.2.2.1.reverse.takeUntil q hqGammaRev).length <
      (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).length
    have hlen :=
      (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).length_takeUntil_lt_length
        hqGamma hqz
    rwa [gamma.1.2.2.1.reverse.takeUntil_takeUntil hzGamma hqGamma] at hlen
  exact (not_lt_of_ge (hmin qs)) hrankLt

lemma rlc_last_gamma_terminal_suffix_top_of_unsafe_end {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    (hgammaEnd : (gamma.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ (z : ↑(rlc_rightCommonSupport gamma delta))
      (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support),
      let pg := gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma
      ¬ pg.Nil ∧
        (∀ q ∈ pg.dropLast.support,
          (q : Site 2) ∉ rlc_pathVertices delta.1) ∧
        (∀ q ∈ pg.dropLast.support,
          (q : Site 2) ∈ rlc_strictTopSet delta) := by
  classical
  obtain ⟨z, hmin⟩ :=
    rlc_exists_min_gamma_reverse_rightCommonSupport gamma delta hinter
  have hzBoth := Finset.mem_inter.mp z.2
  have hzGammaOrig : z.1 ∈ gamma.1.2.2.1.support := by
    simpa [rlc_rightCommonSupport] using hzBoth.1
  have hzDeltaOrig : z.1 ∈ delta.1.2.2.1.support := by
    simpa [rlc_rightCommonSupport] using hzBoth.2
  have hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hzGammaOrig
  have hzPathGamma : (z.1 : Site 2) ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨z.1, hzGammaOrig, rfl⟩
  have hzPathDelta : (z.1 : Site 2) ∈ rlc_pathVertices delta.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨z.1, hzDeltaOrig, rfl⟩
  have hzSafe := rlc_commonRightPathVertex_not_upperUnion
    gamma delta hzPathGamma hzPathDelta
  have hzNeEnd :
      (⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ :
        rect 0 (2 * n) (-n) n) ≠ z.1 := by
    intro h
    apply hzSafe
    have hval := congrArg Subtype.val h
    simpa using hval ▸ hgammaEnd
  have hgammaEndPath : (gamma.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩,
      gamma.1.2.2.1.end_mem_support, rfl⟩
  have hgammaTopDelta : (gamma.1.2.1 : Site 2) ∈
      rlc_strictTopSet delta := by
    rcases hgammaEnd with htopGamma | htopDelta
    · exact False.elim ((Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path gamma)) htopGamma hgammaEndPath)
    · exact htopDelta
  let pg := gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma
  have hpg : ¬ pg.Nil := SimpleGraph.Walk.not_nil_of_ne hzNeEnd
  have hpgPath : pg.IsPath :=
    gamma.1.2.2.2.reverse.takeUntil hzGamma
  have hzNotDrop : z.1 ∉ pg.dropLast.support := by
    have hn := hpgPath.support_nodup
    rw [← pg.support_dropLast_concat hpg] at hn
    have hd : List.Disjoint pg.dropLast.support [z.1] :=
      List.disjoint_of_nodup_append hn
    intro hz
    exact (List.disjoint_left.mp hd) hz (by simp)
  have hAvoid : ∀ q ∈ pg.dropLast.support,
      (q : Site 2) ∉ rlc_pathVertices delta.1 := by
    intro q hq hqDeltaPath
    have hqPg : q ∈ pg.support := by
      rw [← pg.support_dropLast_concat hpg]
      exact List.mem_append_left _ hq
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hqDeltaPath
    obtain ⟨u, huDelta, huq⟩ := hqDeltaPath
    have hueq : u = q := by
      apply Subtype.ext
      exact huq
    subst u
    have hqz := rlc_min_gamma_reverse_rightCommon_prefix_inter_only
      gamma delta z hzGamma hmin hqPg huDelta
    exact hzNotDrop (hqz ▸ hq)
  have hTop : ∀ q ∈ pg.dropLast.support,
      (q : Site 2) ∈ rlc_strictTopSet delta := by
    intro q hq
    exact (rlc_strictTopSet_mem_iff_rectWalk_start_of_avoids
      delta pg.dropLast hAvoid hq).mpr hgammaTopDelta
  exact ⟨z, hzGamma, hpg, hAvoid, hTop⟩

lemma rlc_last_delta_terminal_suffix_top_of_unsafe_end {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    (hdeltaEnd : (delta.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ (z : ↑(rlc_rightCommonSupport delta gamma))
      (hzDelta : z.1 ∈ delta.1.2.2.1.reverse.support),
      let pd := delta.1.2.2.1.reverse.takeUntil z.1 hzDelta
      ¬ pd.Nil ∧
        (∀ q ∈ pd.dropLast.support,
          (q : Site 2) ∉ rlc_pathVertices gamma.1) ∧
        (∀ q ∈ pd.dropLast.support,
          (q : Site 2) ∈ rlc_strictTopSet gamma) := by
  apply rlc_last_gamma_terminal_suffix_top_of_unsafe_end delta gamma
  · exact fun h => hinter h.symm
  · simpa [rlc_rightUpperUnionSet, Set.union_comm] using hdeltaEnd

lemma rlc_last_common_reaches_safe_gamma_endpoint {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    (hgammaEnd : (gamma.1.2.1 : Site 2) ∉
      rlc_rightUpperUnionSet gamma delta) :
    ∃ z : ↑(rlc_rightCommonSupport gamma delta),
      (rlc_rightSafeTraceGraph gamma delta).Reachable z.1
        ⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ := by
  classical
  obtain ⟨z, hmin⟩ :=
    rlc_exists_min_gamma_reverse_rightCommonSupport gamma delta hinter
  have hzBoth := Finset.mem_inter.mp z.2
  have hzGammaOrig : z.1 ∈ gamma.1.2.2.1.support := by
    simpa [rlc_rightCommonSupport] using hzBoth.1
  have hzDeltaOrig : z.1 ∈ delta.1.2.2.1.support := by
    simpa [rlc_rightCommonSupport] using hzBoth.2
  have hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hzGammaOrig
  let y : rect 0 (2 * n) (-n) n :=
    ⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩
  by_cases hyz : y = z.1
  · exact ⟨z, hyz ▸ SimpleGraph.Reachable.refl y⟩
  let pg := gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma
  have hpg : ¬ pg.Nil := SimpleGraph.Walk.not_nil_of_ne hyz
  have hpgPath : pg.IsPath := gamma.1.2.2.2.reverse.takeUntil hzGamma
  have hzNotDrop : z.1 ∉ pg.dropLast.support := by
    have hn := hpgPath.support_nodup
    rw [← pg.support_dropLast_concat hpg] at hn
    have hd : List.Disjoint pg.dropLast.support [z.1] :=
      List.disjoint_of_nodup_append hn
    intro hz
    exact (List.disjoint_left.mp hd) hz (by simp)
  have hAvoid : ∀ q ∈ pg.dropLast.support,
      (q : Site 2) ∉ rlc_pathVertices delta.1 := by
    intro q hq hqDeltaPath
    have hqPg : q ∈ pg.support := by
      rw [← pg.support_dropLast_concat hpg]
      exact List.mem_append_left _ hq
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hqDeltaPath
    obtain ⟨u, huDelta, huq⟩ := hqDeltaPath
    have hueq : u = q := by
      apply Subtype.ext
      exact huq
    subst u
    have hqz := rlc_min_gamma_reverse_rightCommon_prefix_inter_only
      gamma delta z hzGamma hmin hqPg huDelta
    exact hzNotDrop (hqz ▸ hq)
  have hEndNotTopDelta : (gamma.1.2.1 : Site 2) ∉
      rlc_strictTopSet delta := fun h => hgammaEnd (Or.inr h)
  have hSupportSafe : ∀ q ∈ pg.support,
      (q : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
    intro q hq
    have hqGammaRev : q ∈ gamma.1.2.2.1.reverse.support :=
      gamma.1.2.2.1.reverse.support_takeUntil_subset_support hzGamma hq
    have hqGammaOrig : q ∈ gamma.1.2.2.1.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hqGammaRev
    have hqPathGamma : (q : Site 2) ∈ rlc_pathVertices gamma.1 := by
      simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
      exact ⟨q, hqGammaOrig, rfl⟩
    intro hupper
    rcases hupper with htopGamma | htopDelta
    · exact (Set.disjoint_left.mp (rlc_strictTopSet_disjoint_path gamma))
        htopGamma hqPathGamma
    · by_cases hqz : q = z.1
      · subst q
        have hzPathDelta : (z.1 : Site 2) ∈
            rlc_pathVertices delta.1 := by
          simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
          exact ⟨z.1, hzDeltaOrig, rfl⟩
        exact (Set.disjoint_left.mp (rlc_strictTopSet_disjoint_path delta))
          htopDelta hzPathDelta
      · have hqDrop : q ∈ pg.dropLast.support := by
          have hq' := hq
          rw [← pg.support_dropLast_concat hpg] at hq'
          simp only [List.mem_append, List.mem_singleton] at hq'
          exact hq'.resolve_right hqz
        have hiff := rlc_strictTopSet_mem_iff_rectWalk_start_of_avoids
          delta pg.dropLast hAvoid hqDrop
        exact hEndNotTopDelta (hiff.mp htopDelta)
  have pSafe : (rlc_rightSafeTraceGraph gamma delta).Walk y z.1 := by
    apply pg.transfer (rlc_rightSafeTraceGraph gamma delta)
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have heRev : s(u, v) ∈ gamma.1.2.2.1.reverse.edges :=
          gamma.1.2.2.1.reverse.edges_takeUntil_subset_edges hzGamma he
        have heOrig : s(u, v) ∈ gamma.1.2.2.1.edges := by
          simpa [SimpleGraph.Walk.edges_reverse] using heRev
        have hePath : s((u : Site 2), (v : Site 2)) ∈
            rlc_pathEdges gamma.1 := by
          simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
          exact ⟨s(u, v), heOrig, rfl⟩
        exact rlc_rightSafeTraceGraph_adj_of_pathEdge gamma delta
          (Finset.mem_union_left _ hePath)
          (hSupportSafe u (pg.fst_mem_support_of_mem_edges he))
          (hSupportSafe v (pg.snd_mem_support_of_mem_edges he))
  exact ⟨z, ⟨pSafe.reverse⟩⟩

lemma rlc_last_common_reaches_safe_delta_endpoint {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    (hdeltaEnd : (delta.1.2.1 : Site 2) ∉
      rlc_rightUpperUnionSet gamma delta) :
    ∃ z : ↑(rlc_rightCommonSupport delta gamma),
      (rlc_rightSafeTraceGraph gamma delta).Reachable z.1
        ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩ := by
  obtain ⟨z, hz⟩ := rlc_last_common_reaches_safe_gamma_endpoint
    delta gamma (fun h => hinter h.symm)
      (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hdeltaEnd)
  refine ⟨z, ?_⟩
  simpa [rlc_rightSafeTraceGraph, rlc_rightUpperUnionSet,
    Finset.union_comm, Set.union_comm] using hz

/-- Any two common sites of two right diagonal paths are joined in their safe trace graph. -/
def RlcRightCommonSafeConnectivity (n : ℤ) : Prop :=
  ∀ (gamma delta : RlcRightDiagonalPath n)
    (u v : ↑(rlc_rightCommonSupport gamma delta)),
    (rlc_rightSafeTraceGraph gamma delta).Reachable u.1 v.1

lemma rlc_rightSafeTraceReachability_of_commonSafeConnectivity {n : ℤ}
    (hn : 0 < n) (hcommon : RlcRightCommonSafeConnectivity n) :
    RlcRightSafeTraceReachability n := by
  classical
  intro gamma delta
  have finish_from_common : ∀ u : ↑(rlc_rightCommonSupport gamma delta),
      ∃ y : rightSide 0 (2 * n) (-n) n,
        (y : Site 2) ∈ rlc_upperHalf ∧
        (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
        (rlc_rightSafeTraceGraph gamma delta).Reachable u.1
          ⟨y, rightSide_subset y.2⟩ := by
    intro u
    have hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
        (rlc_pathVertices delta.1) := by
      intro hdisj
      have huBoth : u.1 ∈ gamma.1.2.2.1.support.toFinset ∧
          u.1 ∈ delta.1.2.2.1.support.toFinset := by
        exact Finset.mem_inter.mp (by
          simpa [rlc_rightCommonSupport] using u.2)
      have huGamma : (u.1 : Site 2) ∈ rlc_pathVertices gamma.1 := by
        simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        exact ⟨u.1, by simpa using huBoth.1, rfl⟩
      have huDelta : (u.1 : Site 2) ∈ rlc_pathVertices delta.1 := by
        simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        exact ⟨u.1, by simpa using huBoth.2, rfl⟩
      exact (Finset.disjoint_left.mp hdisj) huGamma huDelta
    rcases rlc_exists_safe_right_endpoint hn gamma delta with hgamma | hdelta
    · obtain ⟨v, hv⟩ := rlc_last_common_reaches_safe_gamma_endpoint
        gamma delta hinter hgamma
      exact ⟨gamma.1.2.1, gamma.2.2, hgamma,
        (hcommon gamma delta u v).trans hv⟩
    · obtain ⟨v, hv⟩ := rlc_last_common_reaches_safe_delta_endpoint
        gamma delta hinter hdelta
      have hvMem : v.1 ∈ rlc_rightCommonSupport gamma delta := by
        simpa [rlc_rightCommonSupport, Finset.inter_comm] using v.2
      let v' : ↑(rlc_rightCommonSupport gamma delta) := ⟨v.1, hvMem⟩
      exact ⟨delta.1.2.1, delta.2.2, hdelta,
        (hcommon gamma delta u v').trans (by simpa [v'] using hv)⟩
  obtain ⟨x, hxHalf, hxUnion, hxSafe⟩ :=
    rlc_exists_safe_left_trace_anchor hn gamma delta
  let xs : rect 0 (2 * n) (-n) n := ⟨x, leftSide_subset x.2⟩
  rcases Finset.mem_union.mp hxUnion with hxGamma | hxDelta
  · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hxGamma
    obtain ⟨xg, hxg, hxgEq⟩ := hxGamma
    have hxgSub : xg = xs := by
      apply Subtype.ext
      exact hxgEq
    subst xg
    rcases rlc_safe_vertex_reaches_endpoint_or_common
        gamma delta hxg hxSafe with hEnd | hSwitch
    · have hEndSafe := rlc_rightSafeTraceGraph_reachable_dest_safe
        gamma delta hxSafe hEnd
      exact ⟨x, gamma.1.2.1, hxHalf, gamma.2.2,
        hxSafe, hEndSafe, hEnd⟩
    · obtain ⟨u, huGamma, huDelta, hxu⟩ := hSwitch
      simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        at huGamma huDelta
      obtain ⟨ug, hug, hugEq⟩ := huGamma
      obtain ⟨ud, hud, hudEq⟩ := huDelta
      have hugSub : ug = u := by apply Subtype.ext; exact hugEq
      have hudSub : ud = u := by apply Subtype.ext; exact hudEq
      subst ug
      subst ud
      have huMem : u ∈ rlc_rightCommonSupport gamma delta := by
        simp [rlc_rightCommonSupport, hug, hud]
      let us : ↑(rlc_rightCommonSupport gamma delta) := ⟨u, huMem⟩
      obtain ⟨y, hyHalf, hySafe, huy⟩ := finish_from_common us
      exact ⟨x, y, hxHalf, hyHalf, hxSafe, hySafe,
        hxu.trans (by simpa [us] using huy)⟩
  · simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hxDelta
    obtain ⟨xd, hxd, hxdEq⟩ := hxDelta
    have hxdSub : xd = xs := by
      apply Subtype.ext
      exact hxdEq
    subst xd
    rcases rlc_safe_vertex_reaches_endpoint_or_common
        delta gamma hxd
          (by simpa [rlc_rightUpperUnionSet, Set.union_comm] using hxSafe) with
      hEnd | hSwitch
    · have hEnd' : (rlc_rightSafeTraceGraph gamma delta).Reachable xs
          ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩ := by
        simpa [rlc_rightSafeTraceGraph, rlc_rightUpperUnionSet,
          Finset.union_comm, Set.union_comm] using hEnd
      have hEndSafe := rlc_rightSafeTraceGraph_reachable_dest_safe
        gamma delta hxSafe hEnd'
      exact ⟨x, delta.1.2.1, hxHalf, delta.2.2,
        hxSafe, hEndSafe, hEnd'⟩
    · obtain ⟨u, huDelta, huGamma, hxu⟩ := hSwitch
      have hxu' : (rlc_rightSafeTraceGraph gamma delta).Reachable xs u := by
        simpa [rlc_rightSafeTraceGraph, rlc_rightUpperUnionSet,
          Finset.union_comm, Set.union_comm] using hxu
      simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
        at huGamma huDelta
      obtain ⟨ug, hug, hugEq⟩ := huGamma
      obtain ⟨ud, hud, hudEq⟩ := huDelta
      have hugSub : ug = u := by apply Subtype.ext; exact hugEq
      have hudSub : ud = u := by apply Subtype.ext; exact hudEq
      subst ug
      subst ud
      have huMem : u ∈ rlc_rightCommonSupport gamma delta := by
        simp [rlc_rightCommonSupport, hug, hud]
      let us : ↑(rlc_rightCommonSupport gamma delta) := ⟨u, huMem⟩
      obtain ⟨y, hyHalf, hySafe, huy⟩ := finish_from_common us
      exact ⟨x, y, hxHalf, hyHalf, hxSafe, hySafe,
        hxu'.trans (by simpa [us] using huy)⟩

/-- The lowest left-side trace site is joined in the safe trace graph to an upper-right site. -/
def RlcRightCanonicalAnchorReachability (n : ℤ) : Prop :=
  ∀ gamma delta : RlcRightDiagonalPath n,
    ∃ y : rightSide 0 (2 * n) (-n) n,
      (y : Site 2) ∈ rlc_upperHalf ∧
      (y : Site 2) ∉ rlc_rightUpperUnionSet gamma delta ∧
      (rlc_rightSafeTraceGraph gamma delta).Reachable
        ⟨rlc_rightLeftTraceMinSide gamma delta,
          leftSide_subset (rlc_rightLeftTraceMinSide gamma delta).2⟩
        ⟨y, rightSide_subset y.2⟩

lemma rlc_rightSafeTraceReachability_of_canonicalAnchor {n : ℤ}
    (hn : 0 < n) (hanchor : RlcRightCanonicalAnchorReachability n) :
    RlcRightSafeTraceReachability n := by
  intro gamma delta
  let x := rlc_rightLeftTraceMinSide gamma delta
  obtain ⟨y, hyHalf, hySafe, hxy⟩ := hanchor gamma delta
  refine ⟨x, y, ?_, hyHalf, ?_, hySafe, hxy⟩
  · simpa [x] using rlc_rightLeftTraceMinVertex_lowerHalf gamma delta
  · simpa [x] using
      rlc_rightLeftTraceMinVertex_not_upperUnion hn gamma delta

lemma rlc_exists_min_reverse_rightCommonSupport {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1)) :
    ∃ z : ↑(rlc_rightCommonSupport gamma delta),
      ∀ q : ↑(rlc_rightCommonSupport gamma delta),
        rlc_rightCommonReverseRank gamma delta z ≤
          rlc_rightCommonReverseRank gamma delta q := by
  classical
  have hne := rlc_rightCommonSupport_nonempty_of_not_disjoint
    gamma delta hinter
  let : Nonempty ↑(rlc_rightCommonSupport gamma delta) :=
    ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have huniv : (Finset.univ :
      Finset ↑(rlc_rightCommonSupport gamma delta)).Nonempty :=
    ⟨⟨hne.choose, hne.choose_spec⟩, Finset.mem_univ _⟩
  obtain ⟨z, _hz, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset ↑(rlc_rightCommonSupport gamma delta))
    (rlc_rightCommonReverseRank gamma delta) huniv
  exact ⟨z, fun q => hmin q (by simp)⟩

lemma rlc_min_reverse_rightCommon_prefixes_inter_only {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (z : ↑(rlc_rightCommonSupport gamma delta))
    (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support)
    (hzDelta : z.1 ∈ delta.1.2.2.1.reverse.support)
    (hmin : ∀ q : ↑(rlc_rightCommonSupport gamma delta),
      rlc_rightCommonReverseRank gamma delta z ≤
        rlc_rightCommonReverseRank gamma delta q)
    {q : rect 0 (2 * n) (-n) n}
    (hqGamma : q ∈
      (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).support)
    (hqDelta : q ∈
      (delta.1.2.2.1.reverse.takeUntil z.1 hzDelta).support) :
    q = z.1 := by
  classical
  by_contra hqz
  have hqGammaFull : q ∈ gamma.1.2.2.1.reverse.support :=
    gamma.1.2.2.1.reverse.support_takeUntil_subset_support hzGamma hqGamma
  have hqDeltaFull : q ∈ delta.1.2.2.1.reverse.support :=
    delta.1.2.2.1.reverse.support_takeUntil_subset_support hzDelta hqDelta
  have hqCommon : q ∈ rlc_rightCommonSupport gamma delta := by
    have hqGammaOrig : q ∈ gamma.1.2.2.1.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hqGammaFull
    have hqDeltaOrig : q ∈ delta.1.2.2.1.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hqDeltaFull
    simp [rlc_rightCommonSupport, hqGammaOrig, hqDeltaOrig]
  let qs : ↑(rlc_rightCommonSupport gamma delta) := ⟨q, hqCommon⟩
  have hgammaLt :
      (gamma.1.2.2.1.reverse.takeUntil q hqGammaFull).length <
        (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).length := by
    have hlen :=
      (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).length_takeUntil_lt_length
        hqGamma hqz
    rwa [gamma.1.2.2.1.reverse.takeUntil_takeUntil hzGamma hqGamma] at hlen
  have hdeltaLt :
      (delta.1.2.2.1.reverse.takeUntil q hqDeltaFull).length <
        (delta.1.2.2.1.reverse.takeUntil z.1 hzDelta).length := by
    have hlen :=
      (delta.1.2.2.1.reverse.takeUntil z.1 hzDelta).length_takeUntil_lt_length
        hqDelta hqz
    rwa [delta.1.2.2.1.reverse.takeUntil_takeUntil hzDelta hqDelta] at hlen
  have hrankLt : rlc_rightCommonReverseRank gamma delta qs <
      rlc_rightCommonReverseRank gamma delta z := by
    change (gamma.1.2.2.1.reverse.takeUntil q hqGammaFull).length +
        (delta.1.2.2.1.reverse.takeUntil q hqDeltaFull).length <
      (gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma).length +
        (delta.1.2.2.1.reverse.takeUntil z.1 hzDelta).length
    omega
  exact (not_lt_of_ge (hmin qs)) hrankLt

lemma rlc_terminal_lens_of_unsafe_ends {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    (hgammaEnd : (gamma.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta)
    (hdeltaEnd : (delta.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ z : ↑(rlc_rightCommonSupport gamma delta),
      ∃ (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support)
        (hzDelta : z.1 ∈ delta.1.2.2.1.reverse.support),
      (z.1 : Site 2) ≠ (gamma.1.2.1 : Site 2) ∧
      (z.1 : Site 2) ≠ (delta.1.2.1 : Site 2) ∧
      ∀ q : rect 0 (2 * n) (-n) n,
        q ∈ (gamma.1.2.2.1.reverse.takeUntil z.1
          hzGamma).support →
        q ∈ (delta.1.2.2.1.reverse.takeUntil z.1
          hzDelta).support →
        q = z.1 := by
  classical
  obtain ⟨z, hmin⟩ :=
    rlc_exists_min_reverse_rightCommonSupport gamma delta hinter
  have hzBoth := Finset.mem_inter.mp z.2
  have hzGamma : z.1 ∈ gamma.1.2.2.1.support := by
    simpa [rlc_rightCommonSupport] using hzBoth.1
  have hzDelta : z.1 ∈ delta.1.2.2.1.support := by
    simpa [rlc_rightCommonSupport] using hzBoth.2
  have hzGammaRev : z.1 ∈ gamma.1.2.2.1.reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hzGamma
  have hzDeltaRev : z.1 ∈ delta.1.2.2.1.reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hzDelta
  have hzPathGamma : (z.1 : Site 2) ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨z.1, hzGamma, rfl⟩
  have hzPathDelta : (z.1 : Site 2) ∈ rlc_pathVertices delta.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨z.1, hzDelta, rfl⟩
  have hzSafe := rlc_commonRightPathVertex_not_upperUnion
    gamma delta hzPathGamma hzPathDelta
  have hzNeGamma : (z.1 : Site 2) ≠ (gamma.1.2.1 : Site 2) := by
    intro h
    apply hzSafe
    rwa [h]
  have hzNeDelta : (z.1 : Site 2) ≠ (delta.1.2.1 : Site 2) := by
    intro h
    apply hzSafe
    rwa [h]
  refine ⟨z, hzGammaRev, hzDeltaRev, hzNeGamma, hzNeDelta, ?_⟩
  intro q hqGamma hqDelta
  exact rlc_min_reverse_rightCommon_prefixes_inter_only gamma delta z
    hzGammaRev hzDeltaRev hmin hqGamma hqDelta

lemma rlc_lens_penultimate_ne {V : Type*} {G : SimpleGraph V}
    {a b z : V} (p : G.Walk a z) (q : G.Walk b z)
    (ha : a ≠ z) (hb : b ≠ z)
    (hinter : ∀ u : V, u ∈ p.support → u ∈ q.support → u = z) :
    p.penultimate ≠ q.penultimate := by
  have hp : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne ha
  have hq : ¬ q.Nil := SimpleGraph.Walk.not_nil_of_ne hb
  intro heq
  have hpMem : p.penultimate ∈ p.support := p.getVert_mem_support _
  have hqMem : p.penultimate ∈ q.support := by
    rw [heq]
    exact q.getVert_mem_support _
  have hpz : p.penultimate = z := hinter p.penultimate hpMem hqMem
  exact (p.adj_penultimate hp).ne hpz

lemma rlc_terminal_lens_distinct_branches_of_unsafe_ends {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    (hinter : ¬ Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1))
    (hgammaEnd : (gamma.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta)
    (hdeltaEnd : (delta.1.2.1 : Site 2) ∈
      rlc_rightUpperUnionSet gamma delta) :
    ∃ (z : ↑(rlc_rightCommonSupport gamma delta))
      (hzGamma : z.1 ∈ gamma.1.2.2.1.reverse.support)
      (hzDelta : z.1 ∈ delta.1.2.2.1.reverse.support),
      let pg := gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma
      let pd := delta.1.2.2.1.reverse.takeUntil z.1 hzDelta
      ¬ pg.Nil ∧ ¬ pd.Nil ∧
        ((hypercubicLattice 2).induce
          (rect 0 (2 * n) (-n) n)).Adj pg.penultimate z.1 ∧
        ((hypercubicLattice 2).induce
          (rect 0 (2 * n) (-n) n)).Adj pd.penultimate z.1 ∧
        pg.penultimate ≠ pd.penultimate := by
  obtain ⟨z, hzGamma, hzDelta, hzNeGamma, hzNeDelta, hOnly⟩ :=
    rlc_terminal_lens_of_unsafe_ends gamma delta hinter
      hgammaEnd hdeltaEnd
  let pg := gamma.1.2.2.1.reverse.takeUntil z.1 hzGamma
  let pd := delta.1.2.2.1.reverse.takeUntil z.1 hzDelta
  have hpgStart :
      (⟨gamma.1.2.1, rightSide_subset gamma.1.2.1.2⟩ :
        rect 0 (2 * n) (-n) n) ≠ z.1 := by
    intro h
    apply hzNeGamma
    exact congrArg Subtype.val h.symm
  have hpdStart :
      (⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩ :
        rect 0 (2 * n) (-n) n) ≠ z.1 := by
    intro h
    apply hzNeDelta
    exact congrArg Subtype.val h.symm
  have hpg : ¬ pg.Nil := SimpleGraph.Walk.not_nil_of_ne hpgStart
  have hpd : ¬ pd.Nil := SimpleGraph.Walk.not_nil_of_ne hpdStart
  have hbranches : pg.penultimate ≠ pd.penultimate :=
    rlc_lens_penultimate_ne pg pd hpgStart hpdStart hOnly
  exact ⟨z, hzGamma, hzDelta, hpg, hpd,
    pg.adj_penultimate hpg, pd.adj_penultimate hpd, hbranches⟩

lemma rlc_rightSafeTraceReachability_of_intersecting {n : ℤ} (hn : 0 < n)
    (hinter : RlcRightIntersectingSafeTraceReachability n) :
    RlcRightSafeTraceReachability n := by
  intro gamma delta
  by_cases hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices delta.1)
  · exact rlc_rightSafeTraceReachable_of_disjoint hn gamma delta hdisj
  · exact hinter gamma delta hdisj

lemma rlc_rightSafeTraceGraph_walk_support_safe {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n)
    {x y : rect 0 (2 * n) (-n) n}
    (w : (rlc_rightSafeTraceGraph gamma delta).Walk x y)
    (hx : (x : Site 2) ∉ rlc_rightUpperUnionSet gamma delta)
    {z : rect 0 (2 * n) (-n) n} (hz : z ∈ w.support) :
    (z : Site 2) ∉ rlc_rightUpperUnionSet gamma delta := by
  induction w with
  | nil =>
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      exact hz ▸ hx
  | @cons a b c hab w ih =>
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hab.2.2.1
      · exact ih hab.2.2.2 hz

/-- The safe trace graph of two left diagonal paths. -/
def rlc_leftSafeTraceGraph {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n) :
    SimpleGraph (rect (-2 * n) 0 (-n) n) where
  Adj u v :=
    ((hypercubicLattice 2).induce (rect (-2 * n) 0 (-n) n)).Adj u v ∧
      s((u : Site 2), (v : Site 2)) ∈
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1 ∧
      (u : Site 2) ∉ rlc_leftLowerUnionSet gamma delta ∧
      (v : Site 2) ∉ rlc_leftLowerUnionSet gamma delta
  symm := by
    refine ⟨?_⟩
    intro u v h
    exact ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2.1,
      h.2.2.2, h.2.2.1⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- The safe-trace reachability property for left diagonal paths. -/
def RlcLeftSafeTraceReachability (n : ℤ) : Prop :=
  ∀ gamma delta : RlcLeftDiagonalPath n,
    ∃ (x : leftSide (-2 * n) 0 (-n) n)
      (y : rightSide (-2 * n) 0 (-n) n),
      (x : Site 2) ∈ rlc_lowerHalf ∧
      (y : Site 2) ∈ rlc_upperHalf ∧
      (x : Site 2) ∉ rlc_leftLowerUnionSet gamma delta ∧
      (y : Site 2) ∉ rlc_leftLowerUnionSet gamma delta ∧
      (rlc_leftSafeTraceGraph gamma delta).Reachable
        ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩

lemma rlc_leftSafeTraceGraph_walk_support_safe {n : ℤ}
    (gamma delta : RlcLeftDiagonalPath n)
    {x y : rect (-2 * n) 0 (-n) n}
    (w : (rlc_leftSafeTraceGraph gamma delta).Walk x y)
    (hx : (x : Site 2) ∉ rlc_leftLowerUnionSet gamma delta)
    {z : rect (-2 * n) 0 (-n) n} (hz : z ∈ w.support) :
    (z : Site 2) ∉ rlc_leftLowerUnionSet gamma delta := by
  induction w with
  | nil =>
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      exact hz ▸ hx
  | @cons a b c hab w ih =>
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hab.2.2.1
      · exact ih hab.2.2.2 hz

/-- For every two right diagonal paths there is a third using only their edges whose explored region
  lies in both explored regions. -/
def RlcRightEnvelopeProperty (n : ℤ) : Prop :=
  ∀ gamma delta : RlcRightDiagonalPath n,
    ∃ lambda : RlcRightDiagonalPath n,
      rlc_pathEdges lambda.1 ⊆
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1 ∧
        rlc_rightExploredVertices lambda ⊆
          rlc_rightExploredVertices gamma ∩
            rlc_rightExploredVertices delta

/-- The envelope property for left diagonal paths. -/
def RlcLeftEnvelopeProperty (n : ℤ) : Prop :=
  ∀ gamma delta : RlcLeftDiagonalPath n,
    ∃ lambda : RlcLeftDiagonalPath n,
      rlc_pathEdges lambda.1 ⊆
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1 ∧
        rlc_leftExploredVertices lambda ⊆
          rlc_leftExploredVertices gamma ∩
            rlc_leftExploredVertices delta

/-- For every two right diagonal paths there is a third using only their edges that avoids both
  strict upper regions. -/
def RlcRightFrontierPathProperty (n : ℤ) : Prop :=
  ∀ gamma delta : RlcRightDiagonalPath n,
    ∃ lambda : RlcRightDiagonalPath n,
      rlc_pathEdges lambda.1 ⊆
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1 ∧
        Disjoint (rlc_strictTopSet gamma ∪ rlc_strictTopSet delta)
          (rlc_pathVertices lambda.1 : Set (Site 2))

/-- The frontier-path property for left diagonal paths. -/
def RlcLeftFrontierPathProperty (n : ℤ) : Prop :=
  ∀ gamma delta : RlcLeftDiagonalPath n,
    ∃ lambda : RlcLeftDiagonalPath n,
      rlc_pathEdges lambda.1 ⊆
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges delta.1 ∧
        Disjoint (rlc_strictBottomSet gamma ∪ rlc_strictBottomSet delta)
          (rlc_pathVertices lambda.1 : Set (Site 2))

lemma rlc_rightSafeTraceReachability_of_frontierPathProperty {n : ℤ}
    (hfrontier : RlcRightFrontierPathProperty n) :
    RlcRightSafeTraceReachability n := by
  intro gamma delta
  obtain ⟨lambda, hedges, hsafe⟩ := hfrontier gamma delta
  exact rlc_rightSafeTraceReachable_of_path_safe
    gamma delta lambda hedges hsafe

lemma rlc_rightFrontierPathProperty_of_safeTraceReachability {n : ℤ}
    (hsafe : RlcRightSafeTraceReachability n) :
    RlcRightFrontierPathProperty n := by
  classical
  intro gamma delta
  obtain ⟨x, y, hxHalf, hyHalf, hxSafe, _hySafe, hreach⟩ :=
    hsafe gamma delta
  let q := hreach.some.toPath
  have hle : rlc_rightSafeTraceGraph gamma delta ≤
      (hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n) :=
    fun _ _ h => h.1
  let qRect : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Walk
      ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ :=
    q.1.mapLe hle
  have hqRect : qRect.IsPath := by
    exact (SimpleGraph.Walk.isPath_mapLe hle).mpr q.2
  let lambda0 : RlcCrossingPath 0 (2 * n) (-n) n :=
    ⟨x, y, ⟨qRect, hqRect⟩⟩
  let lambda : RlcRightDiagonalPath n :=
    ⟨lambda0, hxHalf, hyHalf⟩
  refine ⟨lambda, ?_, ?_⟩
  · intro e he
    simp only [rlc_pathEdges, lambda, lambda0, Finset.mem_image,
      List.mem_toFinset] at he
    obtain ⟨e0, he0, rfl⟩ := he
    have heq : e0 ∈ q.1.edges := by
      rw [← SimpleGraph.Walk.edges_mapLe_eq_edges hle q.1]
      exact he0
    induction e0 using Sym2.inductionOn with
    | _ u v =>
        exact (q.1.adj_of_mem_edges heq).2.1
  · rw [Set.disjoint_left]
    intro z hzUpper hzPath
    change z ∈ qRect.support.toFinset.image Subtype.val at hzPath
    rw [Finset.mem_image] at hzPath
    obtain ⟨u, hu, huz⟩ := hzPath
    have hu' : u ∈ qRect.support := by simpa using hu
    have huq : u ∈ q.1.support := by
      simpa [qRect, SimpleGraph.Walk.support_mapLe_eq_support] using hu'
    have huSafe := rlc_rightSafeTraceGraph_walk_support_safe
      gamma delta q.1 hxSafe huq
    exact huSafe (huz ▸ hzUpper)

lemma rlc_rightSafeTraceReachability_iff_frontierPathProperty {n : ℤ} :
    RlcRightSafeTraceReachability n ↔ RlcRightFrontierPathProperty n := by
  constructor
  · exact rlc_rightFrontierPathProperty_of_safeTraceReachability
  · exact rlc_rightSafeTraceReachability_of_frontierPathProperty

lemma rlc_leftFrontierPathProperty_of_safeTraceReachability {n : ℤ}
    (hsafe : RlcLeftSafeTraceReachability n) :
    RlcLeftFrontierPathProperty n := by
  classical
  intro gamma delta
  obtain ⟨x, y, hxHalf, hyHalf, hxSafe, _hySafe, hreach⟩ :=
    hsafe gamma delta
  let q := hreach.some.toPath
  have hle : rlc_leftSafeTraceGraph gamma delta ≤
      (hypercubicLattice 2).induce (rect (-2 * n) 0 (-n) n) :=
    fun _ _ h => h.1
  let qRect : ((hypercubicLattice 2).induce
      (rect (-2 * n) 0 (-n) n)).Walk
      ⟨x, leftSide_subset x.2⟩ ⟨y, rightSide_subset y.2⟩ :=
    q.1.mapLe hle
  have hqRect : qRect.IsPath := by
    exact (SimpleGraph.Walk.isPath_mapLe hle).mpr q.2
  let lambda0 : RlcCrossingPath (-2 * n) 0 (-n) n :=
    ⟨x, y, ⟨qRect, hqRect⟩⟩
  let lambda : RlcLeftDiagonalPath n :=
    ⟨lambda0, hxHalf, hyHalf⟩
  refine ⟨lambda, ?_, ?_⟩
  · intro e he
    simp only [rlc_pathEdges, lambda, lambda0, Finset.mem_image,
      List.mem_toFinset] at he
    obtain ⟨e0, he0, rfl⟩ := he
    have heq : e0 ∈ q.1.edges := by
      rw [← SimpleGraph.Walk.edges_mapLe_eq_edges hle q.1]
      exact he0
    induction e0 using Sym2.inductionOn with
    | _ u v =>
        exact (q.1.adj_of_mem_edges heq).2.1
  · rw [Set.disjoint_left]
    intro z hzLower hzPath
    change z ∈ qRect.support.toFinset.image Subtype.val at hzPath
    rw [Finset.mem_image] at hzPath
    obtain ⟨u, hu, huz⟩ := hzPath
    have hu' : u ∈ qRect.support := by simpa using hu
    have huq : u ∈ q.1.support := by
      simpa [qRect, SimpleGraph.Walk.support_mapLe_eq_support] using hu'
    have huSafe := rlc_leftSafeTraceGraph_walk_support_safe
      gamma delta q.1 hxSafe huq
    exact huSafe (huz ▸ hzLower)

lemma rlc_leftFrontierPathProperty_of_right {n : ℤ}
    (hright : RlcRightFrontierPathProperty n) :
    RlcLeftFrontierPathProperty n := by
  classical
  intro gamma delta
  let gammaR := rlc_rot180LeftPath gamma
  let deltaR := rlc_rot180LeftPath delta
  obtain ⟨lambdaR, hedges, hdisj⟩ := hright gammaR deltaR
  let lambda := rlc_rot180RightPath lambdaR
  refine ⟨lambda, ?_, ?_⟩
  · dsimp only [lambda]
    rw [rlc_pathEdges_rot180RightPath]
    intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he
    have heInput := hedges he0
    rw [Finset.mem_union] at heInput
    rcases heInput with heGamma | heDelta
    · dsimp only [gammaR] at heGamma
      rw [rlc_pathEdges_rot180LeftPath] at heGamma
      obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp heGamma
      have hback := congrArg (Sym2.map rlc_rot180) hae
      have : Sym2.map rlc_rot180 e0 = a := by simpa using hback.symm
      exact Finset.mem_union_left _ (this ▸ ha)
    · dsimp only [deltaR] at heDelta
      rw [rlc_pathEdges_rot180LeftPath] at heDelta
      obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp heDelta
      have hback := congrArg (Sym2.map rlc_rot180) hae
      have : Sym2.map rlc_rot180 e0 = a := by simpa using hback.symm
      exact Finset.mem_union_right _ (this ▸ ha)
  · rw [Set.disjoint_left]
    intro z hzLower hzPath
    dsimp only [lambda] at hzPath
    rw [rlc_pathVertices_rot180RightPath] at hzPath
    change z ∈ (rlc_pathVertices lambdaR.1).image rlc_rot180 at hzPath
    rw [Finset.mem_image] at hzPath
    obtain ⟨a, ha, haz⟩ := hzPath
    have hza : rlc_rot180 z = a := by
      apply rlc_rot180.injective
      simpa using haz.symm
    apply (Set.disjoint_left.mp hdisj) ?_ (hza ▸ ha)
    rcases hzLower with hzGamma | hzDelta
    · left
      exact (rlc_rot180_mem_strictTop_iff_mem_strictBottom gamma z).mpr hzGamma
    · right
      exact (rlc_rot180_mem_strictTop_iff_mem_strictBottom delta z).mpr hzDelta

lemma rlc_rightEnvelopeProperty_of_frontierPath {n : ℤ}
    (hfrontier : RlcRightFrontierPathProperty n) :
    RlcRightEnvelopeProperty n := by
  intro gamma delta
  obtain ⟨lambda, hedges, hdisj⟩ := hfrontier gamma delta
  refine ⟨lambda, hedges, ?_⟩
  have hdisjGamma : Disjoint (rlc_strictTopSet gamma)
      (rlc_pathVertices lambda.1 : Set (Site 2)) := by
    rw [Set.disjoint_left]
    intro z hz hzp
    exact (Set.disjoint_left.mp hdisj) (Or.inl hz) hzp
  have hdisjDelta : Disjoint (rlc_strictTopSet delta)
      (rlc_pathVertices lambda.1 : Set (Site 2)) := by
    rw [Set.disjoint_left]
    intro z hz hzp
    exact (Set.disjoint_left.mp hdisj) (Or.inr hz) hzp
  have htopGamma : rlc_strictTopSet gamma ⊆ rlc_strictTopSet lambda :=
    rlc_strictTopSet_mono_of_disjoint_path gamma lambda hdisjGamma
  have htopDelta : rlc_strictTopSet delta ⊆ rlc_strictTopSet lambda :=
    rlc_strictTopSet_mono_of_disjoint_path delta lambda hdisjDelta
  intro z hz
  rw [Finset.mem_inter]
  rw [rlc_rightExploredVertices, Finset.mem_sdiff] at hz
  constructor
  · rw [rlc_rightExploredVertices, Finset.mem_sdiff]
    refine ⟨hz.1, ?_⟩
    intro hzTop
    exact hz.2 (by
      simpa using htopGamma (by simpa using hzTop))
  · rw [rlc_rightExploredVertices, Finset.mem_sdiff]
    refine ⟨hz.1, ?_⟩
    intro hzTop
    exact hz.2 (by
      simpa using htopDelta (by simpa using hzTop))

lemma rlc_leftEnvelopeProperty_of_frontierPath {n : ℤ}
    (hfrontier : RlcLeftFrontierPathProperty n) :
    RlcLeftEnvelopeProperty n := by
  intro gamma delta
  obtain ⟨lambda, hedges, hdisj⟩ := hfrontier gamma delta
  refine ⟨lambda, hedges, ?_⟩
  have hdisjGamma : Disjoint (rlc_strictBottomSet gamma)
      (rlc_pathVertices lambda.1 : Set (Site 2)) := by
    rw [Set.disjoint_left]
    intro z hz hzp
    exact (Set.disjoint_left.mp hdisj) (Or.inl hz) hzp
  have hdisjDelta : Disjoint (rlc_strictBottomSet delta)
      (rlc_pathVertices lambda.1 : Set (Site 2)) := by
    rw [Set.disjoint_left]
    intro z hz hzp
    exact (Set.disjoint_left.mp hdisj) (Or.inr hz) hzp
  have hbottomGamma : rlc_strictBottomSet gamma ⊆
      rlc_strictBottomSet lambda :=
    rlc_strictBottomSet_mono_of_disjoint_path gamma lambda hdisjGamma
  have hbottomDelta : rlc_strictBottomSet delta ⊆
      rlc_strictBottomSet lambda :=
    rlc_strictBottomSet_mono_of_disjoint_path delta lambda hdisjDelta
  intro z hz
  rw [Finset.mem_inter]
  rw [rlc_leftExploredVertices, Finset.mem_sdiff] at hz
  constructor
  · rw [rlc_leftExploredVertices, Finset.mem_sdiff]
    refine ⟨hz.1, ?_⟩
    intro hzBottom
    exact hz.2 (by
      simpa using hbottomGamma (by simpa using hzBottom))
  · rw [rlc_leftExploredVertices, Finset.mem_sdiff]
    refine ⟨hz.1, ?_⟩
    intro hzBottom
    exact hz.2 (by
      simpa using hbottomDelta (by simpa using hzBottom))

lemma rlc_envelopeProperties_of_rightSafeTraceReachability {n : ℤ}
    (hsafe : RlcRightSafeTraceReachability n) :
    RlcRightEnvelopeProperty n ∧ RlcLeftEnvelopeProperty n := by
  have hright : RlcRightFrontierPathProperty n :=
    rlc_rightFrontierPathProperty_of_safeTraceReachability hsafe
  have hleft : RlcLeftFrontierPathProperty n :=
    rlc_leftFrontierPathProperty_of_right hright
  exact ⟨rlc_rightEnvelopeProperty_of_frontierPath hright,
    rlc_leftEnvelopeProperty_of_frontierPath hleft⟩

lemma rlc_pathOpen_of_edges_subset_union {a b c d : ℤ}
    (lambda gamma delta : RlcCrossingPath a b c d)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hedges : rlc_pathEdges lambda ⊆
      rlc_pathEdges gamma ∪ rlc_pathEdges delta)
    (hgamma : omega ∈ rlc_pathOpen gamma)
    (hdelta : omega ∈ rlc_pathOpen delta) :
    omega ∈ rlc_pathOpen lambda := by
  intro e he
  rcases Finset.mem_union.mp (hedges he) with he | he
  · exact hgamma e he
  · exact hdelta e he

lemma rlc_rightLowestCandidate_pairwiseDisjoint {n : ℤ}
    (henv : RlcRightEnvelopeProperty n) :
    Pairwise (Disjoint on fun gamma : RlcRightDiagonalPath n =>
      rlc_rightLowestCandidate gamma) := by
  intro gamma delta hne
  change Disjoint (rlc_rightLowestCandidate gamma)
    (rlc_rightLowestCandidate delta)
  rw [Set.disjoint_left]
  intro omega hgamma hdelta
  obtain ⟨lambda, hedges, hregion⟩ := henv gamma delta
  have hlambda : omega ∈ rlc_pathOpen lambda.1 :=
    rlc_pathOpen_of_edges_subset_union lambda.1 gamma.1 delta.1 hedges
      hgamma.1 hdelta.1
  have hLG : rlc_rightExploredVertices lambda ⊆
      rlc_rightExploredVertices gamma := fun z hz =>
    (Finset.mem_inter.mp (hregion hz)).1
  have hLD : rlc_rightExploredVertices lambda ⊆
      rlc_rightExploredVertices delta := fun z hz =>
    (Finset.mem_inter.mp (hregion hz)).2
  by_cases hEqLG : rlc_rightExploredVertices lambda =
      rlc_rightExploredVertices gamma
  · have hGD : rlc_rightExploredVertices gamma ⊆
        rlc_rightExploredVertices delta := by
      intro z hz
      exact hLD (hEqLG.symm ▸ hz)
    by_cases hEqGD : rlc_rightExploredVertices gamma =
        rlc_rightExploredVertices delta
    · have hindex : rlc_rightPathIndex gamma ≠
          rlc_rightPathIndex delta := by
        intro hidx
        apply hne
        apply (Fintype.equivFin (RlcRightDiagonalPath n)).injective
        apply Fin.ext
        exact hidx
      rcases lt_or_gt_of_ne hindex with hlt | hgt
      · exact (rlc_rightLowestCandidate_not_open_of_below hdelta
          (Or.inr ⟨hEqGD, hlt⟩)) hgamma.1
      · exact (rlc_rightLowestCandidate_not_open_of_below hgamma
          (Or.inr ⟨hEqGD.symm, hgt⟩)) hdelta.1
    · have hstrict : rlc_rightExploredVertices gamma ⊂
          rlc_rightExploredVertices delta :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hGD, hEqGD⟩
      exact (rlc_rightLowestCandidate_not_open_of_below hdelta
        (Or.inl hstrict)) hgamma.1
  · have hstrict : rlc_rightExploredVertices lambda ⊂
        rlc_rightExploredVertices gamma :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hLG, hEqLG⟩
    exact (rlc_rightLowestCandidate_not_open_of_below hgamma
      (Or.inl hstrict)) hlambda

lemma rlc_leftHighestCandidate_pairwiseDisjoint {n : ℤ}
    (henv : RlcLeftEnvelopeProperty n) :
    Pairwise (Disjoint on fun gamma : RlcLeftDiagonalPath n =>
      rlc_leftHighestCandidate gamma) := by
  intro gamma delta hne
  change Disjoint (rlc_leftHighestCandidate gamma)
    (rlc_leftHighestCandidate delta)
  rw [Set.disjoint_left]
  intro omega hgamma hdelta
  obtain ⟨lambda, hedges, hregion⟩ := henv gamma delta
  have hlambda : omega ∈ rlc_pathOpen lambda.1 :=
    rlc_pathOpen_of_edges_subset_union lambda.1 gamma.1 delta.1 hedges
      hgamma.1 hdelta.1
  have hLG : rlc_leftExploredVertices lambda ⊆
      rlc_leftExploredVertices gamma := fun z hz =>
    (Finset.mem_inter.mp (hregion hz)).1
  have hLD : rlc_leftExploredVertices lambda ⊆
      rlc_leftExploredVertices delta := fun z hz =>
    (Finset.mem_inter.mp (hregion hz)).2
  by_cases hEqLG : rlc_leftExploredVertices lambda =
      rlc_leftExploredVertices gamma
  · have hGD : rlc_leftExploredVertices gamma ⊆
        rlc_leftExploredVertices delta := by
      intro z hz
      exact hLD (hEqLG.symm ▸ hz)
    by_cases hEqGD : rlc_leftExploredVertices gamma =
        rlc_leftExploredVertices delta
    · have hindex : rlc_leftPathIndex gamma ≠
          rlc_leftPathIndex delta := by
        intro hidx
        apply hne
        apply (Fintype.equivFin (RlcLeftDiagonalPath n)).injective
        apply Fin.ext
        exact hidx
      rcases lt_or_gt_of_ne hindex with hlt | hgt
      · exact (rlc_leftHighestCandidate_not_open_of_above hdelta
          (Or.inr ⟨hEqGD, hlt⟩)) hgamma.1
      · exact (rlc_leftHighestCandidate_not_open_of_above hgamma
          (Or.inr ⟨hEqGD.symm, hgt⟩)) hdelta.1
    · have hstrict : rlc_leftExploredVertices gamma ⊂
          rlc_leftExploredVertices delta :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hGD, hEqGD⟩
      exact (rlc_leftHighestCandidate_not_open_of_above hdelta
        (Or.inl hstrict)) hgamma.1
  · have hstrict : rlc_leftExploredVertices lambda ⊂
        rlc_leftExploredVertices gamma :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hLG, hEqLG⟩
    exact (rlc_leftHighestCandidate_not_open_of_above hgamma
      (Or.inl hstrict)) hlambda

lemma rlc_extremalPairCandidate_pairwiseDisjoint {n : ℤ}
    (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n) :
    Pairwise (Disjoint on fun pair : RlcDiagonalPathPair n =>
      rlc_extremalPairCandidate pair) := by
  intro pair pair' hne
  by_cases hrightEq : pair.1 = pair'.1
  · have hleftNe : pair.2 ≠ pair'.2 := fun h =>
      hne (Prod.ext hrightEq h)
    exact (rlc_leftHighestCandidate_pairwiseDisjoint hleft hleftNe).mono
      inter_subset_right inter_subset_right
  · exact (rlc_rightLowestCandidate_pairwiseDisjoint hright hrightEq).mono
      inter_subset_left inter_subset_left

/-! ## F. Connectors across the axis -/

/-- Reflection in the vertical axis: `(x, y) ↦ (-x, y)`. -/
def rlc_flipXFun (x : Site 2) : Site 2 := ![-x 0, x 1]

/-- Reflection in the vertical axis, as an equivalence of sites. -/
def rlc_flipX : Site 2 ≃ Site 2 where
  toFun := rlc_flipXFun
  invFun := rlc_flipXFun
  left_inv x := by funext i; fin_cases i <;> simp [rlc_flipXFun]
  right_inv x := by funext i; fin_cases i <;> simp [rlc_flipXFun]

@[simp] lemma rlc_flipX_involutive (x : Site 2) : rlc_flipX (rlc_flipX x) = x := by
  funext i
  fin_cases i <;> simp [rlc_flipX, rlc_flipXFun]

lemma rlc_flipX_eq_self_of_zero {x : Site 2} (hx : x 0 = 0) :
    rlc_flipX x = x := by
  funext i
  fin_cases i <;> simp [rlc_flipX, rlc_flipXFun, hx]

/-- The heights at which a set of sites meets the vertical axis `x = 0`. -/
noncomputable def rlc_axisHeights (P : Finset (Site 2)) : Finset ℤ :=
  (P.filter fun z => z 0 = 0).image fun z => z 1

@[simp] lemma rlc_mem_axisHeights_iff (P : Finset (Site 2)) (t : ℤ) :
    t ∈ rlc_axisHeights P ↔ ![0, t] ∈ P := by
  classical
  constructor
  · intro ht
    obtain ⟨z, hz, hzt⟩ := Finset.mem_image.mp ht
    have hz0 : z 0 = 0 := (Finset.mem_filter.mp hz).2
    have hz1 : z 1 = t := hzt
    have : z = ![0, t] := by
      funext i
      fin_cases i <;> simp [hz0, hz1]
    simpa [this] using (Finset.mem_filter.mp hz).1
  · intro ht
    apply Finset.mem_image.mpr
    exact ⟨![0, t], by simp [ht], by simp⟩

lemma rlc_exists_finset_gap (A B : Finset ℤ) {x y : ℤ}
    (hx : x ∈ A) (hy : y ∈ B) (hxy : x < y) :
    ∃ a b : ℤ, a ∈ A ∧ b ∈ B ∧ x ≤ a ∧ a < b ∧
      b ≤ y ∧ ∀ t : ℤ, a < t → t < b → t ∉ A ∧ t ∉ B := by
  classical
  let Bup := B.filter fun t => x < t
  have hBup : Bup.Nonempty := ⟨y, by simp [Bup, hy, hxy]⟩
  let b := Bup.min' hBup
  have hbBup : b ∈ Bup := Bup.min'_mem hBup
  have hbB : b ∈ B := (Finset.mem_filter.mp hbBup).1
  have hxb : x < b := (Finset.mem_filter.mp hbBup).2
  have hby : b ≤ y := Bup.min'_le y (by simp [Bup, hy, hxy])
  let Adown := A.filter fun t => t < b
  have hAdown : Adown.Nonempty := ⟨x, by simp [Adown, hx, hxb]⟩
  let a := Adown.max' hAdown
  have haAdown : a ∈ Adown := Adown.max'_mem hAdown
  have haA : a ∈ A := (Finset.mem_filter.mp haAdown).1
  have hab : a < b := (Finset.mem_filter.mp haAdown).2
  have hxa : x ≤ a := Adown.le_max' x (by simp [Adown, hx, hxb])
  refine ⟨a, b, haA, hbB, hxa, hab, hby, ?_⟩
  intro t hat htb
  constructor
  · intro htA
    have htAdown : t ∈ Adown := by simp [Adown, htA, htb]
    exact (not_lt_of_ge (Adown.le_max' t htAdown)) hat
  · intro htB
    have hxt : x < t := lt_of_le_of_lt hxa hat
    have htBup : t ∈ Bup := by simp [Bup, htB, hxt]
    exact (not_lt_of_ge (Bup.min'_le t htBup)) htb

/-- The sites of the two diagonal paths and of their reflections in the vertical axis. -/
noncomputable def rlc_connectorBarrier {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Site 2) :=
  rlc_pathVertices gamma.1 ∪ rlc_pathVertices gamma'.1 ∪
    (rlc_pathVertices gamma.1).image rlc_flipX ∪
    (rlc_pathVertices gamma'.1).image rlc_flipX

lemma rlc_axis_mem_connectorBarrier_iff {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (t : ℤ) :
    ![0, t] ∈ rlc_connectorBarrier gamma gamma' ↔
      ![0, t] ∈ rlc_pathVertices gamma.1 ∨
      ![0, t] ∈ rlc_pathVertices gamma'.1 := by
  classical
  let z : Site 2 := ![0, t]
  have hz : rlc_flipX z = z := rlc_flipX_eq_self_of_zero (by simp [z])
  have himage (P : Finset (Site 2)) : z ∈ P.image rlc_flipX ↔ z ∈ P := by
    constructor
    · intro h
      obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp h
      have : w = z := by
        calc
          w = rlc_flipX (rlc_flipX w) := (rlc_flipX_involutive w).symm
          _ = rlc_flipX z := congrArg rlc_flipX hwz
          _ = z := hz
      simpa [this] using hw
    · intro h
      exact Finset.mem_image.mpr ⟨z, h, hz⟩
  change z ∈ rlc_connectorBarrier gamma gamma' ↔ _
  simp only [rlc_connectorBarrier, Finset.mem_union, himage]
  tauto

/-- The box `[-2n, 2n] × [-n, n]`, as a `Finset`. -/
noncomputable def rlc_connectorBox (n : ℤ) : Finset (Site 2) :=
  (rect_finite (-2 * n) (2 * n) (-n) n).toFinset

/-- The sites of the connector box not on the connector barrier. -/
noncomputable def rlc_connectorAllowed {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Site 2) :=
  rlc_connectorBox n \ rlc_connectorBarrier gamma gamma'

/-- The allowed sites reachable from the origin inside the allowed region. -/
def rlc_connectorOriginRegionSet {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (Site 2) :=
  {z | ∃ (hz : z ∈ rlc_connectorAllowed gamma gamma')
      (ho : origin 2 ∈ rlc_connectorAllowed gamma gamma'),
    ((hypercubicLattice 2).induce
      (rlc_connectorAllowed gamma gamma' : Set (Site 2))).Reachable
      ⟨origin 2, ho⟩ ⟨z, hz⟩}

lemma rlc_connectorOriginRegionSet_finite {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (rlc_connectorOriginRegionSet gamma gamma').Finite := by
  apply (rlc_connectorAllowed gamma gamma').finite_toSet.subset
  rintro z ⟨hz, _ho, _hreach⟩
  exact hz

/-- The origin region of the connector, as a `Finset`. -/
noncomputable def rlc_connectorOriginRegion {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Site 2) :=
  (rlc_connectorOriginRegionSet_finite gamma gamma').toFinset

/-- The edges with both endpoints in the origin region of the connector. -/
noncomputable def rlc_connectorEdges {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  (edgesWithinFinset (rlc_connectorBox n)).filter fun e =>
    ∃ z ∈ rlc_connectorOriginRegion gamma gamma', z ∈ e

/-- The configuration `omega` restricted to the edge set `U` (edges outside `U` closed). -/
noncomputable def rlc_maskConfig (U : Finset (Sym2 (Site 2)))
    (omega : ConfigSpace (Sym2 (Site 2))) : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if e ∈ U then omega e else false

lemma rlc_maskConfig_congr {U : Finset (Sym2 (Site 2))}
    {omega omega' : ConfigSpace (Sym2 (Site 2))}
    (h : ∀ e ∈ (U : Set (Sym2 (Site 2))), omega e = omega' e) :
    rlc_maskConfig U omega = rlc_maskConfig U omega' := by
  funext e
  by_cases he : e ∈ U
  · simp only [rlc_maskConfig, ite_eq_left he]
    exact h e he
  · simp [rlc_maskConfig, he]

lemma rlc_maskConfig_mono (U : Finset (Sym2 (Site 2)))
    {omega omega' : ConfigSpace (Sym2 (Site 2))} (h : omega ≤ omega') :
    rlc_maskConfig U omega ≤ rlc_maskConfig U omega' := by
  intro e
  by_cases he : e ∈ U <;> simp [rlc_maskConfig, he, h e]

/-- The event that the two diagonal paths are joined inside the connector box using only connector
  edges. -/
def rlc_connectorEvent {n : ℤ}
  (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ rlc_pathVertices gamma.1,
    ∃ y ∈ rlc_pathVertices gamma'.1,
    ∃ (hxR : x ∈ rect (-2 * n) (2 * n) (-n) n)
      (hyR : y ∈ rect (-2 * n) (2 * n) (-n) n),
      ConnectedWithin 2
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
        (rect (-2 * n) (2 * n) (-n) n) ⟨x, hxR⟩ ⟨y, hyR⟩}

lemma rlc_connectorEvent_dependsOn {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DependsOn ((rlc_connectorEvent gamma gamma').indicator (fun _ => (1 : ℝ)))
      (rlc_connectorEdges gamma gamma' : Set (Sym2 (Site 2))) := by
  intro omega omega' hagree
  have hmask : rlc_maskConfig (rlc_connectorEdges gamma gamma') omega =
      rlc_maskConfig (rlc_connectorEdges gamma gamma') omega' :=
    rlc_maskConfig_congr hagree
  have hevent : omega ∈ rlc_connectorEvent gamma gamma' ↔
      omega' ∈ rlc_connectorEvent gamma gamma' := by
    simp only [rlc_connectorEvent, Set.mem_ofPred_eq, hmask]
  by_cases hmem : omega ∈ rlc_connectorEvent gamma gamma'
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]

lemma rlc_connectorEvent_measurableSet {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    MeasurableSet (rlc_connectorEvent gamma gamma') :=
  measurableSet_of_dependsOn (rlc_connectorEvent_dependsOn gamma gamma')

lemma rlc_maskConfig_le (U : Finset (Sym2 (Site 2)))
    (omega : ConfigSpace (Sym2 (Site 2))) : rlc_maskConfig U omega ≤ omega := by
  intro e
  by_cases he : e ∈ U
  · simp [rlc_maskConfig, he]
  · simp [rlc_maskConfig, he]

lemma rlc_pathOpen_connected_start {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hopen : omega ∈ rlc_pathOpen gamma)
    {z : Site 2} (hz : z ∈ rlc_pathVertices gamma) :
    ∃ hzR : z ∈ rect a b c d,
      ConnectedWithin 2 omega (rect a b c d)
        ⟨(gamma.1 : Site 2), leftSide_subset gamma.1.2⟩ ⟨z, hzR⟩ := by
  classical
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset] at hz
  obtain ⟨zs, hzs, rfl⟩ := hz
  let q := gamma.2.2.1.takeUntil zs hzs
  have hqopen : ∀ e ∈ q.edges.toFinset.image (Sym2.map Subtype.val),
      omega e = true := by
    intro e he
    simp only [Finset.mem_image, List.mem_toFinset] at he
    obtain ⟨e0, he0, rfl⟩ := he
    apply hopen
    simp only [rlc_pathEdges, Finset.mem_image, List.mem_toFinset]
    exact ⟨e0, gamma.2.2.1.edges_takeUntil_subset_edges hzs he0, rfl⟩
  exact ⟨zs.2, ⟨rlc_openWalkOfEdges omega q hqopen⟩⟩

lemma rlc_pathOpen_connected_finish {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hopen : omega ∈ rlc_pathOpen gamma)
    {z : Site 2} (hz : z ∈ rlc_pathVertices gamma) :
    ∃ hzR : z ∈ rect a b c d,
      ConnectedWithin 2 omega (rect a b c d) ⟨z, hzR⟩
        ⟨(gamma.2.1 : Site 2), rightSide_subset gamma.2.1.2⟩ := by
  obtain ⟨hzR, hstart⟩ := rlc_pathOpen_connected_start gamma omega hopen hz
  have hfull : ConnectedWithin 2 omega (rect a b c d)
      ⟨(gamma.1 : Site 2), leftSide_subset gamma.1.2⟩
      ⟨(gamma.2.1 : Site 2), rightSide_subset gamma.2.1.2⟩ := by
    refine ⟨rlc_openWalkOfEdges omega gamma.2.2.1 ?_⟩
    intro e he
    exact hopen e (by simpa only [rlc_pathEdges] using he)
  exact ⟨hzR, hstart.symm.trans hfull⟩

lemma rlc_connector_glues_horizontal (n : ℤ) (_hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩
        rlc_connectorEvent gamma gamma' ⊆
      horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
  intro omega homega
  obtain ⟨⟨hgamma, hgamma'⟩, hconn⟩ := homega
  obtain ⟨x, hxg, y, hyg, hxR, hyR, hxyMask⟩ := hconn
  obtain ⟨_hxSmall, hxToRightSmall⟩ :=
    rlc_pathOpen_connected_finish gamma.1 omega hgamma hxg
  obtain ⟨_hySmall, hleftToYSmall⟩ :=
    rlc_pathOpen_connected_start gamma'.1 omega hgamma' hyg
  have hrightSub : rect 0 (2 * n) (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hleftSub : rect (-2 * n) 0 (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hxToRight := StatMech.Lattice.connectedWithin_mono_set omega
    hrightSub hxToRightSmall
  have hleftToY := StatMech.Lattice.connectedWithin_mono_set omega
    hleftSub hleftToYSmall
  have hxy : ConnectedWithin 2 omega (rect (-2 * n) (2 * n) (-n) n)
      ⟨x, hxR⟩ ⟨y, hyR⟩ :=
    StatMech.TwoDim.connectedWithin_mono
      (rlc_maskConfig_le (rlc_connectorEdges gamma gamma') omega) hxyMask
  let xL : leftSide (-2 * n) (2 * n) (-n) n :=
    ⟨gamma'.1.1, by
      rw [mem_leftSide, mem_rect]
      have h := gamma'.1.1.2
      rw [mem_leftSide, mem_rect] at h
      exact ⟨⟨by omega, by omega, h.1.2.2.1, h.1.2.2.2⟩, h.2⟩⟩
  let yR : rightSide (-2 * n) (2 * n) (-n) n :=
    ⟨gamma.1.2.1, by
      rw [mem_rightSide, mem_rect]
      have h := gamma.1.2.1.2
      rw [mem_rightSide, mem_rect] at h
      exact ⟨⟨by omega, by omega, h.1.2.2.1, h.1.2.2.2⟩, h.2⟩⟩
  refine ⟨xL, yR, ?_⟩
  exact hleftToY.trans (hxy.symm.trans hxToRight)

lemma rlc_originRegion_not_barrier {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {z : Site 2} (hz : z ∈ rlc_connectorOriginRegion gamma gamma') :
    z ∉ rlc_connectorBarrier gamma gamma' := by
  have hzset : z ∈ rlc_connectorOriginRegionSet gamma gamma' := by
    simpa [rlc_connectorOriginRegion] using hz
  obtain ⟨hzAllowed, _ho, _hreach⟩ := hzset
  exact (Finset.mem_sdiff.mp hzAllowed).2

lemma rlc_rightPathEdges_disjoint_connector {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Disjoint (rlc_pathEdges gamma.1) (rlc_connectorEdges gamma gamma') := by
  rw [Finset.disjoint_left]
  intro e hePath heConnector
  simp only [rlc_connectorEdges, Finset.mem_filter] at heConnector
  obtain ⟨_zbox, z, hzRegion, hze⟩ := heConnector
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hePath
    rw [Sym2.mem_iff] at hze
    rcases hze with rfl | rfl
    · exact rlc_originRegion_not_barrier hzRegion (by
        simp [rlc_connectorBarrier, hends.1])
    · exact rlc_originRegion_not_barrier hzRegion (by
        simp [rlc_connectorBarrier, hends.2])

lemma rlc_leftPathEdges_disjoint_connector {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Disjoint (rlc_pathEdges gamma'.1) (rlc_connectorEdges gamma gamma') := by
  rw [Finset.disjoint_left]
  intro e hePath heConnector
  simp only [rlc_connectorEdges, Finset.mem_filter] at heConnector
  obtain ⟨_zbox, z, hzRegion, hze⟩ := heConnector
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hePath
    rw [Sym2.mem_iff] at hze
    rcases hze with rfl | rfl
    · exact rlc_originRegion_not_barrier hzRegion (by
        simp [rlc_connectorBarrier, hends.1])
    · exact rlc_originRegion_not_barrier hzRegion (by
        simp [rlc_connectorBarrier, hends.2])

lemma rlc_rightPathVertex_mem_connectorBox {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1) :
    z ∈ rect (-2 * n) (2 * n) (-n) n := by
  have hzsmall := rlc_pathVertex_mem_rect gamma.1 hz
  rw [mem_rect] at hzsmall ⊢
  omega

lemma rlc_leftPathVertex_mem_connectorBox {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1) :
    z ∈ rect (-2 * n) (2 * n) (-n) n := by
  have hzsmall := rlc_pathVertex_mem_rect gamma.1 hz
  rw [mem_rect] at hzsmall ⊢
  omega

lemma rlc_mem_connectorEvent_of_common_vertex {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1)
    (hz' : z ∈ rlc_pathVertices gamma'.1) :
    omega ∈ rlc_connectorEvent gamma gamma' := by
  let hzR := rlc_rightPathVertex_mem_connectorBox gamma hz
  let hzR' := rlc_leftPathVertex_mem_connectorBox gamma' hz'
  refine ⟨z, hz, z, hz', hzR, hzR', ?_⟩
  simpa only using
    (connectedWithin_refl
      (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
      (rect (-2 * n) (2 * n) (-n) n) ⟨z, hzR⟩)

lemma rlc_pathVertices_disjoint_of_not_connector {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  exact hno (rlc_mem_connectorEvent_of_common_vertex gamma gamma' omega hz hz')

lemma rlc_axis_endpoints_strict_of_disjoint {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    (gamma.1.1 : Site 2) 1 < (gamma'.1.2.1 : Site 2) 1 := by
  let x : Site 2 := gamma.1.1
  let y : Site 2 := gamma'.1.2.1
  have hxPath : x ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨x, by simpa [x] using leftSide_subset gamma.1.1.2⟩,
      gamma.1.2.2.1.start_mem_support, rfl⟩
  have hyPath : y ∈ rlc_pathVertices gamma'.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨y, by simpa [y] using rightSide_subset gamma'.1.2.1.2⟩,
      gamma'.1.2.2.1.end_mem_support, rfl⟩
  have hxy : x ≠ y := by
    intro h
    exact (Finset.disjoint_left.mp
      hdisj) hxPath (by simpa [h] using hyPath)
  have hx0 : x 0 = 0 := by simpa only [x] using gamma.1.1.2.2
  have hy0 : y 0 = 0 := by simpa only [y] using gamma'.1.2.1.2.2
  have hxy1 : x 1 ≠ y 1 := by
    intro h1
    apply hxy
    funext i
    fin_cases i
    · exact hx0.trans hy0.symm
    · exact h1
  have hxLower : x 1 ≤ 0 := gamma.2.1
  have hyUpper : 0 ≤ y 1 := gamma'.2.2
  change x 1 < y 1
  omega

lemma rlc_axis_endpoints_strict_of_not_connector {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    (gamma.1.1 : Site 2) 1 < (gamma'.1.2.1 : Site 2) 1 :=
  rlc_axis_endpoints_strict_of_disjoint gamma gamma'
    (rlc_pathVertices_disjoint_of_not_connector gamma gamma' omega hno)

lemma rlc_exists_axis_barrier_gap_of_disjoint {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    ∃ a b : ℤ,
      a ∈ rlc_axisHeights (rlc_pathVertices gamma.1) ∧
      b ∈ rlc_axisHeights (rlc_pathVertices gamma'.1) ∧
      (gamma.1.1 : Site 2) 1 ≤ a ∧ a < b ∧
      b ≤ (gamma'.1.2.1 : Site 2) 1 ∧
      ∀ t : ℤ, a < t → t < b →
        ![0, t] ∉ rlc_connectorBarrier gamma gamma' := by
  let x : Site 2 := gamma.1.1
  let y : Site 2 := gamma'.1.2.1
  have hxPath : x ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨x, by simpa [x] using leftSide_subset gamma.1.1.2⟩,
      gamma.1.2.2.1.start_mem_support, rfl⟩
  have hyPath : y ∈ rlc_pathVertices gamma'.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨y, by simpa [y] using rightSide_subset gamma'.1.2.1.2⟩,
      gamma'.1.2.2.1.end_mem_support, rfl⟩
  have hx0 : x 0 = 0 := by simpa only [x] using gamma.1.1.2.2
  have hy0 : y 0 = 0 := by simpa only [y] using gamma'.1.2.1.2.2
  have hxAxis : x 1 ∈ rlc_axisHeights (rlc_pathVertices gamma.1) := by
    rw [rlc_mem_axisHeights_iff]
    have hvec : ![0, x 1] = x := by
      funext i
      fin_cases i <;> simp [hx0]
    simpa [hvec] using hxPath
  have hyAxis : y 1 ∈ rlc_axisHeights (rlc_pathVertices gamma'.1) := by
    rw [rlc_mem_axisHeights_iff]
    have hvec : ![0, y 1] = y := by
      funext i
      fin_cases i <;> simp [hy0]
    simpa [hvec] using hyPath
  have hxy : x 1 < y 1 := by
    simpa only [x, y] using
      rlc_axis_endpoints_strict_of_disjoint gamma gamma' hdisj
  obtain ⟨a, b, ha, hb, hxa, hab, hby, hgap⟩ :=
    rlc_exists_finset_gap
      (rlc_axisHeights (rlc_pathVertices gamma.1))
      (rlc_axisHeights (rlc_pathVertices gamma'.1)) hxAxis hyAxis hxy
  refine ⟨a, b, ha, hb, hxa, hab, hby, ?_⟩
  intro t hat htb hbarrier
  obtain ⟨htA, htB⟩ := hgap t hat htb
  rw [rlc_axis_mem_connectorBarrier_iff] at hbarrier
  rcases hbarrier with hbarrier | hbarrier
  · exact htA ((rlc_mem_axisHeights_iff _ _).2 hbarrier)
  · exact htB ((rlc_mem_axisHeights_iff _ _).2 hbarrier)

/-- A gap on the vertical axis between a height met by the right path and a higher height met by the
  left path, with no path site strictly in between. -/
structure RlcAxisBarrierGap {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) where
  lower : ℤ
  upper : ℤ
  lower_mem : lower ∈ rlc_axisHeights (rlc_pathVertices gamma.1)
  upper_mem : upper ∈ rlc_axisHeights (rlc_pathVertices gamma'.1)
  start_le : (gamma.1.1 : Site 2) 1 ≤ lower
  lower_lt_upper : lower < upper
  upper_le_finish : upper ≤ (gamma'.1.2.1 : Site 2) 1
  interior_free : ∀ t : ℤ, lower < t → t < upper →
    ![0, t] ∉ rlc_connectorBarrier gamma gamma'

lemma rlc_axisBarrierGap_nonempty_of_disjoint {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    Nonempty (RlcAxisBarrierGap gamma gamma') := by
  obtain ⟨a, b, ha, hb, hstart, hab, hfinish, hfree⟩ :=
    rlc_exists_axis_barrier_gap_of_disjoint gamma gamma' hdisj
  exact ⟨⟨a, b, ha, hb, hstart, hab, hfinish, hfree⟩⟩

/-- An axis barrier gap of the two paths, if one exists. -/
noncomputable def rlc_axisBarrierGap? {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Option (RlcAxisBarrierGap gamma gamma') :=
  if hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1) then
    some (Classical.choice (rlc_axisBarrierGap_nonempty_of_disjoint gamma gamma' hdisj))
  else none

lemma rlc_axisBarrierGap?_eq_some_of_disjoint {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    ∃ G : RlcAxisBarrierGap gamma gamma', rlc_axisBarrierGap? gamma gamma' = some G := by
  refine ⟨Classical.choice
    (rlc_axisBarrierGap_nonempty_of_disjoint gamma gamma' hdisj), ?_⟩
  simp [rlc_axisBarrierGap?, hdisj]

lemma rlc_axisBarrierGap?_eq_none_of_not_disjoint {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdisj : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    rlc_axisBarrierGap? gamma gamma' = none := by
  simp [rlc_axisBarrierGap?, hdisj]

/-- The site of the right path on the axis at the lower gap height. -/
def RlcAxisBarrierGap.lowerVertex {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') : Site 2 := ![0, G.lower]

/-- The site just above the lower gap vertex: the seed of the gap region. -/
def RlcAxisBarrierGap.seedVertex {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') : Site 2 := ![0, G.lower + 1]

/-- The site of the left path on the axis at the upper gap height. -/
def RlcAxisBarrierGap.upperVertex {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') : Site 2 := ![0, G.upper]

/-- The vertical edge from the lower gap vertex to the seed vertex. -/
def RlcAxisBarrierGap.firstEdge {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') : Sym2 (Site 2) :=
  s(G.lowerVertex, G.seedVertex)

lemma RlcAxisBarrierGap.lowerVertex_mem_right {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    G.lowerVertex ∈ rlc_pathVertices gamma.1 := by
  simpa [RlcAxisBarrierGap.lowerVertex] using
    (rlc_mem_axisHeights_iff (rlc_pathVertices gamma.1) G.lower).mp G.lower_mem

lemma RlcAxisBarrierGap.upperVertex_mem_left {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    G.upperVertex ∈ rlc_pathVertices gamma'.1 := by
  simpa [RlcAxisBarrierGap.upperVertex] using
    (rlc_mem_axisHeights_iff (rlc_pathVertices gamma'.1) G.upper).mp G.upper_mem

lemma RlcAxisBarrierGap.seedVertex_not_barrier_of_lt {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (h : G.lower + 1 < G.upper) :
    G.seedVertex ∉ rlc_connectorBarrier gamma gamma' := by
  exact G.interior_free (G.lower + 1) (by omega) h

lemma RlcAxisBarrierGap.seedVertex_mem_box_of_lt {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (h : G.lower + 1 < G.upper) :
    G.seedVertex ∈ rlc_connectorBox n := by
  have hstart := leftSide_subset gamma.1.1.2
  have hfinish := rightSide_subset gamma'.1.2.1.2
  rw [mem_rect] at hstart hfinish
  have hlower : -n ≤ G.lower := le_trans hstart.2.2.1 G.start_le
  have hupper : G.upper ≤ n := le_trans G.upper_le_finish hfinish.2.2.2
  simp only [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect,
    RlcAxisBarrierGap.seedVertex, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

lemma RlcAxisBarrierGap.seedVertex_mem_allowed_of_lt {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (h : G.lower + 1 < G.upper) :
    G.seedVertex ∈ rlc_connectorAllowed gamma gamma' := by
  rw [rlc_connectorAllowed, Finset.mem_sdiff]
  exact ⟨G.seedVertex_mem_box_of_lt hn h, G.seedVertex_not_barrier_of_lt h⟩

lemma RlcAxisBarrierGap.firstEdge_lattice {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    G.firstEdge ∈ (hypercubicLattice 2).edgeSet := by
  change s(G.lowerVertex, G.seedVertex) ∈ (hypercubicLattice 2).edgeSet
  rw [SimpleGraph.mem_edgeSet]
  simp [RlcAxisBarrierGap.lowerVertex, RlcAxisBarrierGap.seedVertex,
    hypercubicLattice_adj, Fin.sum_univ_two]

/-- The allowed sites reachable from the seed vertex of an axis gap. -/
def rlc_axisGapRegionSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') : Set (Site 2) :=
  {z | ∃ (hz : z ∈ rlc_connectorAllowed gamma gamma')
      (hs : G.seedVertex ∈ rlc_connectorAllowed gamma gamma'),
    ((hypercubicLattice 2).induce
      (rlc_connectorAllowed gamma gamma' : Set (Site 2))).Reachable
      ⟨G.seedVertex, hs⟩ ⟨z, hz⟩}

lemma rlc_axisGapRegionSet_finite {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    (rlc_axisGapRegionSet G).Finite := by
  apply (rlc_connectorAllowed gamma gamma').finite_toSet.subset
  rintro z ⟨hz, _hs, _hreach⟩
  exact hz

/-- The region of an axis gap, as a `Finset`. -/
noncomputable def rlc_axisGapRegion {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') : Finset (Site 2) :=
  (rlc_axisGapRegionSet_finite G).toFinset

lemma RlcAxisBarrierGap.seedVertex_mem_region_of_lt {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (h : G.lower + 1 < G.upper) :
    G.seedVertex ∈ rlc_axisGapRegion G := by
  have hs := G.seedVertex_mem_allowed_of_lt hn h
  have hsSet : G.seedVertex ∈ rlc_axisGapRegionSet G :=
    ⟨hs, hs, SimpleGraph.Reachable.refl _⟩
  simpa [rlc_axisGapRegion] using hsSet

lemma RlcAxisBarrierGap.axisVertex_mem_region_of_between {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n) {t : ℤ}
    (hlower : G.lower < t) (hupper : t < G.upper) :
    ![0, t] ∈ rlc_axisGapRegion G := by
  have hgap : G.lower + 1 < G.upper := by omega
  have hs := G.seedVertex_mem_allowed_of_lt hn hgap
  have hzBox : ![0, t] ∈ rlc_connectorBox n := by
    have hlowerBox := rlc_rightPathVertex_mem_connectorBox
      gamma G.lowerVertex_mem_right
    have hupperBox := rlc_leftPathVertex_mem_connectorBox
      gamma' G.upperVertex_mem_left
    simp only [RlcAxisBarrierGap.lowerVertex, RlcAxisBarrierGap.upperVertex,
      mem_rect, Matrix.cons_val_zero, Matrix.cons_val_one] at hlowerBox hupperBox
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hzAllowed : ![0, t] ∈ rlc_connectorAllowed gamma gamma' := by
    rw [rlc_connectorAllowed, Finset.mem_sdiff]
    exact ⟨hzBox, G.interior_free t hlower hupper⟩
  let w := sw_vertSeg 0 (G.lower + 1) t
  have hw : ∀ z ∈ w.support,
      z ∈ (rlc_connectorAllowed gamma gamma' : Set (Site 2)) := by
    intro z hz
    change z ∈ (sw_vertSeg 0 (G.lower + 1) t).support at hz
    rw [sw_vertSeg_mem_support, Set.uIcc_of_le (by omega)] at hz
    simp only [Set.mem_Icc] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    rw [Finset.mem_coe, rlc_connectorAllowed, Finset.mem_sdiff]
    constructor
    · have hlowerBox := rlc_rightPathVertex_mem_connectorBox
        gamma G.lowerVertex_mem_right
      have hupperBox := rlc_leftPathVertex_mem_connectorBox
        gamma' G.upperVertex_mem_left
      simp only [RlcAxisBarrierGap.lowerVertex,
        RlcAxisBarrierGap.upperVertex, mem_rect, Matrix.cons_val_zero,
        Matrix.cons_val_one] at hlowerBox hupperBox
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · exact G.interior_free r (by omega) (by omega)
  have hreach := walk_induce_reachable (hypercubicLattice 2)
    (rlc_connectorAllowed gamma gamma' : Set (Site 2))
    w hw hs hzAllowed
  have hzSet : ![0, t] ∈ rlc_axisGapRegionSet G :=
    ⟨hzAllowed, hs, hreach⟩
  simpa [rlc_axisGapRegion] using hzSet

/-- The edges with both endpoints in the region of an axis gap. -/
noncomputable def rlc_axisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') : Finset (Sym2 (Site 2)) :=
  (edgesWithinFinset (rlc_connectorBox n)).filter (fun e =>
    ∃ z ∈ rlc_axisGapRegion G, z ∈ e) ∪ {G.firstEdge}

lemma RlcAxisBarrierGap.verticalEdge_mem_axisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n) {t : ℤ}
    (hlower : G.lower ≤ t) (hupper : t < G.upper) :
    s(![0, t], ![0, t + 1]) ∈ rlc_axisGapEdges G := by
  by_cases heq : t = G.lower
  · subst t
    simp [rlc_axisGapEdges, RlcAxisBarrierGap.firstEdge,
      RlcAxisBarrierGap.lowerVertex, RlcAxisBarrierGap.seedVertex]
  · have hlt : G.lower < t := lt_of_le_of_ne hlower (Ne.symm heq)
    have htRegion := G.axisVertex_mem_region_of_between hn hlt hupper
    rw [rlc_axisGapEdges, Finset.mem_union]
    apply Or.inl
    simp only [Finset.mem_filter]
    constructor
    · rw [mem_edgesWithinFinset]
      have htSet : ![0, t] ∈ rlc_axisGapRegionSet G := by
        simpa [rlc_axisGapRegion] using htRegion
      obtain ⟨htAllowed, _hs, _hreach⟩ := htSet
      have htBox := (Finset.mem_sdiff.mp htAllowed).1
      have hnextBox : ![0, t + 1] ∈ rlc_connectorBox n := by
        have hlowerBox := rlc_rightPathVertex_mem_connectorBox
          gamma G.lowerVertex_mem_right
        have hupperBox := rlc_leftPathVertex_mem_connectorBox
          gamma' G.upperVertex_mem_left
        simp only [RlcAxisBarrierGap.lowerVertex,
          RlcAxisBarrierGap.upperVertex, mem_rect, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hlowerBox hupperBox
        simp only [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
      exact ⟨![0, t], htBox, ![0, t + 1], hnextBox, rfl⟩
    · exact ⟨![0, t], htRegion, Sym2.mem_mk_left _ _⟩

/-- The event that the two paths are joined through the region of an axis gap. -/
def rlc_axisGapConnectorEvent {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ rlc_pathVertices gamma.1,
    ∃ y ∈ rlc_pathVertices gamma'.1,
    ∃ (hxR : x ∈ rect (-2 * n) (2 * n) (-n) n)
      (hyR : y ∈ rect (-2 * n) (2 * n) (-n) n),
      ConnectedWithin 2
        (rlc_maskConfig (rlc_axisGapEdges G) omega)
        (rect (-2 * n) (2 * n) (-n) n) ⟨x, hxR⟩ ⟨y, hyR⟩}

lemma rlc_axisGapConnectorEvent_dependsOn {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    DependsOn ((rlc_axisGapConnectorEvent G).indicator (fun _ => (1 : ℝ)))
      (rlc_axisGapEdges G : Set (Sym2 (Site 2))) := by
  intro omega omega' hagree
  have hmask : rlc_maskConfig (rlc_axisGapEdges G) omega =
      rlc_maskConfig (rlc_axisGapEdges G) omega' :=
    rlc_maskConfig_congr hagree
  have hevent : omega ∈ rlc_axisGapConnectorEvent G ↔
      omega' ∈ rlc_axisGapConnectorEvent G := by
    simp only [rlc_axisGapConnectorEvent, Set.mem_ofPred_eq, hmask]
  by_cases hmem : omega ∈ rlc_axisGapConnectorEvent G
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]

lemma rlc_axisGapConnectorEvent_measurableSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    MeasurableSet (rlc_axisGapConnectorEvent G) :=
  measurableSet_of_dependsOn (rlc_axisGapConnectorEvent_dependsOn G)

/-- The connector event chosen adaptively: through an axis gap if one exists, otherwise directly. -/
noncomputable def rlc_adaptiveConnectorEvent {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  match rlc_axisBarrierGap? gamma gamma' with
  | none => Set.univ
  | some G => rlc_axisGapConnectorEvent G

lemma rlc_adaptiveConnectorEvent_measurableSet {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    MeasurableSet (rlc_adaptiveConnectorEvent gamma gamma') := by
  unfold rlc_adaptiveConnectorEvent
  split
  · exact MeasurableSet.univ
  · exact rlc_axisGapConnectorEvent_measurableSet _

lemma rlc_adaptiveConnectorEvent_eq_univ_of_not_disjoint {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdisj : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    rlc_adaptiveConnectorEvent gamma gamma' = Set.univ := by
  rw [rlc_adaptiveConnectorEvent,
    rlc_axisBarrierGap?_eq_none_of_not_disjoint gamma gamma' hdisj]

lemma rlc_adaptiveConnectorEvent_eq_gap_of_some {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (G : RlcAxisBarrierGap gamma gamma')
    (hG : rlc_axisBarrierGap? gamma gamma' = some G) :
    rlc_adaptiveConnectorEvent gamma gamma' = rlc_axisGapConnectorEvent G := by
  rw [rlc_adaptiveConnectorEvent, hG]

lemma rlc_axisGapRegion_not_barrier {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {z : Site 2}
    (hz : z ∈ rlc_axisGapRegion G) :
    z ∉ rlc_connectorBarrier gamma gamma' := by
  have hzset : z ∈ rlc_axisGapRegionSet G := by
    simpa [rlc_axisGapRegion] using hz
  obtain ⟨hzAllowed, _hs, _hreach⟩ := hzset
  exact (Finset.mem_sdiff.mp hzAllowed).2

lemma RlcAxisBarrierGap.seedVertex_not_right_of_disjoint {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    G.seedVertex ∉ rlc_pathVertices gamma.1 := by
  intro hseed
  have hab := G.lower_lt_upper
  have hle : G.lower + 1 ≤ G.upper := by omega
  rcases hle.eq_or_lt with heq | hlt
  · have hseedLeft : G.seedVertex ∈ rlc_pathVertices gamma'.1 := by
      have hu := (rlc_mem_axisHeights_iff
        (rlc_pathVertices gamma'.1) G.upper).mp G.upper_mem
      simpa [RlcAxisBarrierGap.seedVertex, heq] using hu
    exact (Finset.disjoint_left.mp hdisj) hseed hseedLeft
  · have hnotBarrier := G.seedVertex_not_barrier_of_lt hlt
    apply hnotBarrier
    simp [rlc_connectorBarrier, hseed]

lemma RlcAxisBarrierGap.firstEdge_not_mem_rightPath_of_disjoint {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    G.firstEdge ∉ rlc_pathEdges gamma.1 := by
  intro he
  have he' : s(G.lowerVertex, G.seedVertex) ∈ rlc_pathEdges gamma.1 := by
    simpa [RlcAxisBarrierGap.firstEdge] using he
  exact G.seedVertex_not_right_of_disjoint hdisj
    (rlc_pathEdge_endpoints_mem_vertices gamma.1 he').2

lemma RlcAxisBarrierGap.firstEdge_not_mem_leftPath_of_disjoint {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    G.firstEdge ∉ rlc_pathEdges gamma'.1 := by
  intro he
  have he' : s(G.lowerVertex, G.seedVertex) ∈ rlc_pathEdges gamma'.1 := by
    simpa [RlcAxisBarrierGap.firstEdge] using he
  exact (Finset.disjoint_left.mp hdisj) G.lowerVertex_mem_right
    (rlc_pathEdge_endpoints_mem_vertices gamma'.1 he').1

lemma rlc_rightPathEdges_disjoint_axisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    Disjoint (rlc_pathEdges gamma.1) (rlc_axisGapEdges G) := by
  rw [Finset.disjoint_left]
  intro e hePath heGap
  rw [rlc_axisGapEdges, Finset.mem_union] at heGap
  rcases heGap with heRegion | heFirst
  · simp only [Finset.mem_filter] at heRegion
    obtain ⟨_ebox, z, hzRegion, hze⟩ := heRegion
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hePath
      rw [Sym2.mem_iff] at hze
      rcases hze with rfl | rfl
      · exact rlc_axisGapRegion_not_barrier hzRegion (by
          simp [rlc_connectorBarrier, hends.1])
      · exact rlc_axisGapRegion_not_barrier hzRegion (by
          simp [rlc_connectorBarrier, hends.2])
  · have heEq : e = G.firstEdge := by simpa using heFirst
    exact G.firstEdge_not_mem_rightPath_of_disjoint hdisj (heEq ▸ hePath)

lemma rlc_leftPathEdges_disjoint_axisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    Disjoint (rlc_pathEdges gamma'.1) (rlc_axisGapEdges G) := by
  rw [Finset.disjoint_left]
  intro e hePath heGap
  rw [rlc_axisGapEdges, Finset.mem_union] at heGap
  rcases heGap with heRegion | heFirst
  · simp only [Finset.mem_filter] at heRegion
    obtain ⟨_ebox, z, hzRegion, hze⟩ := heRegion
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hePath
      rw [Sym2.mem_iff] at hze
      rcases hze with rfl | rfl
      · exact rlc_axisGapRegion_not_barrier hzRegion (by
          simp [rlc_connectorBarrier, hends.1])
      · exact rlc_axisGapRegion_not_barrier hzRegion (by
          simp [rlc_connectorBarrier, hends.2])
  · have heEq : e = G.firstEdge := by simpa using heFirst
    exact G.firstEdge_not_mem_leftPath_of_disjoint hdisj (heEq ▸ hePath)

lemma rlc_mem_axisGapConnectorEvent_of_firstEdge_open {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hadjGap : G.lower + 1 = G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hopen : omega G.firstEdge = true) :
    omega ∈ rlc_axisGapConnectorEvent G := by
  have hLowerR := rlc_rightPathVertex_mem_connectorBox gamma G.lowerVertex_mem_right
  have hUpperR := rlc_leftPathVertex_mem_connectorBox gamma' G.upperVertex_mem_left
  refine ⟨G.lowerVertex, G.lowerVertex_mem_right,
    G.upperVertex, G.upperVertex_mem_left, hLowerR, hUpperR, ?_⟩
  have hlat : (hypercubicLattice 2).Adj G.lowerVertex G.upperVertex := by
    simp [RlcAxisBarrierGap.lowerVertex, RlcAxisBarrierGap.upperVertex,
      hypercubicLattice_adj, Fin.sum_univ_two, ← hadjGap]
  have hfirst : s(G.lowerVertex, G.upperVertex) = G.firstEdge := by
    simp [RlcAxisBarrierGap.firstEdge, RlcAxisBarrierGap.seedVertex,
      RlcAxisBarrierGap.upperVertex, hadjGap]
  have hfirstMem : G.firstEdge ∈ rlc_axisGapEdges G := by
    simp [rlc_axisGapEdges]
  have hmask : rlc_maskConfig (rlc_axisGapEdges G) omega
      s(G.lowerVertex, G.upperVertex) = true := by
    rw [hfirst, rlc_maskConfig, ite_eq_left hfirstMem]
    exact hopen
  have hstep :
      (openSubgraphInduce 2 (rlc_maskConfig (rlc_axisGapEdges G) omega)
        (rect (-2 * n) (2 * n) (-n) n)).Adj
        ⟨G.lowerVertex, hLowerR⟩ ⟨G.upperVertex, hUpperR⟩ := by
    rw [openSubgraphInduce_adj]
    exact ⟨hlat, hmask⟩
  exact hstep.reachable

lemma rlc_axisGapConnector_half_of_adjacent {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hadjGap : G.lower + 1 = G.upper) :
    (1 : ℝ) / 2 ≤ halfMeasure.real (rlc_axisGapConnectorEvent G) := by
  let Open : Set (ConfigSpace (Sym2 (Site 2))) := {omega | omega G.firstEdge = true}
  have hsub : Open ⊆ rlc_axisGapConnectorEvent G := by
    intro omega homega
    exact rlc_mem_axisGapConnectorEvent_of_firstEdge_open G hadjGap omega homega
  have hprob : halfMeasure.real Open = (1 : ℝ) / 2 := by
    simpa [Open, halfMeasure] using
      (coord_true_prob (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one G.firstEdge)
  rw [← hprob]
  exact measureReal_mono hsub

lemma rlc_adaptiveConnector_half_of_nonadjacent {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hnonadj : ∀ G : RlcAxisBarrierGap gamma gamma',
      G.lower + 1 < G.upper →
      (1 : ℝ) / 2 ≤ halfMeasure.real (rlc_axisGapConnectorEvent G)) :
    (1 : ℝ) / 2 ≤
      halfMeasure.real (rlc_adaptiveConnectorEvent gamma gamma') := by
  by_cases hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)
  · obtain ⟨G, hG⟩ := rlc_axisBarrierGap?_eq_some_of_disjoint gamma gamma' hdisj
    rw [rlc_adaptiveConnectorEvent_eq_gap_of_some gamma gamma' G hG]
    have hle : G.lower + 1 ≤ G.upper := by
      have := G.lower_lt_upper
      omega
    rcases hle.eq_or_lt with hadj | hlt
    · exact rlc_axisGapConnector_half_of_adjacent G hadj
    · exact hnonadj G hlt
  · rw [rlc_adaptiveConnectorEvent_eq_univ_of_not_disjoint gamma gamma' hdisj,
      probReal_univ]
    norm_num

lemma rlc_exists_axis_barrier_gap_of_not_connector {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    ∃ a b : ℤ,
      a ∈ rlc_axisHeights (rlc_pathVertices gamma.1) ∧
      b ∈ rlc_axisHeights (rlc_pathVertices gamma'.1) ∧
      (gamma.1.1 : Site 2) 1 ≤ a ∧ a < b ∧
      b ≤ (gamma'.1.2.1 : Site 2) 1 ∧
      ∀ t : ℤ, a < t → t < b →
        ![0, t] ∉ rlc_connectorBarrier gamma gamma' :=
  rlc_exists_axis_barrier_gap_of_disjoint gamma gamma'
    (rlc_pathVertices_disjoint_of_not_connector gamma gamma' omega hno)

/-- The sites reachable from the right path in the masked configuration inside the connector box. -/
def rlc_connectorReachSet {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) : Set (Site 2) :=
  {z | ∃ (hzR : z ∈ rect (-2 * n) (2 * n) (-n) n),
    ∃ x ∈ rlc_pathVertices gamma.1,
    ∃ hxR : x ∈ rect (-2 * n) (2 * n) (-n) n,
      ConnectedWithin 2
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
        (rect (-2 * n) (2 * n) (-n) n) ⟨x, hxR⟩ ⟨z, hzR⟩}

lemma rlc_connectorReachSet_subset_box {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_connectorReachSet gamma gamma' omega ⊆
      rect (-2 * n) (2 * n) (-n) n := by
  rintro z ⟨hzR, _⟩
  exact hzR

lemma rlc_connectorReachSet_finite {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (rlc_connectorReachSet gamma gamma' omega).Finite :=
  (rect_finite (-2 * n) (2 * n) (-n) n).subset
    (rlc_connectorReachSet_subset_box gamma gamma' omega)

lemma rlc_rightPathVertex_mem_connectorReachSet {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {x : Site 2}
    (hx : x ∈ rlc_pathVertices gamma.1) :
    x ∈ rlc_connectorReachSet gamma gamma' omega := by
  let hxR := rlc_rightPathVertex_mem_connectorBox gamma hx
  exact ⟨hxR, x, hx, hxR,
    connectedWithin_refl
      (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
      (rect (-2 * n) (2 * n) (-n) n) ⟨x, hxR⟩⟩

lemma rlc_connectorReachSet_extend {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hv : v ∈ rlc_connectorReachSet gamma gamma' omega)
    (hwR : w ∈ rect (-2 * n) (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hopen : rlc_maskConfig (rlc_connectorEdges gamma gamma') omega s(v, w) = true) :
    w ∈ rlc_connectorReachSet gamma gamma' omega := by
  obtain ⟨hvR, x, hx, hxR, hxv⟩ := hv
  refine ⟨hwR, x, hx, hxR, hxv.trans ?_⟩
  have hstep :
      (openSubgraphInduce 2
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
        (rect (-2 * n) (2 * n) (-n) n)).Adj ⟨v, hvR⟩ ⟨w, hwR⟩ := by
    rw [openSubgraphInduce_adj]
    exact ⟨hadj, hopen⟩
  exact hstep.reachable

lemma rlc_leftPathVertex_not_mem_connectorReachSet_of_not_connector {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') {y : Site 2}
    (hy : y ∈ rlc_pathVertices gamma'.1) :
    y ∉ rlc_connectorReachSet gamma gamma' omega := by
  rintro ⟨hyR, x, hx, hxR, hxy⟩
  exact hno ⟨x, hx, y, hy, hxR, hyR, hxy⟩

lemma rlc_connectorReachSet_boundary_closed {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hv : v ∈ rlc_connectorReachSet gamma gamma' omega)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hw : w ∉ rlc_connectorReachSet gamma gamma' omega) :
    rlc_maskConfig (rlc_connectorEdges gamma gamma') omega s(v, w) = false := by
  by_cases hwR : w ∈ rect (-2 * n) (2 * n) (-n) n
  · by_contra hopen
    rw [Bool.not_eq_false] at hopen
    exact hw (rlc_connectorReachSet_extend gamma gamma' omega hv hwR hadj hopen)
  · have hnotU : s(v, w) ∉ rlc_connectorEdges gamma gamma' := by
      intro he
      simp only [rlc_connectorEdges, Finset.mem_filter] at he
      rw [mem_edgesWithinFinset] at he
      obtain ⟨x, hx, y, hy, hxy⟩ := he.1
      have hbox : w ∈ rlc_connectorBox n := by
        rw [Sym2.eq_iff] at hxy
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hy
        · exact hx
      exact hwR (by simpa [rlc_connectorBox] using hbox)
    simp [rlc_maskConfig, hnotU]

lemma rlc_connectorReachSet_boundary_dual_open {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hv : v ∈ rlc_connectorReachSet gamma gamma' omega)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hw : w ∉ rlc_connectorReachSet gamma gamma' omega) :
    dualConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
      (crossEdge s(v, w)) = true :=
  (isClosed_iff_dualEdge_isOpen
    (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega) s(v, w)).mp
    (rlc_connectorReachSet_boundary_closed gamma gamma' omega hv hadj hw)

lemma rlc_connectorReachSet_edgeBoundary_closed {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hvw : (v, w) ∈ edgeBoundary 2
      (rlc_connectorReachSet gamma gamma' omega)) :
    rlc_maskConfig (rlc_connectorEdges gamma gamma') omega s(v, w) = false := by
  obtain ⟨hadj, hsplit⟩ := hvw
  by_cases hv : v ∈ rlc_connectorReachSet gamma gamma' omega
  · exact rlc_connectorReachSet_boundary_closed gamma gamma' omega hv hadj
      (hsplit.mp hv)
  · have hw : w ∈ rlc_connectorReachSet gamma gamma' omega := by
      by_contra hw
      exact hv (hsplit.mpr hw)
    rw [Sym2.eq_swap]
    exact rlc_connectorReachSet_boundary_closed gamma gamma' omega hw hadj.symm hv

lemma rlc_connectorReachSet_edgeBoundary_dual_open {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hvw : (v, w) ∈ edgeBoundary 2
      (rlc_connectorReachSet gamma gamma' omega)) :
    dualConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
      (crossEdge s(v, w)) = true :=
    (isClosed_iff_dualEdge_isOpen
    (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega) s(v, w)).mp
    (rlc_connectorReachSet_edgeBoundary_closed gamma gamma' omega hvw)

lemma rlc_faceBoundaryWalk_edges_dual_open {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v f g : Site 2}
    (c : (faceBoundaryGraph
      (rlc_connectorReachSet gamma gamma' omega)).Walk u v)
    (hfg : s(f, g) ∈ c.edges) :
    dualConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
      (crossEdge (sharedPrimalEdge f g)) = true := by
  have hadj : (faceBoundaryGraph
      (rlc_connectorReachSet gamma gamma' omega)).Adj f g :=
    c.adj_of_mem_edges hfg
  have hbd : bdEdge (rlc_connectorReachSet gamma gamma' omega)
      (sharedPrimalEdge f g) :=
    faceBoundaryWalk_edges_bdEdge
      (rlc_connectorReachSet gamma gamma' omega) c hfg
  obtain ⟨p, q, hpq, hadjPQ⟩ :=
    sharedPrimalEdge_isLatticeEdge hadj.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_connectorReachSet gamma gamma' omega) := by
    refine ⟨hadjPQ, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hbd
  rw [hpq]
  exact rlc_connectorReachSet_edgeBoundary_dual_open
    gamma gamma' omega hpqBoundary

lemma rlc_faceBoundaryGraph_le_openFaceDual {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    faceBoundaryGraph (rlc_connectorReachSet gamma gamma' omega) ≤
      openSubgraph 2 (fci_faceDualConfig
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)) := by
  intro f g hfg
  obtain ⟨p, q, hpq, hadjPQ⟩ :=
    sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_connectorReachSet gamma gamma' omega) := by
    refine ⟨hadjPQ, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hclosed := rlc_connectorReachSet_edgeBoundary_closed
    gamma gamma' omega hpqBoundary
  refine ⟨hfg.1, ?_⟩
  rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1, hpq]
  simpa using hclosed

lemma rlc_connectorReachSet_edgeBoundary_nonempty {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega)).Nonempty := by
  let v : Site 2 := gamma.1.2.1
  let w : Site 2 := v + ![1, 0]
  have hvPath : v ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨v, by simpa [v] using rightSide_subset gamma.1.2.1.2⟩,
      gamma.1.2.2.1.end_mem_support, rfl⟩
  have hv : v ∈ rlc_connectorReachSet gamma gamma' omega :=
    rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hvPath
  have hvx : v 0 = 2 * n := by
    simpa only [v] using gamma.1.2.1.2.2
  have hw0 : w 0 = v 0 + 1 := by
    change ((v + (![1, 0] : Site 2) : Site 2) 0) = v 0 + 1
    rw [Pi.add_apply]
    rfl
  have hw1 : w 1 = v 1 := by
    change ((v + (![1, 0] : Site 2) : Site 2) 1) = v 1
    rw [Pi.add_apply]
    simp
  have hadj : (hypercubicLattice 2).Adj v w := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    rw [hw0, hw1]
    simp
  have hw : w ∉ rlc_connectorReachSet gamma gamma' omega := by
    intro hwReach
    have hwR := rlc_connectorReachSet_subset_box gamma gamma' omega hwReach
    rw [mem_rect] at hwR
    have : w 0 = 2 * n + 1 := by
      rw [hw0, hvx]
    omega
  exact ⟨(v, w), hadj, iff_of_true hv hw⟩

lemma rlc_connectorReachSet_dualCircuit {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    ∃ (u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_connectorReachSet gamma gamma' omega)).Walk u u), c.IsCycle := by
  obtain ⟨⟨v, w⟩, hvw⟩ :=
    rlc_connectorReachSet_edgeBoundary_nonempty gamma gamma' omega
  exact exists_dualCircuit_of_finite_of_edgeBoundary
    (rlc_connectorReachSet gamma gamma' omega)
    (rlc_connectorReachSet_finite gamma gamma' omega) hvw

lemma rlc_walk_mem_edgeBoundary_edges (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ u v, (u, v) ∈ edgeBoundary 2 S ∧ s(u, v) ∈ w.edges := by
  classical
  induction w with
  | nil => exact absurd hx hy
  | @cons a b c hab p ih =>
    by_cases hb : b ∈ S
    · obtain ⟨u, v, huv, he⟩ := ih hb hy
      exact ⟨u, v, huv, by simp [he]⟩
    · exact ⟨a, b, ⟨hab, by simp [hx, hb]⟩, by simp⟩

lemma rlc_connectorReachSet_axis_boundary {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    ∃ p q : Site 2,
      (p, q) ∈ edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega) ∧
      p ∈ rect (-2 * n) (2 * n) (-n) n ∧
      q ∈ rect (-2 * n) (2 * n) (-n) n ∧
      p 0 = 0 ∧ q 0 = 0 := by
  let x : Site 2 := gamma.1.1
  let y : Site 2 := gamma'.1.2.1
  have hxPath : x ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨x, leftSide_subset gamma.1.1.2⟩,
      gamma.1.2.2.1.start_mem_support, rfl⟩
  have hyPath : y ∈ rlc_pathVertices gamma'.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨y, rightSide_subset gamma'.1.2.1.2⟩,
      gamma'.1.2.2.1.end_mem_support, rfl⟩
  have hxReach : x ∈ rlc_connectorReachSet gamma gamma' omega :=
    rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hxPath
  have hyNot : y ∉ rlc_connectorReachSet gamma gamma' omega :=
    rlc_leftPathVertex_not_mem_connectorReachSet_of_not_connector
      gamma gamma' omega hno hyPath
  have hx0 : x 0 = 0 := gamma.1.1.2.2
  have hy0 : y 0 = 0 := gamma'.1.2.1.2.2
  have hxy0 : x = ![0, x 1] := by
    ext i
    fin_cases i <;> simp [hx0]
  have hyy0 : y = ![0, y 1] := by
    ext i
    fin_cases i <;> simp [hy0]
  let w : (hypercubicLattice 2).Walk x y :=
    (sw_vertSeg 0 (x 1) (y 1)).copy hxy0.symm hyy0.symm
  obtain ⟨p, q, hpq, hpqEdge⟩ :=
    rlc_walk_mem_edgeBoundary_edges
      (rlc_connectorReachSet gamma gamma' omega) w hxReach hyNot
  have hpSupp : p ∈ w.support := w.fst_mem_support_of_mem_edges hpqEdge
  have hqSupp : q ∈ w.support := w.snd_mem_support_of_mem_edges hpqEdge
  have hsupport (z : Site 2) (hz : z ∈ w.support) :
      ∃ t : ℤ, t ∈ Set.uIcc (x 1) (y 1) ∧ z = ![0, t] := by
    change z ∈ ((sw_vertSeg 0 (x 1) (y 1)).copy _ _).support at hz
    rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hz
    exact hz
  obtain ⟨tp, htp, rfl⟩ := hsupport p hpSupp
  obtain ⟨tq, htq, rfl⟩ := hsupport q hqSupp
  have hxRows : -n ≤ x 1 ∧ x 1 ≤ n := by
    have h := gamma.1.1.2.1
    rw [mem_rect] at h
    exact h.2.2
  have hyRows : -n ≤ y 1 ∧ y 1 ≤ n := by
    have h := gamma'.1.2.1.2.1
    rw [mem_rect] at h
    exact h.2.2
  have htpRows : -n ≤ tp ∧ tp ≤ n := by
    rw [Set.mem_uIcc] at htp
    rcases htp with htp | htp <;> omega
  have htqRows : -n ≤ tq ∧ tq ≤ n := by
    rw [Set.mem_uIcc] at htq
    rcases htq with htq | htq <;> omega
  refine ⟨![0, tp], ![0, tq], hpq, ?_, ?_, by simp, by simp⟩
  · rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

lemma rlc_connectorReachSet_axis_anchored_dualCircuit {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    ∃ (p q f g u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_connectorReachSet gamma gamma' omega)).Walk u u),
      (p, q) ∈ edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega) ∧
      p ∈ rect (-2 * n) (2 * n) (-n) n ∧
      q ∈ rect (-2 * n) (2 * n) (-n) n ∧
      p 0 = 0 ∧ q 0 = 0 ∧
      (faceBoundaryGraph
        (rlc_connectorReachSet gamma gamma' omega)).Adj f g ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  classical
  obtain ⟨p, q, hpq, hpR, hqR, hp0, hq0⟩ :=
    rlc_connectorReachSet_axis_boundary gamma gamma' omega hno
  obtain ⟨f, g, hfgLat, hshared⟩ := jfc_flankingFaces hpq.1
  have hfg : (faceBoundaryGraph
      (rlc_connectorReachSet gamma gamma' omega)).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact hpq.2
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph
    (rlc_connectorReachSet gamma gamma' omega)
    (rlc_connectorReachSet_finite gamma gamma' omega)
  obtain ⟨u, c, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      (faceBoundaryGraph (rlc_connectorReachSet gamma gamma' omega))
      T hT (degree_faceBoundaryGraph_even
        (rlc_connectorReachSet gamma gamma' omega)) hfg
  exact ⟨p, q, f, g, u, c, hpq, hpR, hqR, hp0, hq0,
    hfg, hshared, hcyc, hedge⟩

lemma rlc_connectorReachSet_axis_anchored_openDualCircuit {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    ∃ (p q f g u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_connectorReachSet gamma gamma' omega)).Walk u u),
      (p, q) ∈ edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega) ∧
      p ∈ rect (-2 * n) (2 * n) (-n) n ∧
      q ∈ rect (-2 * n) (2 * n) (-n) n ∧
      p 0 = 0 ∧ q 0 = 0 ∧
      (faceBoundaryGraph
        (rlc_connectorReachSet gamma gamma' omega)).Adj f g ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges ∧
      ∀ a b : Site 2, s(a, b) ∈ c.edges →
        dualConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
          (crossEdge (sharedPrimalEdge a b)) = true := by
  obtain ⟨p, q, f, g, u, c, hpq, hpR, hqR, hp0, hq0,
      hfg, hshared, hcyc, hedge⟩ :=
    rlc_connectorReachSet_axis_anchored_dualCircuit gamma gamma' omega hno
  refine ⟨p, q, f, g, u, c, hpq, hpR, hqR, hp0, hq0,
    hfg, hshared, hcyc, hedge, ?_⟩
  intro a b hab
  exact rlc_faceBoundaryWalk_edges_dual_open gamma gamma' omega c hab

lemma rlc_connectorReachSet_openFaceDualCircuit {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    ∃ (u : Site 2)
      (c : (openSubgraph 2 (fci_faceDualConfig
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega))).Walk u u),
      c.IsCycle := by
  obtain ⟨_p, _q, _f, _g, u, c, _hpq, _hpR, _hqR, _hp0, _hq0,
      _hfg, _hshared, hcyc, _hedge⟩ :=
    rlc_connectorReachSet_axis_anchored_dualCircuit gamma gamma' omega hno
  let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma' omega
  exact ⟨u, c.mapLe hle, hcyc.mapLe hle⟩

/-! ## G. Dual reflection -/

/-- The reflection `(x, y) ↦ (-x - 1, y + 1)` that maps primal edges to dual edges of the faces. -/
def rlc_dualReflectFun (x : Site 2) : Site 2 := ![-x 0 - 1, x 1 + 1]

/-- The inverse of the dual reflection: `(x, y) ↦ (-x - 1, y - 1)`. -/
def rlc_dualReflectInvFun (x : Site 2) : Site 2 := ![-x 0 - 1, x 1 - 1]

/-- The dual reflection, as an equivalence of sites. -/
def rlc_dualReflect : Site 2 ≃ Site 2 where
  toFun := rlc_dualReflectFun
  invFun := rlc_dualReflectInvFun
  left_inv x := by
    ext i
    fin_cases i <;> simp [rlc_dualReflectFun, rlc_dualReflectInvFun]
  right_inv x := by
    ext i
    fin_cases i <;> simp [rlc_dualReflectFun, rlc_dualReflectInvFun]

@[simp] lemma rlc_dualReflect_zero (x : Site 2) :
    rlc_dualReflect x 0 = -x 0 - 1 := by
  rfl

@[simp] lemma rlc_dualReflect_one (x : Site 2) :
    rlc_dualReflect x 1 = x 1 + 1 := by
  rfl

@[simp] lemma rlc_dualReflect_symm_zero (x : Site 2) :
    rlc_dualReflect.symm x 0 = -x 0 - 1 := by
  rfl

@[simp] lemma rlc_dualReflect_symm_one (x : Site 2) :
    rlc_dualReflect.symm x 1 = x 1 - 1 := by
  rfl

lemma rlc_adj_dualReflect (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔
      (hypercubicLattice 2).Adj (rlc_dualReflect x) (rlc_dualReflect y) := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [rlc_dualReflect_zero, rlc_dualReflect_one]
  rw [show (-x 0 - 1) - (-y 0 - 1) = -(x 0 - y 0) by ring,
    Int.natAbs_neg,
    show (x 1 + 1) - (y 1 + 1) = x 1 - y 1 by ring]

/-- The dual reflection, acting on edges. -/
noncomputable def rlc_dualReflectEdge :
    Sym2 (Site 2) ≃ Sym2 (Site 2) :=
  sym2Congr rlc_dualReflect

lemma rlc_dualReflectEdge_symm_apply (e : Sym2 (Site 2)) :
    rlc_dualReflectEdge.symm e = e.map rlc_dualReflect.symm := by
  simp [rlc_dualReflectEdge, sym2Congr]

/-- The dual reflection, acting on configurations. -/
noncomputable def rlc_dualReflectConfig
    (omega : ConfigSpace (Sym2 (Site 2))) :
    ConfigSpace (Sym2 (Site 2)) :=
  Equiv.piCongrLeft (fun _ => Bool) rlc_dualReflectEdge
    (fci_faceDualConfig omega)

lemma rlc_dualReflectConfig_apply
    (omega : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    rlc_dualReflectConfig omega e =
      fci_faceDualConfig omega (e.map rlc_dualReflect.symm) := by
  rw [rlc_dualReflectConfig, Equiv.piCongrLeft_apply, eq_rec_constant,
    rlc_dualReflectEdge_symm_apply]

/-- The composite of the inverse dual reflection with the face-edge equivalence: an equivalence of
  edges. -/
noncomputable def rlc_pimsEdgeEquiv :
    Sym2 (Site 2) ≃ Sym2 (Site 2) :=
  rlc_dualReflectEdge.symm.trans fci_faceEdgeEquiv

lemma rlc_pimsEdgeEquiv_apply (e : Sym2 (Site 2)) :
    rlc_pimsEdgeEquiv e =
      fci_faceEdgeEquiv (e.map rlc_dualReflect.symm) := by
  simp [rlc_pimsEdgeEquiv, Equiv.trans_apply,
    rlc_dualReflectEdge_symm_apply]

lemma rlc_dualReflectConfig_eq_pims
    (omega : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    rlc_dualReflectConfig omega e = !(omega (rlc_pimsEdgeEquiv e)) := by
  rw [rlc_dualReflectConfig_apply, rlc_pimsEdgeEquiv_apply,
    fci_faceDualConfig]

lemma rlc_pimsEdgeEquiv_reflected_mk_of_adj
    {f g : Site 2} (hfg : (hypercubicLattice 2).Adj f g) :
    rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) =
      sharedPrimalEdge f g := by
  rw [rlc_pimsEdgeEquiv_apply, Sym2.map_mk]
  simp only [Equiv.symm_apply_apply]
  exact fci_faceEdgeEquiv_mk_of_adj hfg

lemma rlc_pimsEdgeEquiv_horizontal (a b : ℤ) :
    rlc_pimsEdgeEquiv s(![a, b], ![a + 1, b]) =
      s(![-a - 1, b - 1], ![-a - 1, b]) := by
  rw [rlc_pimsEdgeEquiv_apply, Sym2.map_mk]
  have hadj : (hypercubicLattice 2).Adj
      (![-a - 1, b - 1] : Site 2) ![-a - 2, b - 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hx : rlc_dualReflect.symm (![(a : ℤ), b] : Site 2) =
      ![-a - 1, b - 1] := by
    ext i
    fin_cases i <;> simp
  have hy : rlc_dualReflect.symm (![a + 1, b] : Site 2) =
      ![-a - 2, b - 1] := by
    ext i
    fin_cases i <;> simp
    ring_nf
  have hleft : (![-a - 2, b - 1] : Site 2) =
      ![(-a - 1) - 1, b - 1] := by
    congr 1; ring
  rw [hx, hy, fci_faceEdgeEquiv_mk_of_adj hadj, hleft,
    sharedPrimalEdge_left]
  simp [faceCorner00, faceCorner01]

lemma rlc_pimsEdgeEquiv_vertical (a b : ℤ) :
    rlc_pimsEdgeEquiv s(![a, b], ![a, b + 1]) =
      s(![-a - 1, b], ![-a, b]) := by
  rw [rlc_pimsEdgeEquiv_apply, Sym2.map_mk]
  have hadj : (hypercubicLattice 2).Adj
      (![-a - 1, b - 1] : Site 2) ![-a - 1, b] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hx : rlc_dualReflect.symm (![(a : ℤ), b] : Site 2) =
      ![-a - 1, b - 1] := by
    ext i
    fin_cases i <;> simp
  have hy : rlc_dualReflect.symm (![a, b + 1] : Site 2) =
      ![-a - 1, b] := by
    ext i
    fin_cases i <;> simp
  have htop : (![-a - 1, b] : Site 2) =
      ![-a - 1, (b - 1) + 1] := by
    congr 1; ring_nf
  rw [hx, hy, fci_faceEdgeEquiv_mk_of_adj hadj, htop,
    sharedPrimalEdge_top]
  simp [faceCorner01, faceCorner11]

lemma rlc_reflectedEdge_eq_horizontal_of_shared_vertical
    {f g : Site 2} (hfg : (hypercubicLattice 2).Adj f g) {t : ℤ}
    (hshared : sharedPrimalEdge f g = s(![0, t], ![0, t + 1])) :
    s(rlc_dualReflect f, rlc_dualReflect g) =
      s(![-1, t + 1], ![0, t + 1]) := by
  apply rlc_pimsEdgeEquiv.injective
  rw [rlc_pimsEdgeEquiv_reflected_mk_of_adj hfg, hshared]
  symm
  simpa using (rlc_pimsEdgeEquiv_horizontal (-1) (t + 1))

lemma rlc_dualReflectConfig_mk
    (omega : ConfigSpace (Sym2 (Site 2))) (x y : Site 2) :
    rlc_dualReflectConfig omega
        s(rlc_dualReflect x, rlc_dualReflect y) =
      fci_faceDualConfig omega s(x, y) := by
  rw [rlc_dualReflectConfig_apply, Sym2.map_mk]
  simp

lemma rlc_dualReflectConfig_measurePreserving :
    MeasurePreserving rlc_dualReflectConfig
      halfMeasure halfMeasure := by
  have hreindex : MeasurePreserving
      (Equiv.piCongrLeft (fun _ => Bool) rlc_dualReflectEdge)
      halfMeasure halfMeasure := by
    refine ⟨(MeasurableEquiv.piCongrLeft
      (fun _ => Bool) rlc_dualReflectEdge).measurable, ?_⟩
    rw [halfMeasure]
    unfold bernoulliProductMeasure
    exact Measure.infinitePi_map_piCongrLeft
      (fun _ : Sym2 (Site 2) =>
        bernoulliMeasure (2⁻¹ : ℝ≥0) half_le_one)
      rlc_dualReflectEdge
  exact hreindex.comp fci_faceDualConfig_measurePreserving

/-- The dual reflection as a homomorphism from the open subgraph of the face-dual configuration. -/
noncomputable def rlc_dualReflectOpenHom
    (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraph 2 (fci_faceDualConfig omega) →g
      openSubgraph 2 (rlc_dualReflectConfig omega) where
  toFun := rlc_dualReflect
  map_rel' := by
    intro x y hxy
    rw [openSubgraph_adj] at hxy ⊢
    refine ⟨(rlc_adj_dualReflect x y).mp hxy.1, ?_⟩
    rw [rlc_dualReflectConfig_mk]
    exact hxy.2

/-- The image of an open walk of the face-dual configuration under the dual reflection. -/
noncomputable def rlc_dualReflectOpenWalk
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (w : (openSubgraph 2 (fci_faceDualConfig omega)).Walk x y) :
    (openSubgraph 2 (rlc_dualReflectConfig omega)).Walk
      (rlc_dualReflect x) (rlc_dualReflect y) :=
  w.map (rlc_dualReflectOpenHom omega)

lemma rlc_dualReflectOpenWalk_isCycle
    (omega : ConfigSpace (Sym2 (Site 2))) {x : Site 2}
    {w : (openSubgraph 2 (fci_faceDualConfig omega)).Walk x x}
    (hw : w.IsCycle) :
    (rlc_dualReflectOpenWalk omega w).IsCycle := by
  exact hw.map rlc_dualReflect.injective

/-- The sites reachable from the lower gap vertex in the masked configuration. -/
def rlc_axisGapReachSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Set (Site 2) :=
  {z | ∃ (hzR : z ∈ rect (-2 * n) (2 * n) (-n) n),
    ∃ x ∈ rlc_pathVertices gamma.1,
    ∃ hxR : x ∈ rect (-2 * n) (2 * n) (-n) n,
      ConnectedWithin 2
        (rlc_maskConfig (rlc_axisGapEdges G) omega)
        (rect (-2 * n) (2 * n) (-n) n) ⟨x, hxR⟩ ⟨z, hzR⟩}

lemma rlc_axisGapReachSet_subset_box {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_axisGapReachSet G omega ⊆
      rect (-2 * n) (2 * n) (-n) n := by
  rintro z ⟨hzR, _⟩
  exact hzR

lemma rlc_axisGapReachSet_finite {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (rlc_axisGapReachSet G omega).Finite :=
  (rect_finite (-2 * n) (2 * n) (-n) n).subset
    (rlc_axisGapReachSet_subset_box G omega)

lemma rlc_rightPathVertex_mem_axisGapReachSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {x : Site 2}
    (hx : x ∈ rlc_pathVertices gamma.1) :
    x ∈ rlc_axisGapReachSet G omega := by
  let hxR := rlc_rightPathVertex_mem_connectorBox gamma hx
  exact ⟨hxR, x, hx, hxR,
    connectedWithin_refl
      (rlc_maskConfig (rlc_axisGapEdges G) omega)
      (rect (-2 * n) (2 * n) (-n) n) ⟨x, hxR⟩⟩

lemma rlc_axisGapReachSet_extend {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hv : v ∈ rlc_axisGapReachSet G omega)
    (hwR : w ∈ rect (-2 * n) (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hopen : rlc_maskConfig (rlc_axisGapEdges G) omega s(v, w) = true) :
    w ∈ rlc_axisGapReachSet G omega := by
  obtain ⟨hvR, x, hx, hxR, hxv⟩ := hv
  refine ⟨hwR, x, hx, hxR, hxv.trans ?_⟩
  have hstep :
      (openSubgraphInduce 2
        (rlc_maskConfig (rlc_axisGapEdges G) omega)
        (rect (-2 * n) (2 * n) (-n) n)).Adj ⟨v, hvR⟩ ⟨w, hwR⟩ := by
    rw [openSubgraphInduce_adj]
    exact ⟨hadj, hopen⟩
  exact hstep.reachable

lemma rlc_leftPathVertex_not_mem_axisGapReachSet_of_failure {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_axisGapConnectorEvent G) {y : Site 2}
    (hy : y ∈ rlc_pathVertices gamma'.1) :
    y ∉ rlc_axisGapReachSet G omega := by
  rintro ⟨hyR, x, hx, hxR, hxy⟩
  exact hno ⟨x, hx, y, hy, hxR, hyR, hxy⟩

lemma rlc_axisGapEdges_endpoints_mem_box {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) {v w : Site 2}
    (he : s(v, w) ∈ rlc_axisGapEdges G) :
    v ∈ rect (-2 * n) (2 * n) (-n) n ∧
      w ∈ rect (-2 * n) (2 * n) (-n) n := by
  rw [rlc_axisGapEdges, Finset.mem_union] at he
  rcases he with he | he
  · simp only [Finset.mem_filter] at he
    rw [mem_edgesWithinFinset] at he
    obtain ⟨x, hx, y, hy, hxy⟩ := he.1
    rw [Sym2.eq_iff] at hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [rlc_connectorBox] using And.intro hx hy
    · simpa [rlc_connectorBox] using And.intro hy hx
  · have heq : s(v, w) = s(G.lowerVertex, G.seedVertex) := by
      simpa [RlcAxisBarrierGap.firstEdge] using he
    have hlower := rlc_rightPathVertex_mem_connectorBox
      gamma G.lowerVertex_mem_right
    have hseed := G.seedVertex_mem_box_of_lt hn hlt
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hlower, by simpa [rlc_connectorBox] using hseed⟩
    · exact ⟨by simpa [rlc_connectorBox] using hseed, hlower⟩

lemma rlc_axisGapReachSet_boundary_closed {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hv : v ∈ rlc_axisGapReachSet G omega)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hw : w ∉ rlc_axisGapReachSet G omega) :
    rlc_maskConfig (rlc_axisGapEdges G) omega s(v, w) = false := by
  by_cases hwR : w ∈ rect (-2 * n) (2 * n) (-n) n
  · by_contra hopen
    rw [Bool.not_eq_false] at hopen
    exact hw (rlc_axisGapReachSet_extend G omega hv hwR hadj hopen)
  · have hnotU : s(v, w) ∉ rlc_axisGapEdges G := by
      intro he
      exact hwR (rlc_axisGapEdges_endpoints_mem_box G hn hlt he).2
    simp [rlc_maskConfig, hnotU]

lemma rlc_axisGapReachSet_edgeBoundary_closed {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hvw : (v, w) ∈ edgeBoundary 2 (rlc_axisGapReachSet G omega)) :
    rlc_maskConfig (rlc_axisGapEdges G) omega s(v, w) = false := by
  obtain ⟨hadj, hsplit⟩ := hvw
  by_cases hv : v ∈ rlc_axisGapReachSet G omega
  · exact rlc_axisGapReachSet_boundary_closed G hn hlt omega hv hadj
      (hsplit.mp hv)
  · have hw : w ∈ rlc_axisGapReachSet G omega := by
      by_contra hw
      exact hv (hsplit.mpr hw)
    rw [Sym2.eq_swap]
    exact rlc_axisGapReachSet_boundary_closed G hn hlt omega hw hadj.symm hv

lemma rlc_axisGapFaceBoundaryGraph_le_openFaceDual {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    faceBoundaryGraph (rlc_axisGapReachSet G omega) ≤
      openSubgraph 2 (fci_faceDualConfig
        (rlc_maskConfig (rlc_axisGapEdges G) omega)) := by
  intro f g hfg
  obtain ⟨p, q, hpq, hadjPQ⟩ :=
    sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_axisGapReachSet G omega) := by
    refine ⟨hadjPQ, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hclosed := rlc_axisGapReachSet_edgeBoundary_closed
    G hn hlt omega hpqBoundary
  refine ⟨hfg.1, ?_⟩
  rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1, hpq]
  simpa using hclosed

lemma rlc_axisGapReachSet_axis_boundary {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_axisGapConnectorEvent G) :
    ∃ p q : Site 2,
      (p, q) ∈ edgeBoundary 2 (rlc_axisGapReachSet G omega) ∧
      p 0 = 0 ∧ q 0 = 0 := by
  have hlower : G.lowerVertex ∈ rlc_axisGapReachSet G omega :=
    rlc_rightPathVertex_mem_axisGapReachSet G omega G.lowerVertex_mem_right
  have hupper : G.upperVertex ∉ rlc_axisGapReachSet G omega :=
    rlc_leftPathVertex_not_mem_axisGapReachSet_of_failure
      G omega hno G.upperVertex_mem_left
  let w : (hypercubicLattice 2).Walk G.lowerVertex G.upperVertex :=
    sw_vertSeg 0 G.lower G.upper
  obtain ⟨p, q, hpq, hpqEdge⟩ :=
    rlc_walk_mem_edgeBoundary_edges
      (rlc_axisGapReachSet G omega) w hlower hupper
  have hpSupp : p ∈ w.support := w.fst_mem_support_of_mem_edges hpqEdge
  have hqSupp : q ∈ w.support := w.snd_mem_support_of_mem_edges hpqEdge
  have haxis (z : Site 2) (hz : z ∈ w.support) : z 0 = 0 := by
    change z ∈ (sw_vertSeg 0 G.lower G.upper).support at hz
    rw [sw_vertSeg_mem_support] at hz
    obtain ⟨t, _ht, rfl⟩ := hz
    simp
  exact ⟨p, q, hpq, haxis p hpSupp, haxis q hqSupp⟩

lemma rlc_axisGapReachSet_axis_anchored_dualCircuit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_axisGapConnectorEvent G) :
    ∃ (p q f g u : Site 2)
      (c : (faceBoundaryGraph (rlc_axisGapReachSet G omega)).Walk u u),
      (p, q) ∈ edgeBoundary 2 (rlc_axisGapReachSet G omega) ∧
      p 0 = 0 ∧ q 0 = 0 ∧
      (faceBoundaryGraph (rlc_axisGapReachSet G omega)).Adj f g ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  classical
  obtain ⟨p, q, hpq, hp0, hq0⟩ :=
    rlc_axisGapReachSet_axis_boundary G omega hno
  obtain ⟨f, g, hfgLat, hshared⟩ := jfc_flankingFaces hpq.1
  have hfg : (faceBoundaryGraph
      (rlc_axisGapReachSet G omega)).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact hpq.2
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph
    (rlc_axisGapReachSet G omega) (rlc_axisGapReachSet_finite G omega)
  obtain ⟨u, c, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      (faceBoundaryGraph (rlc_axisGapReachSet G omega)) T hT
      (degree_faceBoundaryGraph_even (rlc_axisGapReachSet G omega)) hfg
  exact ⟨p, q, f, g, u, c, hpq, hp0, hq0,
    hfg, hshared, hcyc, hedge⟩

lemma rlc_axisGapReachSet_openFaceDualCircuit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_axisGapConnectorEvent G) :
    ∃ (p q f g u : Site 2)
      (c : (openSubgraph 2 (fci_faceDualConfig
        (rlc_maskConfig (rlc_axisGapEdges G) omega))).Walk u u),
      p 0 = 0 ∧ q 0 = 0 ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  obtain ⟨p, q, f, g, u, c, _hpq, hp0, hq0, _hfg,
      hshared, hcyc, hedge⟩ :=
    rlc_axisGapReachSet_axis_anchored_dualCircuit G omega hno
  let hle := rlc_axisGapFaceBoundaryGraph_le_openFaceDual G hn hlt omega
  refine ⟨p, q, f, g, u, c.mapLe hle, hp0, hq0, hshared,
    hcyc.mapLe hle, ?_⟩
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  exact hedge

lemma rlc_axisGapReachSet_reflectedOpenDualCircuit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_axisGapConnectorEvent G) :
    ∃ (p q f g u : Site 2)
      (c : (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_maskConfig (rlc_axisGapEdges G) omega))).Walk
          (rlc_dualReflect u) (rlc_dualReflect u)),
      p 0 = 0 ∧ q 0 = 0 ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧
      s(rlc_dualReflect f, rlc_dualReflect g) ∈ c.edges := by
  obtain ⟨p, q, f, g, u, c, hp0, hq0, hshared, hcyc, hedge⟩ :=
    rlc_axisGapReachSet_openFaceDualCircuit G hn hlt omega hno
  let hom := rlc_dualReflectOpenHom
    (rlc_maskConfig (rlc_axisGapEdges G) omega)
  refine ⟨p, q, f, g, u, rlc_dualReflectOpenWalk _ c,
    hp0, hq0, hshared, rlc_dualReflectOpenWalk_isCycle _ hcyc, ?_⟩
  have hEdges : (c.map hom).edges =
      c.edges.map (Sym2.map hom) :=
    SimpleGraph.Walk.edges_map hom c
  have hmapped : Sym2.map hom s(f, g) ∈
      c.edges.map (Sym2.map hom) :=
    List.mem_map_of_mem hedge
  have hedgeEq : Sym2.map hom s(f, g) =
      s(rlc_dualReflect f, rlc_dualReflect g) := by
    rfl
  change s(rlc_dualReflect f, rlc_dualReflect g) ∈ (c.map hom).edges
  exact hedgeEq ▸ hEdges.symm ▸ hmapped

lemma rlc_axisGapConnector_half_of_dual_reflection {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdual : ∀ omega : ConfigSpace (Sym2 (Site 2)),
      omega ∉ rlc_axisGapConnectorEvent G →
      rlc_dualReflectConfig omega ∈ rlc_axisGapConnectorEvent G) :
    (1 : ℝ) / 2 ≤
      halfMeasure.real (rlc_axisGapConnectorEvent G) := by
  apply rlc_connector_half_of_dual_reflection halfMeasure
    rlc_dualReflectConfig rlc_dualReflectConfig_measurePreserving
    (rlc_axisGapConnectorEvent G)
    (rlc_axisGapConnectorEvent_measurableSet G)
  intro omega hno
  exact hdual omega hno

lemma rlc_adaptiveConnector_half_of_dual_reflection {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdual : ∀ (G : RlcAxisBarrierGap gamma gamma')
      (_hlt : G.lower + 1 < G.upper)
      (omega : ConfigSpace (Sym2 (Site 2))),
      omega ∉ rlc_axisGapConnectorEvent G →
      rlc_dualReflectConfig omega ∈ rlc_axisGapConnectorEvent G) :
    (1 : ℝ) / 2 ≤
      halfMeasure.real
        (rlc_adaptiveConnectorEvent gamma gamma') := by
  apply rlc_adaptiveConnector_half_of_nonadjacent gamma gamma'
  intro G hlt
  exact rlc_axisGapConnector_half_of_dual_reflection G
    (hdual G hlt)

/-- The edges of a crossing path reflected in the vertical axis. -/
noncomputable def rlc_reflectedPathEdges {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) : Finset (Sym2 (Site 2)) :=
  (rlc_pathEdges gamma).image (Sym2.map rlc_flipX)

/-- The axis-gap edges together with the reflected path edges. -/
noncomputable def rlc_mixedAxisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') : Finset (Sym2 (Site 2)) :=
  (rlc_axisGapEdges G ∪ rlc_reflectedPathEdges gamma.1 ∪
      rlc_reflectedPathEdges gamma'.1) \
    (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)

lemma RlcAxisBarrierGap.verticalEdge_mem_mixedAxisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) {t : ℤ}
    (hlower : G.lower ≤ t) (hupper : t < G.upper) :
    s(![0, t], ![0, t + 1]) ∈ rlc_mixedAxisGapEdges G := by
  rw [rlc_mixedAxisGapEdges, Finset.mem_sdiff]
  constructor
  · simp only [Finset.mem_union]
    exact Or.inl (Or.inl (G.verticalEdge_mem_axisGapEdges hn hlower hupper))
  · rw [Finset.mem_union]
    push Not
    constructor
    · intro he
      have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he
      by_cases heq : t = G.lower
      · have hfree := G.interior_free (t + 1) (by omega) (by omega)
        exact hfree (by simp [rlc_connectorBarrier, hends.2])
      · have hfree := G.interior_free t (by omega) hupper
        exact hfree (by simp [rlc_connectorBarrier, hends.1])
    · intro he
      have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 he
      by_cases heq : t = G.lower
      · have hfree := G.interior_free (t + 1) (by omega) (by omega)
        exact hfree (by simp [rlc_connectorBarrier, hends.2])
      · have hfree := G.interior_free t (by omega) hupper
        exact hfree (by simp [rlc_connectorBarrier, hends.1])

lemma rlc_rightPathEdges_disjoint_mixedAxisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    Disjoint (rlc_pathEdges gamma.1) (rlc_mixedAxisGapEdges G) := by
  rw [Finset.disjoint_left]
  intro e he hmix
  exact (Finset.mem_sdiff.mp hmix).2 (by simp [he])

lemma rlc_leftPathEdges_disjoint_mixedAxisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    Disjoint (rlc_pathEdges gamma'.1) (rlc_mixedAxisGapEdges G) := by
  rw [Finset.disjoint_left]
  intro e he hmix
  exact (Finset.mem_sdiff.mp hmix).2 (by simp [he])

/-- The event that the two paths are joined inside the connector box using only edges of `U`. -/
def rlc_supportConnectorEvent {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2))) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ∃ x ∈ rlc_pathVertices gamma.1,
    ∃ y ∈ rlc_pathVertices gamma'.1,
    ∃ (hxR : x ∈ rect (-2 * n) (2 * n) (-n) n)
      (hyR : y ∈ rect (-2 * n) (2 * n) (-n) n),
      ConnectedWithin 2 (rlc_maskConfig U omega)
        (rect (-2 * n) (2 * n) (-n) n) ⟨x, hxR⟩ ⟨y, hyR⟩}

lemma rlc_supportConnectorEvent_isIncreasing {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2))) :
    IsIncreasing (rlc_supportConnectorEvent gamma gamma' U) := by
  intro omega omega' hle
  rintro ⟨x, hx, y, hy, hxR, hyR, hxy⟩
  exact ⟨x, hx, y, hy, hxR, hyR,
    StatMech.TwoDim.connectedWithin_mono (rlc_maskConfig_mono U hle) hxy⟩

lemma rlc_supportConnectorEvent_dependsOn {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2))) :
    DependsOn ((rlc_supportConnectorEvent gamma gamma' U).indicator
      (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site 2))) := by
  intro omega omega' hagree
  have hmask : rlc_maskConfig U omega = rlc_maskConfig U omega' :=
    rlc_maskConfig_congr hagree
  have hevent : omega ∈ rlc_supportConnectorEvent gamma gamma' U ↔
      omega' ∈ rlc_supportConnectorEvent gamma gamma' U := by
    simp only [rlc_supportConnectorEvent, Set.mem_ofPred_eq, hmask]
  by_cases hmem : omega ∈ rlc_supportConnectorEvent gamma gamma' U
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]

lemma rlc_supportConnectorEvent_measurableSet {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2))) :
    MeasurableSet (rlc_supportConnectorEvent gamma gamma' U) :=
  measurableSet_of_dependsOn
    (rlc_supportConnectorEvent_dependsOn gamma gamma' U)

/-- The support-connector event for the mixed axis-gap edge set. -/
noncomputable def rlc_mixedAxisGapConnectorEvent {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_supportConnectorEvent gamma gamma' (rlc_mixedAxisGapEdges G)

lemma rlc_mixedAxisGapConnectorEvent_dependsOn {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    DependsOn ((rlc_mixedAxisGapConnectorEvent G).indicator
      (fun _ => (1 : ℝ)))
      (rlc_mixedAxisGapEdges G : Set (Sym2 (Site 2))) :=
  rlc_supportConnectorEvent_dependsOn gamma gamma'
    (rlc_mixedAxisGapEdges G)

lemma rlc_mixedAxisGapConnectorEvent_measurableSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    MeasurableSet (rlc_mixedAxisGapConnectorEvent G) :=
  rlc_supportConnectorEvent_measurableSet gamma gamma'
    (rlc_mixedAxisGapEdges G)

lemma rlc_supportConnector_glues_horizontal (n : ℤ) (_hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2))) :
    rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩
        rlc_supportConnectorEvent gamma gamma' U ⊆
      horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
  intro omega homega
  obtain ⟨⟨hgamma, hgamma'⟩, hconn⟩ := homega
  obtain ⟨x, hxg, y, hyg, hxR, hyR, hxyMask⟩ := hconn
  obtain ⟨_hxSmall, hxToRightSmall⟩ :=
    rlc_pathOpen_connected_finish gamma.1 omega hgamma hxg
  obtain ⟨_hySmall, hleftToYSmall⟩ :=
    rlc_pathOpen_connected_start gamma'.1 omega hgamma' hyg
  have hrightSub : rect 0 (2 * n) (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hleftSub : rect (-2 * n) 0 (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hxToRight := StatMech.Lattice.connectedWithin_mono_set omega
    hrightSub hxToRightSmall
  have hleftToY := StatMech.Lattice.connectedWithin_mono_set omega
    hleftSub hleftToYSmall
  have hxy : ConnectedWithin 2 omega (rect (-2 * n) (2 * n) (-n) n)
      ⟨x, hxR⟩ ⟨y, hyR⟩ :=
    StatMech.TwoDim.connectedWithin_mono (rlc_maskConfig_le U omega) hxyMask
  let xL : leftSide (-2 * n) (2 * n) (-n) n :=
    ⟨gamma'.1.1, by
      rw [mem_leftSide, mem_rect]
      have h := gamma'.1.1.2
      rw [mem_leftSide, mem_rect] at h
      exact ⟨⟨by omega, by omega, h.1.2.2.1, h.1.2.2.2⟩, h.2⟩⟩
  let yR : rightSide (-2 * n) (2 * n) (-n) n :=
    ⟨gamma.1.2.1, by
      rw [mem_rightSide, mem_rect]
      have h := gamma.1.2.1.2
      rw [mem_rightSide, mem_rect] at h
      exact ⟨⟨by omega, by omega, h.1.2.2.1, h.1.2.2.2⟩, h.2⟩⟩
  refine ⟨xL, yR, ?_⟩
  exact hleftToY.trans (hxy.symm.trans hxToRight)

lemma rlc_mixedAxisGapConnector_glues_horizontal (n : ℤ) (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (G : RlcAxisBarrierGap gamma gamma') :
    rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩
        rlc_mixedAxisGapConnectorEvent G ⊆
      horizontalCrossingEvent (-2 * n) (2 * n) (-n) n :=
  rlc_supportConnector_glues_horizontal n hn gamma gamma'
    (rlc_mixedAxisGapEdges G)

/-- The mixed edge set chosen adaptively from the axis gap, if any. -/
noncomputable def rlc_mixedAdaptiveEdges {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  match rlc_axisBarrierGap? gamma gamma' with
  | none => ∅
  | some G => rlc_mixedAxisGapEdges G

/-- The support-connector event for the adaptive mixed edge set. -/
noncomputable def rlc_mixedAdaptiveConnectorEvent {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  match rlc_axisBarrierGap? gamma gamma' with
  | none => Set.univ
  | some G => rlc_mixedAxisGapConnectorEvent G

lemma rlc_mixedAdaptiveConnectorEvent_dependsOn {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DependsOn ((rlc_mixedAdaptiveConnectorEvent gamma gamma').indicator
      (fun _ => (1 : ℝ)))
      (rlc_mixedAdaptiveEdges gamma gamma' : Set (Sym2 (Site 2))) := by
  unfold rlc_mixedAdaptiveConnectorEvent rlc_mixedAdaptiveEdges
  split
  · intro omega omega' _hagree
    simp
  · exact rlc_mixedAxisGapConnectorEvent_dependsOn _

lemma rlc_mixedAdaptiveConnectorEvent_measurableSet {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    MeasurableSet (rlc_mixedAdaptiveConnectorEvent gamma gamma') :=
  measurableSet_of_dependsOn
    (rlc_mixedAdaptiveConnectorEvent_dependsOn gamma gamma')

lemma rlc_rightPathEdges_disjoint_mixedAdaptiveEdges {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Disjoint (rlc_pathEdges gamma.1)
      (rlc_mixedAdaptiveEdges gamma gamma') := by
  unfold rlc_mixedAdaptiveEdges
  split
  · simp
  · exact rlc_rightPathEdges_disjoint_mixedAxisGapEdges _

lemma rlc_leftPathEdges_disjoint_mixedAdaptiveEdges {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Disjoint (rlc_pathEdges gamma'.1)
      (rlc_mixedAdaptiveEdges gamma gamma') := by
  unfold rlc_mixedAdaptiveEdges
  split
  · simp
  · exact rlc_leftPathEdges_disjoint_mixedAxisGapEdges _

lemma rlc_mixedAdaptiveConnector_glues_horizontal (n : ℤ) (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩
        rlc_mixedAdaptiveConnectorEvent gamma gamma' ⊆
      horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
  intro omega homega
  obtain ⟨⟨hgamma, hgamma'⟩, hconnector⟩ := homega
  by_cases hdisj : Disjoint
      (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)
  · obtain ⟨G, hG⟩ :=
      rlc_axisBarrierGap?_eq_some_of_disjoint gamma gamma' hdisj
    have hmixed : omega ∈ rlc_mixedAxisGapConnectorEvent G := by
      simpa [rlc_mixedAdaptiveConnectorEvent, hG] using hconnector
    exact rlc_mixedAxisGapConnector_glues_horizontal n hn gamma gamma' G
      ⟨⟨hgamma, hgamma'⟩, hmixed⟩
  · obtain ⟨z, hz, hz'⟩ := Finset.not_disjoint_iff.mp hdisj
    apply rlc_connector_glues_horizontal n hn gamma gamma'
    exact ⟨⟨hgamma, hgamma'⟩,
      rlc_mem_connectorEvent_of_common_vertex gamma gamma' omega hz hz'⟩

/-- The configuration with the edges of both paths forced open and the rest restricted to `U`. -/
noncomputable def rlc_wiredConnectorConfig {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2)))
    (omega : ConfigSpace (Sym2 (Site 2))) :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => if e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 then true
    else rlc_maskConfig U omega e

lemma rlc_wiredConnectorConfig_congr {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2)))
    {omega omega' : ConfigSpace (Sym2 (Site 2))}
    (hagree : ∀ e ∈ (U : Set (Sym2 (Site 2))), omega e = omega' e) :
    rlc_wiredConnectorConfig gamma gamma' U omega =
      rlc_wiredConnectorConfig gamma gamma' U omega' := by
  have hmask : rlc_maskConfig U omega = rlc_maskConfig U omega' :=
    rlc_maskConfig_congr hagree
  funext e
  simp only [rlc_wiredConnectorConfig, hmask]

lemma rlc_wiredConnectorConfig_mono {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2)))
    {omega omega' : ConfigSpace (Sym2 (Site 2))} (h : omega ≤ omega') :
    rlc_wiredConnectorConfig gamma gamma' U omega ≤
      rlc_wiredConnectorConfig gamma gamma' U omega' := by
  intro e
  by_cases hp : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
  · simp [rlc_wiredConnectorConfig, hp]
  · simp only [rlc_wiredConnectorConfig, ite_eq_right hp]
    exact rlc_maskConfig_mono U h e

lemma rlc_dualReflect_wired_open_of_support {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {e : Sym2 (Site 2)}
    (heTarget : e ∈
      (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
        rlc_mixedAxisGapEdges G)
    (heSource : rlc_pimsEdgeEquiv e ∈ rlc_mixedAxisGapEdges G)
    (hopen : rlc_dualReflectConfig
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega) e = true) :
    rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G)
      (rlc_dualReflectConfig omega) e = true := by
  have hsourceNotPaths : rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
    intro he
    rw [Finset.mem_union] at he
    rcases he with he | he
    · exact (Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_mixedAxisGapEdges G)) he heSource
    · exact (Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_mixedAxisGapEdges G)) he heSource
  have hrawOpen : rlc_dualReflectConfig omega e = true := by
    rw [rlc_dualReflectConfig_eq_pims] at hopen ⊢
    rw [rlc_wiredConnectorConfig, ite_eq_right hsourceNotPaths,
      rlc_maskConfig, ite_eq_left heSource] at hopen
    exact hopen
  rw [Finset.mem_union] at heTarget
  rcases heTarget with hePath | heU
  · simp [rlc_wiredConnectorConfig, hePath]
  · by_cases hePath : e ∈
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
    · simp [rlc_wiredConnectorConfig, hePath]
    · simp [rlc_wiredConnectorConfig, hePath, rlc_maskConfig, heU,
        hrawOpen]

lemma rlc_dualReflect_wired_walk_of_support {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (p : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega))).Walk x y)
    (hsupport : ∀ e ∈ p.edges,
      e ∈ (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
          rlc_mixedAxisGapEdges G ∧
        rlc_pimsEdgeEquiv e ∈ rlc_mixedAxisGapEdges G) :
    ∃ q : (openSubgraph 2
      (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G)
        (rlc_dualReflectConfig omega))).Walk x y,
      q.edges = p.edges ∧ q.support = p.support := by
  let H := openSubgraph 2
    (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G)
      (rlc_dualReflectConfig omega))
  have htransfer : ∀ e ∈ p.edges, e ∈ H.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have hadj := p.adj_of_mem_edges he
        rw [openSubgraph_adj] at hadj
        rw [SimpleGraph.mem_edgeSet, openSubgraph_adj]
        exact ⟨hadj.1, rlc_dualReflect_wired_open_of_support
          G omega (hsupport s(u, v) he).1 (hsupport s(u, v) he).2
            hadj.2⟩
  let q := p.transfer H htransfer
  exact ⟨q, p.edges_transfer htransfer, p.support_transfer htransfer⟩

lemma rlc_wiredConnectorConfig_le_of_pathOpen {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2)))
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hgamma : omega ∈ rlc_pathOpen gamma.1)
    (hgamma' : omega ∈ rlc_pathOpen gamma'.1) :
    rlc_wiredConnectorConfig gamma gamma' U omega ≤ omega := by
  intro e
  by_cases hp : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
  · have hopen : omega e = true := by
      rw [Finset.mem_union] at hp
      rcases hp with hp | hp
      · exact hgamma e hp
      · exact hgamma' e hp
    rw [rlc_wiredConnectorConfig, ite_eq_left hp, hopen]
  · rw [rlc_wiredConnectorConfig, ite_eq_right hp]
    exact rlc_maskConfig_le U omega e

/-- The event that the lower and upper gap vertices are connected in the wired connector
  configuration. -/
noncomputable def rlc_mixedWiredConnectorEvent {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | ConnectedWithin 2
    (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega)
    (rect (-2 * n) (2 * n) (-n) n)
    ⟨G.lowerVertex,
      rlc_rightPathVertex_mem_connectorBox gamma G.lowerVertex_mem_right⟩
    ⟨G.upperVertex,
      rlc_leftPathVertex_mem_connectorBox gamma' G.upperVertex_mem_left⟩}

lemma rlc_mixedWiredConnectorEvent_isIncreasing {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    IsIncreasing (rlc_mixedWiredConnectorEvent G) := by
  intro omega omega' hle hconn
  exact StatMech.TwoDim.connectedWithin_mono
    (rlc_wiredConnectorConfig_mono gamma gamma'
      (rlc_mixedAxisGapEdges G) hle) hconn

lemma rlc_mixedWiredConnectorEvent_dependsOn {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    DependsOn ((rlc_mixedWiredConnectorEvent G).indicator
      (fun _ => (1 : ℝ)))
      (rlc_mixedAxisGapEdges G : Set (Sym2 (Site 2))) := by
  intro omega omega' hagree
  have hcfg := rlc_wiredConnectorConfig_congr gamma gamma'
    (rlc_mixedAxisGapEdges G) hagree
  have hevent : omega ∈ rlc_mixedWiredConnectorEvent G ↔
      omega' ∈ rlc_mixedWiredConnectorEvent G := by
    simp only [rlc_mixedWiredConnectorEvent, Set.mem_ofPred_eq, hcfg]
  by_cases hmem : omega ∈ rlc_mixedWiredConnectorEvent G
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]

lemma rlc_mixedWiredConnectorEvent_measurableSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    MeasurableSet (rlc_mixedWiredConnectorEvent G) :=
  measurableSet_of_dependsOn (rlc_mixedWiredConnectorEvent_dependsOn G)

lemma rlc_mixedWiredConnector_half_of_dual_reflection {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdual : ∀ omega : ConfigSpace (Sym2 (Site 2)),
      omega ∉ rlc_mixedWiredConnectorEvent G →
      rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G) :
    (1 : ℝ) / 2 ≤
      halfMeasure.real (rlc_mixedWiredConnectorEvent G) := by
  apply rlc_connector_half_of_dual_reflection halfMeasure
    rlc_dualReflectConfig rlc_dualReflectConfig_measurePreserving
    (rlc_mixedWiredConnectorEvent G)
    (rlc_mixedWiredConnectorEvent_measurableSet G)
  intro omega hno
  exact hdual omega hno

lemma rlc_mixedWiredConnector_glues_horizontal (n : ℤ) (_hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (G : RlcAxisBarrierGap gamma gamma') :
    rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩
        rlc_mixedWiredConnectorEvent G ⊆
      horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
  intro omega homega
  obtain ⟨⟨hgamma, hgamma'⟩, hwire⟩ := homega
  have hconn : ConnectedWithin 2 omega
      (rect (-2 * n) (2 * n) (-n) n)
      ⟨G.lowerVertex,
        rlc_rightPathVertex_mem_connectorBox gamma G.lowerVertex_mem_right⟩
      ⟨G.upperVertex,
        rlc_leftPathVertex_mem_connectorBox gamma' G.upperVertex_mem_left⟩ :=
    StatMech.TwoDim.connectedWithin_mono
      (rlc_wiredConnectorConfig_le_of_pathOpen
        gamma gamma' (rlc_mixedAxisGapEdges G) omega hgamma hgamma') hwire
  obtain ⟨_hlowerSmall, hlowerRightSmall⟩ :=
    rlc_pathOpen_connected_finish gamma.1 omega hgamma G.lowerVertex_mem_right
  obtain ⟨_hupperSmall, hleftUpperSmall⟩ :=
    rlc_pathOpen_connected_start gamma'.1 omega hgamma' G.upperVertex_mem_left
  have hrightSub : rect 0 (2 * n) (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hleftSub : rect (-2 * n) 0 (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hlowerRight := StatMech.Lattice.connectedWithin_mono_set omega
    hrightSub hlowerRightSmall
  have hleftUpper := StatMech.Lattice.connectedWithin_mono_set omega
    hleftSub hleftUpperSmall
  let xL : leftSide (-2 * n) (2 * n) (-n) n :=
    ⟨gamma'.1.1, by
      rw [mem_leftSide, mem_rect]
      have h := gamma'.1.1.2
      rw [mem_leftSide, mem_rect] at h
      exact ⟨⟨by omega, by omega, h.1.2.2.1, h.1.2.2.2⟩, h.2⟩⟩
  let yR : rightSide (-2 * n) (2 * n) (-n) n :=
    ⟨gamma.1.2.1, by
      rw [mem_rightSide, mem_rect]
      have h := gamma.1.2.1.2
      rw [mem_rightSide, mem_rect] at h
      exact ⟨⟨by omega, by omega, h.1.2.2.1, h.1.2.2.2⟩, h.2⟩⟩
  refine ⟨xL, yR, ?_⟩
  exact hleftUpper.trans (hconn.symm.trans hlowerRight)

lemma rlc_wiredConnectorConfig_rightPathOpen {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2)))
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_wiredConnectorConfig gamma gamma' U omega ∈
      rlc_pathOpen gamma.1 := by
  intro e he
  simp [rlc_wiredConnectorConfig, he]

lemma rlc_wiredConnectorConfig_leftPathOpen {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2)))
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_wiredConnectorConfig gamma gamma' U omega ∈
      rlc_pathOpen gamma'.1 := by
  intro e he
  simp [rlc_wiredConnectorConfig, he]

lemma rlc_maskConfig_le_wiredConnectorConfig {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2)))
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_maskConfig U omega ≤
      rlc_wiredConnectorConfig gamma gamma' U omega := by
  intro e
  by_cases hp : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 <;>
    simp [rlc_wiredConnectorConfig, hp]

lemma rlc_mixedAxisGapConnectorEvent_subset_mixedWiredConnectorEvent {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    rlc_mixedAxisGapConnectorEvent G ⊆
      rlc_mixedWiredConnectorEvent G := by
  intro omega hconn
  obtain ⟨x, hxPath, y, hyPath, hxR, hyR, hxyMask⟩ := hconn
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  have hrightOpen : eta ∈ rlc_pathOpen gamma.1 :=
    rlc_wiredConnectorConfig_rightPathOpen gamma gamma'
      (rlc_mixedAxisGapEdges G) omega
  have hleftOpen : eta ∈ rlc_pathOpen gamma'.1 :=
    rlc_wiredConnectorConfig_leftPathOpen gamma gamma'
      (rlc_mixedAxisGapEdges G) omega
  obtain ⟨hlowerR, hstartLower⟩ :=
    rlc_pathOpen_connected_start gamma.1 eta hrightOpen
      G.lowerVertex_mem_right
  obtain ⟨_hxSmall, hstartX⟩ :=
    rlc_pathOpen_connected_start gamma.1 eta hrightOpen hxPath
  obtain ⟨_hySmall, hleftStartY⟩ :=
    rlc_pathOpen_connected_start gamma'.1 eta hleftOpen hyPath
  obtain ⟨hupperR, hleftStartUpper⟩ :=
    rlc_pathOpen_connected_start gamma'.1 eta hleftOpen
      G.upperVertex_mem_left
  have hrightSub : rect 0 (2 * n) (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hleftSub : rect (-2 * n) 0 (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hlowerFull : G.lowerVertex ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_rightPathVertex_mem_connectorBox gamma G.lowerVertex_mem_right
  have hupperFull : G.upperVertex ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_leftPathVertex_mem_connectorBox gamma' G.upperVertex_mem_left
  have hlowerX : ConnectedWithin 2 eta
      (rect (-2 * n) (2 * n) (-n) n)
      ⟨G.lowerVertex, hlowerFull⟩ ⟨x, hxR⟩ := by
    simpa only using
      (StatMech.Lattice.connectedWithin_mono_set eta hrightSub
        hstartLower).symm.trans
          (StatMech.Lattice.connectedWithin_mono_set eta hrightSub hstartX)
  have hyUpper : ConnectedWithin 2 eta
      (rect (-2 * n) (2 * n) (-n) n)
      ⟨y, hyR⟩ ⟨G.upperVertex, hupperFull⟩ := by
    simpa only using
      (StatMech.Lattice.connectedWithin_mono_set eta hleftSub
        hleftStartY).symm.trans
          (StatMech.Lattice.connectedWithin_mono_set eta hleftSub
            hleftStartUpper)
  have hxy : ConnectedWithin 2 eta
      (rect (-2 * n) (2 * n) (-n) n) ⟨x, hxR⟩ ⟨y, hyR⟩ :=
    StatMech.TwoDim.connectedWithin_mono
      (rlc_maskConfig_le_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega) hxyMask
  exact hlowerX.trans (hxy.trans hyUpper)

/-- The sites reachable from the lower gap vertex in the wired connector configuration. -/
def rlc_mixedWiredReachSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Set (Site 2) :=
  {z | ∃ (hzR : z ∈ rect (-2 * n) (2 * n) (-n) n),
    ConnectedWithin 2
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega)
      (rect (-2 * n) (2 * n) (-n) n)
      ⟨G.lowerVertex,
        rlc_rightPathVertex_mem_connectorBox gamma G.lowerVertex_mem_right⟩
      ⟨z, hzR⟩}

lemma rlc_mixedWiredReachSet_subset_box {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_mixedWiredReachSet G omega ⊆
      rect (-2 * n) (2 * n) (-n) n := by
  rintro z ⟨hzR, _⟩
  exact hzR

lemma rlc_mixedWiredReachSet_finite {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (rlc_mixedWiredReachSet G omega).Finite :=
  (rect_finite (-2 * n) (2 * n) (-n) n).subset
    (rlc_mixedWiredReachSet_subset_box G omega)

lemma RlcAxisBarrierGap.lowerVertex_mem_mixedWiredReachSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    G.lowerVertex ∈ rlc_mixedWiredReachSet G omega := by
  exact ⟨rlc_rightPathVertex_mem_connectorBox gamma G.lowerVertex_mem_right,
    connectedWithin_refl _ _ _⟩

lemma rlc_rightPathVertex_mem_mixedWiredReachSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {x : Site 2}
    (hx : x ∈ rlc_pathVertices gamma.1) :
    x ∈ rlc_mixedWiredReachSet G omega := by
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  have hopen : eta ∈ rlc_pathOpen gamma.1 :=
    rlc_wiredConnectorConfig_rightPathOpen gamma gamma'
      (rlc_mixedAxisGapEdges G) omega
  obtain ⟨hlR, hstartLower⟩ :=
    rlc_pathOpen_connected_start gamma.1 eta hopen G.lowerVertex_mem_right
  obtain ⟨hxR, hstartX⟩ := rlc_pathOpen_connected_start gamma.1 eta hopen hx
  refine ⟨rlc_rightPathVertex_mem_connectorBox gamma hx, ?_⟩
  have hsub : rect 0 (2 * n) (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  exact (StatMech.Lattice.connectedWithin_mono_set eta hsub
    hstartLower).symm.trans
      (StatMech.Lattice.connectedWithin_mono_set eta hsub hstartX)

lemma rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    {y : Site 2} (hy : y ∈ rlc_pathVertices gamma'.1) :
    y ∉ rlc_mixedWiredReachSet G omega := by
  rintro ⟨hyR, hlowerY⟩
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  have hopen : eta ∈ rlc_pathOpen gamma'.1 :=
    rlc_wiredConnectorConfig_leftPathOpen gamma gamma'
      (rlc_mixedAxisGapEdges G) omega
  obtain ⟨hySmall, hstartY⟩ :=
    rlc_pathOpen_connected_start gamma'.1 eta hopen hy
  obtain ⟨huSmall, hstartUpper⟩ :=
    rlc_pathOpen_connected_start gamma'.1 eta hopen G.upperVertex_mem_left
  have hsub : rect (-2 * n) 0 (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hyUpper : ConnectedWithin 2 eta
      (rect (-2 * n) (2 * n) (-n) n) ⟨y, hyR⟩
      ⟨G.upperVertex,
        rlc_leftPathVertex_mem_connectorBox gamma' G.upperVertex_mem_left⟩ :=
    (StatMech.Lattice.connectedWithin_mono_set eta hsub hstartY).symm.trans
      (StatMech.Lattice.connectedWithin_mono_set eta hsub hstartUpper)
  exact hno (hlowerY.trans hyUpper)

lemma rlc_mixedWiredReachSet_axis_boundary {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ p q : Site 2,
      (p, q) ∈ edgeBoundary 2 (rlc_mixedWiredReachSet G omega) ∧
      p 0 = 0 ∧ q 0 = 0 := by
  have hlower := G.lowerVertex_mem_mixedWiredReachSet omega
  have hupper : G.upperVertex ∉ rlc_mixedWiredReachSet G omega :=
    rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
      G omega hno G.upperVertex_mem_left
  let w : (hypercubicLattice 2).Walk G.lowerVertex G.upperVertex :=
    sw_vertSeg 0 G.lower G.upper
  obtain ⟨p, q, hpq, hpqEdge⟩ :=
    rlc_walk_mem_edgeBoundary_edges
      (rlc_mixedWiredReachSet G omega) w hlower hupper
  have hpSupp : p ∈ w.support := w.fst_mem_support_of_mem_edges hpqEdge
  have hqSupp : q ∈ w.support := w.snd_mem_support_of_mem_edges hpqEdge
  have haxis (z : Site 2) (hz : z ∈ w.support) : z 0 = 0 := by
    change z ∈ (sw_vertSeg 0 G.lower G.upper).support at hz
    rw [sw_vertSeg_mem_support] at hz
    obtain ⟨t, _ht, rfl⟩ := hz
    simp
  exact ⟨p, q, hpq, haxis p hpSupp, haxis q hqSupp⟩

lemma rlc_mixedWiredReachSet_verticalGap_boundary {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ t : ℤ, G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      ((![0, t], ![0, t + 1]) ∈
        edgeBoundary 2 (rlc_mixedWiredReachSet G omega)) := by
  classical
  let S := rlc_mixedWiredReachSet G omega
  have hlower : ![0, G.lower] ∈ S := by
    simpa [S, RlcAxisBarrierGap.lowerVertex] using
      G.lowerVertex_mem_mixedWiredReachSet omega
  have hupper : ![0, G.upper] ∉ S := by
    simpa [S, RlcAxisBarrierGap.upperVertex] using
      (rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
        G omega hno G.upperVertex_mem_left)
  let A : Finset ℤ := (Finset.Icc G.lower G.upper).filter
    (fun t => ![0, t] ∈ S)
  have hlowerA : G.lower ∈ A := by
    simp [A, hlower, le_of_lt G.lower_lt_upper]
  have hA : A.Nonempty := ⟨G.lower, hlowerA⟩
  let t := A.max' hA
  have htA : t ∈ A := A.max'_mem hA
  have htBounds : G.lower ≤ t ∧ t ≤ G.upper := by
    simpa [A] using (Finset.mem_filter.mp htA).1
  have htS : ![0, t] ∈ S := (Finset.mem_filter.mp htA).2
  have htlt : t < G.upper := by
    apply lt_of_le_of_ne htBounds.2
    intro h
    exact hupper (h ▸ htS)
  have hsuccNot : ![0, t + 1] ∉ S := by
    intro hsucc
    have hsuccA : t + 1 ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hsucc⟩
    have hmax := A.le_max' (t + 1) hsuccA
    change t + 1 ≤ t at hmax
    omega
  have hadj : (hypercubicLattice 2).Adj
      (![0, t] : Site 2) ![0, t + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ⟨t, htBounds.1, htlt, htS, hsuccNot,
    ⟨hadj, iff_of_true htS hsuccNot⟩⟩

lemma rlc_mem_connectorBox_flipX {n : ℤ} (z : Site 2) :
    z ∈ rect (-2 * n) (2 * n) (-n) n ↔
      rlc_flipX z ∈ rect (-2 * n) (2 * n) (-n) n := by
  have hzero : rlc_flipX z 0 = -z 0 := rfl
  have hone : rlc_flipX z 1 = z 1 := rfl
  simp only [mem_rect, hzero, hone]
  omega

lemma rlc_reflectedRightPathEdge_endpoint_mem_box {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {e : Sym2 (Site 2)}
    (he : e ∈ rlc_reflectedPathEdges gamma.1) {z : Site 2}
    (hz : z ∈ e) : z ∈ rect (-2 * n) (2 * n) (-n) n := by
  obtain ⟨e0, he0, heq⟩ := Finset.mem_image.mp he
  induction e0 using Sym2.inductionOn with
  | _ x y =>
    have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he0
    have hxR := rlc_rightPathVertex_mem_connectorBox gamma hends.1
    have hyR := rlc_rightPathVertex_mem_connectorBox gamma hends.2
    have heq' : e = s(rlc_flipX x, rlc_flipX y) := by
      simpa [Sym2.map_mk] using heq.symm
    rw [heq', Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact (rlc_mem_connectorBox_flipX x).mp hxR
    · exact (rlc_mem_connectorBox_flipX y).mp hyR

lemma rlc_reflectedLeftPathEdge_endpoint_mem_box {n : ℤ}
    (gamma' : RlcLeftDiagonalPath n) {e : Sym2 (Site 2)}
    (he : e ∈ rlc_reflectedPathEdges gamma'.1) {z : Site 2}
    (hz : z ∈ e) : z ∈ rect (-2 * n) (2 * n) (-n) n := by
  obtain ⟨e0, he0, heq⟩ := Finset.mem_image.mp he
  induction e0 using Sym2.inductionOn with
  | _ x y =>
    have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 he0
    have hxR := rlc_leftPathVertex_mem_connectorBox gamma' hends.1
    have hyR := rlc_leftPathVertex_mem_connectorBox gamma' hends.2
    have heq' : e = s(rlc_flipX x, rlc_flipX y) := by
      simpa [Sym2.map_mk] using heq.symm
    rw [heq', Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact (rlc_mem_connectorBox_flipX x).mp hxR
    · exact (rlc_mem_connectorBox_flipX y).mp hyR

lemma rlc_mixedAxisGapEdges_endpoints_mem_box {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) {v w : Site 2}
    (he : s(v, w) ∈ rlc_mixedAxisGapEdges G) :
    v ∈ rect (-2 * n) (2 * n) (-n) n ∧
      w ∈ rect (-2 * n) (2 * n) (-n) n := by
  have heUnion := (Finset.mem_sdiff.mp he).1
  simp only [Finset.mem_union] at heUnion
  rcases heUnion with heUnion | heLeft
  · rcases heUnion with heGap | heRight
    · exact rlc_axisGapEdges_endpoints_mem_box G hn hlt heGap
    · exact ⟨rlc_reflectedRightPathEdge_endpoint_mem_box gamma heRight
        (Sym2.mem_mk_left v w),
        rlc_reflectedRightPathEdge_endpoint_mem_box gamma heRight
          (Sym2.mem_mk_right v w)⟩
  · exact ⟨rlc_reflectedLeftPathEdge_endpoint_mem_box gamma' heLeft
      (Sym2.mem_mk_left v w),
      rlc_reflectedLeftPathEdge_endpoint_mem_box gamma' heLeft
        (Sym2.mem_mk_right v w)⟩

lemma rlc_exposedPathEdges_endpoints_mem_box {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {v w : Site 2}
    (he : s(v, w) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    v ∈ rect (-2 * n) (2 * n) (-n) n ∧
      w ∈ rect (-2 * n) (2 * n) (-n) n := by
  rw [Finset.mem_union] at he
  rcases he with he | he
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he
    exact ⟨rlc_rightPathVertex_mem_connectorBox gamma hends.1,
      rlc_rightPathVertex_mem_connectorBox gamma hends.2⟩
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 he
    exact ⟨rlc_leftPathVertex_mem_connectorBox gamma' hends.1,
      rlc_leftPathVertex_mem_connectorBox gamma' hends.2⟩

lemma rlc_mixedWiredReachSet_extend {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hv : v ∈ rlc_mixedWiredReachSet G omega)
    (hwR : w ∈ rect (-2 * n) (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hopen : rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega s(v, w) = true) :
    w ∈ rlc_mixedWiredReachSet G omega := by
  obtain ⟨hvR, hlowerV⟩ := hv
  refine ⟨hwR, hlowerV.trans ?_⟩
  have hstep : (openSubgraphInduce 2
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega)
      (rect (-2 * n) (2 * n) (-n) n)).Adj ⟨v, hvR⟩ ⟨w, hwR⟩ := by
    rw [openSubgraphInduce_adj]
    exact ⟨hadj, hopen⟩
  exact hstep.reachable

lemma rlc_mixedWiredReachSet_boundary_closed {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hv : v ∈ rlc_mixedWiredReachSet G omega)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hw : w ∉ rlc_mixedWiredReachSet G omega) :
    rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega s(v, w) = false := by
  by_cases hwR : w ∈ rect (-2 * n) (2 * n) (-n) n
  · by_contra hopen
    rw [Bool.not_eq_false] at hopen
    exact hw (rlc_mixedWiredReachSet_extend G omega hv hwR hadj hopen)
  · have hnotPaths : s(v, w) ∉
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
      intro he
      exact hwR (rlc_exposedPathEdges_endpoints_mem_box he).2
    have hnotU : s(v, w) ∉ rlc_mixedAxisGapEdges G := by
      intro he
      exact hwR (rlc_mixedAxisGapEdges_endpoints_mem_box G hn hlt he).2
    simp [rlc_wiredConnectorConfig, hnotPaths, rlc_maskConfig, hnotU]

lemma rlc_mixedWiredReachSet_edgeBoundary_closed {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hvw : (v, w) ∈ edgeBoundary 2 (rlc_mixedWiredReachSet G omega)) :
    rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega s(v, w) = false := by
  obtain ⟨hadj, hsplit⟩ := hvw
  by_cases hv : v ∈ rlc_mixedWiredReachSet G omega
  · exact rlc_mixedWiredReachSet_boundary_closed G hn hlt omega hv hadj
      (hsplit.mp hv)
  · have hw : w ∈ rlc_mixedWiredReachSet G omega := by
      by_contra hw
      exact hv (hsplit.mpr hw)
    rw [Sym2.eq_swap]
    exact rlc_mixedWiredReachSet_boundary_closed G hn hlt omega hw hadj.symm hv

lemma rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    faceBoundaryGraph (rlc_mixedWiredReachSet G omega) ≤
      openSubgraph 2 (fci_faceDualConfig
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)) := by
  intro f g hfg
  obtain ⟨p, q, hpq, hadjPQ⟩ :=
    sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_mixedWiredReachSet G omega) := by
    refine ⟨hadjPQ, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hclosed := rlc_mixedWiredReachSet_edgeBoundary_closed
    G hn hlt omega hpqBoundary
  refine ⟨hfg.1, ?_⟩
  rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1, hpq]
  simpa using hclosed

lemma rlc_mixedWiredReachSet_axis_anchored_dualCircuit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ (t : ℤ) (f g u : Site 2)
      (c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u u),
      G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g ∧
      sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  classical
  obtain ⟨t, htlower, htupper, htIn, htOut, hpq⟩ :=
    rlc_mixedWiredReachSet_verticalGap_boundary G omega hno
  obtain ⟨f, g, hfgLat, hshared⟩ := jfc_flankingFaces hpq.1
  have hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact hpq.2
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph
    (rlc_mixedWiredReachSet G omega)
    (rlc_mixedWiredReachSet_finite G omega)
  obtain ⟨u, c, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)) T hT
      (degree_faceBoundaryGraph_even (rlc_mixedWiredReachSet G omega)) hfg
  exact ⟨t, f, g, u, c, htlower, htupper, htIn, htOut,
    hfg, hshared, hcyc, hedge⟩

lemma rlc_mixedWiredReachSet_openFaceDualCircuit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ (t : ℤ) (f g u : Site 2)
      (c : (openSubgraph 2 (fci_faceDualConfig
        (rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega))).Walk u u),
      G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      (hypercubicLattice 2).Adj f g ∧
      sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  obtain ⟨t, f, g, u, c, htlower, htupper, htIn, htOut, hfg,
      hshared, hcyc, hedge⟩ :=
    rlc_mixedWiredReachSet_axis_anchored_dualCircuit G omega hno
  let hle := rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega
  refine ⟨t, f, g, u, c.mapLe hle, htlower, htupper, htIn, htOut,
    hfg.1, hshared,
    hcyc.mapLe hle, ?_⟩
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  exact hedge

lemma rlc_mixedWiredReachSet_reflectedOpenDualCircuit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ (t : ℤ) (u : Site 2)
      (c : (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega))).Walk
          (rlc_dualReflect u) (rlc_dualReflect u)),
      G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      c.IsCycle ∧
      s(![-1, t + 1], ![0, t + 1]) ∈ c.edges := by
  obtain ⟨t, f, g, u, c, htlower, htupper, htIn, htOut, hfg,
      hshared, hcyc, hedge⟩ :=
    rlc_mixedWiredReachSet_openFaceDualCircuit G hn hlt omega hno
  let hom := rlc_dualReflectOpenHom
    (rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega)
  refine ⟨t, u, rlc_dualReflectOpenWalk _ c,
    htlower, htupper, htIn, htOut,
    rlc_dualReflectOpenWalk_isCycle _ hcyc, ?_⟩
  have hEdges : (c.map hom).edges = c.edges.map (Sym2.map hom) :=
    SimpleGraph.Walk.edges_map hom c
  have hmapped : Sym2.map hom s(f, g) ∈
      c.edges.map (Sym2.map hom) := List.mem_map_of_mem hedge
  have hedgeEq : Sym2.map hom s(f, g) =
      s(rlc_dualReflect f, rlc_dualReflect g) := by
    rfl
  have hreflected : s(rlc_dualReflect f, rlc_dualReflect g) =
      s(![-1, t + 1], ![0, t + 1]) :=
    rlc_reflectedEdge_eq_horizontal_of_shared_vertical hfg hshared
  change s(![-1, t + 1], ![0, t + 1]) ∈ (c.map hom).edges
  rw [← hreflected]
  exact hedgeEq ▸ hEdges.symm ▸ hmapped

lemma rlc_mixedWiredReachSet_reflectedOpenDualComplementaryArc {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ t : ℤ, G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      ∃ p : (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega))).Walk
          ![-1, t + 1] ![0, t + 1],
        s(![-1, t + 1], ![0, t + 1]) ∉ p.edges := by
  obtain ⟨t, u, c, htlower, htupper, htIn, htOut, hcyc, hedge⟩ :=
    rlc_mixedWiredReachSet_reflectedOpenDualCircuit G hn hlt omega hno
  let H := openSubgraph 2 (rlc_dualReflectConfig
    (rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega))
  have hreach : (H.deleteEdges
      {s(![-1, t + 1], ![0, t + 1])}).Reachable
        ![-1, t + 1] ![0, t + 1] :=
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
      (G := H)).mpr ⟨rlc_dualReflect u, c, hcyc, hedge⟩ |>.2
  obtain ⟨p, hp⟩ :=
    (SimpleGraph.reachable_deleteEdges_iff_exists_walk (G := H)).mp hreach
  exact ⟨t, htlower, htupper, htIn, htOut, p, hp⟩

lemma rlc_mixedWiredFailure_reflectedAnchor_open_raw {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ t : ℤ, G.lower ≤ t ∧ t < G.upper ∧
      rlc_dualReflectConfig omega
        s(![-1, t + 1], ![0, t + 1]) = true := by
  obtain ⟨t, htlower, htupper, htIn, htOut, hpq⟩ :=
    rlc_mixedWiredReachSet_verticalGap_boundary G omega hno
  let e : Sym2 (Site 2) := s(![0, t], ![0, t + 1])
  have hU : e ∈ rlc_mixedAxisGapEdges G := by
    exact G.verticalEdge_mem_mixedAxisGapEdges hn hlt htlower htupper
  have hnotPaths : e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
    intro he
    rw [Finset.mem_union] at he
    rcases he with he | he
    · exact (Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_mixedAxisGapEdges G)) he hU
    · exact (Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_mixedAxisGapEdges G)) he hU
  have hclosed := rlc_mixedWiredReachSet_boundary_closed
    G hn hlt omega htIn hpq.1 htOut
  have homega : omega e = false := by
    change rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega e = false at hclosed
    rw [rlc_wiredConnectorConfig, ite_eq_right hnotPaths,
      rlc_maskConfig, ite_eq_left hU] at hclosed
    exact hclosed
  refine ⟨t, htlower, htupper, ?_⟩
  have hpims : rlc_pimsEdgeEquiv
      s(![-1, t + 1], ![0, t + 1]) = e := by
    simpa [e] using (rlc_pimsEdgeEquiv_horizontal (-1) (t + 1))
  rw [rlc_dualReflectConfig_eq_pims, hpims, homega]
  rfl

end Universality

end StatMech
