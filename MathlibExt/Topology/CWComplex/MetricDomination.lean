/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.FiniteRelativeApproximation
public import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# CW domination of metric spaces with local interpolation

The specified local interpolation constructs the locally finite pointed cover,
weak nerve, original forward/reverse maps and complete relative domination homotopy.
Open subsets of real normed spaces supply that interpolation from their convex balls.
-/

noncomputable section
set_option autoImplicit false

open Set Function Filter Topology
open scoped unitInterval NNReal BigOperators

universe u

namespace Topology.CWComplex.MetricDomination

private def pairFirst {M : Type u} [TopologicalSpace M] (U : Set (M × M)) : C(U, M) :=
  ⟨fun z => z.val.1, continuous_fst.comp continuous_subtype_val⟩

private def pairSecond {M : Type u} [TopologicalSpace M] (U : Set (M × M)) : C(U, M) :=
  ⟨fun z => z.val.2, continuous_snd.comp continuous_subtype_val⟩

/-- Local interpolation data with convex neighborhoods and exact diagonal stationarity. -/
public structure Interpolation (M : Type u) [TopologicalSpace M] where
  /-- Pairs joined by the original interpolation. -/
  domain : Set (M × M)
  /-- The jointly continuous interpolation from the first point to the second point. -/
  homotopy : ContinuousMap.Homotopy
    (⟨fun z => z.val.1, continuous_fst.comp continuous_subtype_val⟩ : C(domain, M))
    (⟨fun z => z.val.2, continuous_snd.comp continuous_subtype_val⟩ : C(domain, M))
  /-- Every diagonal pair stays fixed at every interpolation time. -/
  stationary : ∀ (x : M) (hx : (x, x) ∈ domain) (s : unitInterval),
    homotopy (s, ⟨(x, x), hx⟩) = x
  /-- A specified convex neighborhood of each point. -/
  neighborhood : M → Set M
  /-- The specified neighborhoods are open. -/
  neighborhood_open : ∀ x, IsOpen (neighborhood x)
  /-- Each neighborhood contains its specified point. -/
  neighborhood_mem : ∀ x, x ∈ neighborhood x
  /-- Every pair in one neighborhood belongs to the interpolation domain. -/
  neighborhood_square : ∀ x, ∀ a ∈ neighborhood x, ∀ b ∈ neighborhood x,
    (a, b) ∈ domain
  /-- The interpolation of any such pair stays in the same neighborhood. -/
  neighborhood_stable : ∀ x, ∀ a ∈ neighborhood x, ∀ b ∈ neighborhood x,
    ∀ (hab : (a, b) ∈ domain) (s : unitInterval),
      homotopy (s, ⟨(a, b), hab⟩) ∈ neighborhood x

private def IsConvex {M : Type u} [TopologicalSpace M] (c : Interpolation M)
    (B : Set M) : Prop :=
  (∀ a ∈ B, ∀ b ∈ B, (a, b) ∈ c.domain) ∧
  ∀ a ∈ B, ∀ b ∈ B, ∀ (hab : (a, b) ∈ c.domain) (s : unitInterval),
    c.homotopy (s, ⟨(a, b), hab⟩) ∈ B

private theorem neighborhood_convex {M : Type u} [TopologicalSpace M]
    (c : Interpolation M) (x : M) : IsConvex c (c.neighborhood x) :=
  ⟨c.neighborhood_square x, c.neighborhood_stable x⟩

section StarRefinement

variable {M : Type u} [MetricSpace M]

open Classical in
/-- Empty complements have protective radius one, not infDist(empty)=zero. -/
private def protectiveRadius (c : Interpolation M) (b x : M) : ℝ :=
  if (c.neighborhood b)ᶜ.Nonempty then
    min 1 (Metric.infDist x (c.neighborhood b)ᶜ) else 1

private theorem protectiveRadius_le_one (c : Interpolation M) (b x : M) :
    protectiveRadius c b x ≤ 1 := by
  unfold protectiveRadius
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

private theorem protectiveRadius_lipschitz (c : Interpolation M) (b : M) :
    LipschitzWith 1 (protectiveRadius c b) := by
  unfold protectiveRadius
  split_ifs
  · exact (Metric.lipschitz_infDist_pt ((c.neighborhood b)ᶜ)).const_min 1
  · exact LipschitzWith.const' 1

private theorem protectiveRadius_pos (c : Interpolation M) (x : M) :
    0 < protectiveRadius c x x := by
  unfold protectiveRadius
  split_ifs with hne
  · apply lt_min (by norm_num)
    exact ((c.neighborhood_open x).isClosed_compl.notMem_iff_infDist_pos hne).mp
      (by simpa using c.neighborhood_mem x)
  · norm_num

private def radius (c : Interpolation M) (x : M) : ℝ :=
  ⨆ b : M, protectiveRadius c b x

private theorem protectiveRadius_bddAbove (c : Interpolation M) (x : M) :
    BddAbove (Set.range (fun b : M => protectiveRadius c b x)) :=
  ⟨1, by rintro z ⟨b, rfl⟩; exact protectiveRadius_le_one c b x⟩

private theorem protectiveRadius_le_radius (c : Interpolation M) (b x : M) :
    protectiveRadius c b x ≤ radius c x :=
  le_ciSup (protectiveRadius_bddAbove c x) b

private theorem radius_pos (c : Interpolation M) (x : M) : 0 < radius c x :=
  (protectiveRadius_pos c x).trans_le (protectiveRadius_le_radius c x x)

private theorem radius_le_add (c : Interpolation M) (x y : M) :
    radius c x ≤ radius c y + dist x y := by
  let : Nonempty M := ⟨x⟩
  apply ciSup_le
  intro b
  have h := (protectiveRadius_lipschitz c b).le_add_mul x y
  simp only [NNReal.coe_one, one_mul] at h
  have hb := protectiveRadius_le_radius c b y
  linarith

private theorem exists_half_ball_control (c : Interpolation M) (x : M) :
    ∃ b : M, Metric.ball x (radius c x / 2) ⊆ c.neighborhood b := by
  let : Nonempty M := ⟨x⟩
  have hh : radius c x / 2 < radius c x := by linarith [radius_pos c x]
  obtain ⟨b, hb⟩ := exists_lt_of_lt_ciSup hh
  refine ⟨b, ?_⟩
  intro y hy
  unfold protectiveRadius at hb
  split_ifs at hb with hne
  · by_contra hny
    exact (Metric.notMem_of_dist_lt_infDist
      ((Metric.mem_ball'.mp hy).trans (hb.trans_le (min_le_right _ _)))) hny
  · have hcompl : (c.neighborhood b)ᶜ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    by_contra hny
    have hy' : y ∈ (c.neighborhood b)ᶜ := hny
    rw [hcompl] at hy'
    exact hy'

/-- Derive the point-star refinement using ordinary metric paracompactness. -/
private theorem exists_star_cover (c : Interpolation M) :
    ∃ W : M → Set M,
      (∀ i, IsOpen (W i)) ∧ (⋃ i, W i = Set.univ) ∧ LocallyFinite W ∧
      ∀ x : M, ∃ b : M, ∀ i : M, x ∈ W i → W i ⊆ c.neighborhood b := by
  let balls : M → Set M := fun i => Metric.ball i (radius c i / 8)
  have hopen : ∀ i, IsOpen (balls i) := fun _ => Metric.isOpen_ball
  have hcover : (⋃ i, balls i) = Set.univ := by
    rw [Set.iUnion_eq_univ_iff]
    intro x
    exact ⟨x, Metric.mem_ball_self (by linarith [radius_pos c x])⟩
  obtain ⟨W, hWopen, hWcover, hWfinite, hWsub⟩ := precise_refinement balls hopen hcover
  refine ⟨W, hWopen, hWcover, hWfinite, ?_⟩
  intro x
  obtain ⟨b, hb⟩ := exists_half_ball_control c x
  refine ⟨b, ?_⟩
  intro i hxi y hyi
  have hdix : dist i x < radius c i / 8 := Metric.mem_ball'.mp (hWsub i hxi)
  have hdiy : dist i y < radius c i / 8 := Metric.mem_ball'.mp (hWsub i hyi)
  have hr : radius c i ≤ radius c x + dist i x := radius_le_add c i x
  have ht : dist x y ≤ dist i x + dist i y := by
    simpa only [dist_comm x i] using dist_triangle x i y
  apply hb
  apply Metric.mem_ball'.mpr
  linarith [radius_pos c x]

private def starCover (c : Interpolation M) : M → Set M :=
  Classical.choose (exists_star_cover c)

private theorem starCover_open (c : Interpolation M) (i : M) : IsOpen (starCover c i) :=
  (Classical.choose_spec (exists_star_cover c)).1 i

private theorem starCover_covers (c : Interpolation M) :
    (⋃ i, starCover c i) = Set.univ :=
  (Classical.choose_spec (exists_star_cover c)).2.1

private theorem starCover_locallyFinite (c : Interpolation M) : LocallyFinite (starCover c) :=
  (Classical.choose_spec (exists_star_cover c)).2.2.1

private theorem starCover_control (c : Interpolation M) (x : M) :
    ∃ b : M, ∀ i : M, x ∈ starCover c i → starCover c i ⊆ c.neighborhood b :=
  (Classical.choose_spec (exists_star_cover c)).2.2.2 x

/-- The selected original member exists from covering, without countability. -/
private def selectedIndex (c : Interpolation M) (e : M) : M :=
  Classical.choose ((Set.iUnion_eq_univ_iff.mp (starCover_covers c)) e)

private theorem selectedIndex_mem (c : Interpolation M) (e : M) :
    e ∈ starCover c (selectedIndex c e) :=
  Classical.choose_spec ((Set.iUnion_eq_univ_iff.mp (starCover_covers c)) e)

open Classical in
/-- Only one member keeps e; all other members delete the closed singleton. -/
private def puncturedCover (c : Interpolation M) (e i : M) : Set M :=
  if i = selectedIndex c e then starCover c i else starCover c i \ {e}

private theorem puncturedCover_subset (c : Interpolation M) (e i : M) :
    puncturedCover c e i ⊆ starCover c i := by
  unfold puncturedCover
  split_ifs
  · exact Set.Subset.rfl
  · exact Set.sdiff_subset

private theorem puncturedCover_open (c : Interpolation M) (e i : M) :
    IsOpen (puncturedCover c e i) := by
  unfold puncturedCover
  split_ifs
  · exact starCover_open c i
  · exact IsOpen.sdiff (starCover_open c i) isClosed_singleton

private def Index (c : Interpolation M) (e : M) : Type u :=
  {i : M // (puncturedCover c e i).Nonempty}

private def zeroIndex (c : Interpolation M) (e : M) : Index c e :=
  ⟨selectedIndex c e, e, by simpa [puncturedCover] using selectedIndex_mem c e⟩

private def cover (c : Interpolation M) (e : M) (j : Index c e) : Set M :=
  puncturedCover c e j.val

private theorem cover_open (c : Interpolation M) (e : M) (j : Index c e) :
    IsOpen (cover c e j) := puncturedCover_open c e j.val

private theorem cover_nonempty (c : Interpolation M) (e : M) (j : Index c e) :
    (cover c e j).Nonempty := j.property

private theorem cover_zero_mem (c : Interpolation M) (e : M) :
    e ∈ cover c e (zeroIndex c e) := by
  simpa [cover, zeroIndex, puncturedCover] using selectedIndex_mem c e

private theorem cover_e_iff (c : Interpolation M) (e : M) (j : Index c e) :
    e ∈ cover c e j ↔ j = zeroIndex c e := by
  constructor
  · intro hj
    by_cases h : j.val = selectedIndex c e
    · exact Subtype.ext h
    · have hj' : e ∈ starCover c j.val \ {e} := by
        simpa only [cover, puncturedCover, ite_eq_right h] using hj
      exact (hj'.2 (Set.mem_singleton e)).elim
  · rintro rfl
    exact cover_zero_mem c e

private theorem cover_covers (c : Interpolation M) (e : M) :
    (⋃ j : Index c e, cover c e j) = Set.univ := by
  rw [Set.iUnion_eq_univ_iff]
  intro x
  by_cases hx : x = e
  · subst x
    exact ⟨zeroIndex c e, cover_zero_mem c e⟩
  · obtain ⟨i, hi⟩ := (Set.iUnion_eq_univ_iff.mp (starCover_covers c)) x
    have hxi : x ∈ puncturedCover c e i := by
      unfold puncturedCover
      split_ifs
      · exact hi
      · exact ⟨hi, by simpa only [Set.mem_singleton_iff] using hx⟩
    exact ⟨⟨i, x, hxi⟩, hxi⟩

private theorem cover_locallyFinite (c : Interpolation M) (e : M) :
    LocallyFinite (cover c e) :=
  ((starCover_locallyFinite c).comp_injective Subtype.val_injective).subset
    (fun j => puncturedCover_subset c e j.val)

private theorem cover_control (c : Interpolation M) (e x : M) :
    ∃ b : M, ∀ j : Index c e, x ∈ cover c e j → cover c e j ⊆ c.neighborhood b := by
  obtain ⟨b, hb⟩ := starCover_control c x
  refine ⟨b, ?_⟩
  intro j hxj
  exact (puncturedCover_subset c e j.val).trans
    (hb j.val (puncturedCover_subset c e j.val hxj))

open Classical in
private def representative (c : Interpolation M) (e : M) (j : Index c e) : M :=
  if j = zeroIndex c e then e else Classical.choose (cover_nonempty c e j)

private theorem representative_mem (c : Interpolation M) (e : M) (j : Index c e) :
    representative c e j ∈ cover c e j := by
  unfold representative
  split_ifs with h
  · simpa only [h] using cover_zero_mem c e
  · exact Classical.choose_spec (cover_nonempty c e j)

private theorem representative_zero (c : Interpolation M) (e : M) :
    representative c e (zeroIndex c e) = e := by simp [representative]

/-- The actual nerve faces are exactly the nonempty finite cover intersections. -/
private def nerve (c : Interpolation M) (e : M) :
    PreAbstractSimplicialComplex (Index c e) where
  faces := {s | s.Nonempty ∧ ∃ x : M, ∀ j ∈ s, x ∈ cover c e j}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    obtain ⟨x, hx⟩ := hs.2
    exact ⟨ht, x, fun j hj => hx j (hts hj)⟩

private theorem nerve_singleton (c : Interpolation M) (e : M) (j : Index c e) :
    {j} ∈ nerve c e := by
  obtain ⟨x, hx⟩ := cover_nonempty c e j
  refine ⟨Finset.singleton_nonempty _, x, ?_⟩
  intro i hi
  obtain rfl := Finset.mem_singleton.mp hi
  exact hx

/-- The subordinate locally finite partition is constructed, not an input. -/
private theorem exists_partition (c : Interpolation M) (e : M) :
    ∃ ρ : PartitionOfUnity (Index c e) M, ρ.IsSubordinate (cover c e) :=
  PartitionOfUnity.exists_isSubordinate_of_locallyFinite isClosed_univ (cover c e)
    (cover_open c e) (cover_locallyFinite c e) (by rw [cover_covers])

private def partition (c : Interpolation M) (e : M) : PartitionOfUnity (Index c e) M :=
  Classical.choose (exists_partition c e)

private theorem partition_subordinate (c : Interpolation M) (e : M) :
    (partition c e).IsSubordinate (cover c e) := Classical.choose_spec (exists_partition c e)

open Classical in
private def partitionWeights (c : Interpolation M) (e x : M) : Index c e →₀ ℝ :=
  Finsupp.ofSupportFinite (fun j => partition c e j x)
    ((partition c e).locallyFinite.point_finite x)

private theorem partitionWeights_apply (c : Interpolation M) (e x : M) (j : Index c e) :
    partitionWeights c e x j = partition c e j x := rfl

private theorem partitionWeights_support (c : Interpolation M) (e x : M) :
    (partitionWeights c e x).support = (partition c e).finsupport x := by
  ext j
  simp only [Finsupp.mem_support_iff, partitionWeights_apply,
    PartitionOfUnity.mem_finsupport, Function.mem_support]

private def partitionSimplex (c : Interpolation M) (e x : M) :
    Convexity.StdSimplex ℝ (Index c e) where
  weights := partitionWeights c e x
  nonneg := fun j => (partition c e).nonneg j x
  total := by
    change ∑ j ∈ (partitionWeights c e x).support, partitionWeights c e x j = 1
    rw [partitionWeights_support]
    simp_rw [partitionWeights_apply]
    exact (partition c e).sum_finsupport (Set.mem_univ x)

private theorem partition_support_cover (c : Interpolation M) (e x : M)
    (j : Index c e) (hj : j ∈ (partitionSimplex c e x).weights.support) :
    x ∈ cover c e j :=
  partition_subordinate c e j
    (subset_tsupport (partition c e j) (Finsupp.mem_support_iff.mp hj))

private def toNerve (c : Interpolation M) (e : M) : M → (nerve c e).Realization := fun x =>
  ⟨partitionSimplex c e x, (partitionSimplex c e x).support_weights_nonempty,
    x, partition_support_cover c e x⟩

private theorem toNerve_weights (c : Interpolation M) (e x : M) (j : Index c e) :
    (toNerve c e x).point.weights j = partition c e j x := rfl

/-- Actual locally finite support proves continuity into the weak topology. -/
private theorem toNerve_continuous (c : Interpolation M) (e : M) : Continuous (toNerve c e) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨s, hs⟩ := (partition c e).exists_finset_nhds x
  obtain ⟨O, hbound, hO, hxO⟩ := eventually_nhds_iff.mp hs
  have hsupport : ∀ y : O, (toNerve c e y.val).point.weights.support ⊆ s := by
    intro y j hj
    exact (hbound y.val y.property).2
      (by change partition c e j y.val ≠ 0; exact Finsupp.mem_support_iff.mp hj)
  let g : O → PreAbstractSimplicialComplex.Realization
      (PreAbstractSimplicialComplex.restrictVertices (nerve c e) s) := fun y =>
    ⟨(toNerve c e y.val).point, (toNerve c e y.val).support_mem, hsupport y⟩
  have hg : Continuous g := by
    rw [PreAbstractSimplicialComplex.Realization.continuous_iff_weights]
    intro j
    exact (partition c e j).continuous.comp continuous_subtype_val
  have hpO : Continuous (O.domRestrict (toNerve c e)) :=
    (PreAbstractSimplicialComplex.Realization.continuous_inclusion
      (PreAbstractSimplicialComplex.restrictVertices_le (nerve c e) s)).comp hg
  exact (continuousOn_iff_continuous_domRestrict.mpr hpO x hxO).continuousAt
    (hO.mem_nhds hxO)

private theorem toNerve_point (c : Interpolation M) (e : M) :
    toNerve c e e = PreAbstractSimplicialComplex.Realization.vertex
      (nerve c e) (zeroIndex c e) (nerve_singleton c e _) := by
  apply PreAbstractSimplicialComplex.Realization.ext
  apply (Convexity.StdSimplex.support_weights_eq_singleton).mp
  apply Finset.Subset.antisymm
  · intro j hj
    exact Finset.mem_singleton.mpr
      ((cover_e_iff c e j).mp (partition_support_cover c e e j hj))
  · obtain ⟨j, hj⟩ := (partitionSimplex c e e).support_weights_nonempty
    have hj0 : j = zeroIndex c e :=
      (cover_e_iff c e j).mp (partition_support_cover c e e j hj)
    simpa only [toNerve, hj0, Finset.singleton_subset_iff] using hj

private def forward (c : Interpolation M) (e : M) : C(M, (nerve c e).Realization) :=
  ⟨toNerve c e, toNerve_continuous c e⟩

end StarRefinement

section ControlledExtension

variable {M : Type u} [MetricSpace M]
variable (c : Interpolation M) (e : M)

local instance : DecidableEq (Index c e) := Classical.decEq _

variable [LinearOrder (Index c e)]

private def leastVertex (x : (nerve c e).Realization) : Index c e :=
  x.point.weights.support.min' x.point.support_weights_nonempty

private theorem leastVertex_mem (x : (nerve c e).Realization) :
    leastVertex c e x ∈ x.point.weights.support := Finset.min'_mem _ _

private theorem leastVertex_le (x : (nerve c e).Realization) (j : Index c e)
    (hj : j ∈ x.point.weights.support) : leastVertex c e x ≤ j :=
  Finset.min'_le _ _ hj

omit [LinearOrder (Index c e)] in
private theorem exists_tail_of_not_single (x : (nerve c e).Realization)
    (v : Index c e) (hv : v ∈ x.point.weights.support)
    (hns : x.point.weights.support ≠ {v}) :
    ∃ j ∈ ({v} : Set (Index c e))ᶜ, x.point.weights j ≠ 0 := by
  by_contra h
  apply hns
  ext j
  constructor
  · intro hj
    apply Finset.mem_singleton.mpr
    by_contra hjv
    exact h ⟨j, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hjv,
      Finsupp.mem_support_iff.mp hj⟩
  · intro hj
    obtain rfl := Finset.mem_singleton.mp hj
    exact hv

omit [LinearOrder (Index c e)] in
/-- Restriction uses the native normalized finite barycentric distribution. -/
private def tail (x : (nerve c e).Realization) (v : Index c e)
    (ht : ∃ j ∈ ({v} : Set (Index c e))ᶜ, x.point.weights j ≠ 0) :
    (nerve c e).Realization where
  point := x.point.restrict ({v} : Set (Index c e))ᶜ ht
  support_mem := ((nerve c e).isRelLowerSet_faces x.support_mem).2
    (by
      rw [Convexity.StdSimplex.support_weights_restrict]
      exact Finset.filter_subset _ _)
    (x.point.restrict ({v} : Set (Index c e))ᶜ ht).support_weights_nonempty

omit [LinearOrder (Index c e)] in
private theorem tail_support (x : (nerve c e).Realization) (v : Index c e)
    (ht : ∃ j ∈ ({v} : Set (Index c e))ᶜ, x.point.weights j ≠ 0) :
    (tail c e x v ht).point.weights.support = x.point.weights.support.erase v := by
  ext j
  simp only [tail, Convexity.StdSimplex.support_weights_restrict,
    Finset.mem_filter, Finset.mem_erase, Set.mem_compl_iff, Set.mem_singleton_iff,
    and_comm]

omit [LinearOrder (Index c e)] in
private theorem tail_support_subset (x : (nerve c e).Realization) (v : Index c e)
    (ht : ∃ j ∈ ({v} : Set (Index c e))ᶜ, x.point.weights j ≠ 0) :
    (tail c e x v ht).point.weights.support ⊆ x.point.weights.support := by
  rw [tail_support]
  exact Finset.erase_subset _ _

omit [LinearOrder (Index c e)] in
private theorem tail_card_lt (x : (nerve c e).Realization) (v : Index c e)
    (hv : v ∈ x.point.weights.support)
    (ht : ∃ j ∈ ({v} : Set (Index c e))ᶜ, x.point.weights j ≠ 0) :
    (tail c e x v ht).point.weights.support.card < x.point.weights.support.card := by
  rw [tail_support]
  exact Finset.card_erase_lt_of_mem hv

omit [LinearOrder (Index c e)] in
private def tailMass (x : (nerve c e).Realization) (v : Index c e) : ℝ :=
  (x.point.weights.filter (fun j => j ≠ v)).sum (fun _ r => r)

omit [LinearOrder (Index c e)] in
private theorem tailMass_eq (x : (nerve c e).Realization) (v : Index c e) :
    tailMass c e x v = 1 - x.point.weights v := by
  have h := Finsupp.sum_filter_add_sum_filter_not (fun j => j = v)
    x.point.weights (fun (_ : Index c e) (r : ℝ) => r)
  have hsum : x.point.weights v + tailMass c e x v = 1 := by
    simpa [tailMass, x.point.total] using h
  linarith

omit [LinearOrder (Index c e)] in
private theorem tailMass_nonneg (x : (nerve c e).Realization) (v : Index c e) :
    0 ≤ tailMass c e x v := by
  unfold tailMass
  apply Finsupp.sum_nonneg
  intro j _
  simp only [Finsupp.filter_apply]
  split_ifs
  · exact x.point.nonneg j
  · exact le_rfl

omit [LinearOrder (Index c e)] in
private theorem tailMass_le_one (x : (nerve c e).Realization) (v : Index c e) :
    tailMass c e x v ≤ 1 := by
  rw [tailMass_eq]
  have hnonneg : (0 : ℝ) ≤ x.point.weights v := by
    simpa only [Finsupp.zero_apply] using x.point.nonneg v
  linarith

omit [LinearOrder (Index c e)] in
private theorem tailMass_pos (x : (nerve c e).Realization) (v : Index c e)
    (ht : ∃ j ∈ ({v} : Set (Index c e))ᶜ, x.point.weights j ≠ 0) :
    0 < tailMass c e x v := by
  unfold tailMass
  apply Finsupp.sum_pos
  · intro j hj
    have hnonneg : 0 ≤ x.point.weights.filter (fun j => j ≠ v) j := by
      simp only [Finsupp.filter_apply]
      split_ifs
      · exact x.point.nonneg j
      · exact le_rfl
    exact lt_of_le_of_ne hnonneg (Finsupp.mem_support_iff.mp hj).symm
  · obtain ⟨j, hj, hne⟩ := ht
    apply Finsupp.ne_iff.mpr
    refine ⟨j, ?_⟩
    have hjv : j ≠ v := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hj
    simpa only [Finsupp.filter_apply, ite_eq_left hjv, Finsupp.zero_apply] using hne

omit [LinearOrder (Index c e)] in
private def tailTime (x : (nerve c e).Realization) (v : Index c e) : unitInterval :=
  ⟨tailMass c e x v, tailMass_nonneg c e x v, tailMass_le_one c e x v⟩

omit [LinearOrder (Index c e)] in
private theorem tail_weights (x : (nerve c e).Realization) (v : Index c e)
    (ht : ∃ j ∈ ({v} : Set (Index c e))ᶜ, x.point.weights j ≠ 0) :
    (tail c e x v ht).point.weights =
      (tailMass c e x v)⁻¹ • x.point.weights.filter (fun j => j ≠ v) := by
  simp only [tail, Convexity.StdSimplex.weights_restrict, tailMass,
    Set.mem_compl_iff, Set.mem_singleton_iff]

omit [LinearOrder (Index c e)] in
/-- Every actual nerve face has one convex control containing all representatives. -/
private theorem common_control (x : (nerve c e).Realization) :
    ∃ b : M, ∀ j ∈ x.point.weights.support,
      representative c e j ∈ c.neighborhood b := by
  obtain ⟨a, ha⟩ := x.support_mem.2
  obtain ⟨b, hb⟩ := cover_control c e a
  exact ⟨b, fun j hj => hb j (ha j hj) (representative_mem c e j)⟩

private def Controlled (x : (nerve c e).Realization) (m : M) : Prop :=
  ∀ B : Set M, IsConvex c B →
    (∀ j ∈ x.point.weights.support, representative c e j ∈ B) → m ∈ B

/-- Ordered finite-support recursion. Each recursive value retains every convex control. -/
private def evaluate (x : (nerve c e).Realization) : {m : M // Controlled c e x m} := by
  let v := leastVertex c e x
  have hv : v ∈ x.point.weights.support := leastVertex_mem c e x
  by_cases hsingle : x.point.weights.support = {v}
  · exact ⟨representative c e v, fun B _ hB => hB v hv⟩
  · let ht := exists_tail_of_not_single c e x v hv hsingle
    let y := tail c e x v ht
    let z := evaluate y
    have hpair : (representative c e v, z.val) ∈ c.domain := by
      obtain ⟨b, hb⟩ := common_control c e x
      apply c.neighborhood_square b _ (hb v hv)
      exact z.property (c.neighborhood b) (neighborhood_convex c b)
        (fun j hj => hb j (tail_support_subset c e x v ht hj))
    refine ⟨c.homotopy (tailTime c e x v, ⟨(representative c e v, z.val), hpair⟩), ?_⟩
    intro B hB hrep
    exact hB.2 _ (hrep v hv) _
      (z.property B hB (fun j hj => hrep j (tail_support_subset c e x v ht hj)))
      hpair (tailTime c e x v)
termination_by x.point.weights.support.card
decreasing_by
  exact tail_card_lt c e x v hv ht

private def fromNerve (x : (nerve c e).Realization) : M := (evaluate c e x).val

private theorem fromNerve_control (x : (nerve c e).Realization) (B : Set M)
    (hB : IsConvex c B)
    (hrep : ∀ j ∈ x.point.weights.support, representative c e j ∈ B) :
    fromNerve c e x ∈ B := (evaluate c e x).property B hB hrep

private theorem fromNerve_vertex (j : Index c e) :
    fromNerve c e (PreAbstractSimplicialComplex.Realization.vertex
      (nerve c e) j (nerve_singleton c e j)) = representative c e j := by
  unfold fromNerve
  rw [evaluate.eq_def]
  simp [leastVertex, PreAbstractSimplicialComplex.Realization.vertex]

private theorem fromNerve_recursive (x : (nerve c e).Realization)
    (hns : x.point.weights.support ≠ {leastVertex c e x}) :
    let v := leastVertex c e x
    let ht := exists_tail_of_not_single c e x v (leastVertex_mem c e x) hns
    ∀ hab : (representative c e v, fromNerve c e (tail c e x v ht)) ∈ c.domain,
      fromNerve c e x = c.homotopy
        (tailTime c e x v, ⟨(representative c e v, fromNerve c e (tail c e x v ht)), hab⟩) := by
  intro v ht hab
  unfold fromNerve
  rw [evaluate.eq_def]
  simp only [dite_eq_right hns]
  rfl

omit [LinearOrder (Index c e)] in
private theorem exists_tail_of_ne_vertex (x : (nerve c e).Realization) (v : Index c e)
    (hns : x.point ≠ Convexity.StdSimplex.single v) :
    ∃ j ∈ ({v} : Set (Index c e))ᶜ, x.point.weights j ≠ 0 := by
  by_contra h
  have hsupport : x.point.weights.support ⊆ {v} := by
    intro j hj
    apply Finset.mem_singleton.mpr
    by_contra hjv
    exact h ⟨j, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hjv,
      Finsupp.mem_support_iff.mp hj⟩
  have heq : x.point.weights.support = {v} := by
    apply Finset.Subset.antisymm hsupport
    obtain ⟨j, hj⟩ := x.point.support_weights_nonempty
    have hjv := Finset.mem_singleton.mp (hsupport hj)
    simpa only [hjv, Finset.singleton_subset_iff] using hj
  exact hns ((Convexity.StdSimplex.support_weights_eq_singleton).mp heq)

omit [LinearOrder (Index c e)] in
private def erasedFace (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (ht : (s.val.erase v).Nonempty) :
    PreAbstractSimplicialComplex.Face (nerve c e) :=
  ⟨s.val.erase v, ((nerve c e).isRelLowerSet_faces s.property).2
    (Finset.erase_subset _ _) ht⟩

omit [LinearOrder (Index c e)] in
/-- The actual affine cone on the face opposite v; it lands in the original face. -/
private def conePoint (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty)
    (t : unitInterval) (y : Convexity.StdSimplex ℝ (s.val.erase v)) :
    (nerve c e).Realization where
  point := PreAbstractSimplicialComplex.Realization.segmentPoint t
    (Convexity.StdSimplex.single v)
    (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e) (erasedFace c e s v ht) y).point
  support_mem := ((nerve c e).isRelLowerSet_faces s.property).2
    ((PreAbstractSimplicialComplex.Realization.segmentPoint_support_subset _ _ _).trans
      (Finset.union_subset (by simpa only [Convexity.StdSimplex.weights_single,
         (Finsupp.support_single v (by norm_num : (1 : ℝ) ≠ 0)),
        Finset.singleton_subset_iff] using hv)
        ((PreAbstractSimplicialComplex.Realization.support_map_subtype_subset _ y).trans
          (Finset.erase_subset _ _))))
    (PreAbstractSimplicialComplex.Realization.segmentPoint t
      (Convexity.StdSimplex.single v)
      (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e)
        (erasedFace c e s v ht) y).point).support_weights_nonempty

omit [LinearOrder (Index c e)] in
private theorem conePoint_support_subset (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty)
    (t : unitInterval) (y : Convexity.StdSimplex ℝ (s.val.erase v)) :
    (conePoint c e s v hv ht t y).point.weights.support ⊆ s.val := by
  exact (PreAbstractSimplicialComplex.Realization.segmentPoint_support_subset _ _ _).trans
    (Finset.union_subset (by simpa only [Convexity.StdSimplex.weights_single,
       (Finsupp.support_single v (by norm_num : (1 : ℝ) ≠ 0)),
      Finset.singleton_subset_iff] using hv)
      ((PreAbstractSimplicialComplex.Realization.support_map_subtype_subset _ y).trans
        (Finset.erase_subset _ _)))

omit [LinearOrder (Index c e)] in
private theorem erasedFace_weight_zero (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (ht : (s.val.erase v).Nonempty)
    (y : Convexity.StdSimplex ℝ (s.val.erase v)) :
    (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e)
      (erasedFace c e s v ht) y).point.weights v = 0 := by
  apply Finsupp.notMem_support_iff.mp
  intro h
  have hv := PreAbstractSimplicialComplex.Realization.support_map_subtype_subset _ y h
  exact (Finset.mem_erase.mp hv).1 rfl

omit [LinearOrder (Index c e)] in
private theorem conePoint_weights (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty)
    (t : unitInterval) (y : Convexity.StdSimplex ℝ (s.val.erase v)) :
    (conePoint c e s v hv ht t y).point.weights =
      (1 - (t : ℝ)) • Finsupp.single v 1 + (t : ℝ) •
        (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e)
          (erasedFace c e s v ht) y).point.weights :=
  PreAbstractSimplicialComplex.Realization.segmentPoint_weights _ _ _

omit [LinearOrder (Index c e)] in
private theorem conePoint_weight_vertex (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty)
    (t : unitInterval) (y : Convexity.StdSimplex ℝ (s.val.erase v)) :
    (conePoint c e s v hv ht t y).point.weights v = 1 - (t : ℝ) := by
  rw [conePoint_weights]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_eq_same, mul_one, erasedFace_weight_zero, mul_zero, add_zero]

omit [LinearOrder (Index c e)] in
private theorem conePoint_weight_other (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty)
    (t : unitInterval) (y : Convexity.StdSimplex ℝ (s.val.erase v))
    (j : Index c e) (hj : j ≠ v) :
    (conePoint c e s v hv ht t y).point.weights j = (t : ℝ) *
      (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e)
        (erasedFace c e s v ht) y).point.weights j := by
  rw [conePoint_weights]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_eq_of_ne hj, mul_zero, zero_add]

omit [LinearOrder (Index c e)] in
private theorem conePoint_zero (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty)
    (y : Convexity.StdSimplex ℝ (s.val.erase v)) :
    conePoint c e s v hv ht 0 y = PreAbstractSimplicialComplex.Realization.vertex
      (nerve c e) v (nerve_singleton c e v) := by
  apply PreAbstractSimplicialComplex.Realization.ext
  exact PreAbstractSimplicialComplex.Realization.segmentPoint_zero _ _

omit [LinearOrder (Index c e)] in
private theorem conePoint_one (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty)
    (y : Convexity.StdSimplex ℝ (s.val.erase v)) :
    conePoint c e s v hv ht 1 y = PreAbstractSimplicialComplex.Realization.faceMap
      (nerve c e) (erasedFace c e s v ht) y := by
  apply PreAbstractSimplicialComplex.Realization.ext
  exact PreAbstractSimplicialComplex.Realization.segmentPoint_one _ _

omit [LinearOrder (Index c e)] in
/-- Continuity uses the finite original face restriction, not a target compact carrier. -/
private theorem conePoint_continuous (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty) :
    Continuous (fun p : unitInterval × Convexity.StdSimplex ℝ (s.val.erase v) =>
      conePoint c e s v hv ht p.1 p.2) := by
  let localCone : unitInterval × Convexity.StdSimplex ℝ (s.val.erase v) →
      PreAbstractSimplicialComplex.Realization
        (PreAbstractSimplicialComplex.restrictVertices (nerve c e) s.val) := fun p =>
    ⟨(conePoint c e s v hv ht p.1 p.2).point,
      (conePoint c e s v hv ht p.1 p.2).support_mem,
      conePoint_support_subset c e s v hv ht p.1 p.2⟩
  have hlocal : Continuous localCone := by
    rw [PreAbstractSimplicialComplex.Realization.continuous_iff_weights]
    intro j
    change Continuous (fun p : unitInterval × Convexity.StdSimplex ℝ (s.val.erase v) =>
      (conePoint c e s v hv ht p.1 p.2).point.weights j)
    simp only [conePoint_weights, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      continuous_const).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((PreAbstractSimplicialComplex.Realization.continuous_weight (nerve c e) j).comp
          ((PreAbstractSimplicialComplex.Realization.continuous_faceMap (nerve c e)
            (erasedFace c e s v ht)).comp continuous_snd)))
  exact (PreAbstractSimplicialComplex.Realization.continuous_inclusion
    (PreAbstractSimplicialComplex.restrictVertices_le (nerve c e) s.val)).comp hlocal

omit [LinearOrder (Index c e)] in
private theorem conePoint_filter_tail (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty)
    (t : unitInterval) (y : Convexity.StdSimplex ℝ (s.val.erase v)) :
    (conePoint c e s v hv ht t y).point.weights.filter (fun j => j ≠ v) =
      (t : ℝ) • (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e)
        (erasedFace c e s v ht) y).point.weights := by
  ext j
  by_cases hj : j = v
  · subst j
    simp only [Finsupp.filter_apply, ite_eq_right (not_ne_iff.mpr rfl), Finsupp.smul_apply,
      smul_eq_mul, erasedFace_weight_zero, mul_zero]
  · simp only [Finsupp.filter_apply, ite_eq_left hj, Finsupp.smul_apply, smul_eq_mul,
      conePoint_weight_other c e s v hv ht t y j hj]

omit [LinearOrder (Index c e)] in
private theorem conePoint_tailMass (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty)
    (t : unitInterval) (y : Convexity.StdSimplex ℝ (s.val.erase v)) :
    tailMass c e (conePoint c e s v hv ht t y) v = (t : ℝ) := by
  rw [tailMass_eq, conePoint_weight_vertex]
  ring

omit [LinearOrder (Index c e)] in
private theorem conePoint_tailTime (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty)
    (t : unitInterval) (y : Convexity.StdSimplex ℝ (s.val.erase v)) :
    tailTime c e (conePoint c e s v hv ht t y) v = t :=
  Subtype.ext (conePoint_tailMass c e s v hv ht t y)

omit [LinearOrder (Index c e)] in
private theorem conePoint_tail (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty)
    (t : unitInterval) (hne : t ≠ 0) (y : Convexity.StdSimplex ℝ (s.val.erase v))
    (hrestrict : ∃ j ∈ ({v} : Set (Index c e))ᶜ,
      (conePoint c e s v hv ht t y).point.weights j ≠ 0) :
    tail c e (conePoint c e s v hv ht t y) v hrestrict =
      PreAbstractSimplicialComplex.Realization.faceMap (nerve c e)
        (erasedFace c e s v ht) y := by
  apply PreAbstractSimplicialComplex.Realization.ext
  apply Convexity.StdSimplex.ext
  rw [tail_weights, conePoint_tailMass, conePoint_filter_tail,
    inv_smul_smul₀ (unitInterval.coe_ne_zero.mpr hne)]

omit [LinearOrder (Index c e)] in
private theorem tail_reassembles (x : (nerve c e).Realization) (v : Index c e)
    (ht : ∃ j ∈ ({v} : Set (Index c e))ᶜ, x.point.weights j ≠ 0) :
    PreAbstractSimplicialComplex.Realization.segmentPoint (tailTime c e x v)
      (Convexity.StdSimplex.single v) (tail c e x v ht).point = x.point := by
  apply Convexity.StdSimplex.ext
  rw [PreAbstractSimplicialComplex.Realization.segmentPoint_weights, tail_weights]
  change (1 - tailMass c e x v) • Finsupp.single v 1 +
    tailMass c e x v • ((tailMass c e x v)⁻¹ • x.point.weights.filter (fun j => j ≠ v)) = _
  rw [smul_inv_smul₀ (tailMass_pos c e x v ht).ne', tailMass_eq]
  simp only [sub_sub_cancel, Finsupp.smul_single_one]
  simpa only [Finsupp.filter_eq'] using
    Finsupp.filter_add_filter_not x.point.weights (fun j => j = v)

omit [LinearOrder (Index c e)] in
private def faceRange (s : PreAbstractSimplicialComplex.Face (nerve c e)) :
    Set (nerve c e).Realization :=
  Set.range (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e) s)

omit [LinearOrder (Index c e)] in
private def coneToFace (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty) :
    unitInterval × Convexity.StdSimplex ℝ (s.val.erase v) → faceRange c e s := fun p =>
  ⟨conePoint c e s v hv ht p.1 p.2,
    (PreAbstractSimplicialComplex.Realization.mem_range_faceMap_iff s _).mpr
      (conePoint_support_subset c e s v hv ht p.1 p.2)⟩

omit [LinearOrder (Index c e)] in
private theorem coneToFace_continuous (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty) :
    Continuous (coneToFace c e s v hv ht) :=
  Continuous.subtype_mk (conePoint_continuous c e s v hv ht) _

omit [LinearOrder (Index c e)] in
/-- Every finite-face point has its actual cone presentation, including the vertex. -/
private theorem coneToFace_surjective (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty) :
    Function.Surjective (coneToFace c e s v hv ht) := by
  intro z
  have hsupport : z.val.point.weights.support ⊆ s.val :=
    (PreAbstractSimplicialComplex.Realization.mem_range_faceMap_iff s z.val).mp z.property
  by_cases hz : z.val.point = Convexity.StdSimplex.single v
  · have hcopy : (s.val.erase v).Nonempty := ht
    obtain ⟨j, hj⟩ := hcopy
    refine ⟨(0, Convexity.StdSimplex.single (⟨j, hj⟩ : s.val.erase v)), ?_⟩
    apply Subtype.ext
    change conePoint c e s v hv ht 0
      (Convexity.StdSimplex.single (⟨j, hj⟩ : s.val.erase v)) = z.val
    rw [conePoint_zero]
    exact PreAbstractSimplicialComplex.Realization.ext hz.symm
  · let htail := exists_tail_of_ne_vertex c e z.val v hz
    have htailSupport : (tail c e z.val v htail).point.weights.support ⊆ s.val.erase v := by
      rw [tail_support]
      exact Finset.erase_subset_erase v hsupport
    obtain ⟨y, hy⟩ :=
      (PreAbstractSimplicialComplex.Realization.mem_range_faceMap_iff
        (erasedFace c e s v ht) (tail c e z.val v htail)).mpr htailSupport
    refine ⟨(tailTime c e z.val v, y), ?_⟩
    apply Subtype.ext
    apply PreAbstractSimplicialComplex.Realization.ext
    change PreAbstractSimplicialComplex.Realization.segmentPoint (tailTime c e z.val v)
      (Convexity.StdSimplex.single v)
      (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e)
        (erasedFace c e s v ht) y).point = z.val.point
    rw [hy]
    exact tail_reassembles c e z.val v htail

omit [LinearOrder (Index c e)] in
/-- Compact finite cone domain and the actual Hausdorff face range give quotient descent. -/
private theorem coneToFace_quotient (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty) :
    Topology.IsQuotientMap (coneToFace c e s v hv ht) :=
  Topology.IsQuotientMap.of_surjective_continuous
    (coneToFace_surjective c e s v hv ht) (coneToFace_continuous c e s v hv ht)

omit [LinearOrder (Index c e)] in
private theorem conePoint_support_middle (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty)
    (t : unitInterval) (hzero : t ≠ 0) (hone : t ≠ 1)
    (y : Convexity.StdSimplex ℝ (s.val.erase v)) :
    (conePoint c e s v hv ht t y).point.weights.support =
      insert v (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e)
        (erasedFace c e s v ht) y).point.weights.support := by
  ext j
  by_cases hj : j = v
  · subst j
    rw [Finsupp.mem_support_iff, conePoint_weight_vertex]
    constructor
    · intro _
      exact Finset.mem_insert_self _ _
    · intro _
      exact sub_ne_zero.mpr (unitInterval.coe_ne_one.mpr hone).symm
  · simp only [Finsupp.mem_support_iff, conePoint_weight_other c e s v hv ht t y j hj,
       Finset.mem_insert, hj, false_or, mul_ne_zero_iff]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨unitInterval.coe_ne_zero.mpr hzero, h⟩

private theorem conePoint_least (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (hmin : ∀ j ∈ s.val, v ≤ j)
    (ht : (s.val.erase v).Nonempty) (t : unitInterval) (hzero : t ≠ 0) (hone : t ≠ 1)
    (y : Convexity.StdSimplex ℝ (s.val.erase v)) :
    leastVertex c e (conePoint c e s v hv ht t y) = v := by
  apply le_antisymm
  · apply leastVertex_le
    rw [conePoint_support_middle c e s v hv ht t hzero hone y]
    exact Finset.mem_insert_self _ _
  · exact hmin _ (conePoint_support_subset c e s v hv ht t y
      (leastVertex_mem c e _))

omit [LinearOrder (Index c e)] in
private theorem conePoint_not_single (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (ht : (s.val.erase v).Nonempty)
    (t : unitInterval) (hzero : t ≠ 0) (hone : t ≠ 1)
    (y : Convexity.StdSimplex ℝ (s.val.erase v)) :
    (conePoint c e s v hv ht t y).point.weights.support ≠ {v} := by
  intro hsingle
  obtain ⟨j, hj⟩ :=
    (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e)
      (erasedFace c e s v ht) y).point.support_weights_nonempty
  have hjv : j ≠ v := Finset.ne_of_mem_erase
    (PreAbstractSimplicialComplex.Realization.support_map_subtype_subset _ y hj)
  have hmem : j ∈ (conePoint c e s v hv ht t y).point.weights.support := by
    rw [conePoint_support_middle c e s v hv ht t hzero hone y]
    exact Finset.mem_insert_of_mem hj
  rw [hsingle] at hmem
  exact hjv (Finset.mem_singleton.mp hmem)

/-- The whole cone formula is compatible at every parameter, not just at its boundary. -/
private theorem fromNerve_cone (s : PreAbstractSimplicialComplex.Face (nerve c e))
    (v : Index c e) (hv : v ∈ s.val) (hmin : ∀ j ∈ s.val, v ≤ j)
    (ht : (s.val.erase v).Nonempty) (t : unitInterval)
    (y : Convexity.StdSimplex ℝ (s.val.erase v))
    (hab : (representative c e v, fromNerve c e
      (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e)
        (erasedFace c e s v ht) y)) ∈ c.domain) :
    fromNerve c e (conePoint c e s v hv ht t y) =
      c.homotopy (t, ⟨(representative c e v, fromNerve c e
        (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e)
          (erasedFace c e s v ht) y)), hab⟩) := by
  by_cases hzero : t = 0
  · subst t
    rw [conePoint_zero, fromNerve_vertex, c.homotopy.apply_zero]
    rfl
  by_cases hone : t = 1
  · subst t
    rw [conePoint_one, c.homotopy.apply_one]
    rfl
  let z := conePoint c e s v hv ht t y
  have hm : leastVertex c e z = v := conePoint_least c e s v hv hmin ht t hzero hone y
  have hs : z.point.weights.support ≠ {leastVertex c e z} := by
    simpa only [hm] using conePoint_not_single c e s v hv ht t hzero hone y
  let v' := leastVertex c e z
  let htail := exists_tail_of_not_single c e z v' (leastVertex_mem c e z) hs
  have htailEq : tail c e z v' htail =
      PreAbstractSimplicialComplex.Realization.faceMap (nerve c e)
        (erasedFace c e s v ht) y := by
    simpa only [v', hm] using conePoint_tail c e s v hv ht t hzero y
      (by simpa only [v', hm] using htail)
  have htimeEq : tailTime c e z v' = t := by
    simpa only [v', hm] using conePoint_tailTime c e s v hv ht t y
  have hab' : (representative c e v', fromNerve c e (tail c e z v' htail)) ∈ c.domain := by
    rw [htailEq]
    simpa only [v', hm] using hab
  calc
    fromNerve c e z = c.homotopy
        (tailTime c e z v', ⟨(representative c e v', fromNerve c e (tail c e z v' htail)), hab'⟩) :=
      fromNerve_recursive c e z hs hab'
    _ = c.homotopy (t, ⟨(representative c e v, fromNerve c e
        (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e)
          (erasedFace c e s v ht) y)), hab⟩) := by
      congr 1
      apply Prod.ext htimeEq
      apply Subtype.ext
      exact Prod.ext (congrArg (representative c e) hm) (congrArg (fromNerve c e) htailEq)

omit [LinearOrder (Index c e)] in
private theorem face_common_control (s : PreAbstractSimplicialComplex.Face (nerve c e)) :
    ∃ b : M, ∀ j ∈ s.val, representative c e j ∈ c.neighborhood b := by
  obtain ⟨a, ha⟩ := s.property.2
  obtain ⟨b, hb⟩ := cover_control c e a
  exact ⟨b, fun j hj => hb j (ha j hj) (representative_mem c e j)⟩

/-- Finite-face induction constructs continuity; the extension is never assumed. -/
private theorem fromNerve_continuous : Continuous (fromNerve c e) := by
  have hface : ∀ s : Finset (Index c e), ∀ hs : s ∈ nerve c e,
      Continuous (fromNerve c e ∘
        PreAbstractSimplicialComplex.Realization.faceMap (nerve c e) ⟨s, hs⟩) :=
    fun s => s.strongInduction
      (p := fun s => ∀ hs : s ∈ nerve c e,
        Continuous (fromNerve c e ∘
          PreAbstractSimplicialComplex.Realization.faceMap (nerve c e) ⟨s, hs⟩))
      (fun s ih => by
      intro hs
      let sf : PreAbstractSimplicialComplex.Face (nerve c e) := ⟨s, hs⟩
      let v := s.min' hs.1
      have hv : v ∈ s := Finset.min'_mem _ _
      have hmin : ∀ j ∈ s, v ≤ j := fun j hj => Finset.min'_le _ _ hj
      by_cases ht : (s.erase v).Nonempty
      · let tf := erasedFace c e sf v ht
        have htailCont : Continuous (fromNerve c e ∘
            PreAbstractSimplicialComplex.Realization.faceMap (nerve c e) tf) :=
          ih (s.erase v) (Finset.erase_ssubset hv) tf.property
        obtain ⟨b, hb⟩ := face_common_control c e sf
        have hpair : ∀ y : Convexity.StdSimplex ℝ (s.erase v),
            (representative c e v, fromNerve c e
              (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e) tf y)) ∈ c.domain := by
          intro y
          apply c.neighborhood_square b _ (hb v hv)
          exact fromNerve_control c e _ (c.neighborhood b) (neighborhood_convex c b)
            (fun j hj => hb j (Finset.mem_of_mem_erase
              (PreAbstractSimplicialComplex.Realization.support_map_subtype_subset _ y hj)))
        let pairY : C(Convexity.StdSimplex ℝ (s.erase v), c.domain) :=
          ⟨fun y => ⟨(representative c e v, fromNerve c e
            (PreAbstractSimplicialComplex.Realization.faceMap (nerve c e) tf y)), hpair y⟩,
             Continuous.subtype_mk (continuous_const.prodMk htailCont) _⟩
        let qRange : faceRange c e sf → M := fun z => fromNerve c e z.val
        have hRange : Continuous qRange := by
          apply (coneToFace_quotient c e sf v hv ht).continuous_iff.mpr
          have heq : qRange ∘ coneToFace c e sf v hv ht =
              fun p => c.homotopy (p.1, pairY p.2) := by
            funext p
            exact fromNerve_cone c e sf v hv hmin ht p.1 p.2 (hpair p.2)
          rw [heq]
          exact c.homotopy.continuous.comp
            (continuous_fst.prodMk (pairY.continuous.comp continuous_snd))
        have hchart : Continuous (fun y : Convexity.StdSimplex ℝ s =>
            (⟨PreAbstractSimplicialComplex.Realization.faceMap (nerve c e) sf y,
              ⟨y, rfl⟩⟩ : faceRange c e sf)) :=
           Continuous.subtype_mk
             (PreAbstractSimplicialComplex.Realization.continuous_faceMap (nerve c e) sf) _
        exact hRange.comp hchart
      · have hempty : s.erase v = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
        have hsingleton : s = {v} := by
          ext j
          constructor
          · intro hj
            apply Finset.mem_singleton.mpr
            by_contra hjv
            have hj' : j ∈ s.erase v := Finset.mem_erase.mpr ⟨hjv, hj⟩
            simp only [hempty, Finset.notMem_empty] at hj'
          · intro hj
            obtain rfl := Finset.mem_singleton.mp hj
            exact hv
        have heq : fromNerve c e ∘
            PreAbstractSimplicialComplex.Realization.faceMap (nerve c e) sf =
            fun _ => representative c e v := by
          funext y
          have hsupport : (PreAbstractSimplicialComplex.Realization.faceMap
              (nerve c e) sf y).point.weights.support = {v} := by
            apply Finset.Subset.antisymm
            · simpa only [PreAbstractSimplicialComplex.Realization.faceMap,
                  sf, hsingleton] using
                PreAbstractSimplicialComplex.Realization.support_map_subtype_subset s y
            · obtain ⟨j, hj⟩ :=
                (PreAbstractSimplicialComplex.Realization.faceMap
                  (nerve c e) sf y).point.support_weights_nonempty
              have hjv : j = v := Finset.mem_singleton.mp
                (by simpa only [hsingleton] using
                  PreAbstractSimplicialComplex.Realization.support_map_subtype_subset s y hj)
              simpa only [hjv, Finset.singleton_subset_iff] using hj
          have hy : PreAbstractSimplicialComplex.Realization.faceMap (nerve c e) sf y =
              PreAbstractSimplicialComplex.Realization.vertex
                (nerve c e) v (nerve_singleton c e v) :=
            PreAbstractSimplicialComplex.Realization.ext
              ((Convexity.StdSimplex.support_weights_eq_singleton).mp hsupport)
          change fromNerve c e _ = _
          rw [hy]
          exact fromNerve_vertex c e v
        rw [heq]
        exact continuous_const)
  rw [PreAbstractSimplicialComplex.Realization.continuous_iff]
  exact fun s => hface s.val s.property

private def backward : C((nerve c e).Realization, M) :=
  ⟨fromNerve c e, fromNerve_continuous c e⟩

private theorem backward_point : backward c e
    (PreAbstractSimplicialComplex.Realization.vertex (nerve c e)
      (zeroIndex c e) (nerve_singleton c e _)) = e :=
  (fromNerve_vertex c e _).trans (representative_zero c e)

private theorem comparison_pair (x : M) :
    (backward c e (forward c e x), x) ∈ c.domain := by
  obtain ⟨b, hb⟩ := cover_control c e x
  have hxB : x ∈ c.neighborhood b := by
    obtain ⟨j, hj⟩ := (Set.iUnion_eq_univ_iff.mp (cover_covers c e)) x
    exact hb j hj hj
  have hqB : backward c e (forward c e x) ∈ c.neighborhood b :=
    fromNerve_control c e _ (c.neighborhood b) (neighborhood_convex c b)
      (fun j hj => hb j (partition_support_cover c e x j hj) (representative_mem c e j))
  exact c.neighborhood_square b _ hqB _ hxB

private def comparisonPair : C(M, c.domain) :=
  ⟨fun x => ⟨(backward c e (forward c e x), x), comparison_pair c e x⟩,
    Continuous.subtype_mk
      (((backward c e).continuous.comp (forward c e).continuous).prodMk continuous_id) _⟩

/-- The same actual interpolation gives the joint homotopy on the whole source. -/
private def dominationHomotopy :
    ContinuousMap.Homotopy ((backward c e).comp (forward c e)) (ContinuousMap.id M) where
  toFun z := c.homotopy (z.1, comparisonPair c e z.2)
  continuous_toFun := c.homotopy.continuous.comp
    (continuous_fst.prodMk ((comparisonPair c e).continuous.comp continuous_snd))
  map_zero_left x := c.homotopy.apply_zero (comparisonPair c e x)
  map_one_left x := c.homotopy.apply_one (comparisonPair c e x)

/-- Exact diagonal stationarity fixes the independently selected point at all times. -/
private theorem dominationHomotopy_point (t : unitInterval) :
    dominationHomotopy c e (t, e) = e := by
  have hqp : backward c e (forward c e e) = e := by
    rw [show forward c e e = _ from toNerve_point c e]
    exact backward_point c e
  have hpairEq : comparisonPair c e e =
      (⟨(e, e), by simpa only [hqp] using comparison_pair c e e⟩ : c.domain) :=
    Subtype.ext (Prod.ext hqp rfl)
  change c.homotopy (t, comparisonPair c e e) = e
  rw [hpairEq]
  exact c.stationary e _ t

private def basedDominationHomotopy : ContinuousMap.HomotopyRel
    ((backward c e).comp (forward c e)) (ContinuousMap.id M) ({e} : Set M) where
  toHomotopy := dominationHomotopy c e
  prop' t := by
    intro x hx
    have heq : x = e := Set.mem_singleton_iff.mp hx
    subst x
    change dominationHomotopy c e (t, e) = backward c e (forward c e e)
    rw [dominationHomotopy_point]
    rw [show forward c e e = _ from toNerve_point c e]
    exact (backward_point c e).symm

end ControlledExtension

section Domination

variable {M : Type u} [MetricSpace M]

open Classical in
/-- Complete based domination from the actual metric interpolation data. -/
public theorem metric_based_CW_domination (c : Interpolation M) (e : M) :
    ∃ (J : Type u) (P : PreAbstractSimplicialComplex J) (W : J → Set M)
      (v0 : J) (hv0 : {v0} ∈ P),
      (∀ s : Finset J, s ∈ P ↔ s.Nonempty ∧ ∃ x : M, ∀ j ∈ s, x ∈ W j) ∧
      (∀ j : J, IsOpen (W j) ∧ (W j).Nonempty) ∧
      (⋃ j : J, W j = Set.univ) ∧ LocallyFinite W ∧
      (∀ j : J, e ∈ W j ↔ j = v0) ∧
      let N := P.Realization
      let n0 := PreAbstractSimplicialComplex.Realization.vertex P v0 hv0
      let cw := PreAbstractSimplicialComplex.Realization.classicalCWComplex P
      letI : Topology.CWComplex (Set.univ : Set N) := cw
      ∃ (p : C(M, N)) (q : C(N, M)),
        p e = n0 ∧ q n0 = e ∧
        ∃ H : ContinuousMap.HomotopyRel (q.comp p) (ContinuousMap.id M) ({e} : Set M),
          (∀ t : unitInterval, H (t, e) = e) ∧
          ∃ j : Topology.CWComplex.cell (Set.univ : Set N) 0,
            ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x = n0 := by
  let : LinearOrder (Index c e) := linearOrderOfSTO WellOrderingRel
  refine ⟨Index c e, nerve c e, cover c e, zeroIndex c e, nerve_singleton c e _,
    (fun _ => Iff.rfl), (fun j => ⟨cover_open c e j, cover_nonempty c e j⟩),
    cover_covers c e, cover_locallyFinite c e, cover_e_iff c e, ?_⟩
  refine ⟨forward c e, backward c e, toNerve_point c e, backward_point c e,
    basedDominationHomotopy c e, ?_, ?_⟩
  · intro t
    exact dominationHomotopy_point c e t
  · exact PreAbstractSimplicialComplex.Realization.vertex_is_classical_zeroCell
      (nerve c e) (zeroIndex c e) (nerve_singleton c e _)

end Domination

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def normedPairFamily (U : Set E) : C((U × U) × unitInterval, E) where
  toFun z := (1 - (z.2 : ℝ)) • z.1.1.val + (z.2 : ℝ) • z.1.2.val
  continuous_toFun := by fun_prop

private def normedPairDomain (U : Set E) : Set (U × U) :=
  {p | ∀ t : unitInterval, (1 - (t : ℝ)) • p.1.val + (t : ℝ) • p.2.val ∈ U}

private theorem normedPairDomain_open (U : Set E) (hU : IsOpen U) :
    IsOpen (normedPairDomain U) := by
  have heq : normedPairDomain U = (normedPairFamily U).curry ⁻¹'
      {f : C(unitInterval, E) | Set.MapsTo f Set.univ U} := by
    ext p
    simp [normedPairDomain, normedPairFamily, Set.MapsTo]
  rw [heq]
  exact (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hU).preimage
    (normedPairFamily U).curry.continuous

private theorem normedPairDomain_diagonal (U : Set E) (x : U) :
    (x, x) ∈ normedPairDomain U := by
  intro t
  rw [← add_smul, sub_add_cancel, one_smul]
  exact x.property

private def normedPairHomotopy (U : Set E) :
    ContinuousMap.Homotopy (pairFirst (normedPairDomain U))
      (pairSecond (normedPairDomain U)) where
  toFun z := ⟨(1 - (z.1 : ℝ)) • z.2.val.1.val + (z.1 : ℝ) • z.2.val.2.val,
    z.2.property z.1⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  map_zero_left p := by
    apply Subtype.ext
    simp [pairFirst]
  map_one_left p := by
    apply Subtype.ext
    simp [pairSecond]

private theorem normedPairHomotopy_stationary (U : Set E) (x : U)
    (hx : (x, x) ∈ normedPairDomain U) (t : unitInterval) :
    normedPairHomotopy U (t, ⟨(x, x), hx⟩) = x := by
  apply Subtype.ext
  change (1 - (t : ℝ)) • x.val + (t : ℝ) • x.val = x.val
  rw [← add_smul, sub_add_cancel, one_smul]

private theorem normedOpenConvexNeighborhood (U : Set E) (hU : IsOpen U) (x : U) :
    ∃ N : Set U, IsOpen N ∧ x ∈ N ∧
      (∀ a b : U, a ∈ N → b ∈ N → (a, b) ∈ normedPairDomain U) ∧
      ∀ (a b : U), a ∈ N → b ∈ N →
        ∀ (hab : (a, b) ∈ normedPairDomain U) (t : unitInterval),
          normedPairHomotopy U (t, ⟨(a, b), hab⟩) ∈ N := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x.val x.property
  let N : Set U := Subtype.val ⁻¹' Metric.ball x.val δ
  have hcomb (a b : U) (ha : a ∈ N) (hb : b ∈ N) (t : unitInterval) :
      (1 - (t : ℝ)) • a.val + (t : ℝ) • b.val ∈ Metric.ball x.val δ :=
    (convex_ball x.val δ) ha hb (sub_nonneg.mpr t.property.2) t.property.1
      (by ring)
  refine ⟨N, Metric.isOpen_ball.preimage continuous_subtype_val,
    Metric.mem_ball_self hδ, ?_, ?_⟩
  · intro a b ha hb t
    exact hball (hcomb a b ha hb t)
  · intro a b ha hb hab t
    exact hcomb a b ha hb t

private theorem normedOpenCWDomination (U : Set E) (hU : IsOpen U) (e : U) :
    ∃ (J : Type u) (P : PreAbstractSimplicialComplex J) (W : J → Set U)
      (v0 : J) (hv0 : {v0} ∈ P),
      (∀ s : Finset J, s ∈ P ↔ s.Nonempty ∧ ∃ x : U, ∀ j ∈ s, x ∈ W j) ∧
      (∀ j : J, IsOpen (W j) ∧ (W j).Nonempty) ∧
      (⋃ j : J, W j = Set.univ) ∧ LocallyFinite W ∧
      (∀ j : J, e ∈ W j ↔ j = v0) ∧
      let N := P.Realization
      let n0 := PreAbstractSimplicialComplex.Realization.vertex P v0 hv0
      let cw := PreAbstractSimplicialComplex.Realization.classicalCWComplex P
      letI : Topology.CWComplex (Set.univ : Set N) := cw
      ∃ (p : C(U, N)) (q : C(N, U)),
        p e = n0 ∧ q n0 = e ∧
        ∃ H : ContinuousMap.HomotopyRel (q.comp p) (ContinuousMap.id U) ({e} : Set U),
          (∀ t : unitInterval, H (t, e) = e) ∧
          ∃ j : Topology.CWComplex.cell (Set.univ : Set N) 0,
            ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x = n0 := by
  choose B hBopen hBmem hBsquare hBstable using normedOpenConvexNeighborhood U hU
  let c : Interpolation U :=
    { domain := normedPairDomain U
      homotopy := normedPairHomotopy U
      stationary := normedPairHomotopy_stationary U
      neighborhood := B
      neighborhood_open := hBopen
      neighborhood_mem := hBmem
      neighborhood_square := fun x a ha b hb => hBsquare x a b ha hb
      neighborhood_stable := fun x a ha b hb hab t => hBstable x a b ha hb hab t }
  exact metric_based_CW_domination c e

end Topology.CWComplex.MetricDomination

public section

namespace Topology

/-- An open subset of a real normed space has an actual pointed CW domination,
constructed from convex balls and the existing locally finite nerve recipe. -/
theorem openNormedCWDomination {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hU : IsOpen U) (e : U) :
    ∃ (J : Type u) (P : PreAbstractSimplicialComplex J) (W : J → Set U)
      (v0 : J) (hv0 : {v0} ∈ P),
      (∀ s : Finset J, s ∈ P ↔ s.Nonempty ∧ ∃ x : U, ∀ j ∈ s, x ∈ W j) ∧
      (∀ j : J, IsOpen (W j) ∧ (W j).Nonempty) ∧
      (⋃ j : J, W j = Set.univ) ∧ LocallyFinite W ∧
      (∀ j : J, e ∈ W j ↔ j = v0) ∧
      let N := P.Realization
      let n0 := PreAbstractSimplicialComplex.Realization.vertex P v0 hv0
      let cw := PreAbstractSimplicialComplex.Realization.classicalCWComplex P
      letI : Topology.CWComplex (Set.univ : Set N) := cw
      ∃ (p : C(U, N)) (q : C(N, U)),
        p e = n0 ∧ q n0 = e ∧
        ∃ H : ContinuousMap.HomotopyRel (q.comp p) (ContinuousMap.id U) ({e} : Set U),
          (∀ t : unitInterval, H (t, e) = e) ∧
          ∃ j : Topology.CWComplex.cell (Set.univ : Set N) 0,
            ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x = n0 := by
  exact CWComplex.MetricDomination.normedOpenCWDomination U hU e

end Topology
