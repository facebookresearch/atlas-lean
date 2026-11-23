/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Joint interpolation on the strong metric realization and its raw based loops.
module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.MetricRealization
public import MathlibExt.AlgebraicTopology.SimplicialComplex.FiniteRelativeApproximation
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.Path
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Normalized minimum interpolation in metric realizations
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory Topology Filter Function Set
open scoped unitInterval NNReal
universe u z

namespace MetricLoopELCXSourceOnly37

private abbrev M {V : Type u} (P : PreAbstractSimplicialComplex V) :=
  PreAbstractSimplicialComplex.MetricRealization P

local instance : Fact ((1 : ℝ≥0) ≤ 1) := ⟨le_rfl⟩

-- This is raw barycentric data, not the continuous supported partition return.
private def originalPoint {V : Type u} (P : PreAbstractSimplicialComplex V) (x : M P) :
    P.Realization := Classical.choose x.property

private theorem originalPoint_weights {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : M P) : (originalPoint P x).point.weights = x.val.ofLp :=
  congrArg WithLp.ofLp (Classical.choose_spec x.property)

private theorem coordinate_nonneg {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : M P) (v : V) : 0 ≤ x.val.ofLp v := by
  rw [← originalPoint_weights P x]
  exact (originalPoint P x).point.nonneg v

private theorem coordinate_total {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : M P) : x.val.ofLp.sum (fun _ r => r) = 1 := by
  rw [← originalPoint_weights P x]
  exact (originalPoint P x).point.total

private theorem continuous_coordinate {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) : Continuous (fun x : M P => x.val.ofLp v) :=
  (PreAbstractSimplicialComplex.MetricRealization.continuous_iff_coordinates P
    (fun x : M P => x)).mp continuous_id v

private def minWeights {V : Type u} (P : PreAbstractSimplicialComplex V) (x y : M P) :
    V →₀ ℝ := x.val.ofLp.zipWith min (by simp) y.val.ofLp

private theorem minWeights_apply {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x y : M P) (v : V) : minWeights P x y v = min (x.val.ofLp v) (y.val.ofLp v) := by
  simp only [minWeights, Finsupp.zipWith_apply]

private theorem minWeights_nonneg {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x y : M P) (v : V) : 0 ≤ minWeights P x y v := by
  rw [minWeights_apply]
  exact le_min (coordinate_nonneg P x v) (coordinate_nonneg P y v)

open Classical in
private theorem minWeights_support {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x y : M P) :
    (minWeights P x y).support ⊆ x.val.ofLp.support ∩ y.val.ofLp.support := by
  intro v hv
  have hne := Finsupp.mem_support_iff.mp hv
  apply Finset.mem_inter.mpr
  constructor
  · by_contra hx
    have hx0 : x.val.ofLp v = 0 := Finsupp.notMem_support_iff.mp hx
    apply hne
    rw [minWeights_apply, hx0, min_eq_left (coordinate_nonneg P y v)]
  · by_contra hy
    have hy0 : y.val.ofLp v = 0 := Finsupp.notMem_support_iff.mp hy
    apply hne
    rw [minWeights_apply, hy0, min_eq_right (coordinate_nonneg P x v)]

private def mass {V : Type u} (P : PreAbstractSimplicialComplex V) (x y : M P) : ℝ :=
  (minWeights P x y).sum (fun _ r => r)

private theorem total_on {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : M P) (s : Finset V) (hs : x.val.ofLp.support ⊆ s) :
    ∑ v ∈ s, x.val.ofLp v = 1 := by
  have h := coordinate_total P x
  rw [Finsupp.sum_of_support_subset (s := s) _ hs _ (by simp)] at h
  exact h

-- Only the two points' own finite supports enter this identity.
private theorem distance_on {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x y : M P) (s : Finset V)
    (hx : x.val.ofLp.support ⊆ s) (hy : y.val.ofLp.support ⊆ s) :
    dist x y = ∑ v ∈ s, dist (x.val.ofLp v) (y.val.ofLp v) := by
  classical
  change dist x.val y.val = _
  rw [Finsupp.dist_def]
  simp only [NNReal.coe_one, inv_one, Real.rpow_one]
  rw [Finsupp.sum_of_support_subset (s := s) _
    ((Finsupp.support_zipWith).trans (Finset.union_subset hx hy)) _ (by simp)]
  simp only [Finsupp.zipWith_apply]

private theorem twice_min (a b : ℝ) : 2 * min a b = a + b - dist a b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [min_eq_right hba, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

private theorem mass_eq_distance {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x y : M P) : mass P x y = 1 - dist x y / 2 := by
  classical
  let s := x.val.ofLp.support ∪ y.val.ofLp.support
  have hm : mass P x y = ∑ v ∈ s, min (x.val.ofLp v) (y.val.ofLp v) := by
    unfold mass
    rw [Finsupp.sum_of_support_subset (s := s) (minWeights P x y)
      ((minWeights_support P x y).trans
        (Finset.inter_subset_left.trans Finset.subset_union_left))
      (fun (_ : V) (r : ℝ) => r) (fun _ _ => rfl)]
    simp only [minWeights_apply]
  have hx := total_on P x s Finset.subset_union_left
  have hy := total_on P y s Finset.subset_union_right
  have hd := distance_on P x y s Finset.subset_union_left Finset.subset_union_right
  have htwo : 2 * mass P x y = 2 - dist x y := by
    rw [hm, Finset.mul_sum]
    simp_rw [twice_min]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hx, hy, ← hd]
    ring
  linarith

private theorem mass_continuous {V : Type u} (P : PreAbstractSimplicialComplex V) :
    Continuous (fun p : M P × M P => mass P p.1 p.2) := by
  simp_rw [mass_eq_distance]
  exact continuous_const.sub ((continuous_fst.dist continuous_snd).div_const 2)

private def pairDomain {V : Type u} (P : PreAbstractSimplicialComplex V) :
    Set (M P × M P) := {p | 0 < mass P p.1 p.2}

private theorem pairDomain_open {V : Type u} (P : PreAbstractSimplicialComplex V) :
    IsOpen (pairDomain P) := isOpen_lt continuous_const (mass_continuous P)

private theorem pairDomain_iff_dist {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x y : M P) : (x, y) ∈ pairDomain P ↔ dist x y < 2 := by
  change 0 < mass P x y ↔ _
  rw [mass_eq_distance]
  constructor <;> intro h <;> linarith

private theorem mass_self {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : M P) : mass P x x = 1 := by
  rw [mass_eq_distance, dist_self]
  ring

private theorem diagonal_mem {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : M P) : (x, x) ∈ pairDomain P := by
  change 0 < mass P x x
  rw [mass_self]
  exact zero_lt_one

private def normalizedWeights {V : Type u} (P : PreAbstractSimplicialComplex V)
    (p : pairDomain P) : V →₀ ℝ := (mass P p.val.1 p.val.2)⁻¹ • minWeights P p.val.1 p.val.2

open Classical in
private theorem normalizedWeights_support {V : Type u}
    (P : PreAbstractSimplicialComplex V) (p : pairDomain P) :
    (normalizedWeights P p).support ⊆ p.val.1.val.ofLp.support ∩ p.val.2.val.ofLp.support :=
  Finsupp.support_smul.trans (minWeights_support P p.val.1 p.val.2)

private def commonSimplex {V : Type u} (P : PreAbstractSimplicialComplex V)
    (p : pairDomain P) : Convexity.StdSimplex ℝ V where
  weights := normalizedWeights P p
  nonneg v := by
    change 0 ≤ (mass P p.val.1 p.val.2)⁻¹ * minWeights P p.val.1 p.val.2 v
    exact mul_nonneg (inv_nonneg.mpr p.property.le) (minWeights_nonneg P _ _ v)
  total := by
    classical
    unfold normalizedWeights
    rw [Finsupp.sum_of_support_subset (s := (minWeights P p.val.1 p.val.2).support)
      ((mass P p.val.1 p.val.2)⁻¹ • minWeights P p.val.1 p.val.2)
      Finsupp.support_smul (fun (_ : V) (r : ℝ) => r) (fun _ _ => rfl)]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    change (mass P p.val.1 p.val.2)⁻¹ * mass P p.val.1 p.val.2 = 1
    exact inv_mul_cancel₀ p.property.ne'

open Classical in
private def commonWeakPoint {V : Type u} (P : PreAbstractSimplicialComplex V)
    (p : pairDomain P) : P.Realization where
  point := commonSimplex P p
  support_mem :=
    (P.isRelLowerSet_faces (originalPoint P p.val.1).support_mem).2
      (by
        change (normalizedWeights P p).support ⊆ (originalPoint P p.val.1).point.weights.support
        rw [originalPoint_weights]
        exact (normalizedWeights_support P p).trans Finset.inter_subset_left)
      (commonSimplex P p).support_weights_nonempty

private def commonPoint {V : Type u} (P : PreAbstractSimplicialComplex V)
    (p : pairDomain P) : M P :=
  PreAbstractSimplicialComplex.Realization.toMetric P (commonWeakPoint P p)

private theorem commonPoint_coordinate {V : Type u} (P : PreAbstractSimplicialComplex V)
    (p : pairDomain P) (v : V) :
    (commonPoint P p).val.ofLp v =
      (mass P p.val.1 p.val.2)⁻¹ * min (p.val.1.val.ofLp v) (p.val.2.val.ofLp v) := by
  rw [commonPoint, PreAbstractSimplicialComplex.Realization.toMetric_weights]
  change normalizedWeights P p v = _
  rw [normalizedWeights, Finsupp.smul_apply, smul_eq_mul, minWeights_apply]

open Classical in
private theorem commonPoint_support {V : Type u} (P : PreAbstractSimplicialComplex V)
    (p : pairDomain P) :
    (commonPoint P p).val.ofLp.support ⊆
      p.val.1.val.ofLp.support ∩ p.val.2.val.ofLp.support := by
  rw [commonPoint, PreAbstractSimplicialComplex.Realization.toMetric_weights]
  exact normalizedWeights_support P p

private theorem commonPoint_continuous {V : Type u} (P : PreAbstractSimplicialComplex V) :
    Continuous (commonPoint P) := by
  rw [PreAbstractSimplicialComplex.MetricRealization.continuous_iff_coordinates]
  intro v
  simp_rw [commonPoint_coordinate]
  exact ((mass_continuous P).comp continuous_subtype_val).inv₀
    (fun p => p.property.ne') |>.mul
      (((continuous_coordinate P v).comp
        (continuous_fst.comp continuous_subtype_val)).min
        ((continuous_coordinate P v).comp
          (continuous_snd.comp continuous_subtype_val)))

private theorem commonPoint_self {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : M P) : commonPoint P ⟨(x, x), diagonal_mem P x⟩ = x := by
  apply Subtype.ext
  apply (WithLp.ext_iff _).mpr
  apply Finsupp.ext
  intro v
  rw [commonPoint_coordinate, mass_self, min_self, inv_one, one_mul]

open Classical in
private def blendWeakPoint {V : Type u} (P : PreAbstractSimplicialComplex V)
    (t : unitInterval) (a b : M P) (h : b.val.ofLp.support ⊆ a.val.ofLp.support) :
    P.Realization where
  point := PreAbstractSimplicialComplex.Realization.segmentPoint t
    (originalPoint P a).point (originalPoint P b).point
  support_mem :=
    (P.isRelLowerSet_faces (originalPoint P a).support_mem).2
      ((PreAbstractSimplicialComplex.Realization.segmentPoint_support_subset t _ _).trans
        (Finset.union_subset (Finset.Subset.refl _)
          (by simpa only [originalPoint_weights] using h)))
      (PreAbstractSimplicialComplex.Realization.segmentPoint t _ _).support_weights_nonempty

private def blendValue {V : Type u} (P : PreAbstractSimplicialComplex V)
    (t : unitInterval) (a b : M P) (h : b.val.ofLp.support ⊆ a.val.ofLp.support) : M P :=
  PreAbstractSimplicialComplex.Realization.toMetric P (blendWeakPoint P t a b h)

private theorem blendValue_coordinate {V : Type u} (P : PreAbstractSimplicialComplex V)
    (t : unitInterval) (a b : M P) (h : b.val.ofLp.support ⊆ a.val.ofLp.support) (v : V) :
    (blendValue P t a b h).val.ofLp v =
      (1 - (t : ℝ)) * a.val.ofLp v + (t : ℝ) * b.val.ofLp v := by
  rw [blendValue, PreAbstractSimplicialComplex.Realization.toMetric_weights]
  change (PreAbstractSimplicialComplex.Realization.segmentPoint t
    (originalPoint P a).point (originalPoint P b).point).weights v = _
  rw [PreAbstractSimplicialComplex.Realization.segmentPoint_weights]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, originalPoint_weights]

-- No CompactSpace X premise: only the actual metric coordinate criterion is used.
private def blendHomotopy {V : Type u} (P : PreAbstractSimplicialComplex V)
    {X : Type z} [TopologicalSpace X] (f g : C(X, M P))
    (h : ∀ x, (g x).val.ofLp.support ⊆ (f x).val.ofLp.support) :
    ContinuousMap.Homotopy f g where
  toFun z := blendValue P z.1 (f z.2) (g z.2) (h z.2)
  continuous_toFun := by
    rw [PreAbstractSimplicialComplex.MetricRealization.continuous_iff_coordinates]
    intro v
    simp_rw [blendValue_coordinate]
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_coordinate P v).comp (f.continuous.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((continuous_coordinate P v).comp (g.continuous.comp continuous_snd)))
  map_zero_left x := by
    apply Subtype.ext
    apply (WithLp.ext_iff _).mpr
    apply Finsupp.ext
    intro v
    simp [blendValue_coordinate]
  map_one_left x := by
    apply Subtype.ext
    apply (WithLp.ext_iff _).mpr
    apply Finsupp.ext
    intro v
    simp [blendValue_coordinate]

private theorem blendHomotopy_fixed {V : Type u} (P : PreAbstractSimplicialComplex V)
    {X : Type z} [TopologicalSpace X] (f g : C(X, M P))
    (h : ∀ x, (g x).val.ofLp.support ⊆ (f x).val.ofLp.support)
    (x : X) (hx : f x = g x) (t : unitInterval) :
    blendHomotopy P f g h (t, x) = f x := by
  apply Subtype.ext
  apply (WithLp.ext_iff _).mpr
  apply Finsupp.ext
  intro v
  change (blendValue P t (f x) (g x) (h x)).val.ofLp v = (f x).val.ofLp v
  rw [blendValue_coordinate, ← hx]
  ring

private def firstMap {V : Type u} (P : PreAbstractSimplicialComplex V) :
    C(pairDomain P, M P) := ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩

private def secondMap {V : Type u} (P : PreAbstractSimplicialComplex V) :
    C(pairDomain P, M P) := ⟨fun p => p.val.2, continuous_snd.comp continuous_subtype_val⟩

private def commonMap {V : Type u} (P : PreAbstractSimplicialComplex V) :
    C(pairDomain P, M P) := ⟨commonPoint P, commonPoint_continuous P⟩

open Classical in
private def interpolation {V : Type u} (P : PreAbstractSimplicialComplex V) :
    ContinuousMap.Homotopy (firstMap P) (secondMap P) :=
  (blendHomotopy P (firstMap P) (commonMap P)
    (fun p => (commonPoint_support P p).trans Finset.inter_subset_left)).trans
      (blendHomotopy P (secondMap P) (commonMap P)
        (fun p => (commonPoint_support P p).trans Finset.inter_subset_right)).symm

private theorem interpolation_diagonal {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : M P) (t : unitInterval) :
    interpolation P (t, ⟨(x, x), diagonal_mem P x⟩) = x := by
  rw [interpolation, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact blendHomotopy_fixed P _ _ _ _ (commonPoint_self P x).symm _
  · rw [ContinuousMap.Homotopy.symm_apply]
    exact blendHomotopy_fixed P _ _ _ _ (commonPoint_self P x).symm _

private theorem interpolation_coordinate {V : Type u}
    (P : PreAbstractSimplicialComplex V) (t : unitInterval) (p : pairDomain P) (v : V) :
    (interpolation P (t, p)).val.ofLp v =
      if (t : ℝ) ≤ 1 / 2 then
        (1 - 2 * (t : ℝ)) * p.val.1.val.ofLp v +
          (2 * (t : ℝ)) * ((mass P p.val.1 p.val.2)⁻¹ *
            min (p.val.1.val.ofLp v) (p.val.2.val.ofLp v))
      else
        (2 * (t : ℝ) - 1) * p.val.2.val.ofLp v +
          (2 - 2 * (t : ℝ)) * ((mass P p.val.1 p.val.2)⁻¹ *
            min (p.val.1.val.ofLp v) (p.val.2.val.ofLp v)) := by
  classical
  rw [interpolation, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · change (blendValue P
      ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.property.1, ht⟩⟩
      p.val.1 (commonPoint P p)
      ((commonPoint_support P p).trans Finset.inter_subset_left)).val.ofLp v = _
    rw [blendValue_coordinate, commonPoint_coordinate]
  · rw [ContinuousMap.Homotopy.symm_apply]
    change (blendValue P (unitInterval.symm
      ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.mp ht).le, t.property.2⟩⟩)
      p.val.2 (commonPoint P p)
      ((commonPoint_support P p).trans Finset.inter_subset_right)).val.ofLp v = _
    rw [blendValue_coordinate, commonPoint_coordinate]
    simp only [unitInterval.coe_symm_eq]
    ring

private def star {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) : Set (M P) :=
  {x | 0 < x.val.ofLp v}

private theorem star_open {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) : IsOpen (star P v) := isOpen_lt continuous_const (continuous_coordinate P v)

private theorem star_cover {V : Type u} (P : PreAbstractSimplicialComplex V) :
    (Set.univ : Set (M P)) ⊆ ⋃ v, star P v := by
  intro x _
  obtain ⟨v, hv⟩ := (originalPoint P x).point.support_weights_nonempty
  have hne : x.val.ofLp v ≠ 0 := by
    rw [← originalPoint_weights P x]
    exact Finsupp.mem_support_iff.mp hv
  exact Set.mem_iUnion.mpr ⟨v, lt_of_le_of_ne (coordinate_nonneg P x v) hne.symm⟩

private theorem star_square_domain {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (a b : M P) (ha : a ∈ star P v) (hb : b ∈ star P v) :
    (a, b) ∈ pairDomain P := by
  classical
  have hpos : 0 < minWeights P a b v := by
    rw [minWeights_apply]
    exact lt_min ha hb
  have hv : v ∈ (minWeights P a b).support := Finsupp.mem_support_iff.mpr hpos.ne'
  have hle : minWeights P a b v ≤ mass P a b :=
    Finset.single_le_sum (fun w _ => minWeights_nonneg P a b w) hv
  exact hpos.trans_le hle

private theorem commonPoint_star {V : Type u} (P : PreAbstractSimplicialComplex V)
    (p : pairDomain P) (v : V) (ha : p.val.1 ∈ star P v) (hb : p.val.2 ∈ star P v) :
    commonPoint P p ∈ star P v := by
  change 0 < (commonPoint P p).val.ofLp v
  rw [commonPoint_coordinate]
  exact mul_pos (inv_pos.mpr p.property) (lt_min ha hb)

private theorem positive_blend (t : unitInterval) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < (1 - (t : ℝ)) * a + (t : ℝ) * b := by
  by_cases ht : (t : ℝ) = 1
  · rw [ht]
    simpa using hb
  · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr hlt) ha) (mul_nonneg t.property.1 hb.le)

private theorem blendHomotopy_star {V : Type u} (P : PreAbstractSimplicialComplex V)
    {X : Type z} [TopologicalSpace X] (f g : C(X, M P))
    (h : ∀ x, (g x).val.ofLp.support ⊆ (f x).val.ofLp.support)
    (x : X) (v : V) (hf : f x ∈ star P v) (hg : g x ∈ star P v) (t : unitInterval) :
    blendHomotopy P f g h (t, x) ∈ star P v := by
  change 0 < (blendValue P t (f x) (g x) (h x)).val.ofLp v
  rw [blendValue_coordinate]
  exact positive_blend t hf hg

private theorem interpolation_star {V : Type u} (P : PreAbstractSimplicialComplex V)
    (p : pairDomain P) (v : V) (ha : p.val.1 ∈ star P v) (hb : p.val.2 ∈ star P v)
    (t : unitInterval) : interpolation P (t, p) ∈ star P v := by
  rw [interpolation, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact blendHomotopy_star P _ _ _ p v ha (commonPoint_star P p v ha hb) _
  · rw [ContinuousMap.Homotopy.symm_apply]
    exact blendHomotopy_star P _ _ _ p v hb (commonPoint_star P p v ha hb) _

-- Pull back the existing compact-domain ContinuousMap metric along the genuine
-- raw path embedding; replaceTopology preserves the original compact-open topology.
@[instance_reducible]
private def rawLoopMetric {V : Type u} (P : PreAbstractSimplicialComplex V) (a : M P) :
    MetricSpace (Path a a) :=
  Topology.IsEmbedding.comapMetricSpace
    ((↑) : Path a a → C(unitInterval, M P)) Path.isUniformEmbedding_coe.isEmbedding

private theorem rawLoopMetric_topology {V : Type u} (P : PreAbstractSimplicialComplex V)
    (a : M P) :
    (rawLoopMetric P a).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (Path a a)) :=
  rfl


private abbrev L {V : Type u} (P : PreAbstractSimplicialComplex V) (a : M P) := Path a a

private def pairPathMap {V : Type u} (P : PreAbstractSimplicialComplex V) (a : M P) :
    C(L P a × L P a, C(unitInterval, M P × M P)) where
  toFun p := p.1.toContinuousMap.prodMk p.2.toContinuousMap
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (L P a × L P a) × unitInterval =>
      (z.1.1 z.2, z.1.2 z.2))
    exact (continuous_eval.comp
      ((continuous_fst.fst).prodMk continuous_snd)).prodMk
      (continuous_eval.comp ((continuous_fst.snd).prodMk continuous_snd))

private def loopDomain {V : Type u} (P : PreAbstractSimplicialComplex V) (a : M P) :
    Set (L P a × L P a) := {p | ∀ t, (p.1 t, p.2 t) ∈ pairDomain P}

private theorem loopDomain_open {V : Type u} (P : PreAbstractSimplicialComplex V)
    (a : M P) : IsOpen (loopDomain P a) := by
  have h := ContinuousMap.isOpen_setOfPred_mapsTo
    (isCompact_univ : IsCompact (Set.univ : Set unitInterval)) (pairDomain_open P)
  have heq : loopDomain P a = (pairPathMap P a) ⁻¹'
      {f : C(unitInterval, M P × M P) | Set.MapsTo f Set.univ (pairDomain P)} := by
    ext p
    change (∀ t, (p.1 t, p.2 t) ∈ pairDomain P) ↔
      ∀ t, t ∈ Set.univ → (pairPathMap P a p) t ∈ pairDomain P
    simp only [Set.mem_univ, forall_const]
    rfl
  rw [heq]
  exact h.preimage (pairPathMap P a).continuous

private theorem loopDiagonal_mem {V : Type u} (P : PreAbstractSimplicialComplex V)
    (a : M P) (γ : L P a) : (γ, γ) ∈ loopDomain P a := fun t => diagonal_mem P (γ t)

private def pointPair {V : Type u} (P : PreAbstractSimplicialComplex V) (a : M P)
    (p : loopDomain P a) (t : unitInterval) : pairDomain P :=
  ⟨(p.val.1 t, p.val.2 t), p.property t⟩

private theorem pointPair_continuous {V : Type u} (P : PreAbstractSimplicialComplex V)
    (a : M P) : Continuous (fun z : loopDomain P a × unitInterval => pointPair P a z.1 z.2) :=
  ((continuous_eval.comp
      (((continuous_fst.comp continuous_subtype_val).comp continuous_fst).prodMk
        continuous_snd)).prodMk
    (continuous_eval.comp
      (((continuous_snd.comp continuous_subtype_val).comp continuous_fst).prodMk
        continuous_snd))).subtype_mk _

private theorem pointPair_zero {V : Type u} (P : PreAbstractSimplicialComplex V)
    (a : M P) (p : loopDomain P a) :
    pointPair P a p 0 = ⟨(a, a), diagonal_mem P a⟩ := by
  apply Subtype.ext
  exact Prod.ext p.val.1.source p.val.2.source

private theorem pointPair_one {V : Type u} (P : PreAbstractSimplicialComplex V)
    (a : M P) (p : loopDomain P a) :
    pointPair P a p 1 = ⟨(a, a), diagonal_mem P a⟩ := by
  apply Subtype.ext
  exact Prod.ext p.val.1.target p.val.2.target

private def loopValue {V : Type u} (P : PreAbstractSimplicialComplex V) (a : M P)
    (t : unitInterval) (p : loopDomain P a) : L P a :=
  Path.mk
    ⟨fun r => interpolation P (t, pointPair P a p r),
      (interpolation P).continuous.comp
        (continuous_const.prodMk
          ((pointPair_continuous P a).comp (continuous_const.prodMk continuous_id)))⟩
    (by
      change interpolation P (t, pointPair P a p 0) = a
      rw [pointPair_zero]
      exact interpolation_diagonal P a t)
    (by
      change interpolation P (t, pointPair P a p 1) = a
      rw [pointPair_one]
      exact interpolation_diagonal P a t)

private theorem loopValue_continuous {V : Type u} (P : PreAbstractSimplicialComplex V)
    (a : M P) :
    Continuous (fun z : unitInterval × loopDomain P a => loopValue P a z.1 z.2) := by
  apply Path.continuous_uncurry_iff.mp
  change Continuous (fun z : (unitInterval × loopDomain P a) × unitInterval =>
    interpolation P (z.1.1, pointPair P a z.1.2 z.2))
  exact (interpolation P).continuous.comp
    ((continuous_fst.comp continuous_fst).prodMk
      ((pointPair_continuous P a).comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))

private def loopFirst {V : Type u} (P : PreAbstractSimplicialComplex V) (a : M P) :
    C(loopDomain P a, L P a) := ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩

private def loopSecond {V : Type u} (P : PreAbstractSimplicialComplex V) (a : M P) :
    C(loopDomain P a, L P a) := ⟨fun p => p.val.2, continuous_snd.comp continuous_subtype_val⟩

private def loopInterpolation {V : Type u} (P : PreAbstractSimplicialComplex V) (a : M P) :
    ContinuousMap.Homotopy (loopFirst P a) (loopSecond P a) where
  toFun z := loopValue P a z.1 z.2
  continuous_toFun := loopValue_continuous P a
  map_zero_left p := by
    apply Path.ext
    funext r
    exact (interpolation P).apply_zero (pointPair P a p r)
  map_one_left p := by
    apply Path.ext
    funext r
    exact (interpolation P).apply_one (pointPair P a p r)

private theorem loopInterpolation_diagonal {V : Type u}
    (P : PreAbstractSimplicialComplex V) (a : M P) (γ : L P a) (t : unitInterval) :
    loopInterpolation P a (t, ⟨(γ, γ), loopDiagonal_mem P a γ⟩) = γ := by
  apply Path.ext
  funext r
  exact interpolation_diagonal P (γ r) t

private theorem constantLoop_fixed {V : Type u} (P : PreAbstractSimplicialComplex V)
    (a : M P) (t : unitInterval) :
    loopInterpolation P a
      (t, ⟨(Path.refl a, Path.refl a), loopDiagonal_mem P a (Path.refl a)⟩) = Path.refl a :=
  loopInterpolation_diagonal P a (Path.refl a) t

-- A finite OPEN-STAR cover, not a finite carrier for the strong compact image.
private theorem finite_compact_star_time_cover {V : Type u}
    (P : PreAbstractSimplicialComplex V) (a : M P) (γ : L P a) :
    ∃ (s : Finset unitInterval) (K : unitInterval → Set unitInterval) (v : unitInterval → V),
      (∀ c ∈ s, IsCompact (K c)) ∧
      (Set.univ : Set unitInterval) ⊆ ⋃ c ∈ s, K c ∧
      ∀ c ∈ s, Set.MapsTo γ (K c) (star P (v c)) := by
  classical
  have hp : ∀ r : unitInterval, ∃ v : V, γ r ∈ star P v := by
    intro r
    exact Set.mem_iUnion.mp (star_cover P (Set.mem_univ (γ r)))
  choose v hv using hp
  have hr : ∀ r : unitInterval, ∃ ε : ℝ, 0 < ε ∧
      Metric.ball r ε ⊆ γ ⁻¹' star P (v r) := by
    intro r
    exact Metric.isOpen_iff.mp ((star_open P (v r)).preimage γ.continuous) r (hv r)
  choose ε hε hball using hr
  have hcover : (Set.univ : Set unitInterval) ⊆ ⋃ r : unitInterval, Metric.ball r (ε r / 2) := by
    intro r _
    exact Set.mem_iUnion.mpr ⟨r, Metric.mem_ball_self (half_pos (hε r))⟩
  obtain ⟨s, hs⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set unitInterval)).elim_finite_subcover
      (fun r => Metric.ball r (ε r / 2)) (fun _ => Metric.isOpen_ball) hcover
  refine ⟨s, (fun r => Metric.closedBall r (ε r / 2)), v, ?_, ?_, ?_⟩
  · intro c hc
    exact Metric.isClosed_closedBall.isCompact
  · intro r hr
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hs hr)
    obtain ⟨hcs, hcr⟩ := Set.mem_iUnion.mp hc
    exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hcs, Metric.ball_subset_closedBall hcr⟩⟩
  · intro c hc r hr
    apply hball c
    exact lt_of_le_of_lt hr (half_lt_self (hε c))

private def loopNeighborhood {V : Type u} (P : PreAbstractSimplicialComplex V) (a : M P)
    (s : Finset unitInterval) (K : unitInterval → Set unitInterval) (v : unitInterval → V) :
    Set (L P a) := {γ | ∀ c ∈ s, Set.MapsTo γ (K c) (star P (v c))}

private theorem loopNeighborhood_open {V : Type u} (P : PreAbstractSimplicialComplex V)
    (a : M P) (s : Finset unitInterval) (K : unitInterval → Set unitInterval)
    (v : unitInterval → V) (hK : ∀ c ∈ s, IsCompact (K c)) :
    IsOpen (loopNeighborhood P a s K v) := by
  have heq : loopNeighborhood P a s K v =
      ⋂ c ∈ s, {γ : L P a | Set.MapsTo γ (K c) (star P (v c))} := by
    ext γ
    simp only [loopNeighborhood, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  apply isOpen_biInter_finset
  intro c hc
  exact (ContinuousMap.isOpen_setOfPred_mapsTo (hK c hc) (star_open P (v c))).preimage
    (continuous_induced_dom : Continuous ((↑) : L P a → C(unitInterval, M P)))

private theorem loopNeighborhood_square {V : Type u} (P : PreAbstractSimplicialComplex V)
    (a : M P) (s : Finset unitInterval) (K : unitInterval → Set unitInterval)
    (v : unitInterval → V) (hcover : (Set.univ : Set unitInterval) ⊆ ⋃ c ∈ s, K c)
    (γ δ : L P a) (hγ : γ ∈ loopNeighborhood P a s K v)
    (hδ : δ ∈ loopNeighborhood P a s K v) : (γ, δ) ∈ loopDomain P a := by
  intro r
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ r))
  obtain ⟨hcs, hcr⟩ := Set.mem_iUnion.mp hc
  exact star_square_domain P (v c) (γ r) (δ r) (hγ c hcs hcr) (hδ c hcs hcr)

private theorem loopNeighborhood_stable {V : Type u} (P : PreAbstractSimplicialComplex V)
    (a : M P) (s : Finset unitInterval) (K : unitInterval → Set unitInterval)
    (v : unitInterval → V) (γ δ : L P a) (hγ : γ ∈ loopNeighborhood P a s K v)
    (hδ : δ ∈ loopNeighborhood P a s K v) (hpair : (γ, δ) ∈ loopDomain P a)
    (t : unitInterval) :
    loopInterpolation P a (t, ⟨(γ, δ), hpair⟩) ∈ loopNeighborhood P a s K v := by
  intro c hc r hr
  exact interpolation_star P (pointPair P a ⟨(γ, δ), hpair⟩ r) (v c)
    (hγ c hc hr) (hδ c hc hr) t

private theorem every_loop_convex_neighborhood {V : Type u}
    (P : PreAbstractSimplicialComplex V) (a : M P) (γ : L P a) :
    ∃ N : Set (L P a), IsOpen N ∧ γ ∈ N ∧
      (∀ δ ε : L P a, δ ∈ N → ε ∈ N → (δ, ε) ∈ loopDomain P a) ∧
      ∀ (δ ε : L P a), δ ∈ N → ε ∈ N →
        ∀ (hpair : (δ, ε) ∈ loopDomain P a) (t : unitInterval),
        loopInterpolation P a (t, ⟨(δ, ε), hpair⟩) ∈ N := by
  obtain ⟨s, K, v, hK, hcover, hγ⟩ := finite_compact_star_time_cover P a γ
  refine ⟨loopNeighborhood P a s K v, loopNeighborhood_open P a s K v hK, hγ, ?_, ?_⟩
  · intro δ ε hδ hε
    exact loopNeighborhood_square P a s K v hcover δ ε hδ hε
  · intro δ ε hδ hε hpair t
    exact loopNeighborhood_stable P a s K v δ ε hδ hε hpair t

private theorem constantLoop_closed {V : Type u} (P : PreAbstractSimplicialComplex V)
    (a : M P) : IsClosed ({Path.refl a} : Set (L P a)) := by
  let _ : MetricSpace (L P a) := rawLoopMetric P a
  exact isClosed_singleton

-- The principal original target: all loop components, both endpoint laws,
-- diagonal stationarity, a lambda-convex open cover, and the literal point.
-- No ELCX/metric/CW/inverse packet is an input to this conclusion.
private theorem whole_metric_loop_ELCX {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) :
    let a := PreAbstractSimplicialComplex.Realization.toMetric P
      (PreAbstractSimplicialComplex.Realization.vertex P v hv)
    let e : L P a := Path.refl a
    ∃ d : MetricSpace (L P a),
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (L P a)) ∧
    ∃ U : Set (L P a × L P a), IsOpen U ∧ (∀ γ : L P a, (γ, γ) ∈ U) ∧
      ∃ H : ContinuousMap.Homotopy
        (⟨fun p : U => p.val.1, continuous_fst.comp continuous_subtype_val⟩ : C(U, L P a))
        (⟨fun p : U => p.val.2, continuous_snd.comp continuous_subtype_val⟩ : C(U, L P a)),
        (∀ (γ : L P a) (hγ : (γ, γ) ∈ U) (t : unitInterval), H (t, ⟨(γ, γ), hγ⟩) = γ) ∧
        (∀ γ : L P a, ∃ N : Set (L P a), IsOpen N ∧ γ ∈ N ∧
          (∀ δ ε : L P a, δ ∈ N → ε ∈ N → (δ, ε) ∈ U) ∧
          ∀ (δ ε : L P a), δ ∈ N → ε ∈ N →
            ∀ (hpair : (δ, ε) ∈ U) (t : unitInterval), H (t, ⟨(δ, ε), hpair⟩) ∈ N) ∧
        IsClosed ({e} : Set (L P a)) := by
  let a := PreAbstractSimplicialComplex.Realization.toMetric P
    (PreAbstractSimplicialComplex.Realization.vertex P v hv)
  refine ⟨rawLoopMetric P a, rawLoopMetric_topology P a,
    loopDomain P a, loopDomain_open P a, loopDiagonal_mem P a,
    loopInterpolation P a, ?_, every_loop_convex_neighborhood P a, constantLoop_closed P a⟩
  intro γ hγ t
  exact loopInterpolation_diagonal P a γ t

end MetricLoopELCXSourceOnly37

public section

namespace PreAbstractSimplicialComplex

/-- The full raw metric-loop ELCX structure, including its original topology and literal point. -/
theorem metricLoopLocalConvexity {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) :
    let a : MetricRealization P := Realization.toMetric P (Realization.vertex P v hv)
    let e : Path a a := Path.refl a
    ∃ d : MetricSpace (Path a a),
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (Path a a)) ∧
    ∃ U : Set (Path a a × Path a a), IsOpen U ∧ (∀ γ : Path a a, (γ, γ) ∈ U) ∧
      ∃ H : ContinuousMap.Homotopy
        (⟨fun p : U => p.val.1, continuous_fst.comp continuous_subtype_val⟩ : C(U, Path a a))
        (⟨fun p : U => p.val.2, continuous_snd.comp continuous_subtype_val⟩ : C(U, Path a a)),
        (∀ (γ : Path a a) (hγ : (γ, γ) ∈ U) (t : unitInterval),
          H (t, ⟨(γ, γ), hγ⟩) = γ) ∧
        (∀ γ : Path a a, ∃ N : Set (Path a a), IsOpen N ∧ γ ∈ N ∧
          (∀ δ ε : Path a a, δ ∈ N → ε ∈ N → (δ, ε) ∈ U) ∧
          ∀ (δ ε : Path a a), δ ∈ N → ε ∈ N →
            ∀ (hpair : (δ, ε) ∈ U) (t : unitInterval), H (t, ⟨(δ, ε), hpair⟩) ∈ N) ∧
        IsClosed ({e} : Set (Path a a)) := by
  exact MetricLoopELCXSourceOnly37.whole_metric_loop_ELCX P v hv

end PreAbstractSimplicialComplex

/-! ## The original normalized-minimum point and loop interpolation API -/

public section

namespace PreAbstractSimplicialComplex.MetricRealization

variable {V : Type u} (P : PreAbstractSimplicialComplex V)

/-- Total coordinate overlap of the two original metric barycentric points. -/
def minMass (x y : MetricRealization P) : ℝ := MetricLoopELCXSourceOnly37.mass P x y

private theorem minMass_formula_computed (x y : MetricRealization P) :
    minMass P x y =
      (x.val.ofLp.zipWith min (by simp) y.val.ofLp).sum (fun _ r => r) := rfl

/-- The overlap is the exact finite sum of the coordinatewise minima. -/
theorem minMass_formula (x y : MetricRealization P) :
    minMass P x y =
      (x.val.ofLp.zipWith min (by simp) y.val.ofLp).sum (fun _ r => r) :=
  minMass_formula_computed P x y

/-- The original overlap mass is one minus half the original L1 distance. -/
theorem minMass_eq_distance (x y : MetricRealization P) :
    minMass P x y = 1 - dist x y / 2 :=
  MetricLoopELCXSourceOnly37.mass_eq_distance P x y

/-- Overlap mass is jointly continuous in the original metric topology. -/
theorem continuous_minMass :
    Continuous (fun p : MetricRealization P × MetricRealization P => minMass P p.1 p.2) :=
  MetricLoopELCXSourceOnly37.mass_continuous P

/-- A point has its original total mass one on the diagonal. -/
theorem minMass_self (x : MetricRealization P) : minMass P x x = 1 :=
  MetricLoopELCXSourceOnly37.mass_self P x

/-- The positive-overlap domain of the existing normalized-minimum interpolation. -/
def minPairDomain : Set (MetricRealization P × MetricRealization P) :=
  MetricLoopELCXSourceOnly37.pairDomain P

private theorem mem_minPairDomain_computed (x y : MetricRealization P) :
    (x, y) ∈ minPairDomain P ↔ 0 < minMass P x y := Iff.rfl

/-- Membership keeps exactly the original positive minimum-mass condition. -/
theorem mem_minPairDomain (x y : MetricRealization P) :
    (x, y) ∈ minPairDomain P ↔ 0 < minMass P x y :=
  mem_minPairDomain_computed P x y

/-- The original positive-overlap domain is open. -/
theorem isOpen_minPairDomain : IsOpen (minPairDomain P) :=
  MetricLoopELCXSourceOnly37.pairDomain_open P

/-- The overlap domain retains the exact original distance threshold. -/
theorem mem_minPairDomain_iff_dist (x y : MetricRealization P) :
    (x, y) ∈ minPairDomain P ↔ dist x y < 2 :=
  MetricLoopELCXSourceOnly37.pairDomain_iff_dist P x y

/-- Every original diagonal point belongs to the overlap domain. -/
theorem diagonal_mem_minPairDomain (x : MetricRealization P) :
    (x, x) ∈ minPairDomain P := MetricLoopELCXSourceOnly37.diagonal_mem P x

/-- The original common point obtained by normalizing coordinatewise minima. -/
def normalizedMinPoint (p : minPairDomain P) : MetricRealization P :=
  MetricLoopELCXSourceOnly37.commonPoint P p

/-- Every common-point coordinate uses the exact original minimum and mass. -/
theorem normalizedMinPoint_coordinate (p : minPairDomain P) (v : V) :
    (normalizedMinPoint P p).val.ofLp v =
      (minMass P p.val.1 p.val.2)⁻¹ * min (p.val.1.val.ofLp v) (p.val.2.val.ofLp v) :=
  MetricLoopELCXSourceOnly37.commonPoint_coordinate P p v

open Classical in
/-- The normalized minimum lies in both original finite coordinate supports. -/
theorem normalizedMinPoint_support (p : minPairDomain P) :
    (normalizedMinPoint P p).val.ofLp.support ⊆
      p.val.1.val.ofLp.support ∩ p.val.2.val.ofLp.support :=
  MetricLoopELCXSourceOnly37.commonPoint_support P p

/-- The original normalized common point is continuous on positive overlap. -/
theorem continuous_normalizedMinPoint : Continuous (normalizedMinPoint P) :=
  MetricLoopELCXSourceOnly37.commonPoint_continuous P

/-- The normalized minimum is the same original point on the diagonal. -/
theorem normalizedMinPoint_self (x : MetricRealization P) :
    normalizedMinPoint P ⟨(x, x), diagonal_mem_minPairDomain P x⟩ = x :=
  MetricLoopELCXSourceOnly37.commonPoint_self P x

/-- The original coordinate star of a metric barycentric point. -/
def coordinateStar (v : V) : Set (MetricRealization P) :=
  MetricLoopELCXSourceOnly37.star P v

private theorem mem_coordinateStar_computed (v : V) (x : MetricRealization P) :
    x ∈ coordinateStar P v ↔ 0 < x.val.ofLp v := Iff.rfl

/-- Coordinate-star membership is the original strict coordinate positivity. -/
theorem mem_coordinateStar (v : V) (x : MetricRealization P) :
    x ∈ coordinateStar P v ↔ 0 < x.val.ofLp v :=
  mem_coordinateStar_computed P v x

/-- Every original coordinate star is open in the metric realization. -/
theorem isOpen_coordinateStar (v : V) : IsOpen (coordinateStar P v) :=
  MetricLoopELCXSourceOnly37.star_open P v

/-- The original coordinate stars cover all metric barycentric points. -/
theorem coordinateStar_cover :
    (Set.univ : Set (MetricRealization P)) ⊆ ⋃ v, coordinateStar P v :=
  MetricLoopELCXSourceOnly37.star_cover P

/-- A coordinate star shared by two endpoints supplies positive overlap. -/
theorem coordinateStar_square_minPairDomain (v : V) (x y : MetricRealization P)
    (hx : x ∈ coordinateStar P v) (hy : y ∈ coordinateStar P v) :
    (x, y) ∈ minPairDomain P :=
  MetricLoopELCXSourceOnly37.star_square_domain P v x y hx hy

/-- Normalizing the minima preserves every coordinate star shared by both endpoints. -/
theorem normalizedMinPoint_mem_coordinateStar (p : minPairDomain P) (v : V)
    (hx : p.val.1 ∈ coordinateStar P v) (hy : p.val.2 ∈ coordinateStar P v) :
    normalizedMinPoint P p ∈ coordinateStar P v :=
  MetricLoopELCXSourceOnly37.commonPoint_star P p v hx hy

/-- The existing two-stage homotopy through the normalized coordinate minimum.
Joint continuity is part of this same original homotopy. -/
def minInterpolation : ContinuousMap.Homotopy
    (⟨fun p : minPairDomain P => p.val.1,
      continuous_fst.comp continuous_subtype_val⟩ : C(minPairDomain P, MetricRealization P))
    (⟨fun p : minPairDomain P => p.val.2,
      continuous_snd.comp continuous_subtype_val⟩ : C(minPairDomain P, MetricRealization P)) :=
  MetricLoopELCXSourceOnly37.interpolation P

/-- Every coordinate follows the original half-interval affine clocks and minimum mass. -/
theorem minInterpolation_coordinate (t : unitInterval) (p : minPairDomain P) (v : V) :
    (minInterpolation P (t, p)).val.ofLp v =
      if (t : ℝ) ≤ 1 / 2 then
        (1 - 2 * (t : ℝ)) * p.val.1.val.ofLp v +
          (2 * (t : ℝ)) * ((minMass P p.val.1 p.val.2)⁻¹ *
            min (p.val.1.val.ofLp v) (p.val.2.val.ofLp v))
      else
        (2 * (t : ℝ) - 1) * p.val.2.val.ofLp v +
          (2 - 2 * (t : ℝ)) * ((minMass P p.val.1 p.val.2)⁻¹ *
            min (p.val.1.val.ofLp v) (p.val.2.val.ofLp v)) :=
  MetricLoopELCXSourceOnly37.interpolation_coordinate P t p v

/-- The original point interpolation begins at its entire first endpoint. -/
theorem minInterpolation_zero (p : minPairDomain P) :
    minInterpolation P (0, p) = p.val.1 :=
  (MetricLoopELCXSourceOnly37.interpolation P).apply_zero p

/-- The original point interpolation ends at its entire second endpoint. -/
theorem minInterpolation_one (p : minPairDomain P) :
    minInterpolation P (1, p) = p.val.2 :=
  (MetricLoopELCXSourceOnly37.interpolation P).apply_one p

/-- Every original point diagonal stays stationary at every outer time. -/
theorem minInterpolation_diagonal (x : MetricRealization P)
    (hx : (x, x) ∈ minPairDomain P) (t : unitInterval) :
    minInterpolation P (t, ⟨(x, x), hx⟩) = x :=
  MetricLoopELCXSourceOnly37.interpolation_diagonal P x t

/-- Every outer time preserves every coordinate star shared by the original endpoints. -/
theorem minInterpolation_mem_coordinateStar (p : minPairDomain P) (v : V)
    (hx : p.val.1 ∈ coordinateStar P v) (hy : p.val.2 ∈ coordinateStar P v)
    (t : unitInterval) : minInterpolation P (t, p) ∈ coordinateStar P v :=
  MetricLoopELCXSourceOnly37.interpolation_star P p v hx hy t

variable (a : MetricRealization P)

/-- Original metric-target based-loop pairs with positive overlap at every inner time. -/
def minLoopDomain : Set (Path a a × Path a a) :=
  MetricLoopELCXSourceOnly37.loopDomain P a

private theorem mem_minLoopDomain_computed (γ δ : Path a a) :
    (γ, δ) ∈ minLoopDomain P a ↔ ∀ r : unitInterval, (γ r, δ r) ∈ minPairDomain P := Iff.rfl

/-- Loop-domain membership retains the full point-pair condition at every inner time. -/
theorem mem_minLoopDomain (γ δ : Path a a) :
    (γ, δ) ∈ minLoopDomain P a ↔ ∀ r : unitInterval, (γ r, δ r) ∈ minPairDomain P :=
  mem_minLoopDomain_computed P a γ δ

/-- The original loop overlap domain is open for the original compact-open path topology. -/
theorem isOpen_minLoopDomain : IsOpen (minLoopDomain P a) :=
  MetricLoopELCXSourceOnly37.loopDomain_open P a

/-- Every original based-loop diagonal is in the full overlap domain. -/
theorem diagonal_mem_minLoopDomain (γ : Path a a) :
    (γ, γ) ∈ minLoopDomain P a := MetricLoopELCXSourceOnly37.loopDiagonal_mem P a γ

/-- The original endpoint pair at the same inner time, carrying its earned overlap proof. -/
def minLoopPointPair (p : minLoopDomain P a) (r : unitInterval) : minPairDomain P :=
  MetricLoopELCXSourceOnly37.pointPair P a p r

private theorem minLoopPointPair_val_computed (p : minLoopDomain P a) (r : unitInterval) :
    (minLoopPointPair P a p r).val = (p.val.1 r, p.val.2 r) := rfl

/-- Both original point coordinates keep the same inner loop time. -/
theorem minLoopPointPair_val (p : minLoopDomain P a) (r : unitInterval) :
    (minLoopPointPair P a p r).val = (p.val.1 r, p.val.2 r) :=
  minLoopPointPair_val_computed P a p r

/-- The original inner-time endpoint pair is jointly continuous in loops and time. -/
theorem continuous_minLoopPointPair :
    Continuous (fun z : minLoopDomain P a × unitInterval => minLoopPointPair P a z.1 z.2) :=
  MetricLoopELCXSourceOnly37.pointPair_continuous P a

/-- The original pointwise normalized-minimum homotopy of metric-target based loops.
Both inner endpoints remain the original base point, and joint continuity is retained. -/
def minLoopInterpolation : ContinuousMap.Homotopy
    (⟨fun p : minLoopDomain P a => p.val.1,
      continuous_fst.comp continuous_subtype_val⟩ : C(minLoopDomain P a, Path a a))
    (⟨fun p : minLoopDomain P a => p.val.2,
      continuous_snd.comp continuous_subtype_val⟩ : C(minLoopDomain P a, Path a a)) :=
  MetricLoopELCXSourceOnly37.loopInterpolation P a

private theorem minLoopInterpolation_apply_computed (t : unitInterval)
    (p : minLoopDomain P a) (r : unitInterval) :
    minLoopInterpolation P a (t, p) r =
      minInterpolation P (t, minLoopPointPair P a p r) := rfl

/-- Both independent clocks use the original point interpolation at that same inner time. -/
theorem minLoopInterpolation_apply (t : unitInterval) (p : minLoopDomain P a)
    (r : unitInterval) :
    minLoopInterpolation P a (t, p) r = minInterpolation P (t, minLoopPointPair P a p r) :=
  minLoopInterpolation_apply_computed P a t p r

/-- Every loop coordinate retains the original minimum-mass and both affine outer clocks. -/
theorem minLoopInterpolation_coordinate (t : unitInterval) (p : minLoopDomain P a)
    (r : unitInterval) (v : V) :
    (minLoopInterpolation P a (t, p) r).val.ofLp v =
      if (t : ℝ) ≤ 1 / 2 then
        (1 - 2 * (t : ℝ)) * (p.val.1 r).val.ofLp v +
          (2 * (t : ℝ)) * ((minMass P (p.val.1 r) (p.val.2 r))⁻¹ *
            min ((p.val.1 r).val.ofLp v) ((p.val.2 r).val.ofLp v))
      else
        (2 * (t : ℝ) - 1) * (p.val.2 r).val.ofLp v +
          (2 - 2 * (t : ℝ)) * ((minMass P (p.val.1 r) (p.val.2 r))⁻¹ *
            min ((p.val.1 r).val.ofLp v) ((p.val.2 r).val.ofLp v)) := by
  rw [minLoopInterpolation_apply, minInterpolation_coordinate]
  rw [minLoopPointPair_val]

/-- The original loop interpolation begins at the entire first loop. -/
theorem minLoopInterpolation_zero (p : minLoopDomain P a) :
    minLoopInterpolation P a (0, p) = p.val.1 :=
  (MetricLoopELCXSourceOnly37.loopInterpolation P a).apply_zero p

/-- The original loop interpolation ends at the entire second loop. -/
theorem minLoopInterpolation_one (p : minLoopDomain P a) :
    minLoopInterpolation P a (1, p) = p.val.2 :=
  (MetricLoopELCXSourceOnly37.loopInterpolation P a).apply_one p

/-- Every outer time retains the original inner source endpoint. -/
theorem minLoopInterpolation_source (t : unitInterval) (p : minLoopDomain P a) :
    minLoopInterpolation P a (t, p) 0 = a := (minLoopInterpolation P a (t, p)).source

/-- Every outer time retains the original inner target endpoint. -/
theorem minLoopInterpolation_target (t : unitInterval) (p : minLoopDomain P a) :
    minLoopInterpolation P a (t, p) 1 = a := (minLoopInterpolation P a (t, p)).target

/-- Every original loop diagonal is stationary as a whole loop at every outer time. -/
theorem minLoopInterpolation_diagonal (γ : Path a a)
    (hγ : (γ, γ) ∈ minLoopDomain P a) (t : unitInterval) :
    minLoopInterpolation P a (t, ⟨(γ, γ), hγ⟩) = γ :=
  MetricLoopELCXSourceOnly37.loopInterpolation_diagonal P a γ t

/-- Both clocks preserve each original coordinate star shared at that inner time. -/
theorem minLoopInterpolation_mem_coordinateStar (t : unitInterval) (p : minLoopDomain P a)
    (r : unitInterval) (v : V)
    (hγ : p.val.1 r ∈ coordinateStar P v) (hδ : p.val.2 r ∈ coordinateStar P v) :
    minLoopInterpolation P a (t, p) r ∈ coordinateStar P v := by
  rw [minLoopInterpolation_apply]
  exact minInterpolation_mem_coordinateStar P (minLoopPointPair P a p r) v hγ hδ t

/-- The original finite compact-time star constraints cover the entire loop parameter.
Finiteness concerns these time constraints alone. -/
theorem exists_finite_star_time_cover (γ : Path a a) :
    ∃ (s : Finset unitInterval) (K : unitInterval → Set unitInterval) (v : unitInterval → V),
      (∀ c ∈ s, IsCompact (K c)) ∧
      (Set.univ : Set unitInterval) ⊆ ⋃ c ∈ s, K c ∧
      ∀ c ∈ s, Set.MapsTo γ (K c) (coordinateStar P (v c)) :=
  MetricLoopELCXSourceOnly37.finite_compact_star_time_cover P a γ

/-- The original based-loop neighborhood defined by finite compact-time coordinate stars. -/
def starLoopNeighborhood (s : Finset unitInterval) (K : unitInterval → Set unitInterval)
    (v : unitInterval → V) : Set (Path a a) :=
  MetricLoopELCXSourceOnly37.loopNeighborhood P a s K v

private theorem mem_starLoopNeighborhood_computed (s : Finset unitInterval)
    (K : unitInterval → Set unitInterval) (v : unitInterval → V) (γ : Path a a) :
    γ ∈ starLoopNeighborhood P a s K v ↔
      ∀ c ∈ s, Set.MapsTo γ (K c) (coordinateStar P (v c)) := Iff.rfl

/-- Every original compact-time constraint is preserved in neighborhood membership. -/
theorem mem_starLoopNeighborhood (s : Finset unitInterval) (K : unitInterval → Set unitInterval)
    (v : unitInterval → V) (γ : Path a a) :
    γ ∈ starLoopNeighborhood P a s K v ↔
      ∀ c ∈ s, Set.MapsTo γ (K c) (coordinateStar P (v c)) :=
  mem_starLoopNeighborhood_computed P a s K v γ

/-- The same finite compact-time star neighborhood is open in the original loop topology. -/
theorem isOpen_starLoopNeighborhood (s : Finset unitInterval)
    (K : unitInterval → Set unitInterval) (v : unitInterval → V)
    (hK : ∀ c ∈ s, IsCompact (K c)) : IsOpen (starLoopNeighborhood P a s K v) :=
  MetricLoopELCXSourceOnly37.loopNeighborhood_open P a s K v hK

/-- Two loops in the original covering constraints have positive overlap at every inner time. -/
theorem starLoopNeighborhood_square_minLoopDomain (s : Finset unitInterval)
    (K : unitInterval → Set unitInterval) (v : unitInterval → V)
    (hcover : (Set.univ : Set unitInterval) ⊆ ⋃ c ∈ s, K c)
    (γ δ : Path a a) (hγ : γ ∈ starLoopNeighborhood P a s K v)
    (hδ : δ ∈ starLoopNeighborhood P a s K v) : (γ, δ) ∈ minLoopDomain P a :=
  MetricLoopELCXSourceOnly37.loopNeighborhood_square P a s K v hcover γ δ hγ hδ

/-- The same original interpolation stays in each compact-time star constraint. -/
theorem minLoopInterpolation_mem_starLoopNeighborhood (s : Finset unitInterval)
    (K : unitInterval → Set unitInterval) (v : unitInterval → V) (p : minLoopDomain P a)
    (hγ : p.val.1 ∈ starLoopNeighborhood P a s K v)
    (hδ : p.val.2 ∈ starLoopNeighborhood P a s K v) (t : unitInterval) :
    minLoopInterpolation P a (t, p) ∈ starLoopNeighborhood P a s K v :=
  MetricLoopELCXSourceOnly37.loopNeighborhood_stable P a s K v
    p.val.1 p.val.2 hγ hδ p.property t

/-- Every original metric-target based loop has a neighborhood convex
for this fixed interpolation. -/
theorem exists_minLoop_convex_neighborhood (γ : Path a a) :
    ∃ N : Set (Path a a), IsOpen N ∧ γ ∈ N ∧
      (∀ δ ε : Path a a, δ ∈ N → ε ∈ N → (δ, ε) ∈ minLoopDomain P a) ∧
      ∀ (δ ε : Path a a), δ ∈ N → ε ∈ N →
        ∀ (hpair : (δ, ε) ∈ minLoopDomain P a) (t : unitInterval),
        minLoopInterpolation P a (t, ⟨(δ, ε), hpair⟩) ∈ N :=
  MetricLoopELCXSourceOnly37.every_loop_convex_neighborhood P a γ

end PreAbstractSimplicialComplex.MetricRealization
