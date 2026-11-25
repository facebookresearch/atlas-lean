/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.InductiveDimension.Functions
public import Mathlib.Topology.Metrizable.Basic

import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UniformSpace.HeineCantor
import MathlibExt.Analysis.Convex.BrouwerFixedPoint
import MathlibExt.Topology.InverseLimit

/-!
# Kolmogorov's open map raising dimension

There is a continuous open surjection from a one-dimensional compact metrizable space
onto a two-dimensional compact metrizable space.

The domain is an inverse limit of compact metric spaces with open bonding maps. Fine
covers of multiplicity at most two give a basis with zero-dimensional frontiers.
The target is the unit square, whose lower dimension bound uses Brouwer's fixed-point theorem.
-/

open Function Set Filter Topology TopologicalSpace Metric
open scoped BigOperators

namespace MathlibExt.Topology.ScottishBook136Wanted

private abbrev vertex {n : ℕ} (i : Fin n) : Fin n → ℝ := Pi.single i 1

private def edge {n : ℕ} (i j : Fin n) (t : ℝ) : Fin n → ℝ :=
  (1 - t) • vertex i + t • vertex j

private theorem continuous_edge {n : ℕ} (i j : Fin n) : Continuous (edge i j) := by
  unfold edge
  fun_prop

private theorem edge_zero {n : ℕ} (i j : Fin n) : edge i j 0 = vertex i := by
  simp [edge]

private theorem edge_one {n : ℕ} (i j : Fin n) : edge i j 1 = vertex j := by
  simp [edge]

private def skeleton (n : ℕ) : Set (Fin n → ℝ) :=
  ⋃ i, ⋃ j, edge i j '' Icc (0 : ℝ) 1

private theorem isCompact_skeleton (n : ℕ) : IsCompact (skeleton n) :=
  isCompact_iUnion fun i => isCompact_iUnion fun j =>
    isCompact_Icc.image (continuous_edge i j)

private theorem vertex_mem_skeleton {n : ℕ} (i : Fin n) : vertex i ∈ skeleton n := by
  exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨i, 0, by simp, edge_zero i i⟩⟩

private theorem edge_apply_of_ne {n : ℕ} (i j k : Fin n) (t : ℝ)
    (hi : k ≠ i) (hj : k ≠ j) : edge i j t k = 0 := by
  simp [edge, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hj]

private def height {n : ℕ} (w z : Fin n → ℝ) : ℝ :=
  ∑ i, (z i * w i + z i ^ 2)

private theorem height_vertex {n : ℕ} (w : Fin n → ℝ) (i : Fin n) :
    height w (vertex i) = w i + 1 := by
  unfold height
  rw [← Finset.sum_subset (Finset.singleton_subset_iff.2 (Finset.mem_univ i))]
  · simp
  · intro k _ hk
    simp [Pi.single_eq_of_ne (by simpa using hk : k ≠ i)]

private theorem height_edge {n : ℕ} (w : Fin n → ℝ) (i j : Fin n) (h : i ≠ j) (t : ℝ) :
    height w (edge i j t) =
      (1 - t) * w i + t * w j + (1 - t) ^ 2 + t ^ 2 := by
  unfold height
  rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin n)))]
  · rw [Finset.sum_pair h]
    simp only [edge, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne h, Pi.single_eq_of_ne h.symm, mul_one, mul_zero, add_zero, zero_add]
    ring
  · intro k _ hk
    have hk' : k ≠ i ∧ k ≠ j := by simpa using hk
    simp [edge_apply_of_ne i j k t hk'.1 hk'.2]

private theorem edge_self {n : ℕ} (i : Fin n) (t : ℝ) : edge i i t = vertex i := by
  rw [edge, ← add_smul]
  simp

-- On each edge the height is strictly convex. At a threshold vertex an edge
-- toward a vertex of weight at least four gives nearby strict points.
private theorem mem_closure_strict {n : ℕ} {w z : Fin n → ℝ}
    (hw : ∃ j, 4 ≤ w j) (hz : z ∈ skeleton n) (hh : 2 ≤ height w z) :
    z ∈ closure {v ∈ skeleton n | 2 < height w v} := by
  by_cases ht : 2 < height w z
  · exact subset_closure ⟨hz, ht⟩
  have heq : height w z = 2 := le_antisymm (le_of_not_gt ht) hh
  rw [mem_closure_iff_nhds]
  intro U hU
  have vertex_case (i : Fin n) (hi : z = vertex i) : (U ∩
      {v ∈ skeleton n | 2 < height w v}).Nonempty := by
    obtain ⟨j, hj⟩ := hw
    have hwi : w i = 1 := by rw [hi, height_vertex] at heq; linarith
    have hij : i ≠ j := by rintro rfl; linarith
    have hN : edge i j ⁻¹' U ∈ 𝓝 (0 : ℝ) := by
      apply (continuous_edge i j).continuousAt
      rwa [edge_zero, ← hi]
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hN
    let t := min (r / 2) (1 / 2)
    have ht₀ : 0 < t := lt_min (by positivity) (by norm_num)
    have ht₁ : t ≤ 1 := (min_le_right ..).trans (by norm_num)
    refine ⟨edge i j t, hball ?_, mem_iUnion.2 ⟨i, mem_iUnion.2
      ⟨j, t, ⟨ht₀.le, ht₁⟩, rfl⟩⟩, ?_⟩
    · rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht₀]
      exact (min_le_left ..).trans_lt (by linarith)
    · rw [height_edge w i j hij, hwi]
      nlinarith [mul_nonneg ht₀.le (sub_nonneg.mpr hj)]
  obtain ⟨i, hi⟩ := mem_iUnion.1 hz
  obtain ⟨j, t, htI, hzt⟩ := mem_iUnion.1 hi
  have ht₀ : (0 : ℝ) ≤ t := htI.1
  have ht₁ : t ≤ 1 := htI.2
  by_cases hij : i = j
  · subst j
    exact vertex_case i (hzt.symm.trans (edge_self i t))
  by_cases h0 : t = 0
  · subst t
    exact vertex_case i (hzt.symm.trans (edge_zero i j))
  by_cases h1 : t = 1
  · subst t
    exact vertex_case j (hzt.symm.trans (edge_one i j))
  have hN : edge i j ⁻¹' U ∈ 𝓝 t :=
    (continuous_edge i j).continuousAt (hzt.symm ▸ hU)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hN
  let d := min (r / 2) (min t (1 - t))
  have hd : 0 < d := lt_min (by positivity)
    (lt_min (lt_of_le_of_ne ht₀ (Ne.symm h0)) (by linarith [lt_of_le_of_ne ht₁ h1]))
  have hdt : d ≤ t := (min_le_right ..).trans (min_le_left ..)
  have hd1 : d ≤ 1 - t := (min_le_right ..).trans (min_le_right ..)
  have hdr : d < r := (min_le_left ..).trans_lt (by linarith)
  have hsum : 4 < height w (edge i j (t - d)) + height w (edge i j (t + d)) := by
    rw [← hzt, height_edge w i j hij] at heq
    rw [height_edge w i j hij, height_edge w i j hij]
    nlinarith [sq_pos_of_pos hd]
  have finish (u : ℝ) (hu : u ∈ Icc 0 1) (hNear : u ∈ ball t r)
      (hgt : 2 < height w (edge i j u)) :
      (U ∩ {v ∈ skeleton n | 2 < height w v}).Nonempty :=
    ⟨edge i j u, hball hNear, mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, u, hu, rfl⟩⟩, hgt⟩
  by_cases hl : 2 < height w (edge i j (t - d))
  · apply finish (t - d) ⟨by linarith, by linarith⟩ ?_ hl
    rw [mem_ball, Real.dist_eq, show t - d - t = -d by ring, abs_neg, abs_of_pos hd]
    exact hdr
  · apply finish (t + d) ⟨by linarith, by linarith⟩ ?_ (by linarith)
    rwa [mem_ball, Real.dist_eq, show t + d - t = d by ring, abs_of_pos hd]

private def resolution {A : Type} {n : ℕ} (w : Fin n → A → ℝ) :
    Set (A × (Fin n → ℝ)) :=
  {p | p.2 ∈ skeleton n ∧ 2 ≤ height (fun i => w i p.1) p.2}

private theorem isClosed_resolution {A : Type} [TopologicalSpace A] {n : ℕ}
    (w : Fin n → A → ℝ) (hw : ∀ i, Continuous (w i)) : IsClosed (resolution w) := by
  change IsClosed (Prod.snd ⁻¹' skeleton n ∩
    {p : A × (Fin n → ℝ) | 2 ≤ height (fun i => w i p.1) p.2})
  refine ((isCompact_skeleton n).isClosed.preimage
    (continuous_snd : Continuous (Prod.snd : A × (Fin n → ℝ) → _))).inter ?_
  apply isClosed_le continuous_const
  unfold height
  apply continuous_finsetSum _
  intro i _
  fun_prop (disch := assumption)

private def resolutionProj {A : Type} {n : ℕ} (w : Fin n → A → ℝ) :
    resolution w → A := fun p => p.val.1

private theorem resolutionProj_surjective {A : Type} {n : ℕ} (w : Fin n → A → ℝ)
    (hw : ∀ a, ∃ i, 4 ≤ w i a) : Surjective (resolutionProj w) := by
  intro a
  obtain ⟨i, hi⟩ := hw a
  refine ⟨⟨(a, vertex i), vertex_mem_skeleton i, ?_⟩, rfl⟩
  change 2 ≤ height (fun i => w i a) (vertex i)
  rw [height_vertex]
  linarith

private theorem resolutionProj_isOpenMap {A : Type} [TopologicalSpace A] {n : ℕ}
    (w : Fin n → A → ℝ) (hc : ∀ i, Continuous (w i)) (hw : ∀ a, ∃ i, 4 ≤ w i a) :
    IsOpenMap (resolutionProj w) := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro a ⟨⟨⟨a, z⟩, hz, hh⟩, hp, rfl⟩
  obtain ⟨V, hV, hVU⟩ := (mem_nhds_subtype _ _ _).1 (hU.mem_nhds hp)
  obtain ⟨P, Q, hP, ha, hQ, hzQ, hPQ⟩ := mem_nhds_prod_iff'.1 hV
  obtain ⟨v, hvQ, hvs, hvh⟩ := mem_closure_iff_nhds.mp
    (mem_closure_strict (hw a) hz hh) Q (hQ.mem_nhds hzQ)
  have hcont : Continuous (fun b => height (fun i => w i b) v) := by
    unfold height
    exact continuous_finsetSum _ fun i _ => ((hc i).const_mul _).add continuous_const
  apply mem_of_superset ((hP.inter (isOpen_lt continuous_const hcont)).mem_nhds ⟨ha, hvh⟩)
  rintro b ⟨hb, hbh⟩
  exact ⟨⟨(b, v), hvs, le_of_lt hbh⟩, hVU (hPQ ⟨hb, hvQ⟩), rfl⟩

private theorem resolution_cover {A : Type} {n : ℕ} (w : Fin n → A → ℝ)
    (p : resolution w) : ∃ i, 0 < p.val.2 i ∧ 0 < w i p.val.1 := by
  obtain ⟨i, hi⟩ := mem_iUnion.1 p.property.1
  obtain ⟨j, t, ht, he⟩ := mem_iUnion.1 hi
  have hp := p.property.2
  change 2 ≤ height (fun i => w i p.val.1) p.val.2 at hp
  have vertex_case (i : Fin n) (h : p.val.2 = vertex i) :
      ∃ k, 0 < p.val.2 k ∧ 0 < w k p.val.1 := by
    rw [h, height_vertex] at hp
    exact ⟨i, by simp [h], by linarith⟩
  by_cases hij : i = j
  · subst j
    exact vertex_case i (he.symm.trans (edge_self i t))
  by_cases h0 : t = 0
  · subst t
    exact vertex_case i (he.symm.trans (edge_zero i j))
  by_cases h1 : t = 1
  · subst t
    exact vertex_case j (he.symm.trans (edge_one i j))
  have ht₀ : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h0)
  have ht₁ : t < 1 := lt_of_le_of_ne ht.2 h1
  have hi' : p.val.2 i = 1 - t := by simp [← he, edge, Pi.single_eq_of_ne hij]
  have hj' : p.val.2 j = t := by simp [← he, edge, Pi.single_eq_of_ne (Ne.symm hij)]
  by_contra! h
  have hwi := h i (by rw [hi']; linarith)
  have hwj := h j (hj' ▸ ht₀)
  rw [← he, height_edge _ i j hij] at hp
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht₁.le) hwi,
    mul_nonpos_of_nonneg_of_nonpos ht₀.le hwj,
    mul_nonneg ht₀.le (sub_nonneg.mpr ht₁.le)]

private theorem exists_two_indices {n : ℕ} {z : Fin n → ℝ} (hz : z ∈ skeleton n) :
    ∃ i j, ∀ k, z k ≠ 0 → k = i ∨ k = j := by
  obtain ⟨i, hi⟩ := mem_iUnion.1 hz
  obtain ⟨j, t, _, rfl⟩ := mem_iUnion.1 hi
  exact ⟨i, j, fun k hk => or_iff_not_imp_left.2 fun hi =>
    by_contradiction fun hj => hk (edge_apply_of_ne i j k t hi hj)⟩

private structure CompactMetric where
  carrier : Type
  metric : MetricSpace carrier
  compact : @CompactSpace carrier metric.toUniformSpace.toTopologicalSpace

attribute [instance] CompactMetric.metric CompactMetric.compact

private structure Refinement (A : CompactMetric) (r : ℝ) where
  space : CompactMetric
  proj : space.carrier → A.carrier
  continuous_proj : Continuous proj
  open_proj : IsOpenMap proj
  surjective_proj : Surjective proj
  dist_proj : ∀ x y, dist (proj x) (proj y) ≤ dist x y
  cover : ∃ (n : ℕ) (U : Fin n → Set space.carrier) (c : Fin n → A.carrier),
    (∀ i, IsOpen (U i)) ∧ (∀ x, ∃ i, x ∈ U i) ∧
    (∀ x, ∃ i j, ∀ k, x ∈ U k → k = i ∨ k = j) ∧
    (∀ i, U i ⊆ proj ⁻¹' ball (c i) r)

private theorem exists_finite_ball_cover {A : Type} [MetricSpace A] [CompactSpace A]
    {r : ℝ} (hr : 0 < r) : ∃ (n : ℕ) (c : Fin n → A), ∀ a, ∃ i, dist a (c i) < r := by
  obtain ⟨s, _, hs, hcov⟩ := isCompact_univ.finite_cover_balls (X := A) hr
  have := hs.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  refine ⟨n, fun i => (e.symm i).val, fun a => ?_⟩
  obtain ⟨b, hb⟩ := mem_iUnion.1 (hcov (mem_univ a))
  obtain ⟨hbs, hab⟩ := mem_iUnion.1 hb
  exact ⟨e ⟨b, hbs⟩, by simpa using hab⟩

private noncomputable def refineSpace (A : CompactMetric) (r : ℝ) (hr : 0 < r) :
    Refinement A r := by
  let E := exists_finite_ball_cover (A := A.carrier) (half_pos hr)
  let n := E.choose
  let c := E.choose_spec.choose
  have hc : ∀ a, ∃ i, dist a (c i) < r / 2 := E.choose_spec.choose_spec
  let w (i : Fin n) (a : A.carrier) := 8 * (1 - dist a (c i) / r)
  have hwcont (i : Fin n) : Continuous (w i) := by unfold w; fun_prop
  have hw (a : A.carrier) : ∃ i, 4 ≤ w i a := by
    obtain ⟨i, hi⟩ := hc a
    have := (div_lt_iff₀ hr).2 (show dist a (c i) < (1 / 2 : ℝ) * r by linarith)
    exact ⟨i, by dsimp [w]; linarith⟩
  letI : CompactSpace (resolution w) := isCompact_iff_compactSpace.1
    ((isCompact_univ.prod (isCompact_skeleton n)).of_isClosed_subset
      (isClosed_resolution w hwcont) (fun p hp => ⟨mem_univ _, hp.1⟩))
  refine ⟨⟨resolution w, inferInstance, inferInstance⟩, resolutionProj w,
    continuous_fst.comp continuous_subtype_val, resolutionProj_isOpenMap w hwcont hw,
    resolutionProj_surjective w hw, fun x y => ?_, ?_⟩
  · exact le_max_left ..
  let U (i : Fin n) : Set (resolution w) :=
    {p | 0 < p.val.2 i ∧ 0 < w i p.val.1}
  refine ⟨n, U, c, fun i => ?_, resolution_cover w, fun p => ?_, fun i p hp => ?_⟩
  · change IsOpen ({p : resolution w | 0 < p.val.2 i} ∩
      {p : resolution w | 0 < w i p.val.1})
    exact (isOpen_lt continuous_const
      ((continuous_apply i).comp (continuous_snd.comp continuous_subtype_val))).inter
      (isOpen_lt continuous_const ((hwcont i).comp (continuous_fst.comp continuous_subtype_val)))
  · obtain ⟨i, j, h⟩ := exists_two_indices p.property.1
    exact ⟨i, j, fun k hk => h k (ne_of_gt hk.1)⟩
  have hi : 0 < w i p.val.1 := hp.2
  have hd : dist p.val.1 (c i) / r < 1 := by dsimp [w] at hi; linarith
  exact (div_lt_iff₀ hr).1 hd |>.trans_eq (one_mul r)

private noncomputable def radius (n : ℕ) : ℝ := 1 / (n + 1)

private theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity

private noncomputable def level (A : CompactMetric) : ℕ → CompactMetric
  | 0 => A
  | n + 1 => (refineSpace (level A n) (radius n) (radius_pos n)).space

private noncomputable abbrev step (A : CompactMetric) (n : ℕ) :=
  refineSpace (level A n) (radius n) (radius_pos n)

private noncomputable def transition (A : CompactMetric) {i j : ℕ} (h : i ≤ j) :
    (level A j).carrier → (level A i).carrier :=
  Nat.decreasingInduction (motive := fun i _ => (level A j).carrier → (level A i).carrier)
    (fun k _ f => (step A k).proj ∘ f) id h

private theorem transition_refl (A : CompactMetric) (i : ℕ) :
    transition A (le_refl i) = id := by simp [transition]

private theorem transition_succ (A : CompactMetric) {i j : ℕ} (h : i + 1 ≤ j) :
    transition A (Nat.le_of_succ_le h) = (step A i).proj ∘ transition A h := by
  exact Nat.decreasingInduction_succ_left
    (motive := fun i _ => (level A j).carrier → (level A i).carrier)
    (fun k _ f => (step A k).proj ∘ f) id h _

private theorem transition_comp (A : CompactMetric) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    transition A hij ∘ transition A hjk = transition A (hij.trans hjk) := by
  induction hij using Nat.decreasingInduction with
  | self => simp [transition_refl]
  | of_succ i hi ih =>
    rw [transition_succ A hi, transition_succ A (hi.trans_le hjk)]
    exact congrArg ((step A i).proj ∘ ·) ih

private theorem transition_properties (A : CompactMetric) {i j : ℕ} (h : i ≤ j) :
    Continuous (transition A h) ∧ IsOpenMap (transition A h) ∧
    ∀ x y, dist (transition A h x) (transition A h y) ≤ dist x y := by
  induction h using Nat.decreasingInduction with
  | self => simp [transition_refl, continuous_id, IsOpenMap.id]
  | of_succ i hi ih =>
    rw [transition_succ A hi]
    exact ⟨(step A i).continuous_proj.comp ih.1, (step A i).open_proj.comp ih.2.1,
      fun x y => ((step A i).dist_proj _ _).trans (ih.2.2 x y)⟩

private noncomputable abbrev Limit (A : CompactMetric) :=
  InverseLimit.carrier (fun _ _ h => transition A h)

private theorem compactSpace_limit (A : CompactMetric) : CompactSpace (Limit A) :=
  isCompact_iff_compactSpace.1 <|
    InverseLimit.isCompact_carrier fun _ _ h => (transition_properties A h).1

private def projection (A : CompactMetric) (i : ℕ) (x : Limit A) : (level A i).carrier :=
  x.val i

private theorem continuous_projection (A : CompactMetric) (i : ℕ) :
    Continuous (projection A i) := (continuous_apply i).comp continuous_subtype_val

private theorem projection_compat (A : CompactMetric) {i j : ℕ} (h : i ≤ j) (x : Limit A) :
    transition A h (projection A j x) = projection A i x :=
  x.property h

private theorem projection_surjective (A : CompactMetric) (n : ℕ) :
    Surjective (projection A n) := by
  intro a
  let next {k : ℕ} (x : (level A k).carrier) : (level A (k + 1)).carrier :=
    ((step A k).surjective_proj x).choose
  have hnext (k : ℕ) (x : (level A k).carrier) :
      (step A k).proj (next x) = x := ((step A k).surjective_proj x).choose_spec
  let f (k : ℕ) : (level A k).carrier :=
    if h : k ≤ n then transition A h a else Nat.leRecOn (motive := fun k => (level A k).carrier)
      (by omega : n ≤ k) @next a
  have hlow {k : ℕ} (h : k ≤ n) : f k = transition A h a := dite_eq_left h
  have hhigh {k : ℕ} (h : n ≤ k) : f k = Nat.leRecOn h @next a := by
    rcases eq_or_lt_of_le h with rfl | h'
    · rw [hlow (le_refl _), transition_refl, Nat.leRecOn_self]
      rfl
    · exact dite_eq_right (not_le_of_gt h')
  have hstep (k : ℕ) : (step A k).proj (f (k + 1)) = f k := by
    by_cases hk : k + 1 ≤ n
    · rw [hlow hk, hlow (Nat.le_of_succ_le hk), transition_succ A hk]
      rfl
    · have hk' : n ≤ k := by omega
      rw [hhigh hk', hhigh (by omega : n ≤ k + 1), Nat.leRecOn_succ hk', hnext]
  have hcompat (i j : ℕ) (h : i ≤ j) : transition A h (f j) = f i := by
    induction h using Nat.decreasingInduction with
    | self => rw [transition_refl]; rfl
    | of_succ k hk ih =>
      rw [transition_succ A hk]
      change (step A k).proj (transition A hk (f j)) = f k
      rw [ih, hstep]
  exact ⟨⟨f, fun _ _ h => hcompat _ _ h⟩, by
    change f n = a
    rw [hlow (le_refl _), transition_refl]
    rfl⟩

private theorem exists_projection_neighborhood (A : CompactMetric) (n : ℕ)
    {x : Limit A} {U : Set (Limit A)} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ j ≥ n, ∃ V : Set (level A j).carrier, IsOpen V ∧ projection A j x ∈ V ∧
      projection A j ⁻¹' V ⊆ U := by
  obtain ⟨W, hW, hWU⟩ := (mem_nhds_subtype _ _ _).1 (hU.mem_nhds hx)
  obtain ⟨D, ⟨V, F, hV, rfl⟩, hxD, hDW⟩ :=
    (isTopologicalBasis_pi (fun _ => isTopologicalBasis_opens)).mem_nhds_iff.1 hW
  let j := max n (F.sup id)
  have hj (i : ℕ) (hi : i ∈ F) : i ≤ j :=
    (Finset.le_sup (f := id) hi).trans (le_max_right ..)
  let S : Set (level A j).carrier :=
    ⋂ i : F, transition A (hj i i.property) ⁻¹' V i
  refine ⟨j, le_max_left .., S, isOpen_iInter_of_finite (fun i => ?_), ?_, ?_⟩
  · exact (hV i i.property).preimage (transition_properties A (hj i i.property)).1
  · exact mem_iInter.2 fun i => by
      change transition A (hj i i.property) (projection A j x) ∈ V i
      rw [projection_compat]
      exact hxD i i.property
  · intro y hy
    apply hWU (hDW ?_)
    intro i hi
    have h := mem_iInter.1 hy ⟨i, hi⟩
    change transition A (hj i hi) (projection A j y) ∈ V i at h
    rwa [projection_compat] at h

private theorem isOpenMap_projection (A : CompactMetric) (n : ℕ) :
    IsOpenMap (projection A n) := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨j, hj, V, hV, hxV, hVU⟩ := exists_projection_neighborhood A n hU hx
  refine mem_of_superset
    (((transition_properties A hj).2.1 V hV).mem_nhds ⟨_, hxV, projection_compat A hj x⟩) ?_
  rintro z ⟨v, hv, rfl⟩
  obtain ⟨t, ht⟩ := projection_surjective A j v
  refine ⟨t, hVU (by rwa [mem_preimage, ht]), ?_⟩
  rw [← ht, projection_compat]

private theorem radius_antitone : Antitone radius := by
  intro i j hij
  unfold radius
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.succ_le_succ hij

private theorem projection_dist_mono (A : CompactMetric) (x y : Limit A) :
    Monotone fun n => dist (projection A n x) (projection A n y) := by
  intro i j hij
  change dist (projection A i x) (projection A i y) ≤
    dist (projection A j x) (projection A j y)
  rw [← projection_compat A hij x, ← projection_compat A hij y]
  exact (transition_properties A hij).2.2 _ _

private noncomputable abbrev limitMetric (A : CompactMetric) : MetricSpace (Limit A) :=
  metrizableSpaceMetric _

attribute [local instance] limitMetric compactSpace_limit

private theorem exists_small_cover_limit (A : CompactMetric) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (U : Fin n → Set (Limit A)), (∀ i, IsOpen (U i)) ∧
      (∀ x, ∃ i, x ∈ U i) ∧ (∀ x, ∃ i j, ∀ k, x ∈ U k → k = i ∨ k = j) ∧
      (∀ i x y, x ∈ U i → y ∈ U i → dist x y < ε) := by
  classical
  -- Compactness makes one stage suffice to detect all pairs at distance at least ε.
  let K : Set (Limit A × Limit A) := {p | ε ≤ dist p.1 p.2}
  let V (n : ℕ) : Set (Limit A × Limit A) :=
    {p | 2 * radius n < dist (projection A n p.1) (projection A n p.2)}
  have hV (n : ℕ) : IsOpen (V n) := isOpen_lt continuous_const
    (((continuous_projection A n).comp continuous_fst).dist
      ((continuous_projection A n).comp continuous_snd))
  have hMono : Monotone V := fun _ _ hij _ hp =>
    (mul_le_mul_of_nonneg_left (radius_antitone hij) (by norm_num : (0 : ℝ) ≤ 2)).trans_lt
      (hp.trans_le (projection_dist_mono A _ _ hij))
  have hKV : K ⊆ ⋃ n, V n := by
    rintro ⟨x, y⟩ hxy
    have hne : x ≠ y := by
      intro h
      subst y
      exact hε.not_ge (by simpa [K] using hxy)
    obtain ⟨k, hk⟩ : ∃ k, projection A k x ≠ projection A k y := by
      by_contra! h
      exact hne (Subtype.ext (funext h))
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos (dist_pos.mpr hk))
    have hn' : 2 * radius n < dist (projection A k x) (projection A k y) := by
      unfold radius
      linarith
    refine mem_iUnion.2 ⟨max k n, ?_⟩
    exact (mul_le_mul_of_nonneg_left (radius_antitone (le_max_right k n))
      (by norm_num : (0 : ℝ) ≤ 2)).trans_lt
      (hn'.trans_le (projection_dist_mono A x y (le_max_left k n)))
  have hK : IsCompact K := (isClosed_le continuous_const
    (continuous_fst.dist continuous_snd)).isCompact
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover V hV hKV
  let N := F.sup id
  have hKN : K ⊆ V N := by
    intro p hp
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hF hp)
    obtain ⟨hnF, hv⟩ := mem_iUnion.1 hn
    exact hMono (Finset.le_sup (f := id) hnF) hv
  obtain ⟨n, U, c, hU, hcov, htwo, hball⟩ := (step A N).cover
  refine ⟨n, fun i => projection A (N + 1) ⁻¹' U i,
    fun i => (hU i).preimage (continuous_projection A _),
    fun x => hcov (projection A (N + 1) x),
    fun x => htwo (projection A (N + 1) x), ?_⟩
  intro i x y hx hy
  have hproj (z : Limit A) (hz : projection A (N + 1) z ∈ U i) :
      projection A N z ∈ ball (c i) (radius N) := by
    have h := hball i hz
    change (step A N).proj (projection A (N + 1) z) ∈ ball (c i) (radius N) at h
    have hc := projection_compat A (Nat.le_succ N) z
    rw [transition_succ A (le_refl (N + 1)), transition_refl] at hc
    change (step A N).proj (projection A (N + 1) z) = projection A N z at hc
    rwa [hc] at h
  by_contra! h
  have H := hKN (show (x, y) ∈ K from h)
  have hx' := mem_ball.1 (hproj x hx)
  have hy' := mem_ball'.1 (hproj y hy)
  change 2 * radius N < dist (projection A N x) (projection A N y) at H
  linarith [dist_triangle (projection A N x) (c i) (projection A N y)]

private def Good {X : Type} [MetricSpace X] (ε : ℝ) : Set C(X, ℝ) :=
  {f | ∃ (n : ℕ) (U : Fin n → Set X), (∀ i, IsOpen (U i)) ∧
    Pairwise (Disjoint on U) ∧ (∀ i x y, x ∈ U i → y ∈ U i → dist x y < ε) ∧
    f ⁻¹' {0} ⊆ ⋃ i, U i}

private theorem isOpen_good {X : Type} [MetricSpace X] [CompactSpace X] (ε : ℝ) :
    IsOpen (Good (X := X) ε) := by
  rw [isOpen_iff_mem_nhds]
  intro f hf
  obtain ⟨n, V, hV, hdis, hsmall, hzero⟩ := hf
  let K := (⋃ i, V i)ᶜ
  have hK : IsCompact K := (isOpen_iUnion hV).isClosed_compl.isCompact
  have hpos (x : X) (hx : x ∈ K) : 0 < |f x| := by
    apply abs_pos.mpr
    exact fun h => hx (hzero h)
  have hδ : ∃ δ > 0, ∀ x ∈ K, δ ≤ |f x| := by
    rcases K.eq_empty_or_nonempty with hK0 | hKne
    · exact ⟨1, zero_lt_one, by simp [hK0]⟩
    obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hKne f.continuous.abs.continuousOn
    exact ⟨|f x|, hpos x hx, hmin⟩
  obtain ⟨δ, hδ, hle⟩ := hδ
  refine mem_of_superset (ball_mem_nhds f hδ) ?_
  intro g hg
  refine ⟨n, V, hV, hdis, hsmall, fun x hx => ?_⟩
  by_contra h
  have hd := (ContinuousMap.dist_apply_le_dist (f := g) (g := f) x).trans_lt (mem_ball.1 hg)
  change g x = 0 at hx
  rw [Real.dist_eq, hx, zero_sub, abs_neg] at hd
  exact (not_lt_of_ge (hle x h)) hd

private theorem exists_ne_zero_near (a ε : ℝ) (hε : 0 < ε) :
    ∃ b ≠ 0, |b - a| < ε := by
  by_cases ha : a = 0
  · refine ⟨ε / 2, by positivity, ?_⟩
    rw [ha, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  · exact ⟨a, ha, by simpa⟩

private theorem dense_good {X : Type} [MetricSpace X] [CompactSpace X] {ε : ℝ}
    (hε : 0 < ε) (covers : ∀ δ > 0, ∃ (n : ℕ) (U : Fin n → Set X),
      (∀ i, IsOpen (U i)) ∧ (∀ x, ∃ i, x ∈ U i) ∧
      (∀ x, ∃ i j, ∀ k, x ∈ U k → k = i ∨ k = j) ∧
      (∀ i x y, x ∈ U i → y ∈ U i → dist x y < δ)) :
    Dense (Good (X := X) ε) := by
  classical
  intro f
  rw [Metric.mem_closure_iff]
  intro η hη
  obtain ⟨δ, hδ, hcomm⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous f.continuous) (η / 3) (by positivity)
  obtain ⟨n, U, hU, hcov, htwo, hsmall⟩ := covers (min δ ε) (lt_min hδ hε)
  have hcover : (univ : Set X) ⊆ ⋃ i, U i :=
    fun x _ => mem_iUnion.2 (hcov x)
  obtain ⟨w, hsupport, hsum, hw, _⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact hU isCompact_univ hcover
  have hsum' (x : X) : (∑ i, w i x) = 1 := by
    simpa using hsum (mem_univ x)
  have hmem {i : Fin n} {x : X} (h : w i x ≠ 0) : x ∈ U i :=
    hsupport i (subset_closure h)
  have hcoeff (i : Fin n) : ∃ b ≠ 0, ∀ x ∈ U i, |b - f x| < η / 3 + η / 3 := by
    rcases (U i).eq_empty_or_nonempty with h | ⟨a, ha⟩
    · exact ⟨1, one_ne_zero, by simp [h]⟩
    obtain ⟨b, hb, hb'⟩ := exists_ne_zero_near (f a) (η / 3) (by positivity)
    refine ⟨b, hb, fun x hx => ?_⟩
    have hax := hcomm ((hsmall i a x ha hx).trans_le (min_le_left ..))
    rw [Real.dist_eq] at hax
    have := abs_add_le (b - f a) (f a - f x)
    rw [show b - f a + (f a - f x) = b - f x by ring] at this
    linarith
  choose b hb hb' using hcoeff
  let g : C(X, ℝ) := ∑ i, ContinuousMap.const X (b i) * w i
  have hg (x : X) : g x = ∑ i, b i * w i x := by simp [g]
  refine ⟨g, ?_, (ContinuousMap.dist_lt_iff hη).2 fun x => ?_⟩
  · -- Only intersections of two support sets can meet the zero fiber.
    let P := {p : Fin n × Fin n // p.1 < p.2}
    let e := Fintype.equivFin P
    let V (j : Fin (Fintype.card P)) : Set X := U (e.symm j).val.1 ∩ U (e.symm j).val.2
    refine ⟨_, V, fun j => (hU _).inter (hU _), ?_, fun j x y hx hy => ?_, ?_⟩
    · intro j k hjk
      apply Set.disjoint_left.2
      intro x hj hk
      obtain ⟨i, l, h⟩ := htwo x
      have hj₁ := h _ hj.1
      have hj₂ := h _ hj.2
      have hk₁ := h _ hk.1
      have hk₂ := h _ hk.2
      have hj' := (e.symm j).property
      have hk' := (e.symm k).property
      apply hjk (e.symm.injective (Subtype.ext (Prod.ext ?_ ?_)))
      all_goals rcases hj₁ with h | h <;> rcases hj₂ with h | h <;>
        rcases hk₁ with h | h <;> rcases hk₂ with h | h <;> grind
    · exact (hsmall _ x y hx.1 hy.1).trans_le (min_le_right ..)
    intro x hx
    change g x = 0 at hx
    obtain ⟨i, hi⟩ : ∃ i, w i x ≠ 0 := by
      by_contra! h
      have H := hsum' x
      simp [h] at H
    obtain ⟨j, hij, hj⟩ : ∃ j, i ≠ j ∧ w j x ≠ 0 := by
      by_contra! h
      have hothers : ∀ k ≠ i, w k x = 0 := fun k hk => h k (Ne.symm hk)
      have hi' : w i x = 1 := by
        rw [← hsum' x, Finset.sum_eq_single i]
        · exact fun k _ hk => hothers k hk
        · simp
      rw [hg, Finset.sum_eq_single i] at hx
      · exact hb i (by simpa [hi'] using hx)
      · intro k _ hk
        simp [hothers k hk]
      · simp
    rcases lt_or_gt_of_ne hij with h | h
    · exact mem_iUnion.2 ⟨e ⟨(i, j), h⟩, by simpa [V] using ⟨hmem hi, hmem hj⟩⟩
    · exact mem_iUnion.2 ⟨e ⟨(j, i), h⟩, by simpa [V] using ⟨hmem hj, hmem hi⟩⟩
  · rw [dist_comm, Real.dist_eq, hg, ← mul_one (f x), ← hsum' x, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    calc
      |∑ i, (b i * w i x - f x * w i x)| ≤
          ∑ i, |b i * w i x - f x * w i x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (η / 3 + η / 3) * w i x := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : w i x = 0
        · simp [hi]
        rw [← sub_mul, abs_mul, abs_of_nonneg (hw i x).1]
        exact mul_le_mul_of_nonneg_right (hb' i x (hmem hi)).le (hw i x).1
      _ < η := by rw [← Finset.mul_sum, hsum', mul_one]; linarith

private theorem zeroDimensional_good_fiber {X : Type} [MetricSpace X] {f : C(X, ℝ)}
    (hf : ∀ n, f ∈ Good (radius n)) : ZeroDimensionalSpace (f ⁻¹' {0}) := by
  rw [zeroDimensionalSpace_iff_isTopologicalBasis_isClopen]
  refine isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.isOpen) ?_
  intro x W hx hW
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hW.mem_nhds hx)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨n, U, hU, hdis, hsmall, hcover⟩ := hf m
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover x.property)
  let V : Set (f ⁻¹' {0}) := Subtype.val ⁻¹' U i
  refine ⟨V, ⟨?_, (hU i).preimage continuous_subtype_val⟩, hi, ?_⟩
  · apply isOpen_compl_iff.mp
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcover y.property)
    have hji : j ≠ i := by
      rintro rfl
      exact hy hj
    have ho := (hU j).preimage (continuous_subtype_val (p := fun z => z ∈ f ⁻¹' {0}))
    refine mem_of_superset (ho.mem_nhds hj) fun z hz hz' => ?_
    exact (Set.disjoint_left.1 (hdis hji)) hz hz'
  · intro y hy
    apply hball
    exact (hsmall i y.val x.val hy hi).trans hm

private theorem dim_limit_le (A : CompactMetric) : HasSmallInductiveDimensionLE (Limit A) 1 := by
  let X := Limit A
  let B : Set (Set X) := {U | IsOpen U ∧ ZeroDimensionalSpace (frontier U)}
  refine .succ 1 B (isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.1) ?_)
    (fun _ h => h.2)
  intro x W hx hW
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (hW.mem_nhds hx)
  let g : C(X, ℝ) := ⟨fun y => dist y x - δ / 2, (continuous_id.dist continuous_const).sub
    continuous_const⟩
  have hdense : Dense (⋂ n, Good (X := X) (radius n)) :=
    dense_iInter_of_isOpen_nat (fun _ => isOpen_good _) (fun n =>
      dense_good (radius_pos n) fun _ => exists_small_cover_limit A)
  obtain ⟨f, hfN, hfG⟩ := mem_closure_iff_nhds.1 (hdense g) _ (ball_mem_nhds g (by positivity :
    0 < δ / 2))
  have hf (y : X) : |f y - (dist y x - δ / 2)| < δ / 2 :=
    (ContinuousMap.dist_lt_iff (half_pos hδ)).1 (mem_ball.1 hfN) y
  let U : Set X := {y | f y < 0}
  have hU : IsOpen U := isOpen_lt f.continuous continuous_const
  have hfront : frontier U ⊆ f ⁻¹' {0} := by
    intro y hy
    rw [hU.frontier_eq] at hy
    have hle : f y ≤ 0 := closure_minimal (fun _ h => le_of_lt h)
      (isClosed_le f.continuous continuous_const) hy.1
    exact le_antisymm hle (le_of_not_gt hy.2)
  have hzero := zeroDimensional_good_fiber (fun n => mem_iInter.1 hfG n)
  refine ⟨U, ⟨hU, (IsInducing.id.restrict hfront).hasSmallInductiveDimensionLE hzero⟩,
    ?_, ?_⟩
  · have h := (abs_lt.1 (hf x)).2
    simp only [dist_self] at h
    change f x < 0
    linarith
  · intro y hy
    apply hball
    have h := (abs_lt.1 (hf y)).1
    change f y < 0 at hy
    change dist y x < δ
    linarith

private theorem zeroDimensional_of_open_surj {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space Y] (f : X → Y)
    (hc : Continuous f) (ho : IsOpenMap f) (hs : Surjective f) (hX : ZeroDimensionalSpace X) :
    ZeroDimensionalSpace Y := by
  rw [zeroDimensionalSpace_iff_isTopologicalBasis_isClopen]
  refine isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.isOpen) ?_
  intro y U hy hU
  obtain ⟨x, rfl⟩ := hs y
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isClopen_mem_of_isOpen (hU.preimage hc) hy
  exact ⟨f '' V, ⟨hc.isClosedMap _ hV.isClosed, ho _ hV.isOpen⟩,
    mem_image_of_mem f hxV, image_subset_iff.2 hVU⟩

private theorem sphere_real_finite (x r : ℝ) : (sphere x r).Finite := by
  refine (Set.toFinite ({x - r, x + r} : Set ℝ)).subset ?_
  intro y hy
  rw [mem_sphere, Real.dist_eq] at hy
  rcases le_or_gt 0 (y - x) with h | h
  · rw [abs_of_nonneg h] at hy
    exact mem_insert_of_mem _ (mem_singleton_iff.2 (by linarith))
  · rw [abs_of_neg h] at hy
    exact mem_insert_iff.2 (Or.inl (by linarith))

-- Balls with radii avoiding the distances to the finitely many lines
-- have finite frontier in a subspace of those lines.
private theorem dim_subset_lines_le {a b : Set ℝ} (ha : a.Finite) (hb : b.Finite)
    {S : Set (ℝ × ℝ)} (hS : ∀ p ∈ S, p.1 ∈ a ∨ p.2 ∈ b) :
    HasSmallInductiveDimensionLE S 1 := by
  let B : Set (Set S) := {U | IsOpen U ∧ ZeroDimensionalSpace (frontier U)}
  refine .succ 1 B (isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.1) ?_)
    (fun _ h => h.2)
  intro x W hx hW
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hW.mem_nhds hx)
  let D : Set ℝ := (fun y => dist y x.val.1) '' a ∪ (fun y => dist y x.val.2) '' b
  have hD : D.Finite := (ha.image _).union (hb.image _)
  obtain ⟨r, hrD, hr⟩ := (hD.countable.dense_compl ℝ).exists_mem_open
    isOpen_Ioo (nonempty_Ioo.2 hε)
  refine ⟨ball x r, ⟨isOpen_ball, ?_⟩, mem_ball_self hr.1,
    (ball_subset_ball hr.2.le).trans hball⟩
  have hfin : ((Subtype.val : S → ℝ × ℝ) '' frontier (ball x r)).Finite := by
    refine ((ha.prod (sphere_real_finite x.val.2 r)).union
      ((sphere_real_finite x.val.1 r).prod hb)).subset ?_
    rintro p ⟨y, hy, rfl⟩
    have hs := frontier_ball_subset_sphere hy
    change dist y.val x.val = r at hs
    rw [Prod.dist_eq, max_eq_iff] at hs
    rcases hS y.val y.property with hy₁ | hy₂
    · rcases hs with ⟨hs, _⟩ | ⟨hs, _⟩
      · exact (hrD (Or.inl ⟨y.val.1, hy₁, hs⟩)).elim
      · exact Or.inl ⟨hy₁, hs⟩
    · rcases hs with ⟨hs, _⟩ | ⟨hs, _⟩
      · exact Or.inr ⟨hs, hy₂⟩
      · exact (hrD (Or.inr ⟨y.val.2, hy₂, hs⟩)).elim
  have hfin' : (frontier (ball x r)).Finite :=
    hfin.of_finite_image Subtype.val_injective.injOn
  exact Set.Countable.zeroDimensionalSpace hfin'.countable

private theorem dim_plane_le : HasSmallInductiveDimensionLE (ℝ × ℝ) 2 := by
  let B : Set (Set (ℝ × ℝ)) := {U | IsOpen U ∧ HasSmallInductiveDimensionLE (frontier U) 1}
  refine .succ 2 B (isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.1) ?_)
    (fun _ h => h.2)
  intro x W hx hW
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hW.mem_nhds hx)
  refine ⟨ball x ε, ⟨isOpen_ball, ?_⟩, mem_ball_self hε, hball⟩
  refine dim_subset_lines_le (sphere_real_finite x.1 ε) (sphere_real_finite x.2 ε)
    (fun p hp => ?_)
  have h := frontier_ball_subset_sphere hp
  rw [mem_sphere, Prod.dist_eq, max_eq_iff] at h
  exact h.imp And.left And.left

private abbrev Square := (Icc (0 : ℝ × ℝ) 1 : Set (ℝ × ℝ))

private theorem dim_square_le : HasSmallInductiveDimensionLE Square 2 :=
  IsInducing.subtypeVal.hasSmallInductiveDimensionLE dim_plane_le

private theorem eq_zero_of_clamp_eq {a b x u : ℝ} (h : max a (min b (x - u)) = x)
    (ha : a ≤ x) (hb : x ≤ b) (hu₁ : x = a → u ≤ 0) (hu₂ : x = b → 0 ≤ u) : u = 0 := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have hxb : x < b := lt_of_le_of_ne hb (fun h => hu.not_ge (hu₂ h))
    have H : x < min b (x - u) := lt_min hxb (by linarith)
    exact (H.not_ge ((le_max_right ..).trans_eq h)).elim
  · exact hu
  · have hax : a < x := lt_of_le_of_ne ha (fun h => hu.not_ge (hu₁ h.symm))
    have H : max a (min b (x - u)) < x :=
      max_lt hax ((min_le_right ..).trans_lt (by linarith))
    exact (H.ne h).elim

-- Poincaré–Miranda on a rectangle follows by applying Brouwer to a clamped step.
private theorem exists_common_zero {a b : ℝ × ℝ} (hab : a ≤ b)
    (F : ↥(Icc a b) → ℝ × ℝ) (hc : Continuous F)
    (h₁ : ∀ x, x.val.1 = a.1 → (F x).1 ≤ 0)
    (h₂ : ∀ x, x.val.1 = b.1 → 0 ≤ (F x).1)
    (h₃ : ∀ x, x.val.2 = a.2 → (F x).2 ≤ 0)
    (h₄ : ∀ x, x.val.2 = b.2 → 0 ≤ (F x).2) :
    ∃ x, F x = 0 := by
  let clamp (x : ℝ × ℝ) : ℝ × ℝ :=
    (max a.1 (min b.1 x.1), max a.2 (min b.2 x.2))
  have hmem (x : ℝ × ℝ) : clamp x ∈ Icc a b :=
    ⟨⟨le_max_left .., le_max_left ..⟩,
      ⟨max_le hab.1 (min_le_left ..), max_le hab.2 (min_le_left ..)⟩⟩
  have hclamp : Continuous clamp := by unfold clamp; fun_prop
  let step (x : ℝ × ℝ) := clamp (x - F ⟨clamp x, hmem x⟩)
  have hstep : Continuous step := by
    exact hclamp.comp (continuous_id.sub (hc.comp (hclamp.subtype_mk hmem)))
  have hconv : Convex ℝ (Icc a b) := by
    convert (convex_Icc (𝕜 := ℝ) a.1 b.1).prod (convex_Icc (𝕜 := ℝ) a.2 b.2) using 1
    ext x
    simp only [mem_Icc, Set.mem_prod, Prod.le_def]
    tauto
  obtain ⟨x, hx, hfix⟩ :=
    MathlibExt.Analysis.Convex.BrouwerFixedPoint.exists_fixedPoint isCompact_Icc hconv
      ⟨a, le_rfl, hab⟩ hstep.continuousOn (fun x _ => hmem (x - F ⟨clamp x, hmem x⟩))
  have heq : clamp x = x :=
    Prod.ext
      (by change max a.1 (min b.1 x.1) = x.1; rw [min_eq_right hx.2.1, max_eq_right hx.1.1])
      (by change max a.2 (min b.2 x.2) = x.2; rw [min_eq_right hx.2.2, max_eq_right hx.1.2])
  have hsub : (⟨clamp x, hmem x⟩ : ↥(Icc a b)) = ⟨x, hx⟩ :=
    Subtype.ext heq
  change clamp (x - F ⟨clamp x, hmem x⟩) = x at hfix
  rw [hsub] at hfix
  refine ⟨⟨x, hx⟩, Prod.ext ?_ ?_⟩
  · exact eq_zero_of_clamp_eq (congrArg Prod.fst hfix) hx.1.1 hx.2.1 (h₁ ⟨x, hx⟩) (h₂ ⟨x, hx⟩)
  · exact eq_zero_of_clamp_eq (congrArg Prod.snd hfix) hx.1.2 hx.2.2 (h₃ ⟨x, hx⟩) (h₄ ⟨x, hx⟩)

private theorem dim_square_not_le_one : ¬ HasSmallInductiveDimensionLE Square 1 := by
  intro hdim
  obtain ⟨B, hB, hFront⟩ : ∃ B : Set (Set Square), IsTopologicalBasis B ∧
      ∀ U ∈ B, ZeroDimensionalSpace (frontier U) := by
    cases hdim with
    | succ n B hB hFront => exact ⟨B, hB, hFront⟩
  let c : Square := ⟨(0, 1 / 2), by norm_num [Prod.le_def]⟩
  let W : Set Square := {x | x.val.1 < 1 / 2}
  have hW : IsOpen W := isOpen_lt (continuous_fst.comp continuous_subtype_val) continuous_const
  have hcW : c ∈ W := by norm_num [W, c]
  obtain ⟨U, hUB, hcU, hUW⟩ := hB.exists_subset_of_mem_open hcW hW
  have hU := hB.isOpen hUB
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hcU)
  let r := min (ε / 2) (1 / 4)
  have hr : 0 < r := lt_min (half_pos hε) (by norm_num)
  have hrε : r < ε := (min_le_left ..).trans_lt (by linarith)
  have hr₄ : r ≤ 1 / 4 := min_le_right ..
  let a : ℝ × ℝ := (0, 1 / 2 - r)
  let b : ℝ × ℝ := (1, 1 / 2 + r)
  have hab : a ≤ b := ⟨by norm_num [a, b], by dsimp [a, b]; linarith⟩
  have hzeroa : (0 : ℝ × ℝ) ≤ a := ⟨by norm_num [a], by dsimp [a]; linarith⟩
  have hbone : b ≤ (1 : ℝ × ℝ) := ⟨by norm_num [b], by dsimp [b]; linarith⟩
  let incl (x : ↥(Icc a b)) : Square :=
    ⟨x.val, le_trans hzeroa x.property.1, le_trans x.property.2 hbone⟩
  have hleft (x : ↥(Icc a b)) (hx : x.val.1 = a.1) : incl x ∈ U := by
    apply hball
    change max (dist x.val.1 (0 : ℝ)) (dist x.val.2 (1 / 2 : ℝ)) < ε
    rw [max_lt_iff, show a.1 = 0 from rfl] at *
    refine ⟨by simpa [hx] using hε, ?_⟩
    have hx₁ : a.2 ≤ x.val.2 := x.property.1.2
    have hx₂ : x.val.2 ≤ b.2 := x.property.2.2
    rw [Real.dist_eq, abs_lt]
    dsimp [a, b] at hx₁ hx₂
    constructor <;> linarith
  have hclos : closure U ⊆ {x : Square | x.val.1 ≤ 1 / 2} :=
    closure_minimal (fun x hx => show x.val.1 ≤ 1 / 2 from
      (show x.val.1 < 1 / 2 from hUW hx).le)
      (isClosed_le (continuous_fst.comp continuous_subtype_val) continuous_const)
  have hright (x : ↥(Icc a b)) (hx : x.val.1 = b.1) :
      incl x ∉ closure U := by
    intro h
    have hh : x.val.1 ≤ 1 / 2 := hclos h
    norm_num [hx, b] at hh
  let f (x : Square) := infDist x (closure U) - infDist x Uᶜ
  have hf : Continuous f := (continuous_infDist_pt _).sub (continuous_infDist_pt _)
  have hUn : U.Nonempty := ⟨c, hcU⟩
  have hUc : Uᶜ.Nonempty :=
    ⟨incl ⟨b, hab, le_rfl⟩, fun h => hright ⟨b, hab, le_rfl⟩ rfl (subset_closure h)⟩
  have hf_left (x : Square) (h : x ∈ U) : f x < 0 := by
    have hp := (hU.isClosed_compl.notMem_iff_infDist_pos hUc).1 (show x ∉ Uᶜ by simpa using h)
    dsimp [f]
    rw [infDist_zero_of_mem (subset_closure h)]
    exact sub_neg_of_lt hp
  have hf_right (x : Square) (h : x ∉ closure U) : 0 < f x := by
    have hp := (isClosed_closure.notMem_iff_infDist_pos
      (hUn.mono (subset_closure (s := U)))).1 h
    have h' : x ∈ Uᶜ := fun hx => h (subset_closure hx)
    dsimp [f]
    rwa [infDist_zero_of_mem h', sub_zero]
  have hf_front {x : Square} (h : f x = 0) : x ∈ frontier U := by
    rw [hU.frontier_eq]
    exact ⟨by_contradiction (fun hn => (hf_right x hn).ne' h),
      fun hn => (hf_left x hn).ne h⟩
  let Bottom : Set Square := {x | x.val.2 = a.2}
  let Top : Set Square := {x | x.val.2 = b.2}
  have hBottom : IsClosed Bottom :=
    isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const
  have hTop : IsClosed Top :=
    isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const
  have hBT : Disjoint Bottom Top := by
    apply Set.disjoint_left.2
    intro x hx hy
    change x.val.2 = 1 / 2 - r at hx
    change x.val.2 = 1 / 2 + r at hy
    linarith
  let Z := frontier U
  have : ZeroDimensionalSpace Z := hFront _ hUB
  have : CompactSpace Z := isCompact_iff_compactSpace.1 isClosed_frontier.isCompact
  obtain ⟨C, hC, hBC, hCT⟩ :=
    exists_clopen_of_closed_subset_open
      (hBottom.preimage (continuous_subtype_val (p := fun x => x ∈ Z)))
      (hTop.preimage continuous_subtype_val).isOpen_compl
      (fun _ hx hy => Set.disjoint_left.1 hBT hx hy)
  let L : Set Square := Bottom ∪ Subtype.val '' C
  let H : Set Square := Top ∪ Subtype.val '' Cᶜ
  have hL : IsClosed L := hBottom.union
    (hC.isClosed.isCompact.image continuous_subtype_val).isClosed
  have hH : IsClosed H := hTop.union
    (hC.compl.isClosed.isCompact.image continuous_subtype_val).isClosed
  have hLH : Disjoint L H := by
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    refine ⟨⟨hBT, ?_⟩, ?_, disjoint_image_of_injective Subtype.val_injective disjoint_compl_right⟩
    · apply Set.disjoint_left.2
      rintro _ hx ⟨z, hz, rfl⟩
      exact hz (hBC hx)
    · apply Set.disjoint_left.2
      rintro _ ⟨z, hz, rfl⟩ hx
      exact hCT hz hx
  obtain ⟨g, hg₀, hg₁, _⟩ := exists_continuous_zero_one_of_isClosed hL hH hLH
  have hnonzero (x : Square) (hx : x ∈ Z) : g x - 1 / 2 ≠ 0 := by
    by_cases h : (⟨x, hx⟩ : Z) ∈ C
    · rw [show g x = 0 from hg₀ (Or.inr ⟨⟨x, hx⟩, h, rfl⟩)]
      norm_num
    · rw [show g x = 1 from hg₁ (Or.inr ⟨⟨x, hx⟩, h, rfl⟩)]
      norm_num
  have hincl : Continuous incl := continuous_subtype_val.subtype_mk _
  let F (x : ↥(Icc a b)) := (f (incl x), g (incl x) - 1 / 2)
  obtain ⟨x, hx⟩ := exists_common_zero hab F
    ((hf.comp hincl).prodMk ((g.continuous.comp hincl).sub continuous_const))
    (fun x hx => (hf_left _ (hleft x hx)).le) (fun x hx => (hf_right _ (hright x hx)).le)
    (fun x hx => by
      change g (incl x) - 1 / 2 ≤ 0
      rw [show g (incl x) = 0 from hg₀ (Or.inl hx)]
      norm_num)
    (fun x hx => by
      change 0 ≤ g (incl x) - 1 / 2
      rw [show g (incl x) = 1 from hg₁ (Or.inl hx)]
      norm_num)
  exact hnonzero _ (hf_front (congrArg Prod.fst hx)) (congrArg Prod.snd hx)

public section

/--
**Kolmogorov's open map raising dimension.** An interior (open) mapping can raise dimension:
there are compact metrizable spaces $X$ and $Y$, where $X$ has small inductive dimension exactly
$1$ and $Y$ has small inductive dimension exactly $2$, and a continuous open surjective map
$f \colon X \to Y$. A space has small inductive dimension exactly $n$ when its small inductive
dimension is at most $n$ but not at most $n - 1$.

Source: S. Eilenberg, Problem 136 of the Scottish Book, asking whether an
interior mapping can increase dimension; answered affirmatively by
A. Kolmogorov, Annals of Mathematics 38 (1937), pp. 34-38, who gave an example
of a continuous interior mapping raising dimension from 1 to 2, as recorded in
the typescript Ad 136.
-/
theorem kolmogorovInteriorMapRaisesDimension :
    ∃ (X Y : Type) (_ : TopologicalSpace X) (_ : TopologicalSpace Y) (_ : CompactSpace X)
      (_ : CompactSpace Y) (_ : TopologicalSpace.MetrizableSpace X)
      (_ : TopologicalSpace.MetrizableSpace Y),
      HasSmallInductiveDimensionLE X 1 ∧ ¬ HasSmallInductiveDimensionLE X 0 ∧
        HasSmallInductiveDimensionLE Y 2 ∧ ¬ HasSmallInductiveDimensionLE Y 1 ∧
        ∃ f : X → Y, Continuous f ∧ IsOpenMap f ∧ Function.Surjective f := by
  let Y : CompactMetric := ⟨Square, inferInstance, inferInstance⟩
  let f := projection Y 0
  have hc : Continuous f := continuous_projection Y 0
  have ho : IsOpenMap f := isOpenMap_projection Y 0
  have hs : Surjective f := projection_surjective Y 0
  refine ⟨Limit Y, Square, inferInstance, inferInstance, compactSpace_limit Y, inferInstance,
    inferInstance, inferInstance, dim_limit_le Y, ?_, dim_square_le, dim_square_not_le_one,
    f, hc, ho, hs⟩
  intro h
  exact dim_square_not_le_one (.mono (by decide : 0 ≤ 1)
    (zeroDimensional_of_open_surj f hc ho hs h))

end

end MathlibExt.Topology.ScottishBook136Wanted
