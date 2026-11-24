/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua
-/

module

public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.MeasureTheory.VectorMeasure.Basic

import MathlibExt.Algebra.Star.StarProjection.FiniteSum

/-!
# Projection-valued measures on Hilbert spaces

A projection-valued measure (`ProjectionValuedMeasure`) assigns an orthogonal
projection to every measurable set, sends the empty set to zero and the whole
space to one, turns intersections into products, and is countably additive in
the strong operator topology.  Strong additivity is represented directly by
pointwise norm-convergent `HasSum` statements.

The bundle is defined on all sets, following Mathlib's `VectorMeasure`
convention that nonmeasurable sets are canonically sent to zero.  It does not
extend `VectorMeasure X (H →L[ℂ] H)`, since that would incorrectly require
operator-norm countable additivity.  For a fixed vector `h`, however,
`E.applyVectorMeasure h` is a genuine `H`-valued vector measure; this derived
adapter lets the ordinary finite-union and complement API be reused without
strengthening the PVM laws.

The basic API uses Mathlib's canonical `IsStarProjection`.  It includes
measurable-set extensionality, projection/order/complement laws, disjoint
orthogonality and finite additivity, and the strong-sum semantics of a
countable orthogonal family of projections.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped InnerProduct InnerProductSpace Topology

namespace MathlibExt.Analysis.InnerProductSpace

noncomputable section

universe u v

variable {X : Type u} {H : Type v}
variable [MeasurableSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A projection-valued measure with pointwise-norm (strong-operator)
countable additivity. Nonmeasurable sets are canonically assigned zero. -/
@[ext]
structure ProjectionValuedMeasure (X : Type u) (H : Type v)
    [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The projection assigned to a set. -/
  toFun : Set X → H →L[ℂ] H
  /-- Nonmeasurable sets are assigned zero. -/
  not_measurable' : ∀ {s : Set X}, ¬ MeasurableSet s → toFun s = 0
  /-- Every measurable value is an orthogonal projection. -/
  projection' : ∀ s : Set X, MeasurableSet s → IsStarProjection (toFun s)
  /-- The empty set is assigned zero. -/
  empty' : toFun ∅ = 0
  /-- The whole space is assigned the identity. -/
  univ' : toFun Set.univ = 1
  /-- Intersections are sent to products. -/
  inter' : ∀ s : Set X, MeasurableSet s → ∀ t : Set X, MeasurableSet t →
    toFun (s ∩ t) = toFun s * toFun t
  /-- Countable additivity in the strong operator topology. -/
  m_iUnion' : ∀ (s : ℕ → Set X), (∀ n, MeasurableSet (s n)) →
    (Pairwise fun i j ↦ Disjoint (s i) (s j)) → ∀ h : H,
      HasSum (fun n ↦ toFun (s n) h) (toFun (⋃ n, s n) h)

namespace ProjectionValuedMeasure

instance : CoeFun (ProjectionValuedMeasure X H) (fun _ ↦ Set X → H →L[ℂ] H) where
  coe E := E.toFun

@[simp]
theorem not_measurable (E : ProjectionValuedMeasure X H) {s : Set X}
    (hs : ¬ MeasurableSet s) : E s = 0 :=
  E.not_measurable' hs

/-- Every value of a PVM is a star projection; a nonmeasurable set has value
zero. -/
theorem isStarProjection (E : ProjectionValuedMeasure X H) (s : Set X) :
    IsStarProjection (E s) := by
  by_cases hs : MeasurableSet s
  · exact E.projection' s hs
  · rw [E.not_measurable hs]
    exact IsStarProjection.zero _

theorem projection (E : ProjectionValuedMeasure X H) (s : Set X)
    (hs : MeasurableSet s) : IsStarProjection (E s) :=
  E.projection' s hs

@[simp]
theorem empty (E : ProjectionValuedMeasure X H) : E ∅ = 0 :=
  E.empty'

@[simp]
theorem univ (E : ProjectionValuedMeasure X H) : E Set.univ = 1 :=
  E.univ'

theorem inter (E : ProjectionValuedMeasure X H) (s : Set X) (hs : MeasurableSet s)
    (t : Set X) (ht : MeasurableSet t) :
    E (s ∩ t) = E s * E t :=
  E.inter' s hs t ht

theorem m_iUnion (E : ProjectionValuedMeasure X H) (s : ℕ → Set X)
    (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise fun i j ↦ Disjoint (s i) (s j)) (h : H) :
    HasSum (fun n ↦ E (s n) h) (E (⋃ n, s n) h) :=
  E.m_iUnion' s hs hdisj h

/-- Two PVMs agreeing on measurable sets are equal. -/
theorem ext_measurable {E F : ProjectionValuedMeasure X H}
    (h : ∀ s : Set X, MeasurableSet s → E s = F s) : E = F := by
  apply ProjectionValuedMeasure.ext
  funext s
  by_cases hs : MeasurableSet s
  · exact h s hs
  · rw [E.not_measurable hs, F.not_measurable hs]

/-- Evaluation of a PVM on one vector is an ordinary vector measure. This is
a derived pointwise adapter, not an operator-valued vector measure. -/
def applyVectorMeasure (E : ProjectionValuedMeasure X H) (h : H) :
    VectorMeasure X H where
  measureOf' s := E s h
  empty' := by simp
  not_measurable' := by
    intro s hs
    rw [E.not_measurable hs]
    rfl
  m_iUnion' := by
    intro s hs hdisj
    exact E.m_iUnion s hs hdisj h

@[simp]
theorem applyVectorMeasure_apply (E : ProjectionValuedMeasure X H) (h : H) (s : Set X) :
    E.applyVectorMeasure h s = E s h :=
  rfl

/-- A PVM is finitely additive on disjoint measurable sets. -/
theorem union (E : ProjectionValuedMeasure X H) {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    E (s ∪ t) = E s + E t := by
  apply ContinuousLinearMap.ext
  intro h
  exact (E.applyVectorMeasure h).of_union hdisj hs ht

/-- The projection of a measurable complement is `1 - E s`. -/
theorem compl (E : ProjectionValuedMeasure X H) {s : Set X} (hs : MeasurableSet s) :
    E sᶜ = 1 - E s := by
  apply ContinuousLinearMap.ext
  intro h
  simpa only [applyVectorMeasure_apply, E.univ, one_apply_eq_self, sub_apply] using
    (VectorMeasure.of_compl (v := E.applyVectorMeasure h) hs)

/-- Projections of disjoint measurable sets multiply to zero. -/
theorem mul_eq_zero_of_disjoint (E : ProjectionValuedMeasure X H) {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    E s * E t = 0 := by
  rw [← E.inter s hs t ht, Set.disjoint_iff_inter_eq_empty.mp hdisj, E.empty]

/-- Projections of disjoint measurable sets have orthogonal images. -/
theorem inner_apply_eq_zero_of_disjoint (E : ProjectionValuedMeasure X H) {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hdisj : Disjoint s t)
    (x y : H) :
    ⟪E s x, E t y⟫_ℂ = 0 := by
  calc
    ⟪E s x, E t y⟫_ℂ = ⟪x, ((E s)†) (E t y)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right (E s) x (E t y)).symm
    _ = ⟪x, (E s * E t) y⟫_ℂ := by
      rw [← ContinuousLinearMap.star_eq_adjoint,
        (E.projection s hs).isSelfAdjoint.star_eq]
      rfl
    _ = 0 := by rw [E.mul_eq_zero_of_disjoint hs ht hdisj]; simp

/-- The PVM is monotone on measurable sets in the canonical projection order. -/
theorem mono (E : ProjectionValuedMeasure X H) {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t) :
    E s ≤ E t := by
  rw [ContinuousLinearMap.le_def]
  apply ContinuousLinearMap.IsPositive.of_isStarProjection
  apply (E.projection s hs).sub_of_mul_eq_left (E.projection t ht)
  rw [← E.inter s hs t ht, Set.inter_eq_left.mpr hst]

/-- A finite union of pairwise-disjoint measurable sets is sent to the finite
sum of its projections. -/
theorem biUnion_finset (E : ProjectionValuedMeasure X H) {I : Type*}
    (u : Finset I) (s : I → Set X)
    (hs : ∀ i ∈ u, MeasurableSet (s i))
    (hdisj : (u : Set I).PairwiseDisjoint s) :
    E (⋃ i ∈ u, s i) = ∑ i ∈ u, E (s i) := by
  apply ContinuousLinearMap.ext
  intro h
  calc
    E (⋃ i ∈ u, s i) h = ∑ i ∈ u, E (s i) h :=
      (E.applyVectorMeasure h).of_biUnion_finset hdisj hs
    _ = (∑ i ∈ u, E (s i)) h := by simp

/-- The point-mass PVM at `x`: a measurable set containing `x` is assigned
the identity projection and every other set is assigned zero. -/
noncomputable def dirac (x : X) : ProjectionValuedMeasure X H := by
  classical
  refine
    { toFun := fun s ↦ if MeasurableSet s then if x ∈ s then 1 else 0 else 0
      not_measurable' := ?_
      projection' := ?_
      empty' := by simp
      univ' := by simp
      inter' := ?_
      m_iUnion' := ?_ }
  · intro s hs
    simp [hs]
  · intro s hs
    by_cases hxs : x ∈ s
    · simp [hs, hxs, IsStarProjection.one]
    · simp [hs, hxs, IsStarProjection.zero]
  · intro s hs t ht
    by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;>
      simp [hs, ht, hxs, hxt]
  · intro s hs hdisj h
    have hu : MeasurableSet (⋃ n, s n) := MeasurableSet.iUnion hs
    by_cases hx : ∃ k, x ∈ s k
    · obtain ⟨k, hk⟩ := hx
      have hmem (n : ℕ) : x ∈ s n ↔ n = k := by
        constructor
        · intro hn
          by_contra hnk
          exact Set.disjoint_left.1 (hdisj hnk) hn hk
        · intro hnk
          simpa [hnk] using hk
      have hxu : x ∈ ⋃ n, s n := Set.mem_iUnion_of_mem k hk
      simp_rw [hs, ite_true, hmem]
      have hop (n : ℕ) :
          (if n = k then (1 : H →L[ℂ] H) else 0) h = if n = k then h else 0 := by
        split_ifs <;> simp
      simp_rw [hop]
      simpa [hu, hxu] using (hasSum_ite_eq k h)
    · have hn (n : ℕ) : x ∉ s n := fun hxn ↦ hx ⟨n, hxn⟩
      have hnu : x ∉ ⋃ n, s n := by simp [hn]
      simp [hs, hu, hn, hnu, zero_apply]

@[simp]
theorem dirac_apply_of_mem (x : X) {s : Set X} (hs : MeasurableSet s) (hxs : x ∈ s) :
    dirac (H := H) x s = 1 := by
  simp [dirac, hs, hxs]

@[simp]
theorem dirac_apply_of_not_mem (x : X) {s : Set X} (hxs : x ∉ s) :
    dirac (H := H) x s = 0 := by
  by_cases hs : MeasurableSet s <;> simp [dirac, hs, hxs]

/-! ## Strong sums of orthogonal projections -/

private def projectionPartialSum (P : ℕ → H →L[ℂ] H) (u : Finset ℕ) : H →L[ℂ] H :=
  ∑ i ∈ u, P i

private theorem projectionPartialSum_isStarProjection
    (P : ℕ → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i))
    (horth : Pairwise fun i j ↦ P i * P j = 0) (u : Finset ℕ) :
    IsStarProjection (projectionPartialSum P u) := by
  change IsStarProjection (∑ i ∈ u, P i)
  exact IsStarProjection.finset_sum_of_pairwise_mul_eq_zero u P
    (fun i _ => hP i) (fun i _ j _ hij => horth hij)

private theorem projectionPartialSum_mul_of_subset
    (P : ℕ → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i))
    (horth : Pairwise fun i j ↦ P i * P j = 0)
    {u v : Finset ℕ} (huv : u ⊆ v) :
    projectionPartialSum P v * projectionPartialSum P u = projectionPartialSum P u := by
  classical
  rw [projectionPartialSum, projectionPartialSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul, Finset.sum_eq_single i]
  · exact (hP i).isIdempotentElem.eq
  · intro j hj hji
    exact horth hji
  · intro hin
    exact (hin (huv hi)).elim

/-- Conway IX.1.5: a countable pairwise-orthogonal family of projections sums
strongly to the projection onto the closed supremum of their ranges. -/
theorem exists_hasSum_of_pairwise_orthogonal
    (P : ℕ → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i))
    (horth : Pairwise fun i j ↦ P i * P j = 0) :
    ∃ Q : H →L[ℂ] H, IsStarProjection Q ∧
      (∀ h : H, HasSum (fun i ↦ P i h) (Q h)) ∧
      LinearMap.range Q.toLinearMap =
        (⨆ i, LinearMap.range (P i).toLinearMap).topologicalClosure := by
  classical
  let R : Finset ℕ → Submodule ℂ H := fun u ↦
    LinearMap.range (projectionPartialSum P u).toLinearMap
  have hQ (u : Finset ℕ) : IsStarProjection (projectionPartialSum P u) :=
    projectionPartialSum_isStarProjection P hP horth u
  have projectionPartialSum_apply (u : Finset ℕ) (x : H) :
      projectionPartialSum P u x = ∑ i ∈ u, P i x := by
    change ((↑(∑ i ∈ u, P i) : H →ₗ[ℂ] H) x) = ∑ i ∈ u, P i x
    rw [ContinuousLinearMap.toLinearMap_sum, LinearMap.sum_apply]
    simp only [ContinuousLinearMap.coe_coe]
  have projectionPartialSum_toLinearMap_apply (u : Finset ℕ) (x : H) :
      (projectionPartialSum P u).toLinearMap x = ∑ i ∈ u, P i x :=
    projectionPartialSum_apply u x
  let hR (u : Finset ℕ) : (R u).HasOrthogonalProjection := by
    dsimp only [R]
    exact ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
      (hQ u).isIdempotentElem
  have hprojection (u : Finset ℕ) :
      (R u).starProjection = projectionPartialSum P u := by
    apply ContinuousLinearMap.IsStarProjection.ext (isStarProjection_starProjection) (hQ u)
    rw [Submodule.range_starProjection]
  have hRmono : Monotone R := by
    intro u v huv
    rintro y ⟨x, rfl⟩
    refine ⟨projectionPartialSum P u x, ?_⟩
    have hmul := projectionPartialSum_mul_of_subset P hP horth huv
    change projectionPartialSum P v (projectionPartialSum P u x) = projectionPartialSum P u x
    rw [← mul_apply_eq_comp, hmul]
  have hRsup : ⨆ u, R u = ⨆ i, LinearMap.range (P i).toLinearMap := by
    apply le_antisymm
    · refine iSup_le ?_
      intro u
      rintro y ⟨x, rfl⟩
      rw [projectionPartialSum_toLinearMap_apply]
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self _ x)
    · refine iSup_le ?_
      intro i y hy
      apply Submodule.mem_iSup_of_mem ({i} : Finset ℕ)
      simpa only [R, projectionPartialSum, Finset.sum_singleton] using hy
  let U : Submodule ℂ H :=
    (⨆ i, LinearMap.range (P i).toLinearMap).topologicalClosure
  let : CompleteSpace U := by
    dsimp only [U]
    exact Submodule.topologicalClosure.completeSpace _
  let : U.HasOrthogonalProjection := by
    infer_instance
  let Q : H →L[ℂ] H := U.starProjection
  refine ⟨Q, isStarProjection_starProjection, ?_, ?_⟩
  · intro h
    have ht := Submodule.starProjection_tendsto_closure_iSup R hRmono h
    rw [hRsup] at ht
    simp_rw [hprojection, projectionPartialSum_apply] at ht
    change Filter.Tendsto (fun u : Finset ℕ ↦ ∑ i ∈ u, P i h) Filter.atTop
      (nhds (Q h))
    simpa only [Q, U] using ht
  · exact Submodule.range_starProjection U

end ProjectionValuedMeasure

end

end MathlibExt.Analysis.InnerProductSpace
