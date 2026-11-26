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
# Projection-valued measures on complex Hilbert spaces

For a measurable space `X` and complete complex Hilbert space `H`, a PVM assigns to each
measurable set `s` an orthogonal projection `E(s)` on `H`. It satisfies `E(∅)=0`, `E(X)=I`,
`E(s∩t)=E(s)E(t)`, and `Σ_n E(s_n)h=E(⋃n s_n)h` in the Hilbert norm whenever the measurable sets
`s_n` are pairwise disjoint. Nonmeasurable sets are assigned zero.

For fixed `h`, the map `s ↦ E(s)h` is an `H`-valued vector measure. Disjoint sets yield
orthogonal projection ranges, complements give `E(sᶜ)=I-E(s)`, and measurable inclusion gives
the projection order. Operator-norm countable additivity is not imposed.

A countable family of pairwise orthogonal projections sums strongly to the orthogonal projection
onto the closed span of all their ranges.
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

/-- **Projection-valued measure with strong countable additivity.** Let `X` be a measurable
space and `H` a complete complex Hilbert space. a PVM sends measurable sets to orthogonal
projections, satisfies `E(∅)=0`, `E(X)=I`, `E(s∩t)=E(s)E(t)` and `Σ_n E(s_n)h=E(⋃n s_n)h`
in norm for disjoint measurable `s_n`. Nonmeasurable sets have value zero. -/
@[ext]
structure ProjectionValuedMeasure (X : Type u) (H : Type v)
    [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- **Set-valued operator function of a PVM.** Let `X` be a measurable space and `H` a
  complete complex Hilbert space. the function `E : Set X → B(H)` assigns a bounded
  complex-linear projection operator to each measurable set and zero to nonmeasurable
  sets. -/
  toFun : Set X → H →L[ℂ] H
  /-- **Zero value on nonmeasurable sets.** Let `X` be a measurable space and `H` a complete
  complex Hilbert space. the set-operator function of a PVM satisfies `E(s)=0` whenever `s
  ⊆ X` is not measurable. -/
  not_measurable' : ∀ {s : Set X}, ¬ MeasurableSet s → toFun s = 0
  /-- **Orthogonal projection values of a PVM.** Let `X` be a measurable space and `H` a
  complete complex Hilbert space. for every measurable `s ⊆ X`, its PVM value satisfies
  `E(s)²=E(s)` and `E(s)*=E(s)`. -/
  projection' : ∀ s : Set X, MeasurableSet s → IsStarProjection (toFun s)
  /-- **Empty-set value of a PVM.** Let `X` be a measurable space and `H` a complete complex
  Hilbert space. the set-operator function satisfies `E(∅)=0`. -/
  empty' : toFun ∅ = 0
  /-- **Identity value on the whole space.** Let `X` be a measurable space and `H` a complete
  complex Hilbert space. the PVM value of the whole measurable space is `E(X)=I_H`. -/
  univ' : toFun Set.univ = 1
  /-- **Intersection law of a PVM.** Let `X` be a measurable space and `H` a complete complex
  Hilbert space. for measurable `s,t ⊆ X`, `E(s∩t)=E(s)E(t)`, with operator multiplication
  given by composition. -/
  inter' : ∀ s : Set X, MeasurableSet s → ∀ t : Set X, MeasurableSet t →
    toFun (s ∩ t) = toFun s * toFun t
  /-- **Strong countable additivity of a PVM.** Let `X` be a measurable space and `H` a
  complete complex Hilbert space. for pairwise disjoint measurable sets `s_n` and every `h
  ∈ H`, the series `Σ_n E(s_n)h` has sum `E(⋃n s_n)h` in the Hilbert norm. -/
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

/-- **Orthogonal projection property for every PVM value.** Let `X` be a measurable space and
`H` a complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly
countably additive PVM. for every set `s ⊆ X`, `E(s)²=E(s)` and `E(s)*=E(s)`;
nonmeasurable sets have the zero projection. -/
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

/-- **PVM equality from measurable-set values.** Let `X` be a measurable space and `H` a
complete complex Hilbert space. two strongly countably additive PVMs `E,F` are equal if
`E(s)=F(s)` for every measurable set `s ⊆ X`. -/
theorem ext_measurable {E F : ProjectionValuedMeasure X H}
    (h : ∀ s : Set X, MeasurableSet s → E s = F s) : E = F := by
  apply ProjectionValuedMeasure.ext
  funext s
  by_cases hs : MeasurableSet s
  · exact h s hs
  · rw [E.not_measurable hs, F.not_measurable hs]

/-- **Vector measure obtained by evaluating a PVM.** Let `X` be a measurable space and `H` a
complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly
countably additive PVM. for `h ∈ H`, `applyVectorMeasure E h : VectorMeasure X H` is `s ↦
E(s)h`, countably additive in the norm of `H`. -/
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

/-- **Finite additivity of PVM projections.** Let `X` be a measurable space and `H` a complete
complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly countably
additive PVM. for disjoint measurable `s,t`, `E(s∪t)=E(s)+E(t)`. -/
theorem union (E : ProjectionValuedMeasure X H) {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    E (s ∪ t) = E s + E t := by
  apply ContinuousLinearMap.ext
  intro h
  exact (E.applyVectorMeasure h).of_union hdisj hs ht

/-- **Projection of a measurable complement.** Let `X` be a measurable space and `H` a
complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly
countably additive PVM. for a measurable set `s ⊆ X`, `E(sᶜ)=I_H-E(s)`. -/
theorem compl (E : ProjectionValuedMeasure X H) {s : Set X} (hs : MeasurableSet s) :
    E sᶜ = 1 - E s := by
  apply ContinuousLinearMap.ext
  intro h
  simpa only [applyVectorMeasure_apply, E.univ, one_apply_eq_self, sub_apply] using
    (VectorMeasure.of_compl (v := E.applyVectorMeasure h) hs)

/-- **Zero product of disjoint spectral projections.** Let `X` be a measurable space and `H` a
complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly
countably additive PVM. if measurable `s,t` are disjoint, `E(s)E(t)=0`. -/
theorem mul_eq_zero_of_disjoint (E : ProjectionValuedMeasure X H) {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    E s * E t = 0 := by
  rw [← E.inter s hs t ht, Set.disjoint_iff_inter_eq_empty.mp hdisj, E.empty]

/-- **Orthogonality of disjoint spectral ranges.** Let `X` be a measurable space and `H` a
complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly
countably additive PVM. for disjoint measurable `s,t` and any `x,y ∈ H`,
`⟨E(s)x,E(t)y⟩=0`. -/
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

/-- **Monotonicity of spectral projections.** Let `X` be a measurable space and `H` a complete
complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly countably
additive PVM. if measurable `s,t` satisfy `s ⊆ t`, then `E(s)≤E(t)` in the order of
positive Hilbert-space operators. -/
theorem mono (E : ProjectionValuedMeasure X H) {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t) :
    E s ≤ E t := by
  rw [ContinuousLinearMap.le_def]
  apply ContinuousLinearMap.IsPositive.of_isStarProjection
  apply (E.projection s hs).sub_of_mul_eq_left (E.projection t ht)
  rw [← E.inter s hs t ht, Set.inter_eq_left.mpr hst]

/-- **Projection of a finite disjoint union.** Let `X` be a measurable space and `H` a
complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly
countably additive PVM. for a finite index set `u` and pairwise disjoint measurable `s_i`
with `i ∈ u`, `E(⋃i∈u s_i)=Σ_i∈u E(s_i)`. The empty finite family is allowed. -/
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

/-- **Point-mass projection-valued measure.** Let `X` be a measurable space and `H` a complete
complex Hilbert space. for `x ∈ X`, `dirac x` assigns `I_H` to measurable sets containing
`x` and zero to every other set. The singleton `{x}` need not be measurable. -/
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

/-- **Strong sum of countably many orthogonal projections.** Let `H` be a complete complex
Hilbert space and `P_n : H →L[ℂ] H` orthogonal projections satisfying `P_i P_j=0` for
`i≠j`. There is an orthogonal projection `Q` with `Σ_n P_n h=Qh` in norm for every `h ∈
H`, and `range Q` is the closure of the linear span of all `range P_n`. -/
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
