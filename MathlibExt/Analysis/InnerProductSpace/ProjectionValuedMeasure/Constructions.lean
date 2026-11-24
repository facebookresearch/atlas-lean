/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
# Constructions of projection-valued measures

This file supplies functorial and model constructions for projection-valued measures: transport by
a unitary equivalence, arbitrary Hilbert direct sums and inflations, and atomic diagonal measures.
All countable additivity remains pointwise-norm (strong-operator) additivity.

## Primary source

John B. Conway, *A Course in Functional Analysis*, 2nd ed., Chapter IX, §1,
Examples 1.7–1.8 (inflation and atomic measures). The direct-sum and atomic
models here allow arbitrary index types over measurable spaces; strong
countable additivity is expressed by pointwise `HasSum`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace MathlibExt.Analysis.InnerProductSpace

noncomputable section

universe u v w z

namespace ProjectionValuedMeasure

/-! ## Unitary transport -/

variable {X : Type u} [MeasurableSpace X]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Transport a projection-valued measure through a unitary linear equivalence. -/
noncomputable def unitaryTransport (U : H ≃ₗᵢ[ℂ] K) (E : ProjectionValuedMeasure X H) :
    ProjectionValuedMeasure X K where
  toFun s := U.conjStarAlgEquiv (E s)
  not_measurable' := by
    intro s hs
    rw [E.not_measurable hs, map_zero]
  projection' := by
    intro s hs
    exact (E.projection s hs).map U.conjStarAlgEquiv
  empty' := by rw [E.empty, map_zero]
  univ' := by rw [E.univ, map_one]
  inter' := by
    intro s hs t ht
    rw [E.inter s hs t ht, map_mul]
  m_iUnion' := by
    intro s hs hdisj y
    have hsum := E.m_iUnion s hs hdisj (U.symm y)
    have htransport := hsum.map U.toLinearEquiv.toLinearMap.toAddMonoidHom U.continuous
    change HasSum (fun n ↦ U (E (s n) (U.symm y))) (U (E (⋃ n, s n) (U.symm y)))
      at htransport
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] using htransport

@[simp]
theorem unitaryTransport_apply (U : H ≃ₗᵢ[ℂ] K) (E : ProjectionValuedMeasure X H)
    (s : Set X) (y : K) :
    unitaryTransport U E s y = U (E s (U.symm y)) :=
  rfl

/-- The range of a transported projection is the unitary image of the original range. -/
theorem range_unitaryTransport (U : H ≃ₗᵢ[ℂ] K) (E : ProjectionValuedMeasure X H)
    (s : Set X) :
    LinearMap.range (unitaryTransport U E s).toLinearMap =
      (LinearMap.range (E s).toLinearMap).map U.toLinearEquiv.toLinearMap := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨E s (U.symm z), ⟨U.symm z, rfl⟩, ?_⟩
    rfl
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    refine ⟨U x, ?_⟩
    simp

@[simp]
theorem unitaryTransport_refl (E : ProjectionValuedMeasure X H) :
    unitaryTransport (LinearIsometryEquiv.refl ℂ H) E = E := by
  apply ext_measurable
  intro s _hs
  apply ContinuousLinearMap.ext
  intro x
  rfl

variable {G : Type z} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Successive unitary transports agree with transport through the composite unitary. -/
theorem unitaryTransport_trans (U : H ≃ₗᵢ[ℂ] K) (V : K ≃ₗᵢ[ℂ] G)
    (E : ProjectionValuedMeasure X H) :
    unitaryTransport V (unitaryTransport U E) = unitaryTransport (U.trans V) E := by
  apply ext_measurable
  intro s _hs
  apply ContinuousLinearMap.ext
  intro x
  rfl

@[simp]
theorem unitaryTransport_symm (U : H ≃ₗᵢ[ℂ] K) (E : ProjectionValuedMeasure X H) :
    unitaryTransport U.symm (unitaryTransport U E) = E := by
  simpa using unitaryTransport_trans U U.symm E

/-! ## Arbitrary Hilbert direct sums -/

section DirectSum

variable {ι : Type z} {F : ι → Type v}
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
  [∀ i, CompleteSpace (F i)]

/-- The coordinatewise operator associated to a family of PVM values. -/
noncomputable def directSumValue (E : ∀ i, ProjectionValuedMeasure X (F i)) (s : Set X) :
    lp F 2 →L[ℂ] lp F 2 :=
  lp.mapCLM 2 (fun i ↦ E i s) zero_le_one fun i ↦
    IsStarProjection.norm_le _ ((E i).isStarProjection s)

@[simp]
theorem directSumValue_apply (E : ∀ i, ProjectionValuedMeasure X (F i))
    (s : Set X) (f : lp F 2) (i : ι) :
    directSumValue E s f i = E i s (f i) :=
  rfl

private theorem directSumValue_isStarProjection
    (E : ∀ i, ProjectionValuedMeasure X (F i)) (s : Set X) :
    IsStarProjection (directSumValue E s) := by
  constructor
  · change directSumValue E s * directSumValue E s = directSumValue E s
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext i
    change E i s (E i s (f i)) = E i s (f i)
    simpa only [mul_apply_eq_comp] using
      congrArg (fun T : F i →L[ℂ] F i ↦ T (f i)) ((E i).isStarProjection s).isIdempotentElem.eq
  · rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint]
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro f g
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro i
    rw [directSumValue_apply, directSumValue_apply]
    calc
      ⟪E i s (f i), g i⟫_ℂ =
          ⟪f i, (ContinuousLinearMap.adjoint (E i s)) (g i)⟫_ℂ :=
        (ContinuousLinearMap.adjoint_inner_right (E i s) (f i) (g i)).symm
      _ = ⟪f i, E i s (g i)⟫_ℂ := by
        rw [← ContinuousLinearMap.star_eq_adjoint,
          ((E i).isStarProjection s).isSelfAdjoint.star_eq]

/-- The Hilbert direct sum of an arbitrary family of projection-valued measures. -/
@[no_expose]
noncomputable def directSum (E : ∀ i, ProjectionValuedMeasure X (F i)) :
    ProjectionValuedMeasure X (lp F 2) where
  toFun s := directSumValue E s
  not_measurable' := by
    intro s hs
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext i
    simp [directSumValue_apply, (E i).not_measurable hs]
  projection' := fun s _hs ↦ directSumValue_isStarProjection E s
  empty' := by
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext i
    simp
  univ' := by
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext i
    simp
  inter' := by
    intro s hs t ht
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext i
    simp only [directSumValue_apply, mul_apply_eq_comp]
    change E i (s ∩ t) (f i) = (E i s * E i t) (f i)
    rw [(E i).inter s hs t ht]
  m_iUnion' := by
    intro s hs hdisj f
    let P : ℕ → lp F 2 →L[ℂ] lp F 2 := fun n ↦ directSumValue E (s n)
    have hP (n : ℕ) : IsStarProjection (P n) := directSumValue_isStarProjection E (s n)
    have horth : Pairwise fun m n ↦ P m * P n = 0 := by
      intro m n hmn
      apply ContinuousLinearMap.ext
      intro y
      apply lp.ext
      funext i
      change E i (s m) (E i (s n) (y i)) = 0
      have hzero := (E i).mul_eq_zero_of_disjoint (hs m) (hs n) (hdisj hmn)
      simpa only [mul_apply_eq_comp, zero_apply] using
        congrArg (fun T : F i →L[ℂ] F i ↦ T (y i)) hzero
    obtain ⟨Q, _hQproj, hQsum, _hQrange⟩ :=
      exists_hasSum_of_pairwise_orthogonal P hP horth
    have hQeq : Q = directSumValue E (⋃ n, s n) := by
      apply ContinuousLinearMap.ext
      intro y
      apply lp.ext
      funext i
      have hleft := (hQsum y).map (lp.evalCLM ℂ F 2 i).toLinearMap.toAddMonoidHom
        (lp.evalCLM ℂ F 2 i).continuous
      have hright := (E i).m_iUnion s hs hdisj (y i)
      have hfamily : (fun n ↦ (P n y) i) = fun n ↦ E i (s n) (y i) := by
        funext n
        rfl
      change HasSum (fun n ↦ (P n y) i) ((Q y) i) at hleft
      rw [hfamily] at hleft
      change (Q y) i = E i (⋃ n, s n) (y i)
      exact hleft.unique hright
    rw [← hQeq]
    exact hQsum f

@[simp]
theorem directSum_apply (E : ∀ i, ProjectionValuedMeasure X (F i))
    (s : Set X) (f : lp F 2) (i : ι) :
    directSum E s f i = E i s (f i) := by
  change directSumValue E s f i = E i s (f i)
  exact directSumValue_apply E s f i

/-- Inflation of a PVM by an arbitrary index type. -/
noncomputable def inflate (ι : Type z) (E : ProjectionValuedMeasure X H) :
    ProjectionValuedMeasure X (lp (fun _ : ι ↦ H) 2) :=
  directSum (fun _ : ι ↦ E)

@[simp]
theorem inflate_apply (ι : Type z) (E : ProjectionValuedMeasure X H)
    (s : Set X) (f : lp (fun _ : ι ↦ H) 2) (i : ι) :
    inflate ι E s f i = E s (f i) := by
  change directSum (fun _ : ι ↦ E) s f i = E s (f i)
  exact directSum_apply (fun _ : ι ↦ E) s f i

end DirectSum

/-! ## Atomic diagonal PVMs -/

section Atomic

variable {ι : Type z}

open scoped Classical

/-- The diagonal atomic PVM determined by points `x i`. Repeated points are allowed. -/
noncomputable def atomicDiagonal (x : ι → X) :
    ProjectionValuedMeasure X (lp (fun _ : ι ↦ ℂ) 2) :=
  directSum fun i ↦ ProjectionValuedMeasure.dirac (H := ℂ) (x i)

@[simp]
theorem atomicDiagonal_apply_of_mem (x : ι → X) {s : Set X} (hs : MeasurableSet s)
    (f : lp (fun _ : ι ↦ ℂ) 2) {i : ι} (hi : x i ∈ s) :
    atomicDiagonal x s f i = f i := by
  rw [atomicDiagonal, directSum_apply, dirac_apply_of_mem (x i) hs hi, one_apply_eq_self]

@[simp]
theorem atomicDiagonal_apply_of_not_mem (x : ι → X) {s : Set X}
    (f : lp (fun _ : ι ↦ ℂ) 2) {i : ι} (hi : x i ∉ s) :
    atomicDiagonal x s f i = 0 := by
  rw [atomicDiagonal, directSum_apply, dirac_apply_of_not_mem (x i) hi, zero_apply]

theorem atomicDiagonal_apply (x : ι → X) {s : Set X} (hs : MeasurableSet s)
    (f : lp (fun _ : ι ↦ ℂ) 2) (i : ι) :
    atomicDiagonal x s f i = if x i ∈ s then f i else 0 := by
  split_ifs with hi
  · exact atomicDiagonal_apply_of_mem x hs f hi
  · exact atomicDiagonal_apply_of_not_mem x f hi

variable {L : Type v} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- Transport the atomic diagonal PVM through a Hilbert basis. -/
noncomputable def atomicOfHilbertBasis (b : HilbertBasis ι ℂ L) (x : ι → X) :
    ProjectionValuedMeasure X L :=
  unitaryTransport b.repr.symm (atomicDiagonal x)

/-- Coordinate action of the atomic PVM transported through a Hilbert basis. -/
theorem atomicOfHilbertBasis_repr_apply (b : HilbertBasis ι ℂ L) (x : ι → X)
    {s : Set X} (hs : MeasurableSet s) (v : L) (i : ι) :
    b.repr (atomicOfHilbertBasis b x s v) i =
      if x i ∈ s then b.repr v i else 0 := by
  rw [atomicOfHilbertBasis, unitaryTransport_apply]
  simpa only [LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply] using
    atomicDiagonal_apply x hs (b.repr v) i

@[simp]
theorem atomicOfHilbertBasis_apply_basis_of_mem (b : HilbertBasis ι ℂ L) (x : ι → X)
    {s : Set X} (hs : MeasurableSet s) {i : ι} (hi : x i ∈ s) :
    atomicOfHilbertBasis b x s (b i) = b i := by
  classical
  apply b.repr.injective
  ext j
  rw [atomicOfHilbertBasis_repr_apply b x hs]
  by_cases hji : j = i
  · subst j
    simp [b.repr_self, lp.single_apply, hi]
  · simp [b.repr_self, lp.single_apply, hji]

@[simp]
theorem atomicOfHilbertBasis_apply_basis_of_not_mem (b : HilbertBasis ι ℂ L) (x : ι → X)
    {s : Set X} (hs : MeasurableSet s) {i : ι} (hi : x i ∉ s) :
    atomicOfHilbertBasis b x s (b i) = 0 := by
  classical
  apply b.repr.injective
  ext j
  rw [atomicOfHilbertBasis_repr_apply b x hs]
  by_cases hji : j = i
  · subst j
    simp [hi]
  · simp [b.repr_self, lp.single_apply, hji]

/-- The range of an atomic Hilbert-basis projection is the closed span of the selected basis
vectors. -/
theorem range_atomicOfHilbertBasis (b : HilbertBasis ι ℂ L) (x : ι → X)
    (s : Set X) (hs : MeasurableSet s) :
    LinearMap.range (atomicOfHilbertBasis b x s).toLinearMap =
      (Submodule.span ℂ (b '' {i | x i ∈ s})).topologicalClosure := by
  let P := atomicOfHilbertBasis b x s
  apply le_antisymm
  · rintro y ⟨v, rfl⟩
    have hsum := b.hasSum_repr (P v)
    apply mem_closure_of_tendsto hsum
    filter_upwards with u
    apply Submodule.sum_mem
    intro i hiu
    by_cases hi : x i ∈ s
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨i, hi, rfl⟩
    · have hcoeff : b.repr (P v) i = 0 := by
        simpa only [P, ite_eq_right hi] using atomicOfHilbertBasis_repr_apply b x hs v i
      simp [hcoeff]
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.2
      rintro y ⟨i, hi, rfl⟩
      exact ⟨b i, atomicOfHilbertBasis_apply_basis_of_mem b x hs hi⟩
    · let T := atomicOfHilbertBasis b x s
      have hT : T * T = T := ((atomicOfHilbertBasis b x).projection s hs).isIdempotentElem
      have hRange : (LinearMap.range T.toLinearMap : Set L) = {y | T y = y} := by
        ext y
        constructor
        · rintro ⟨z, rfl⟩
          change T (T z) = T z
          simpa only [mul_apply_eq_comp] using
            congrArg (fun S : L →L[ℂ] L ↦ S z) hT
        · intro hy
          exact ⟨y, hy⟩
      change IsClosed (LinearMap.range T.toLinearMap : Set L)
      rw [hRange]
      exact isClosed_eq T.continuous continuous_id

end Atomic

end ProjectionValuedMeasure

end

end MathlibExt.Analysis.InnerProductSpace
