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
# Unitary transport, Hilbert sums and atomic PVMs

Projection-valued measures on a measurable space `X` transport through a unitary `U : H ≃ K` by
`E_U(s)=U E(s) U⁻¹`. Families `E_i` on complete complex Hilbert spaces `H_i` have the Hilbert
direct sum PVM on `ℓ²(H_i)`, with `(E_⊕(s)f)_i=E_i(s)f_i`.

For any index type and points `x_i ∈ X`, the atomic diagonal PVM on `ℓ²(ι,ℂ)` has coordinate
value `f_i` when `x_i∈s` and zero otherwise. A Hilbert basis transports this PVM to its Hilbert
space, with range the closed span of basis vectors selected by the measurable set.

Indices may be empty or uncountable, and atomic points may repeat. All countable additivity is
strong operator additivity. These constructions include Conway, A Course in Functional Analysis,
Chapter IX, §1, Examples 1.7–1.8.
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

/-- **Unitary transport of a projection-valued measure.** Let `X` be a measurable space and
`H` a complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly
countably additive PVM. for a complete complex Hilbert space `K` and unitary `U : H ≃ₗᵢ[ℂ]
K`, `unitaryTransport U E` is the PVM `s ↦ U E(s) U⁻¹` on `K`. -/
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

/-- **Range of a unitarily transported spectral projection.** Let `X` be a measurable space
and `H` a complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a
strongly countably additive PVM. for a unitary `U : H ≃ₗᵢ[ℂ] K` between complete complex
Hilbert spaces and any set `s`, `range((unitaryTransport U E)(s))=U(range E(s))`. -/
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

/-- **Composition of unitary PVM transports.** Let `X` be a measurable space and `H` a
complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly
countably additive PVM. for unitaries `U : H ≃ K` and `V : K ≃ G` between complete complex
Hilbert spaces, transporting first by `U` then by `V` equals transport by `V∘U`. -/
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

/-- **Coordinate operator of a Hilbert sum of PVMs.** Let `X` be a measurable space, `ι` any
index type, and `H_i` complete complex Hilbert spaces with PVMs `E_i` on `X`. For any set
`s`, `directSumValue E s` acts on `lp H 2` by `(E_i(s)f_i)_i`, with operator norm at most
one. -/
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

/-- **Hilbert direct sum of projection-valued measures.** Let `X` be a measurable space and
`E_i` PVMs on complete complex Hilbert spaces `H_i`, indexed by any type `ι`. Their direct
sum is the strongly countably additive PVM on `lp H 2` with coordinate `(directSum E s
f)_i=E_i(s)f_i`. Empty and uncountable index types are allowed. -/
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

/-- **Inflation of a PVM on a Hilbert sequence sum.** Let `X` be a measurable space and `H` a
complete complex Hilbert space. Let `E : ProjectionValuedMeasure X H` be a strongly
countably additive PVM. for any index type `ι`, `inflate ι E` is the PVM on `lp (fun _ : ι
=> H) 2` acting coordinatewise by `(inflate ι E)(s)f_i=E(s)f_i`. -/
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

/-- **Atomic diagonal projection-valued measure.** For a measurable space `X`, any index type
`ι` and map `x : ι → X`, `atomicDiagonal x` is the PVM on `lp (fun _ : ι => ℂ) 2` sending
a measurable set `s` to the coordinate projection onto indices with `x_i∈s`. Repeated
points and empty indices are allowed. -/
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

/-- **Atomic PVM associated to a Hilbert basis.** Let `X` be a measurable space, `L` a
complete complex Hilbert space, `b : HilbertBasis ι ℂ L` and `x : ι → X`. The PVM
`atomicOfHilbertBasis b x` selects the basis vectors `b_i` whose points `x_i` lie in the
measurable set. -/
noncomputable def atomicOfHilbertBasis (b : HilbertBasis ι ℂ L) (x : ι → X) :
    ProjectionValuedMeasure X L :=
  unitaryTransport b.repr.symm (atomicDiagonal x)

/-- **Basis coefficients of an atomic spectral projection.** Let `X` be measurable, `L` a
complete complex Hilbert space, `b : HilbertBasis ι ℂ L` and `x : ι → X`. For measurable
`s`, `v ∈ L` and `i : ι`, the `i`th Hilbert-basis coefficient of `atomicOfHilbertBasis b x
s v` equals that of `v` if `x_i∈s`, and is zero otherwise. -/
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

/-- **Closed selected-basis span of an atomic PVM.** Let `X` be measurable, `L` a complete
complex Hilbert space, `b : HilbertBasis ι ℂ L` and `x : ι → X`. For measurable `s`,
`range(atomicOfHilbertBasis b x s)` is the norm closure of `span ℂ {b_i : x_i∈s}`. -/
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
