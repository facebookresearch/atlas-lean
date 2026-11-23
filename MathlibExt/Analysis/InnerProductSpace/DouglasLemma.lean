/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Douglas' lemma for bounded operators on Hilbert spaces

For bounded operators `A B : E →L[𝕜] F` between Hilbert spaces, Douglas' lemma
(R. G. Douglas, 1966) says the following three conditions are equivalent:

* `A.range ≤ B.range`;
* there is a bounded operator `C : E →L[𝕜] E` with `A = B ∘L C`;
* there is a constant `c ≥ 0` with `‖(A†) y‖ ≤ c * ‖(B†) y‖` for all `y` (majorization).

The implication from range inclusion to factorization is proved with the closed
graph theorem: for each `x`, the factor `C x` is defined as the unique element of
`(ker B)ᗮ` mapped by `B` to `A x`, and the resulting linear map is closed-graph
continuous. The implication from majorization to factorization is proved by
extending the bounded map `B† y ↦ A† y` from the range of `B†` to its closure
(`LinearMap.extendOfNorm`) and then taking adjoints.

This is a companion to the adjoint/range material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` (the closed
range theorem, the Fredholm alternative). It is not one of the 72 v1 targets,
and Douglas' lemma is not in the pinned Mathlib (which has the adjoint, the
orthogonal-complement identities, the closed graph theorem and `extendOfNorm`,
but no range-factorization statement) or in base MathlibExt.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.DouglasLemma

open scoped InnerProduct

variable {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
  (A B : E →L[𝕜] F)

/-- Adjoints preserve operator norm. -/
theorem norm_adjoint (T : E →L[𝕜] F) : ‖T†‖ = ‖T‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- Two points of `(ker B)ᗮ` with the same image under `B` are equal, since
their difference lies in `ker B ∩ (ker B)ᗮ`. -/
theorem eq_of_mem_orthogonal_and_apply {z₁ z₂ : E} (h₁ : z₁ ∈ B.kerᗮ)
    (h₂ : z₂ ∈ B.kerᗮ) (hB : B z₁ = B z₂) : z₁ = z₂ := by
  have hdiff : z₁ - z₂ ∈ B.ker := LinearMap.mem_ker.mpr (by
    show B (z₁ - z₂) = 0
    rw [map_sub, hB, sub_self])
  have hdiff2 : z₁ - z₂ ∈ B.kerᗮ := B.kerᗮ.sub_mem h₁ h₂
  have h0 : inner 𝕜 (z₁ - z₂) (z₁ - z₂) = 0 :=
    (Submodule.mem_orthogonal _ _).mp hdiff2 _ hdiff
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)

/-- If `A.range ≤ B.range`, every `A x` has a preimage under `B` in `(ker B)ᗮ`. -/
theorem exists_mem_orthogonal_apply (h : A.range ≤ B.range) (x : E) :
    ∃ z : E, z ∈ B.kerᗮ ∧ B z = A x := by
  obtain ⟨w, hw⟩ := h (LinearMap.mem_range_self (A : E →ₗ[𝕜] F) x)
  refine ⟨B.kerᗮ.starProjection w, Submodule.starProjection_apply_mem _ _, ?_⟩
  have hsub : w - B.kerᗮ.starProjection w = B.ker.starProjection w := by
    rw [Submodule.starProjection_orthogonal_val]
    exact sub_sub_cancel _ _
  have h0 : B (w - B.kerᗮ.starProjection w) = 0 := by
    rw [hsub]
    exact LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem B.ker w)
  have hBz : B (B.kerᗮ.starProjection w) = B w := by
    have h1 : B (B.kerᗮ.starProjection w) - B w = 0 := by
      rw [← map_sub,
        show B.kerᗮ.starProjection w - w = -(w - B.kerᗮ.starProjection w) by abel, map_neg, h0,
        neg_zero]
    exact sub_eq_zero.mp h1
  rw [hBz]
  exact hw

/-- The underlying function of the canonical factor: the chosen preimage of `A x`
in `(ker B)ᗮ`. -/
noncomputable def douglasFactorFun (h : A.range ≤ B.range) (x : E) : E :=
  Classical.choose (exists_mem_orthogonal_apply A B h x)

/-- The defining properties of the chosen preimage. -/
theorem douglasFactorFun_spec (h : A.range ≤ B.range) (x : E) :
    douglasFactorFun A B h x ∈ B.kerᗮ ∧ B (douglasFactorFun A B h x) = A x :=
  Classical.choose_spec (exists_mem_orthogonal_apply A B h x)

/-- The canonical factor as a linear map. -/
noncomputable def douglasFactorLin (h : A.range ≤ B.range) : E →ₗ[𝕜] E where
  toFun := douglasFactorFun A B h
  map_add' x y := by
    apply eq_of_mem_orthogonal_and_apply B (douglasFactorFun_spec A B h (x + y)).1
    · exact B.kerᗮ.add_mem (douglasFactorFun_spec A B h x).1
        (douglasFactorFun_spec A B h y).1
    · calc B (douglasFactorFun A B h (x + y)) = A (x + y) :=
          (douglasFactorFun_spec A B h (x + y)).2
        _ = A x + A y := map_add _ _ _
        _ = B (douglasFactorFun A B h x) + B (douglasFactorFun A B h y) := by
          rw [← (douglasFactorFun_spec A B h x).2, ← (douglasFactorFun_spec A B h y).2]
        _ = B (douglasFactorFun A B h x + douglasFactorFun A B h y) := (map_add _ _ _).symm
  map_smul' c x := by
    apply eq_of_mem_orthogonal_and_apply B (douglasFactorFun_spec A B h (c • x)).1
    · exact B.kerᗮ.smul_mem c (douglasFactorFun_spec A B h x).1
    · calc B (douglasFactorFun A B h (c • x)) = A (c • x) :=
          (douglasFactorFun_spec A B h (c • x)).2
        _ = c • A x := map_smul _ _ _
        _ = c • B (douglasFactorFun A B h x) := by
          rw [← (douglasFactorFun_spec A B h x).2]
        _ = B (c • douglasFactorFun A B h x) := (map_smul _ _ _).symm

/-- The canonical factor is continuous, by the (sequential) closed graph theorem:
if `u n → x` and `C (u n) → y`, then `y ∈ (ker B)ᗮ` (the orthogonal complement
is closed) and `B y = A x` (continuity of `A` and `B`), so `y = C x` by
uniqueness of the preimage in `(ker B)ᗮ`. -/
theorem continuous_douglasFactorLin (h : A.range ≤ B.range) :
    Continuous (douglasFactorLin A B h) := by
  apply LinearMap.continuous_of_seq_closed_graph
  intro u x y hu hgy
  have hyMem : y ∈ B.kerᗮ :=
    (Submodule.isClosed_orthogonal B.ker).mem_of_tendsto hgy
      (Filter.Eventually.of_forall fun n => (douglasFactorFun_spec A B h (u n)).1)
  have hB : B y = A x := by
    have h1 : Filter.Tendsto (fun n => B (douglasFactorLin A B h (u n))) Filter.atTop (nhds (B y)) :=
      (B.continuous.tendsto _).comp hgy
    have h2 : Filter.Tendsto (fun n => A (u n)) Filter.atTop (nhds (A x)) := (A.continuous.tendsto _).comp hu
    have hEq : (fun n => B (douglasFactorLin A B h (u n))) = fun n => A (u n) :=
      funext fun n => (douglasFactorFun_spec A B h (u n)).2
    rw [hEq] at h1
    exact tendsto_nhds_unique h1 h2
  exact eq_of_mem_orthogonal_and_apply B hyMem (douglasFactorFun_spec A B h x).1
    (by rw [hB]; exact (douglasFactorFun_spec A B h x).2.symm)

/-- The canonical factor in Douglas' lemma: for `x : E`, the unique element of
`(ker B)ᗮ` mapped by `B` to `A x`. -/
noncomputable def douglasFactor (h : A.range ≤ B.range) : E →L[𝕜] E where
  toLinearMap := douglasFactorLin A B h
  cont := continuous_douglasFactorLin A B h

/-- The canonical factor lands in `(ker B)ᗮ`. -/
theorem douglasFactor_mem_orthogonal (h : A.range ≤ B.range) (x : E) :
    douglasFactor A B h x ∈ B.kerᗮ :=
  douglasFactorFun_spec A B h x |>.1

/-- The canonical factor is a preimage: `B (C x) = A x`. -/
theorem apply_douglasFactor (h : A.range ≤ B.range) (x : E) :
    B (douglasFactor A B h x) = A x :=
  douglasFactorFun_spec A B h x |>.2

/-- The canonical factor factors `A` through `B`. -/
theorem eq_comp_douglasFactor (h : A.range ≤ B.range) : A = B ∘L douglasFactor A B h := by
  ext x
  exact (apply_douglasFactor A B h x).symm

/-- The canonical factor is the unique operator with the two defining properties. -/
theorem douglasFactor_eq_of_mem_orthogonal_and_apply {C : E →L[𝕜] E}
    (hC : ∀ x, C x ∈ B.kerᗮ ∧ B (C x) = A x) (h : A.range ≤ B.range) :
    C = douglasFactor A B h := by
  ext x
  exact eq_of_mem_orthogonal_and_apply B (hC x).1 (douglasFactorFun_spec A B h x).1
    (by rw [(hC x).2, apply_douglasFactor A B h x])

/-- Douglas' lemma, range form: `A.range ≤ B.range` iff `A = B ∘L C` for some
bounded `C`. -/
theorem range_le_iff_exists_factorization :
    A.range ≤ B.range ↔ ∃ C : E →L[𝕜] E, A = B ∘L C := by
  refine ⟨fun h => ⟨douglasFactor A B h, eq_comp_douglasFactor A B h⟩, ?_⟩
  rintro ⟨C, rfl⟩
  exact LinearMap.range_comp_le_range (C : E →ₗ[𝕜] E) (B : E →ₗ[𝕜] F)

/-- If `A = B ∘L C`, then majorization holds with constant `‖C‖`. -/
theorem majorization_of_factorization {C : E →L[𝕜] E} (hC : A = B ∘L C) (y : F) :
    ‖(A†) y‖ ≤ ‖C‖ * ‖(B†) y‖ := by
  have hAdj : A† = C† ∘L B† := by rw [hC]; exact ContinuousLinearMap.adjoint_comp _ _
  rw [hAdj]
  calc ‖(C† ∘L B†) y‖ = ‖(C†) ((B†) y)‖ := rfl
    _ ≤ ‖C†‖ * ‖(B†) y‖ := C†.le_opNorm _
    _ = ‖C‖ * ‖(B†) y‖ := by rw [norm_adjoint]

/-- Douglas' lemma, factorization form with a norm bound: majorization with
constant `c` yields a factor `C` with `A = B ∘L C` and `‖C‖ ≤ c`. -/
theorem exists_factorization_of_majorization {c : ℝ} (hc : 0 ≤ c)
    (hmaj : ∀ y : F, ‖(A†) y‖ ≤ c * ‖(B†) y‖) :
    ∃ C : E →L[𝕜] E, A = B ∘L C ∧ ‖C‖ ≤ c := by
  -- `S` is the closure of the range of `B†`.
  let S : Submodule 𝕜 E := B†.range.topologicalClosure
  -- `e` is `B†` with codomain restricted to `S`; its range is dense in `S`.
  let e : F →ₗ[𝕜] ↥S := LinearMap.codRestrict S (B† : F →ₗ[𝕜] E)
    (fun y => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ _))
  have hdense : DenseRange e := by
    intro x
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hx : (x : E) ∈ closure ((B†.range : Submodule 𝕜 E) : Set E) := x.2
    obtain ⟨w, hw, hdist⟩ := Metric.mem_closure_iff.mp hx ε hε
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hw
    refine ⟨e y, LinearMap.mem_range_self _ _, ?_⟩
    have hcoe : ((e y : ↥S) : E) = w := by
      show (B† : F →ₗ[𝕜] E) y = w
      exact hy
    rw [Subtype.dist_eq, hcoe]
    exact hdist
  have hnorm : ∀ y : F, ‖(A† : F →ₗ[𝕜] E) y‖ ≤ c * ‖e y‖ := fun y => hmaj y
  -- `D` is the bounded extension of `B† y ↦ A† y` from `range B†` to `S`.
  let D : ↥S →L[𝕜] E := (A† : F →ₗ[𝕜] E).extendOfNorm e
  have hDnorm : ‖D‖ ≤ c := LinearMap.opNorm_extendOfNorm_le hdense hc hnorm
  have hW : (D ∘L S.orthogonalProjectionOnto) ∘L B† = A† := by
    ext y
    show D (S.orthogonalProjectionOnto ((B†) y)) = (A†) y
    have hcoe : ((e y : ↥S) : E) = (B†) y := rfl
    have hproj : S.orthogonalProjectionOnto ((B†) y) = e y := by
      rw [← hcoe]
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (e y)
    rw [hproj]
    show D (e y) = (A†) y
    exact LinearMap.extendOfNorm_eq hdense ⟨c, hnorm⟩ y
  refine ⟨(D ∘L S.orthogonalProjectionOnto)†, ?_, ?_⟩
  · calc A = (A†)† := (ContinuousLinearMap.adjoint_adjoint A).symm
      _ = ((D ∘L S.orthogonalProjectionOnto) ∘L B†)† := by rw [hW]
      _ = B†† ∘L (D ∘L S.orthogonalProjectionOnto)† :=
        ContinuousLinearMap.adjoint_comp _ _
      _ = B ∘L (D ∘L S.orthogonalProjectionOnto)† := by
        rw [ContinuousLinearMap.adjoint_adjoint]
  · calc ‖(D ∘L S.orthogonalProjectionOnto)†‖ = ‖D ∘L S.orthogonalProjectionOnto‖ :=
        norm_adjoint _
      _ ≤ ‖D‖ * ‖S.orthogonalProjectionOnto‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ c * 1 :=
        mul_le_mul hDnorm S.orthogonalProjectionOnto_norm_le (norm_nonneg _) hc
      _ = c := mul_one c

/-- Douglas' lemma, majorization form: majorization holds iff `A` factors
through `B`. -/
theorem majorization_iff_exists_factorization :
    (∃ c : ℝ, 0 ≤ c ∧ ∀ y : F, ‖(A†) y‖ ≤ c * ‖(B†) y‖) ↔
      ∃ C : E →L[𝕜] E, A = B ∘L C := by
  constructor
  · rintro ⟨c, hc, hmaj⟩
    obtain ⟨C, hC, -⟩ := exists_factorization_of_majorization A B hc hmaj
    exact ⟨C, hC⟩
  · rintro ⟨C, rfl⟩
    exact ⟨‖C‖, norm_nonneg _, fun y => majorization_of_factorization (B ∘L C) B rfl y⟩

/-- Douglas' lemma, range/majorization form: `A.range ≤ B.range` iff
majorization holds. -/
theorem range_le_iff_majorization :
    A.range ≤ B.range ↔ ∃ c : ℝ, 0 ≤ c ∧ ∀ y : F, ‖(A†) y‖ ≤ c * ‖(B†) y‖ := by
  rw [range_le_iff_exists_factorization, majorization_iff_exists_factorization]

end MathlibExt.Analysis.InnerProductSpace.DouglasLemma
