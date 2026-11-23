/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm

/-!
# Hilbert–Schmidt operators on `ℓ²(ℕ, 𝕜)`

A matrix `a : ℕ → ℕ → 𝕜` is **Hilbert–Schmidt** if the squared norms of its
entries are summable (`IsHilbertSchmidt`), and its **Hilbert–Schmidt operator**
`hsOperator a ha` is the bounded operator on `ℓ²(ℕ, 𝕜)` acting by
`(hsOperator a ha x) i = ∑' j, a i j * x j`. This file develops its basic
theory: boundedness by the Hilbert–Schmidt norm, the adjoint (conjugate
transpose), compactness via finite truncations, the matrix characterization
(a bounded operator whose matrix is Hilbert–Schmidt is the Hilbert–Schmidt
operator of its matrix), and the diagonal and rank-one examples.

This is a companion to the Hilbert-space / spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(the Green's operator of the Sturm–Liouville problem there is a
Hilbert–Schmidt integral operator). It is not one of the 72 v1 targets:
v1 never defines Hilbert–Schmidt operators. Pinned Mathlib supplies `ℓ²`,
its inner product (`lp.inner_eq_tsum`), single-coordinate vectors
(`lp.single`), and the abstract compact-operator API. The existing
`MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm` supplies an
extended-valued operator norm in a countable family on real Hilbert spaces.
This file adds the `RCLike` matrix construction and connects its finite
real norm to that existing extended quantity on real `ℓ²`.
See e.g. Reed–Simon, *Methods of Modern Mathematical Physics I:
Functional Analysis*, Section VI.6.

## Main declarations

* `IsHilbertSchmidt` : a matrix is Hilbert–Schmidt if its squared entry
  norms are summable.
* `hsNormSq` : the squared Hilbert–Schmidt norm `∑' p, ‖a p.1 p.2‖ ^ 2`.
* `hsOperator` : the Hilbert–Schmidt operator of a matrix, as a bounded
  operator on `ℓ²(ℕ, 𝕜)`.
* `hsOperator_apply` : its pointwise action.
* `norm_hsOperator_le` : `‖hsOperator a ha‖ ≤ Real.sqrt (hsNormSq a ha)`.
* `adjoint_hsOperator` : `(hsOperator a ha)†` is the Hilbert–Schmidt
  operator of the conjugate-transpose matrix.
* `isCompactOperator_hsOperator` : every Hilbert–Schmidt operator is compact.
* `eq_hsOperator_of_isHilbertSchmidt_matrix` : a bounded operator whose
  matrix is Hilbert–Schmidt is the Hilbert–Schmidt operator of its matrix.
* `isCompactOperator_of_isHilbertSchmidt_matrix` /
  `norm_le_of_isHilbertSchmidt_matrix` : compactness and norm bound for a
  bounded operator with a Hilbert–Schmidt matrix.
* `hsDiagonal` / `hsRankOne` : the diagonal and rank-one matrices, with
  their action and squared Hilbert–Schmidt norm.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.HilbertSchmidt

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal NNReal

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Norm squared of an `ℓ²(ℕ, 𝕜)` vector is the sum of the squared coordinate norms. -/
theorem norm_sq_lp_eq_tsum (f : ℓ²(ℕ, 𝕜)) :
    ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (E := fun _ : ℕ => 𝕜) f
  rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num] at h
  have h2 : ‖f‖ ^ (2 : ℝ) = ‖f‖ ^ 2 := by rw [Real.rpow_two]
  rw [h2] at h
  rw [h]
  apply tsum_congr
  intro i
  rw [Real.rpow_two]

/-- Summability of squared coordinate norms from `Memℓp`. -/
theorem summable_norm_sq_of_memℓp {f : ℕ → 𝕜} (hf : Memℓp f 2) :
    Summable fun i => ‖f i‖ ^ 2 := by
  have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp hf
  simpa using h

/-- `Memℓp` at `2` from summability of squared norms. -/
theorem memℓp_of_summable_norm_sq {f : ℕ → 𝕜} (hf : Summable fun i => ‖f i‖ ^ 2) :
    Memℓp f 2 := by
  apply (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr
  simpa using hf

/-- A matrix is Hilbert–Schmidt if the squared norms of its entries are summable. -/
def IsHilbertSchmidt (a : ℕ → ℕ → 𝕜) : Prop :=
  Summable fun p : ℕ × ℕ => ‖a p.1 p.2‖ ^ 2

/-- The finite squared Hilbert–Schmidt norm: the sum of the squared entry norms.
The witness restricts this real quantity to summable matrices, avoiding the
zero default of a nonsummable real `tsum`. Divergent operators are handled
by the existing extended-valued operator norm. -/
noncomputable def hsNormSq (a : ℕ → ℕ → 𝕜) (_ha : IsHilbertSchmidt a) : ℝ :=
  ∑' p : ℕ × ℕ, ‖a p.1 p.2‖ ^ 2

theorem isHilbertSchmidt_iff {a : ℕ → ℕ → 𝕜} :
    IsHilbertSchmidt a ↔ Summable fun p : ℕ × ℕ => ‖a p.1 p.2‖ ^ 2 := Iff.rfl

/-- Fiber summability: each row of a Hilbert–Schmidt matrix is square-summable. -/
theorem summable_row_of_isHilbertSchmidt {a : ℕ → ℕ → 𝕜} (ha : IsHilbertSchmidt a) (i : ℕ) :
    Summable fun j => ‖a i j‖ ^ 2 := by
  have h : Summable ((fun p : ℕ × ℕ => ‖a p.1 p.2‖ ^ 2) ∘ fun j => (i, j)) :=
    ha.comp_injective (fun j₁ j₂ h => by simpa using congrArg Prod.snd h)
  exact h

/-- The row vector of a Hilbert–Schmidt matrix, as an `ℓ²` element (conjugated). -/
noncomputable def hsRow (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) (i : ℕ) : ℓ²(ℕ, 𝕜) :=
  ⟨fun j => star (a i j), by
    apply memℓp_of_summable_norm_sq
    simpa [norm_star] using summable_row_of_isHilbertSchmidt ha i⟩

theorem hsRow_apply (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) (i j : ℕ) :
    hsRow a ha i j = star (a i j) := rfl

theorem norm_sq_hsRow (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) (i : ℕ) :
    ‖hsRow a ha i‖ ^ 2 = ∑' j, ‖a i j‖ ^ 2 := by
  rw [norm_sq_lp_eq_tsum]
  apply tsum_congr
  intro j
  rw [hsRow_apply, norm_star]

theorem summable_norm_sq_hsRow (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) :
    Summable fun i => ‖hsRow a ha i‖ ^ 2 := by
  have h : Summable fun i => ∑' j, ‖a i j‖ ^ 2 := ha.prod
  refine h.congr (fun i => ?_)
  rw [norm_sq_hsRow]

/-- The coordinate series defining the Hilbert–Schmidt operator is summable. -/
theorem summable_hsCoord {a : ℕ → ℕ → 𝕜} (ha : IsHilbertSchmidt a) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    Summable fun j => a i j * x j := by
  have h := lp.summable_inner (𝕜 := 𝕜) (hsRow a ha i) x
  refine h.congr (fun j => ?_)
  rw [hsRow_apply, RCLike.inner_apply', starRingEnd_apply, star_star]

/-- The coordinate series is the inner product with the row vector. -/
theorem hsCoord_eq_inner {a : ℕ → ℕ → 𝕜} (ha : IsHilbertSchmidt a) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    (∑' j, a i j * x j) = ⟪hsRow a ha i, x⟫_𝕜 := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr (fun j => ?_)
  rw [hsRow_apply, RCLike.inner_apply', starRingEnd_apply, star_star]

/-- The coordinate series of a Hilbert–Schmidt matrix applied to an `ℓ²` vector is in `ℓ²`. -/
theorem memℓp_hsCoord {a : ℕ → ℕ → 𝕜} (ha : IsHilbertSchmidt a) (x : ℓ²(ℕ, 𝕜)) :
    Memℓp (fun i => ∑' j, a i j * x j) 2 := by
  apply memℓp_of_summable_norm_sq
  refine Summable.of_nonneg_of_le (f := fun i => ‖hsRow a ha i‖ ^ 2 * ‖x‖ ^ 2) (fun i => by positivity) (fun i => ?_) ?_
  · rw [hsCoord_eq_inner ha]
    calc ‖⟪hsRow a ha i, x⟫_𝕜‖ ^ 2
        ≤ (‖hsRow a ha i‖ * ‖x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := 𝕜) _ _) 2
      _ = ‖hsRow a ha i‖ ^ 2 * ‖x‖ ^ 2 := mul_pow _ _ _
  · exact (summable_norm_sq_hsRow a ha).mul_right _

/-- The Hilbert–Schmidt operator of a matrix, as a linear map. -/
noncomputable def hsLinMap (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) :
    ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun x := ⟨fun i => ∑' j, a i j * x j, memℓp_hsCoord ha x⟩
  map_add' x y := by
    apply lp.ext
    funext i
    show (∑' j, a i j * (x + y) j) = (∑' j, a i j * x j) + (∑' j, a i j * y j)
    rw [← (summable_hsCoord ha x i).tsum_add (summable_hsCoord ha y i)]
    refine tsum_congr (fun j => ?_)
    simp only [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c x := by
    apply lp.ext
    funext i
    show (∑' j, a i j * (c • x) j) = c * (∑' j, a i j * x j)
    rw [← tsum_mul_left]
    refine tsum_congr (fun j => ?_)
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- The squared norms of the coordinates of a Hilbert–Schmidt image are summable. -/
theorem summable_norm_sq_hsLinMap (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) (x : ℓ²(ℕ, 𝕜)) :
    Summable fun i => ‖hsLinMap a ha x i‖ ^ 2 :=
  summable_norm_sq_of_memℓp (memℓp_hsCoord ha x)

/-- Pointwise action of the Hilbert–Schmidt linear map. -/
theorem hsLinMap_apply (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    hsLinMap a ha x i = ∑' j, a i j * x j :=
  rfl

/-- The Hilbert–Schmidt operator is bounded by the square root of `hsNormSq`. -/
theorem norm_hsLinMap_le (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) (x : ℓ²(ℕ, 𝕜)) :
    ‖hsLinMap a ha x‖ ≤ Real.sqrt (hsNormSq a ha) * ‖x‖ := by
  have hsq : ‖hsLinMap a ha x‖ ^ 2 ≤ hsNormSq a ha * ‖x‖ ^ 2 := by
    rw [norm_sq_lp_eq_tsum]
    have hsum : Summable fun i => ‖hsRow a ha i‖ ^ 2 * ‖x‖ ^ 2 :=
      (summable_norm_sq_hsRow a ha).mul_right _
    have htsum : ∑' i, (‖hsRow a ha i‖ ^ 2 * ‖x‖ ^ 2) = hsNormSq a ha * ‖x‖ ^ 2 := by
      rw [tsum_mul_right]
      congr 1
      calc ∑' i, ‖hsRow a ha i‖ ^ 2 = ∑' i, ∑' j, ‖a i j‖ ^ 2 :=
            tsum_congr fun i => norm_sq_hsRow a ha i
        _ = ∑' p : ℕ × ℕ, ‖a p.1 p.2‖ ^ 2 :=
            (ha.tsum_prod' fun i => summable_row_of_isHilbertSchmidt ha i).symm
        _ = hsNormSq a ha := rfl
    rw [← htsum]
    refine (summable_norm_sq_hsLinMap a ha x).tsum_le_tsum (fun i => ?_) hsum
    · show ‖∑' j, a i j * x j‖ ^ 2 ≤ ‖hsRow a ha i‖ ^ 2 * ‖x‖ ^ 2
      rw [hsCoord_eq_inner ha]
      calc ‖⟪hsRow a ha i, x⟫_𝕜‖ ^ 2
          ≤ (‖hsRow a ha i‖ * ‖x‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := 𝕜) _ _) 2
        _ = ‖hsRow a ha i‖ ^ 2 * ‖x‖ ^ 2 := mul_pow _ _ _
  have hnn : 0 ≤ hsNormSq a ha := tsum_nonneg (fun p => by positivity)
  calc ‖hsLinMap a ha x‖ = Real.sqrt (‖hsLinMap a ha x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (hsNormSq a ha * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (hsNormSq a ha) * ‖x‖ := by
        rw [Real.sqrt_mul hnn, Real.sqrt_sq (norm_nonneg _)]

/-- The Hilbert–Schmidt operator of a matrix, as a bounded operator on `ℓ²(ℕ, 𝕜)`. -/
noncomputable def hsOperator (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) :
    ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  (hsLinMap a ha).mkContinuous (Real.sqrt (hsNormSq a ha)) (norm_hsLinMap_le a ha)

/-- Pointwise action of the Hilbert–Schmidt operator. -/
theorem hsOperator_apply (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    hsOperator a ha x i = ∑' j, a i j * x j :=
  rfl

/-- The operator norm of a Hilbert–Schmidt operator is at most its Hilbert–Schmidt norm. -/
theorem norm_hsOperator_le (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) :
    ‖hsOperator a ha‖ ≤ Real.sqrt (hsNormSq a ha) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (norm_hsLinMap_le a ha)

/-- The zero matrix is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_zero : IsHilbertSchmidt (0 : ℕ → ℕ → 𝕜) := by
  show Summable (fun p : ℕ × ℕ => ‖(0 : ℕ → ℕ → 𝕜) p.1 p.2‖ ^ 2)
  have h0 : (fun p : ℕ × ℕ => ‖(0 : ℕ → ℕ → 𝕜) p.1 p.2‖ ^ 2) = 0 := by
    funext p
    simp
  rw [h0]
  exact summable_zero

/-- The Hilbert–Schmidt operator of the zero matrix is zero. -/
theorem hsOperator_zero : hsOperator (0 : ℕ → ℕ → 𝕜) isHilbertSchmidt_zero = 0 := by
  ext x i
  simp [hsOperator_apply]

/-- The negative of a Hilbert–Schmidt matrix is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_neg {a : ℕ → ℕ → 𝕜} (ha : IsHilbertSchmidt a) :
    IsHilbertSchmidt (-a) := by
  refine ha.congr (fun p => ?_)
  simp [norm_neg]

/-- The sum of Hilbert–Schmidt matrices is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_add {a b : ℕ → ℕ → 𝕜} (ha : IsHilbertSchmidt a)
    (hb : IsHilbertSchmidt b) : IsHilbertSchmidt (a + b) := by
  refine Summable.of_nonneg_of_le (f := fun p => 2 * ‖a p.1 p.2‖ ^ 2 + 2 * ‖b p.1 p.2‖ ^ 2) (fun p => by positivity) (fun p => ?_) ?_
  · simp only [Pi.add_apply]
    calc ‖a p.1 p.2 + b p.1 p.2‖ ^ 2
        ≤ (‖a p.1 p.2‖ + ‖b p.1 p.2‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      _ ≤ 2 * ‖a p.1 p.2‖ ^ 2 + 2 * ‖b p.1 p.2‖ ^ 2 := by
          nlinarith [sq_nonneg (‖a p.1 p.2‖ - ‖b p.1 p.2‖),
            norm_nonneg (a p.1 p.2), norm_nonneg (b p.1 p.2)]
  · exact (ha.mul_left 2).add (hb.mul_left 2)

/-- The difference of Hilbert–Schmidt matrices is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_sub {a b : ℕ → ℕ → 𝕜} (ha : IsHilbertSchmidt a)
    (hb : IsHilbertSchmidt b) : IsHilbertSchmidt (a - b) := by
  have h := isHilbertSchmidt_add ha (isHilbertSchmidt_neg hb)
  convert h using 1
  funext i j
  simp [sub_eq_add_neg]

/-- A scalar multiple of a Hilbert–Schmidt matrix is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_smul {a : ℕ → ℕ → 𝕜} (ha : IsHilbertSchmidt a) (c : 𝕜) :
    IsHilbertSchmidt (c • a) := by
  refine (ha.mul_left (‖c‖ ^ 2)).congr (fun p => ?_)
  simp [Pi.smul_apply, mul_pow]

/-- The Hilbert–Schmidt operator of a sum is the sum of the operators. -/
theorem hsOperator_add {a b : ℕ → ℕ → 𝕜} (ha : IsHilbertSchmidt a) (hb : IsHilbertSchmidt b) :
    hsOperator (a + b) (isHilbertSchmidt_add ha hb) = hsOperator a ha + hsOperator b hb := by
  ext x i
  simp only [hsOperator_apply, add_apply, lp.coeFn_add, Pi.add_apply]
  rw [← (summable_hsCoord ha x i).tsum_add (summable_hsCoord hb x i)]
  refine tsum_congr (fun j => ?_)
  rw [add_mul]

/-- The Hilbert–Schmidt operator of a difference is the difference of the operators. -/
theorem hsOperator_sub {a b : ℕ → ℕ → 𝕜} (ha : IsHilbertSchmidt a) (hb : IsHilbertSchmidt b) :
    hsOperator (a - b) (isHilbertSchmidt_sub ha hb) = hsOperator a ha - hsOperator b hb := by
  ext x i
  simp only [hsOperator_apply, sub_apply, lp.coeFn_sub, Pi.sub_apply]
  rw [← (summable_hsCoord ha x i).tsum_sub (summable_hsCoord hb x i)]
  refine tsum_congr (fun j => ?_)
  rw [sub_mul]

/-- The Hilbert–Schmidt operator of a scalar multiple is the scalar multiple of the operator. -/
theorem hsOperator_smul {a : ℕ → ℕ → 𝕜} (ha : IsHilbertSchmidt a) (c : 𝕜) :
    hsOperator (c • a) (isHilbertSchmidt_smul ha c) = c • hsOperator a ha := by
  ext x i
  simp only [hsOperator_apply, smul_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [← tsum_mul_left]
  refine tsum_congr (fun j => ?_)
  rw [mul_assoc]

/-- The conjugate transpose of a matrix: `(aᵀ*) i j = star (a j i)`. -/
def hsTransposeStar (a : ℕ → ℕ → 𝕜) : ℕ → ℕ → 𝕜 := fun i j => star (a j i)

theorem hsTransposeStar_apply (a : ℕ → ℕ → 𝕜) (i j : ℕ) :
    hsTransposeStar a i j = star (a j i) := rfl

/-- The conjugate transpose of a Hilbert–Schmidt matrix is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_transposeStar {a : ℕ → ℕ → 𝕜} (ha : IsHilbertSchmidt a) :
    IsHilbertSchmidt (hsTransposeStar a) := by
  have h := ha.comp_injective (Equiv.injective (Equiv.prodComm ℕ ℕ))
  refine h.congr (fun p => ?_)
  simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
    hsTransposeStar, norm_star]

/-- The matrix of a bounded operator on `ℓ²(ℕ, 𝕜)`: entry `(i, j)` is the `i`-th
coordinate of the image of the `j`-th standard basis vector. -/
def hsMatrix (T : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) (i j : ℕ) : 𝕜 :=
  T (lp.single 2 j (1 : 𝕜)) i

theorem hsMatrix_apply (T : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) (i j : ℕ) :
    hsMatrix T i j = T (lp.single 2 j (1 : 𝕜)) i := rfl

/-- A bounded operator whose matrix is Hilbert–Schmidt is the Hilbert–Schmidt
operator of its matrix. -/
theorem eq_hsOperator_of_isHilbertSchmidt_matrix (T : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜))
    (hT : IsHilbertSchmidt (hsMatrix T)) :
    T = hsOperator (hsMatrix T) hT := by
  ext x i
  rw [hsOperator_apply]
  have h1 : ∀ z : ℓ²(ℕ, 𝕜), ∀ k : ℕ, z k = ⟪lp.single 2 k (1 : 𝕜), z⟫_𝕜 := by
    intro z k
    simp only [lp.inner_single_left, RCLike.inner_apply', map_one, one_mul]
  rw [h1 (T x) i, ← ContinuousLinearMap.adjoint_inner_left, lp.inner_eq_tsum]
  refine tsum_congr (fun j => ?_)
  rw [RCLike.inner_apply, h1 ((T†) (lp.single 2 i (1 : 𝕜))) j, inner_conj_symm,
    ContinuousLinearMap.adjoint_inner_left, ← h1 (T (lp.single 2 j (1 : 𝕜))) i]
  exact mul_comm _ _

/-- The matrix of a Hilbert–Schmidt operator is the matrix itself. -/
theorem hsMatrix_hsOperator (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) :
    hsMatrix (hsOperator a ha) = a := by
  funext i j
  show (hsOperator a ha (lp.single 2 j (1 : 𝕜))) i = a i j
  rw [hsOperator_apply]
  have hz : ∀ k, k ≠ j → a i k * ((lp.single 2 j (1 : 𝕜) : ℓ²(ℕ, 𝕜)) k) = 0 := by
    intro k hk
    rw [lp.single_apply_ne (E := fun _ : ℕ => 𝕜) 2 j (1 : 𝕜) hk, mul_zero]
  have h := tsum_eq_single (L := SummationFilter.unconditional ℕ) j hz
  rw [lp.single_apply_self, mul_one] at h
  exact h

/-- The Hilbert–Schmidt operator depends only on the matrix, not on the summability proof. -/
theorem hsOperator_congr {m m' : ℕ → ℕ → 𝕜} (h : m = m') (hm : IsHilbertSchmidt m)
    (hm' : IsHilbertSchmidt m') :
    hsOperator m hm = hsOperator m' hm' := by
  subst h
  rfl

/-- The adjoint of a Hilbert–Schmidt operator is the Hilbert–Schmidt operator
of the conjugate-transpose matrix. -/
theorem adjoint_hsOperator (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) :
    (hsOperator a ha)† =
      hsOperator (hsTransposeStar a) (isHilbertSchmidt_transposeStar ha) := by
  have hmat : hsMatrix ((hsOperator a ha)†) = hsTransposeStar (hsMatrix (hsOperator a ha)) := by
    funext i j
    show (((hsOperator a ha)†) (lp.single 2 j (1 : 𝕜))) i = star (hsMatrix (hsOperator a ha) j i)
    have h1 : ∀ z : ℓ²(ℕ, 𝕜), ∀ k : ℕ, z k = ⟪lp.single 2 k (1 : 𝕜), z⟫_𝕜 := by
      intro z k
      simp only [lp.inner_single_left, RCLike.inner_apply', map_one, one_mul]
    rw [h1, ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, ← h1,
      starRingEnd_apply]
    rfl
  have hHS : IsHilbertSchmidt (hsMatrix ((hsOperator a ha)†)) := by
    rw [hmat, hsMatrix_hsOperator]
    exact isHilbertSchmidt_transposeStar ha
  have h1 : hsMatrix ((hsOperator a ha)†) = hsTransposeStar a := by
    rw [hmat, hsMatrix_hsOperator]
  calc (hsOperator a ha)† = hsOperator (hsMatrix ((hsOperator a ha)†)) hHS :=
        eq_hsOperator_of_isHilbertSchmidt_matrix _ hHS
    _ = hsOperator (hsTransposeStar a) (isHilbertSchmidt_transposeStar ha) :=
        hsOperator_congr h1 _ _

/-- The truncation of a matrix to the top-left `N × N` block. -/
def hsTrunc (a : ℕ → ℕ → 𝕜) (N : ℕ) : ℕ → ℕ → 𝕜 :=
  fun i j => if i < N ∧ j < N then a i j else 0

theorem hsTrunc_apply (a : ℕ → ℕ → 𝕜) (N : ℕ) (i j : ℕ) :
    hsTrunc a N i j = if i < N ∧ j < N then a i j else 0 := rfl

/-- A truncation of any matrix is Hilbert–Schmidt: it is supported on a finite set. -/
theorem isHilbertSchmidt_hsTrunc (a : ℕ → ℕ → 𝕜) (N : ℕ) :
    IsHilbertSchmidt (hsTrunc a N) := by
  refine summable_of_ne_finset_zero (s := Finset.range N ×ˢ Finset.range N) (fun p hp => ?_)
  have hlt : ¬ (p.1 < N ∧ p.2 < N) := by
    intro h
    exact hp (by rw [Finset.mem_product]; exact ⟨Finset.mem_range.mpr h.1, Finset.mem_range.mpr h.2⟩)
  simp [hsTrunc, hlt]

/-- A finite sum of compact operators is compact. -/
private theorem isCompactOperator_finset_sum {S : Finset ℕ}
    {T : ℕ → ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)} (hT : ∀ i ∈ S, IsCompactOperator (T i)) :
    IsCompactOperator (∑ i ∈ S, T i : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) := by
  induction S using Finset.induction with
  | empty =>
      simpa using isCompactOperator_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hT _ (Finset.mem_insert_self _ _)).add
        (ih (fun i hi' => hT i (Finset.mem_insert_of_mem hi')))

/-- A rank-one operator on `ℓ²` is compact: it factors through the one-dimensional space `𝕜`. -/
theorem isCompactOperator_rankOne (x y : ℓ²(ℕ, 𝕜)) :
    IsCompactOperator (InnerProductSpace.rankOne 𝕜 x y) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton 𝕜 x)).comp_clm (innerSL 𝕜 y)

/-- The action of a scaled rank-one operator on standard basis vectors, pointwise. -/
theorem rankOne_single_apply (b : 𝕜) (i j : ℕ) (x : ℓ²(ℕ, 𝕜)) (k : ℕ) :
    ((b • InnerProductSpace.rankOne 𝕜 (lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜))
      (lp.single (E := fun _ : ℕ => 𝕜) 2 j (1 : 𝕜))) x) k =
      if k = i then b * x j else 0 := by
  rw [smul_apply, InnerProductSpace.rankOne_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
  by_cases h : k = i
  · subst h
    rw [ite_eq_left rfl, Pi.single_eq_same, mul_one]
    congr 1
    simp [lp.inner_single_left]
  · rw [ite_eq_right h, Pi.single_eq_of_ne h, mul_zero, mul_zero]

/-- A truncated Hilbert–Schmidt operator is a finite sum of rank-one operators. -/
theorem hsOperator_hsTrunc_eq_sum (a : ℕ → ℕ → 𝕜) (N : ℕ) :
    hsOperator (hsTrunc a N) (isHilbertSchmidt_hsTrunc a N) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (a i j) • InnerProductSpace.rankOne 𝕜
          (lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜))
          (lp.single (E := fun _ : ℕ => 𝕜) 2 j (1 : 𝕜)) := by
  ext x k
  rw [hsOperator_apply]
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply, rankOne_single_apply]
  have hfactor : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, if k = i then a i j * x j else 0)
      = ∑ i ∈ Finset.range N,
        (if k = i then ∑ j ∈ Finset.range N, a i j * x j else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (Finset.ite_sum_zero (k = i) (Finset.range N) (fun j => a i j * x j)).symm
  rw [hfactor, Finset.sum_ite_eq (Finset.range N) k
    (fun i => ∑ j ∈ Finset.range N, a i j * x j)]
  by_cases hk : k < N
  · rw [ite_eq_left (Finset.mem_range.mpr hk)]
    have hz : ∀ j ∉ Finset.range N, hsTrunc a N k j * x j = 0 := by
      intro j hj
      rw [Finset.mem_range] at hj
      simp [hsTrunc, hj]
    rw [(hasSum_sum_of_ne_finset_zero hz).tsum_eq]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    simp [hsTrunc, hk, hj]
  · rw [ite_eq_right (fun h => hk (Finset.mem_range.mp h))]
    have hzero : (∑' j, hsTrunc a N k j * x j) = ∑' _ : ℕ, (0 : 𝕜) := by
      apply tsum_congr
      intro j
      simp [hsTrunc, hk]
    rw [hzero, tsum_zero]

/-- A truncated Hilbert–Schmidt operator is compact. -/
theorem isCompactOperator_hsOperator_hsTrunc (a : ℕ → ℕ → 𝕜) (N : ℕ) :
    IsCompactOperator (hsOperator (hsTrunc a N) (isHilbertSchmidt_hsTrunc a N)) := by
  rw [hsOperator_hsTrunc_eq_sum]
  apply isCompactOperator_finset_sum
  intro i _
  apply isCompactOperator_finset_sum
  intro j _
  show IsCompactOperator ((a i j) • ⇑(InnerProductSpace.rankOne 𝕜
    (lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜))
    (lp.single (E := fun _ : ℕ => 𝕜) 2 j (1 : 𝕜))))
  exact (isCompactOperator_rankOne _ _).smul _

/-- The squared Hilbert–Schmidt norm of the truncation error is the tail sum. -/
theorem hsNormSq_sub_hsTrunc (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) (N : ℕ) :
    hsNormSq (a - hsTrunc a N)
      (isHilbertSchmidt_sub ha (isHilbertSchmidt_hsTrunc a N)) =
      hsNormSq a ha - ∑ p ∈ Finset.range N ×ˢ Finset.range N, ‖a p.1 p.2‖ ^ 2 := by
  have hmem : ∀ p : ℕ × ℕ, (p ∈ Finset.range N ×ˢ Finset.range N ↔ p.1 < N ∧ p.2 < N) := by
    intro p
    simp [Finset.mem_product]
  have hsplit : ∀ p : ℕ × ℕ,
      ‖(a - hsTrunc a N) p.1 p.2‖ ^ 2 +
        (if p ∈ Finset.range N ×ˢ Finset.range N then ‖a p.1 p.2‖ ^ 2 else 0) =
        ‖a p.1 p.2‖ ^ 2 := by
    intro p
    by_cases hp : p ∈ Finset.range N ×ˢ Finset.range N
    · rw [ite_eq_left hp]
      have h2 : (a - hsTrunc a N) p.1 p.2 = 0 := by
        simp [hsTrunc, (hmem p).mp hp]
      rw [h2]
      simp
    · rw [ite_eq_right hp]
      have h2 : (a - hsTrunc a N) p.1 p.2 = a p.1 p.2 := by
        have h1 : ¬ (p.1 < N ∧ p.2 < N) := fun h => hp ((hmem p).mpr h)
        simp [hsTrunc, h1]
      rw [h2]
      simp
  have hsum_g0 : (∑' p : ℕ × ℕ, (if p ∈ Finset.range N ×ˢ Finset.range N then ‖a p.1 p.2‖ ^ 2 else 0))
      = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
        (if p ∈ Finset.range N ×ˢ Finset.range N then ‖a p.1 p.2‖ ^ 2 else 0) :=
    (hasSum_sum_of_ne_finset_zero (s := Finset.range N ×ˢ Finset.range N)
      (f := fun p => if p ∈ Finset.range N ×ˢ Finset.range N then ‖a p.1 p.2‖ ^ 2 else 0)
      (fun p hp => ite_eq_right hp)).tsum_eq
  have hsum_g : ∑' p : ℕ × ℕ, (if p ∈ Finset.range N ×ˢ Finset.range N then ‖a p.1 p.2‖ ^ 2 else 0)
      = ∑ p ∈ Finset.range N ×ˢ Finset.range N, ‖a p.1 p.2‖ ^ 2 := by
    rw [hsum_g0]
    apply Finset.sum_congr rfl
    intro b hb
    rw [ite_eq_left hb]
  have hsum_f : Summable fun p : ℕ × ℕ => ‖(a - hsTrunc a N) p.1 p.2‖ ^ 2 :=
    isHilbertSchmidt_sub ha (isHilbertSchmidt_hsTrunc a N)
  have hsum_g' : Summable fun p : ℕ × ℕ =>
      (if p ∈ Finset.range N ×ˢ Finset.range N then ‖a p.1 p.2‖ ^ 2 else 0) :=
    (hasSum_sum_of_ne_finset_zero (s := Finset.range N ×ˢ Finset.range N)
      (f := fun p => if p ∈ Finset.range N ×ˢ Finset.range N then ‖a p.1 p.2‖ ^ 2 else 0)
      (fun p hp => ite_eq_right hp)).summable
  have htsum : ∑' p : ℕ × ℕ, ‖a p.1 p.2‖ ^ 2
      = ∑' p : ℕ × ℕ, ‖(a - hsTrunc a N) p.1 p.2‖ ^ 2
        + ∑' p : ℕ × ℕ, (if p ∈ Finset.range N ×ˢ Finset.range N then ‖a p.1 p.2‖ ^ 2 else 0) := by
    rw [← (hsum_f.tsum_add hsum_g')]
    apply tsum_congr
    intro p
    exact (hsplit p).symm
  unfold hsNormSq
  linarith [htsum, hsum_g]

/-- The partial sums of the squared norms over expanding squares converge to `hsNormSq`. -/
theorem tendsto_hsTrunc_finset_sum {a : ℕ → ℕ → 𝕜} (ha : IsHilbertSchmidt a) :
    Tendsto (fun N => ∑ p ∈ Finset.range N ×ˢ Finset.range N, ‖a p.1 p.2‖ ^ 2) atTop
      (𝓝 (hsNormSq a ha)) := by
  show Tendsto (fun N => ∑ p ∈ Finset.range N ×ˢ Finset.range N, ‖a p.1 p.2‖ ^ 2) atTop
    (𝓝 (∑' p : ℕ × ℕ, ‖a p.1 p.2‖ ^ 2))
  have htoptop : Tendsto (fun N => Finset.range N ×ˢ Finset.range N) atTop atTop := by
    rw [tendsto_atTop]
    intro S
    filter_upwards [eventually_ge_atTop (S.sup (fun p => p.1 + p.2) + 1)] with N hN
    show S ⊆ Finset.range N ×ˢ Finset.range N
    intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    have h1 : p.1 + p.2 ≤ S.sup (fun p => p.1 + p.2) :=
      Finset.le_sup (f := fun q : ℕ × ℕ => q.1 + q.2) hp
    constructor <;> omega
  have h : Tendsto (fun S : Finset (ℕ × ℕ) => ∑ p ∈ S, ‖a p.1 p.2‖ ^ 2) atTop
      (𝓝 (∑' p : ℕ × ℕ, ‖a p.1 p.2‖ ^ 2)) := ha.hasSum
  exact h.comp htoptop

/-- The squared Hilbert–Schmidt norm of the truncation error tends to zero. -/
theorem tendsto_hsNormSq_sub_hsTrunc {a : ℕ → ℕ → 𝕜} (ha : IsHilbertSchmidt a) :
    Tendsto (fun N => hsNormSq (a - hsTrunc a N)
      (isHilbertSchmidt_sub ha (isHilbertSchmidt_hsTrunc a N))) atTop (𝓝 0) := by
  have h := tendsto_hsTrunc_finset_sum ha
  have heq : (fun N => hsNormSq (a - hsTrunc a N)
      (isHilbertSchmidt_sub ha (isHilbertSchmidt_hsTrunc a N))) = fun N =>
      hsNormSq a ha - ∑ p ∈ Finset.range N ×ˢ Finset.range N, ‖a p.1 p.2‖ ^ 2 := by
    funext N
    exact hsNormSq_sub_hsTrunc a ha N
  rw [heq]
  have h2 : Tendsto (fun N =>
      hsNormSq a ha - ∑ p ∈ Finset.range N ×ˢ Finset.range N, ‖a p.1 p.2‖ ^ 2) atTop
      (𝓝 (hsNormSq a ha - hsNormSq a ha)) := tendsto_const_nhds.sub h
  rwa [sub_self] at h2

/-- The truncated operators converge in norm to the Hilbert–Schmidt operator. -/
theorem tendsto_hsOperator_hsTrunc (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) :
    Tendsto (fun N => hsOperator (hsTrunc a N) (isHilbertSchmidt_hsTrunc a N)) atTop
      (𝓝 (hsOperator a ha)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun N => Real.sqrt (hsNormSq (a - hsTrunc a N)
      (isHilbertSchmidt_sub ha (isHilbertSchmidt_hsTrunc a N)))) ?_ ?_ ?_
  · intro N
    exact norm_nonneg _
  · intro N
    have h1 : hsOperator (hsTrunc a N) (isHilbertSchmidt_hsTrunc a N) - hsOperator a ha =
        -(hsOperator (a - hsTrunc a N)
          (isHilbertSchmidt_sub ha (isHilbertSchmidt_hsTrunc a N))) := by
      rw [hsOperator_sub, neg_sub]
    rw [h1, norm_neg]
    exact norm_hsOperator_le _ _
  · have h := (Real.continuous_sqrt.tendsto 0).comp (tendsto_hsNormSq_sub_hsTrunc ha)
    rw [Real.sqrt_zero] at h
    exact h

/-- Every Hilbert–Schmidt operator on `ℓ²(ℕ, 𝕜)` is compact. -/
theorem isCompactOperator_hsOperator (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) :
    IsCompactOperator (hsOperator a ha) := by
  refine isCompactOperator_of_tendsto (tendsto_hsOperator_hsTrunc a ha) ?_
  exact Filter.Eventually.of_forall (fun N => isCompactOperator_hsOperator_hsTrunc a N)

/-- A bounded operator whose matrix is Hilbert–Schmidt is compact. -/
theorem isCompactOperator_of_isHilbertSchmidt_matrix (T : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜))
    (hT : IsHilbertSchmidt (hsMatrix T)) : IsCompactOperator T := by
  rw [eq_hsOperator_of_isHilbertSchmidt_matrix T hT]
  exact isCompactOperator_hsOperator _ hT

/-- A bounded operator whose matrix is Hilbert–Schmidt has norm at most its
Hilbert–Schmidt norm. -/
theorem norm_le_of_isHilbertSchmidt_matrix (T : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜))
    (hT : IsHilbertSchmidt (hsMatrix T)) :
    ‖T‖ ≤ Real.sqrt (hsNormSq (hsMatrix T) hT) := by
  conv_lhs => rw [eq_hsOperator_of_isHilbertSchmidt_matrix T hT]
  exact norm_hsOperator_le _ hT

/-- The diagonal matrix with diagonal `d`. -/
def hsDiagonal (d : ℕ → 𝕜) : ℕ → ℕ → 𝕜 := fun i j => if i = j then d i else 0

/-- A row of a diagonal matrix is square-summable. -/
theorem summable_hsDiagonal_row (d : ℕ → 𝕜) (i : ℕ) :
    Summable fun j => ‖hsDiagonal d i j‖ ^ 2 := by
  have h : (fun j => ‖hsDiagonal d i j‖ ^ 2) = fun j => if j = i then ‖d i‖ ^ 2 else 0 := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [hsDiagonal]
    · simp [hsDiagonal, hj, show i ≠ j from fun hh => hj hh.symm]
  rw [h]
  have hf : ∀ j, j ≠ i → (if j = i then ‖d i‖ ^ 2 else 0) = 0 := fun j hj => ite_eq_right hj
  exact (hasSum_single i hf).summable

/-- The squared norms in a row of a diagonal matrix sum to the squared diagonal entry. -/
theorem tsum_hsDiagonal_row (d : ℕ → 𝕜) (i : ℕ) :
    ∑' j, ‖hsDiagonal d i j‖ ^ 2 = ‖d i‖ ^ 2 := by
  have h : (fun j => ‖hsDiagonal d i j‖ ^ 2) = fun j => if j = i then ‖d i‖ ^ 2 else 0 := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [hsDiagonal]
    · simp [hsDiagonal, hj, show i ≠ j from fun hh => hj hh.symm]
  rw [h]
  have hf : ∀ j, j ≠ i → (if j = i then ‖d i‖ ^ 2 else 0) = 0 := fun j hj => ite_eq_right hj
  simp

/-- A diagonal matrix with square-summable diagonal is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_hsDiagonal {d : ℕ → 𝕜} (hd : Summable fun i => ‖d i‖ ^ 2) :
    IsHilbertSchmidt (hsDiagonal d) := by
  refine summable_prod_of_nonneg (fun p => by positivity) |>.mpr
    ⟨fun i => summable_hsDiagonal_row d i, ?_⟩
  exact hd.congr (fun i => (tsum_hsDiagonal_row d i).symm)

/-- The squared Hilbert–Schmidt norm of a diagonal matrix is the sum of the squared
diagonal entries. -/
theorem hsNormSq_hsDiagonal {d : ℕ → 𝕜} (hd : Summable fun i => ‖d i‖ ^ 2) :
    hsNormSq (hsDiagonal d) (isHilbertSchmidt_hsDiagonal hd) = ∑' i, ‖d i‖ ^ 2 := by
  show ∑' p : ℕ × ℕ, ‖hsDiagonal d p.1 p.2‖ ^ 2 = ∑' i, ‖d i‖ ^ 2
  rw [(isHilbertSchmidt_hsDiagonal hd).tsum_prod' (fun i => summable_hsDiagonal_row d i)]
  exact tsum_congr fun i => tsum_hsDiagonal_row d i

/-- A diagonal Hilbert–Schmidt operator acts by pointwise multiplication by the diagonal. -/
theorem hsOperator_hsDiagonal_apply {d : ℕ → 𝕜} (hd : Summable fun i => ‖d i‖ ^ 2)
    (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    hsOperator (hsDiagonal d) (isHilbertSchmidt_hsDiagonal hd) x i = d i * x i := by
  rw [hsOperator_apply]
  have hterm : ∀ j, hsDiagonal d i j * x j = if i = j then d i * x j else 0 := by
    intro j
    by_cases h : i = j
    · subst h
      simp [hsDiagonal]
    · simp [hsDiagonal, h]
  rw [tsum_congr hterm]
  have hf : ∀ j, j ≠ i → (if i = j then d i * x j else 0) = 0 :=
    fun j hj => ite_eq_right (fun h => hj h.symm)
  simp

/-- The rank-one matrix `u i * star (v j)`. -/
def hsRankOne (u v : ℕ → 𝕜) : ℕ → ℕ → 𝕜 := fun i j => u i * star (v j)

/-- The squared norms of the entries of a rank-one matrix are summable over the product. -/
theorem summable_hsRankOne_sq {u v : ℓ²(ℕ, 𝕜)} :
    Summable fun p : ℕ × ℕ => ‖u p.1‖ ^ 2 * ‖v p.2‖ ^ 2 := by
  refine summable_prod_of_nonneg (fun p => by positivity) |>.mpr ⟨fun i => ?_, ?_⟩
  · exact (summable_norm_sq_of_memℓp v.2).mul_left (‖u i‖ ^ 2)
  · have h : (fun i => ∑' j, ‖u i‖ ^ 2 * ‖v j‖ ^ 2)
        = fun i => ‖u i‖ ^ 2 * (∑' j, ‖v j‖ ^ 2) := by
      funext i
      rw [tsum_mul_left]
    rw [h]
    exact (summable_norm_sq_of_memℓp u.2).mul_right (∑' j, ‖v j‖ ^ 2)

/-- A rank-one matrix with `ℓ²` vectors is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_hsRankOne {u v : ℓ²(ℕ, 𝕜)} :
    IsHilbertSchmidt (hsRankOne u v) := by
  refine summable_hsRankOne_sq (𝕜 := 𝕜) (u := u) (v := v) |>.congr (fun p => ?_)
  simp [hsRankOne, norm_mul, mul_pow]

/-- A rank-one Hilbert–Schmidt operator acts as the inner product with `v` times `u`. -/
theorem hsOperator_hsRankOne_apply {u v : ℓ²(ℕ, 𝕜)} (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    hsOperator (hsRankOne u v) isHilbertSchmidt_hsRankOne x i =
      u i * ⟪v, x⟫_𝕜 := by
  rw [hsOperator_apply]
  conv_rhs => rw [lp.inner_eq_tsum]
  rw [← tsum_mul_left]
  refine tsum_congr (fun j => ?_)
  show (u i * star (v j)) * x j = u i * ⟪v j, x j⟫_𝕜
  rw [mul_assoc, RCLike.inner_apply, starRingEnd_apply, mul_comm (star (v j)) (x j)]

/-- The squared Hilbert–Schmidt norm of a rank-one matrix is `‖u‖² * ‖v‖²`. -/
theorem hsNormSq_hsRankOne {u v : ℓ²(ℕ, 𝕜)} :
    hsNormSq (hsRankOne u v) isHilbertSchmidt_hsRankOne = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have hu : Summable fun i => ‖u i‖ ^ 2 := summable_norm_sq_of_memℓp u.2
  have hv : Summable fun i => ‖v i‖ ^ 2 := summable_norm_sq_of_memℓp v.2
  calc hsNormSq (hsRankOne u v) isHilbertSchmidt_hsRankOne
      = ∑' p : ℕ × ℕ, ‖u p.1‖ ^ 2 * ‖v p.2‖ ^ 2 := by
        unfold hsNormSq
        apply tsum_congr
        intro p
        simp [hsRankOne, norm_mul, mul_pow]
    _ = (∑' i, ‖u i‖ ^ 2) * (∑' j, ‖v j‖ ^ 2) :=
        (Summable.tsum_mul_tsum hu hv (summable_hsRankOne_sq (𝕜 := 𝕜) (u := u) (v := v))).symm
    _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by rw [← norm_sq_lp_eq_tsum u, ← norm_sq_lp_eq_tsum v]

private theorem ofReal_norm_sq_lp_eq_tsum (f : ℓ²(ℕ, ℝ)) :
    ENNReal.ofReal (‖f‖ ^ 2) = ∑' i, ENNReal.ofReal (‖f i‖ ^ 2) := by
  rw [norm_sq_lp_eq_tsum,
    ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) (summable_norm_sq_of_memℓp f.2)]

/-- In the standard `ℓ²` basis, the existing extended operator squared norm
equals the finite matrix squared norm. This bridge is specialized to real
scalars because the canonical operator norm API is real-only. -/
theorem canonical_hsNormSq_eq_ofReal_matrix (T : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ))
    (hT : IsHilbertSchmidt (hsMatrix T)) :
    MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm.hsNormSq T
      (fun j => lp.single 2 j (1 : ℝ)) = ENNReal.ofReal (hsNormSq (hsMatrix T) hT) := by
  unfold MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm.hsNormSq hsNormSq
  rw [ENNReal.ofReal_tsum_of_nonneg (fun p => sq_nonneg _) hT]
  have hprod : (∑' p : ℕ × ℕ, ENNReal.ofReal (‖hsMatrix T p.1 p.2‖ ^ 2)) =
      ∑' i, ∑' j, ENNReal.ofReal (‖hsMatrix T i j‖ ^ 2) := ENNReal.tsum_prod'
  rw [hprod, ENNReal.tsum_comm]
  exact tsum_congr (fun j => ofReal_norm_sq_lp_eq_tsum (T (lp.single 2 j (1 : ℝ))))

/-- The constructed real Hilbert–Schmidt operator has the canonical extended
squared norm given by the finite squared norm of its matrix. -/
theorem canonical_hsNormSq_hsOperator (a : ℕ → ℕ → ℝ) (ha : IsHilbertSchmidt a) :
    MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm.hsNormSq (hsOperator a ha)
      (fun j => lp.single 2 j (1 : ℝ)) = ENNReal.ofReal (hsNormSq a ha) := by
  simpa only [hsNormSq, hsMatrix_hsOperator] using
    canonical_hsNormSq_eq_ofReal_matrix (hsOperator a ha)
      (by rw [hsMatrix_hsOperator]; exact ha)

end MathlibExt.Analysis.InnerProductSpace.HilbertSchmidt
