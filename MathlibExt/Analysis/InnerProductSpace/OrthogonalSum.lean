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

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Orthogonal products and rectangular operator blocks

The carrier is exactly `WithLp 2 (H × K)`, with Mathlib's existing norm,
topology and inner product. The two inclusions are genuine linear isometries.
The four block extractors are continuous linear maps in their operator input,
so they can be composed with a representation's underlying linear map.

Coordinates and block operators need no component completeness. Automatic
adjoints and the block-diagonal star-algebra homomorphism use complete real or
complex inner-product spaces, as required by Mathlib's adjoint API. No new
carrier, norm, Hilbert-space dictionary or nontriviality assumption is added.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- For arbitrary types `H` and `K`, the orthogonal-sum type is the product `H × K` viewed through
the ℓ² type synonym; with normed factors it has the Euclidean product norm.

The orthogonal product, without a new carrier or norm. -/
abbrev OrthogonalSum (H : Type*) (K : Type*) := WithLp 2 (H × K)

namespace OrthogonalSum

universe u𝕜 uH uK uH₁ uK₁ uH₂ uK₂ uH₃ uK₃

section Coordinates

variable {𝕜 : Type u𝕜} [NormedField 𝕜]
variable (H : Type uH) (K : Type uK)
variable [NormedAddCommGroup H] [NormedSpace 𝕜 H]
variable [NormedAddCommGroup K] [NormedSpace 𝕜 K]

/-- Let `𝕜` be a normed field and let `H` and `K` be normed `𝕜`-vector spaces. Their two-factor sum
carries the Euclidean product norm.

The isometric inclusion into the first orthogonal summand. -/
def inl : H →ₗᵢ[𝕜] OrthogonalSum H K where
  toLinearMap :=
    (WithLp.linearEquiv 2 𝕜 (H × K)).symm.toLinearMap.comp
      (LinearMap.inl 𝕜 H K)
  norm_map' h := by
    change ‖WithLp.toLp 2 (h, (0 : K))‖ = ‖h‖
    exact WithLp.norm_toLp_fst 2 H K h

/-- Let `𝕜` be a normed field and let `H` and `K` be normed `𝕜`-vector spaces. Their two-factor sum
carries the Euclidean product norm.

The isometric inclusion into the second orthogonal summand. -/
def inr : K →ₗᵢ[𝕜] OrthogonalSum H K where
  toLinearMap :=
    (WithLp.linearEquiv 2 𝕜 (H × K)).symm.toLinearMap.comp
      (LinearMap.inr 𝕜 H K)
  norm_map' k := by
    change ‖WithLp.toLp 2 ((0 : H), k)‖ = ‖k‖
    exact WithLp.norm_toLp_snd 2 H K k

@[simp]
theorem inl_apply (h : H) :
    inl (𝕜 := 𝕜) H K h = WithLp.toLp 2 (h, (0 : K)) :=
  rfl

@[simp]
theorem inr_apply (k : K) :
    inr (𝕜 := 𝕜) H K k = WithLp.toLp 2 ((0 : H), k) :=
  rfl

@[simp]
theorem fst_inl (h : H) : (inl (𝕜 := 𝕜) H K h).fst = h :=
  rfl

@[simp]
theorem snd_inl (h : H) : (inl (𝕜 := 𝕜) H K h).snd = 0 :=
  rfl

@[simp]
theorem fst_inr (k : K) : (inr (𝕜 := 𝕜) H K k).fst = 0 :=
  rfl

@[simp]
theorem snd_inr (k : K) : (inr (𝕜 := 𝕜) H K k).snd = k :=
  rfl

/-- Let `𝕜` be a normed field and let `H` and `K` be normed `𝕜`-vector spaces. Their two-factor sum
carries the Euclidean product norm.

Every vector is the sum of its two orthogonal coordinates. -/
theorem inl_fst_add_inr_snd (x : OrthogonalSum H K) :
    inl (𝕜 := 𝕜) H K x.fst + inr (𝕜 := 𝕜) H K x.snd = x := by
  apply WithLp.ofLp_injective 2
  change ((WithLp.ofLp x).1 + 0, 0 + (WithLp.ofLp x).2) = WithLp.ofLp x
  simp only [add_zero, zero_add]

end Coordinates

section Blocks

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {H₁ : Type uH₁} {K₁ : Type uK₁} {H₂ : Type uH₂} {K₂ : Type uK₂}
variable [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
variable [NormedAddCommGroup K₁] [NormedSpace 𝕜 K₁]
variable [NormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]
variable [NormedAddCommGroup K₂] [NormedSpace 𝕜 K₂]

/-- Let `𝕜` be a nontrivially normed field and let `H₁`, `K₁`, `H₂` and `K₂` be normed `𝕜`-vector
spaces. The source and target two-factor sums carry the Euclidean product norms.

First-to-first operator block, continuously linear in the operator. -/
def block11 :
    (OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) →L[𝕜] H₁ →L[𝕜] H₂ :=
  ((ContinuousLinearMap.compL 𝕜 H₁ (OrthogonalSum H₁ K₁) H₂).flip
      (inl (𝕜 := 𝕜) H₁ K₁).toContinuousLinearMap).comp
    (ContinuousLinearMap.compL 𝕜 (OrthogonalSum H₁ K₁)
      (OrthogonalSum H₂ K₂) H₂ (WithLp.fstL 2 𝕜 H₂ K₂))

/-- Let `𝕜` be a nontrivially normed field and let `H₁`, `K₁`, `H₂` and `K₂` be normed `𝕜`-vector
spaces. The source and target two-factor sums carry the Euclidean product norms.

Second-to-first operator block, with its rectangular type. -/
def block12 :
    (OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) →L[𝕜] K₁ →L[𝕜] H₂ :=
  ((ContinuousLinearMap.compL 𝕜 K₁ (OrthogonalSum H₁ K₁) H₂).flip
      (inr (𝕜 := 𝕜) H₁ K₁).toContinuousLinearMap).comp
    (ContinuousLinearMap.compL 𝕜 (OrthogonalSum H₁ K₁)
      (OrthogonalSum H₂ K₂) H₂ (WithLp.fstL 2 𝕜 H₂ K₂))

/-- Let `𝕜` be a nontrivially normed field and let `H₁`, `K₁`, `H₂` and `K₂` be normed `𝕜`-vector
spaces. The source and target two-factor sums carry the Euclidean product norms.

First-to-second operator block, with its rectangular type. -/
def block21 :
    (OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) →L[𝕜] H₁ →L[𝕜] K₂ :=
  ((ContinuousLinearMap.compL 𝕜 H₁ (OrthogonalSum H₁ K₁) K₂).flip
      (inl (𝕜 := 𝕜) H₁ K₁).toContinuousLinearMap).comp
    (ContinuousLinearMap.compL 𝕜 (OrthogonalSum H₁ K₁)
      (OrthogonalSum H₂ K₂) K₂ (WithLp.sndL 2 𝕜 H₂ K₂))

/-- Let `𝕜` be a nontrivially normed field and let `H₁`, `K₁`, `H₂` and `K₂` be normed `𝕜`-vector
spaces. The source and target two-factor sums carry the Euclidean product norms.

Second-to-second operator block, continuously linear in the operator. -/
def block22 :
    (OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) →L[𝕜] K₁ →L[𝕜] K₂ :=
  ((ContinuousLinearMap.compL 𝕜 K₁ (OrthogonalSum H₁ K₁) K₂).flip
      (inr (𝕜 := 𝕜) H₁ K₁).toContinuousLinearMap).comp
    (ContinuousLinearMap.compL 𝕜 (OrthogonalSum H₁ K₁)
      (OrthogonalSum H₂ K₂) K₂ (WithLp.sndL 2 𝕜 H₂ K₂))

theorem block11_eq (T : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) :
    block11 T = (WithLp.fstL 2 𝕜 H₂ K₂).comp
      (T.comp (inl (𝕜 := 𝕜) H₁ K₁).toContinuousLinearMap) := by
  simp only [block11, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_assoc]

theorem block12_eq (T : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) :
    block12 T = (WithLp.fstL 2 𝕜 H₂ K₂).comp
      (T.comp (inr (𝕜 := 𝕜) H₁ K₁).toContinuousLinearMap) := by
  simp only [block12, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_assoc]

theorem block21_eq (T : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) :
    block21 T = (WithLp.sndL 2 𝕜 H₂ K₂).comp
      (T.comp (inl (𝕜 := 𝕜) H₁ K₁).toContinuousLinearMap) := by
  simp only [block21, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_assoc]

theorem block22_eq (T : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) :
    block22 T = (WithLp.sndL 2 𝕜 H₂ K₂).comp
      (T.comp (inr (𝕜 := 𝕜) H₁ K₁).toContinuousLinearMap) := by
  simp only [block22, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_assoc]

@[simp]
theorem block11_apply (T : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) (h : H₁) :
    block11 T h = (T (inl (𝕜 := 𝕜) H₁ K₁ h)).fst := by
  rw [block11_eq]
  rfl

@[simp]
theorem block12_apply (T : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) (k : K₁) :
    block12 T k = (T (inr (𝕜 := 𝕜) H₁ K₁ k)).fst := by
  rw [block12_eq]
  rfl

@[simp]
theorem block21_apply (T : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) (h : H₁) :
    block21 T h = (T (inl (𝕜 := 𝕜) H₁ K₁ h)).snd := by
  rw [block21_eq]
  rfl

@[simp]
theorem block22_apply (T : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) (k : K₁) :
    block22 T k = (T (inr (𝕜 := 𝕜) H₁ K₁ k)).snd := by
  rw [block22_eq]
  rfl

/-- Let `𝕜` be a nontrivially normed field and let `H₁`, `K₁`, `H₂` and `K₂` be normed `𝕜`-vector
spaces. The source and target two-factor sums carry the Euclidean product norms.

Reconstruction of the first coordinate uses the two blocks. -/
theorem fst_apply_eq (T : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂)
    (x : OrthogonalSum H₁ K₁) :
    (T x).fst = block11 T x.fst + block12 T x.snd := by
  have hx := inl_fst_add_inr_snd (𝕜 := 𝕜) H₁ K₁ x
  calc
    (T x).fst = (T (inl (𝕜 := 𝕜) H₁ K₁ x.fst +
        inr (𝕜 := 𝕜) H₁ K₁ x.snd)).fst := congrArg (fun y => (T y).fst) hx.symm
    _ = _ := by rw [map_add, WithLp.add_fst, block11_apply, block12_apply]

/-- Let `𝕜` be a nontrivially normed field and let `H₁`, `K₁`, `H₂` and `K₂` be normed `𝕜`-vector
spaces. The source and target two-factor sums carry the Euclidean product norms.

Reconstruction of the second coordinate uses the two blocks. -/
theorem snd_apply_eq (T : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂)
    (x : OrthogonalSum H₁ K₁) :
    (T x).snd = block21 T x.fst + block22 T x.snd := by
  have hx := inl_fst_add_inr_snd (𝕜 := 𝕜) H₁ K₁ x
  calc
    (T x).snd = (T (inl (𝕜 := 𝕜) H₁ K₁ x.fst +
        inr (𝕜 := 𝕜) H₁ K₁ x.snd)).snd := congrArg (fun y => (T y).snd) hx.symm
    _ = _ := by rw [map_add, WithLp.add_snd, block21_apply, block22_apply]

/-- Let `𝕜` be a nontrivially normed field and let `H₁`, `K₁`, `H₂` and `K₂` be normed `𝕜`-vector
spaces. The source and target two-factor sums carry the Euclidean product norms.

The diagonal action on the orthogonal products. -/
def blockDiagonal (S : H₁ →L[𝕜] H₂) (T : K₁ →L[𝕜] K₂) :
    OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂ :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 H₂ K₂).symm.toContinuousLinearMap.comp
    ((S.comp (WithLp.fstL 2 𝕜 H₁ K₁)).prod
      (T.comp (WithLp.sndL 2 𝕜 H₁ K₁)))

@[simp]
theorem blockDiagonal_apply (S : H₁ →L[𝕜] H₂) (T : K₁ →L[𝕜] K₂)
    (x : OrthogonalSum H₁ K₁) :
    blockDiagonal S T x = WithLp.toLp 2 (S x.fst, T x.snd) :=
  rfl

@[simp]
theorem block11_blockDiagonal (S : H₁ →L[𝕜] H₂) (T : K₁ →L[𝕜] K₂) :
    block11 (blockDiagonal S T) = S := by
  ext h
  rw [block11_apply, blockDiagonal_apply, inl_apply]
  rfl

@[simp]
theorem block12_blockDiagonal (S : H₁ →L[𝕜] H₂) (T : K₁ →L[𝕜] K₂) :
    block12 (blockDiagonal S T) = 0 := by
  ext k
  rw [block12_apply, blockDiagonal_apply, inr_apply]
  change S 0 = 0
  exact map_zero S

@[simp]
theorem block21_blockDiagonal (S : H₁ →L[𝕜] H₂) (T : K₁ →L[𝕜] K₂) :
    block21 (blockDiagonal S T) = 0 := by
  ext h
  rw [block21_apply, blockDiagonal_apply, inl_apply]
  change T 0 = 0
  exact map_zero T

@[simp]
theorem block22_blockDiagonal (S : H₁ →L[𝕜] H₂) (T : K₁ →L[𝕜] K₂) :
    block22 (blockDiagonal S T) = T := by
  ext k
  rw [block22_apply, blockDiagonal_apply, inr_apply]
  rfl

@[simp]
theorem blockDiagonal_zero :
    blockDiagonal (0 : H₁ →L[𝕜] H₂) (0 : K₁ →L[𝕜] K₂) = 0 := by
  ext x
  rw [blockDiagonal_apply]
  rfl

theorem blockDiagonal_add (S₁ S₂ : H₁ →L[𝕜] H₂) (T₁ T₂ : K₁ →L[𝕜] K₂) :
    blockDiagonal (S₁ + S₂) (T₁ + T₂) = blockDiagonal S₁ T₁ + blockDiagonal S₂ T₂ := by
  ext x
  apply WithLp.ofLp_injective 2
  rfl

theorem blockDiagonal_smul (c : 𝕜) (S : H₁ →L[𝕜] H₂) (T : K₁ →L[𝕜] K₂) :
    blockDiagonal (c • S) (c • T) = c • blockDiagonal S T := by
  ext x
  apply WithLp.ofLp_injective 2
  rfl

@[simp]
theorem blockDiagonal_one :
    blockDiagonal (1 : H₁ →L[𝕜] H₁) (1 : K₁ →L[𝕜] K₁) = 1 := by
  ext x
  rw [blockDiagonal_apply]
  change WithLp.toLp 2 (x.fst, x.snd) = x
  exact WithLp.toLp_ofLp 2 x

@[simp]
theorem block11_one :
    block11 (1 : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₁ K₁) = 1 := by
  rw [← blockDiagonal_one, block11_blockDiagonal]

@[simp]
theorem block12_one :
    block12 (1 : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₁ K₁) = 0 := by
  rw [← blockDiagonal_one, block12_blockDiagonal]

@[simp]
theorem block21_one :
    block21 (1 : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₁ K₁) = 0 := by
  rw [← blockDiagonal_one, block21_blockDiagonal]

@[simp]
theorem block22_one :
    block22 (1 : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₁ K₁) = 1 := by
  rw [← blockDiagonal_one, block22_blockDiagonal]

section Composition

variable {H₃ : Type uH₃} {K₃ : Type uK₃}
variable [NormedAddCommGroup H₃] [NormedSpace 𝕜 H₃]
variable [NormedAddCommGroup K₃] [NormedSpace 𝕜 K₃]

theorem blockDiagonal_comp (S₂ : H₂ →L[𝕜] H₃) (T₂ : K₂ →L[𝕜] K₃)
    (S₁ : H₁ →L[𝕜] H₂) (T₁ : K₁ →L[𝕜] K₂) :
    blockDiagonal (S₂.comp S₁) (T₂.comp T₁) =
      (blockDiagonal S₂ T₂).comp (blockDiagonal S₁ T₁) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, blockDiagonal_apply,
    WithLp.fst, WithLp.snd]

theorem block11_comp (T : OrthogonalSum H₂ K₂ →L[𝕜] OrthogonalSum H₃ K₃)
    (S : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) :
    block11 (T.comp S) = (block11 T).comp (block11 S) +
      (block12 T).comp (block21 S) := by
  ext h
  simpa only [block11_apply, block12_apply, block21_apply,
    ContinuousLinearMap.comp_apply, _root_.add_apply] using
      fst_apply_eq T (S (inl (𝕜 := 𝕜) H₁ K₁ h))

theorem block12_comp (T : OrthogonalSum H₂ K₂ →L[𝕜] OrthogonalSum H₃ K₃)
    (S : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) :
    block12 (T.comp S) = (block11 T).comp (block12 S) +
      (block12 T).comp (block22 S) := by
  ext k
  simpa only [block11_apply, block12_apply, block22_apply,
    ContinuousLinearMap.comp_apply, _root_.add_apply] using
      fst_apply_eq T (S (inr (𝕜 := 𝕜) H₁ K₁ k))

theorem block21_comp (T : OrthogonalSum H₂ K₂ →L[𝕜] OrthogonalSum H₃ K₃)
    (S : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) :
    block21 (T.comp S) = (block21 T).comp (block11 S) +
      (block22 T).comp (block21 S) := by
  ext h
  simpa only [block11_apply, block21_apply, block22_apply,
    ContinuousLinearMap.comp_apply, _root_.add_apply] using
      snd_apply_eq T (S (inl (𝕜 := 𝕜) H₁ K₁ h))

theorem block22_comp (T : OrthogonalSum H₂ K₂ →L[𝕜] OrthogonalSum H₃ K₃)
    (S : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) :
    block22 (T.comp S) = (block21 T).comp (block12 S) +
      (block22 T).comp (block22 S) := by
  ext k
  simpa only [block12_apply, block21_apply, block22_apply,
    ContinuousLinearMap.comp_apply, _root_.add_apply] using
      snd_apply_eq T (S (inr (𝕜 := 𝕜) H₁ K₁ k))

end Composition

end Blocks

section InnerCoordinates

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable (H : Type uH) (K : Type uK)
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

theorem inner_inl_left (h : H) (x : OrthogonalSum H K) :
    inner 𝕜 (inl (𝕜 := 𝕜) H K h) x = inner 𝕜 h x.fst := by
  simp only [inl_apply, WithLp.prod_inner_apply, WithLp.fst,
    inner_zero_left, add_zero]

theorem inner_inl_right (x : OrthogonalSum H K) (h : H) :
    inner 𝕜 x (inl (𝕜 := 𝕜) H K h) = inner 𝕜 x.fst h := by
  simp only [inl_apply, WithLp.prod_inner_apply, WithLp.fst,
    inner_zero_right, add_zero]

theorem inner_inr_left (k : K) (x : OrthogonalSum H K) :
    inner 𝕜 (inr (𝕜 := 𝕜) H K k) x = inner 𝕜 k x.snd := by
  simp only [inr_apply, WithLp.prod_inner_apply, WithLp.snd,
    inner_zero_left, zero_add]

theorem inner_inr_right (x : OrthogonalSum H K) (k : K) :
    inner 𝕜 x (inr (𝕜 := 𝕜) H K k) = inner 𝕜 x.snd k := by
  simp only [inr_apply, WithLp.prod_inner_apply, WithLp.snd,
    inner_zero_right, zero_add]

theorem inner_inl_inr (h : H) (k : K) :
    inner 𝕜 (inl (𝕜 := 𝕜) H K h) (inr (𝕜 := 𝕜) H K k) = 0 := by
  simp only [inner_inl_left, fst_inr, inner_zero_right]

variable [CompleteSpace H] [CompleteSpace K]

/-- Let `𝕜` be a nontrivially normed field and let `H₁`, `K₁`, `H₂` and `K₂` be normed `𝕜`-vector
spaces. The source and target two-factor sums carry the Euclidean product norms.

The adjoint of the first isometric inclusion is the first coordinate. -/
@[simp]
theorem adjoint_inl :
    ContinuousLinearMap.adjoint (inl (𝕜 := 𝕜) H K).toContinuousLinearMap =
      WithLp.fstL 2 𝕜 H K := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x h
  exact (inner_inl_right (𝕜 := 𝕜) H K x h).symm

/-- Let `𝕜` be a nontrivially normed field and let `H₁`, `K₁`, `H₂` and `K₂` be normed `𝕜`-vector
spaces. The source and target two-factor sums carry the Euclidean product norms.

The adjoint of the second isometric inclusion is the second coordinate. -/
@[simp]
theorem adjoint_inr :
    ContinuousLinearMap.adjoint (inr (𝕜 := 𝕜) H K).toContinuousLinearMap =
      WithLp.sndL 2 𝕜 H K := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x k
  exact (inner_inr_right (𝕜 := 𝕜) H K x k).symm

@[simp]
theorem adjoint_fstL :
    ContinuousLinearMap.adjoint (WithLp.fstL 2 𝕜 H K) =
      (inl (𝕜 := 𝕜) H K).toContinuousLinearMap := by
  rw [← adjoint_inl, ContinuousLinearMap.adjoint_adjoint]

@[simp]
theorem adjoint_sndL :
    ContinuousLinearMap.adjoint (WithLp.sndL 2 𝕜 H K) =
      (inr (𝕜 := 𝕜) H K).toContinuousLinearMap := by
  rw [← adjoint_inr, ContinuousLinearMap.adjoint_adjoint]

end InnerCoordinates

section BlockAdjoints

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {H₁ : Type uH₁} {K₁ : Type uK₁} {H₂ : Type uH₂} {K₂ : Type uK₂}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup K₁] [InnerProductSpace 𝕜 K₁] [CompleteSpace K₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
variable [NormedAddCommGroup K₂] [InnerProductSpace 𝕜 K₂] [CompleteSpace K₂]

@[simp]
theorem adjoint_block11 (T : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) :
    ContinuousLinearMap.adjoint (block11 T) =
      block11 (ContinuousLinearMap.adjoint T) := by
  simp only [block11_eq, ContinuousLinearMap.adjoint_comp,
    adjoint_inl, adjoint_fstL, ContinuousLinearMap.comp_assoc]

@[simp]
theorem adjoint_block12 (T : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) :
    ContinuousLinearMap.adjoint (block12 T) =
      block21 (ContinuousLinearMap.adjoint T) := by
  simp only [block12_eq, block21_eq, ContinuousLinearMap.adjoint_comp,
    adjoint_inr, adjoint_fstL, ContinuousLinearMap.comp_assoc]

@[simp]
theorem adjoint_block21 (T : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) :
    ContinuousLinearMap.adjoint (block21 T) =
      block12 (ContinuousLinearMap.adjoint T) := by
  simp only [block21_eq, block12_eq, ContinuousLinearMap.adjoint_comp,
    adjoint_inl, adjoint_sndL, ContinuousLinearMap.comp_assoc]

@[simp]
theorem adjoint_block22 (T : OrthogonalSum H₁ K₁ →L[𝕜] OrthogonalSum H₂ K₂) :
    ContinuousLinearMap.adjoint (block22 T) =
      block22 (ContinuousLinearMap.adjoint T) := by
  simp only [block22_eq, ContinuousLinearMap.adjoint_comp,
    adjoint_inr, adjoint_sndL, ContinuousLinearMap.comp_assoc]

theorem adjoint_blockDiagonal (S : H₁ →L[𝕜] H₂) (T : K₁ →L[𝕜] K₂) :
    ContinuousLinearMap.adjoint (blockDiagonal S T) =
      blockDiagonal (ContinuousLinearMap.adjoint S) (ContinuousLinearMap.adjoint T) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  simp only [blockDiagonal_apply, WithLp.prod_inner_apply, WithLp.fst, WithLp.snd,
    ContinuousLinearMap.adjoint_inner_left]

end BlockAdjoints

section DiagonalAlgebra

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {H : Type uH} {K : Type uK}
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- Let `𝕜` be a nontrivially normed field and let `H₁`, `K₁`, `H₂` and `K₂` be normed `𝕜`-vector
spaces. The source and target two-factor sums carry the Euclidean product norms.

The unital star-algebra map taking two operators to their orthogonal diagonal. -/
def blockDiagonalStarAlgHom :
    ((H →L[𝕜] H) × (K →L[𝕜] K)) →⋆ₐ[𝕜]
      (OrthogonalSum H K →L[𝕜] OrthogonalSum H K) where
  toFun p := blockDiagonal p.1 p.2
  map_zero' := blockDiagonal_zero
  map_one' := blockDiagonal_one
  map_add' p q := blockDiagonal_add p.1 q.1 p.2 q.2
  map_mul' p q := by
    change blockDiagonal (p.1.comp q.1) (p.2.comp q.2) =
      (blockDiagonal p.1 p.2).comp (blockDiagonal q.1 q.2)
    exact blockDiagonal_comp p.1 p.2 q.1 q.2
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change blockDiagonal (c • (1 : H →L[𝕜] H)) (c • (1 : K →L[𝕜] K)) =
      c • (1 : OrthogonalSum H K →L[𝕜] OrthogonalSum H K)
    rw [blockDiagonal_smul, blockDiagonal_one]
  map_star' p := by
    change blockDiagonal (star p.1) (star p.2) = star (blockDiagonal p.1 p.2)
    simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_blockDiagonal]

@[simp]
theorem blockDiagonalStarAlgHom_apply (S : H →L[𝕜] H) (T : K →L[𝕜] K) :
    blockDiagonalStarAlgHom (S, T) = blockDiagonal S T :=
  rfl

end DiagonalAlgebra

end OrthogonalSum
