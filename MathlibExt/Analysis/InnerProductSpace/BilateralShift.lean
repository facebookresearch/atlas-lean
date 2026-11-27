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

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Right bilateral shift on vector-valued square-summable sequences

For a real or complex normed inner-product space `G`, the shift on `ℓ²(ℤ,G)` is `Sx(n)=x(n-1)`.
It is a linear isometry, moving a singleton at `n` to the singleton at `n+1`. Reindexing by any
equivalence of `ℤ` also preserves the square-summable norm.

When `G` is complete, the adjoint is the left shift `S*x(n)=x(n+1)`. Both `S*S=I` and `SS*=I`,
so `S` is unitary. The norm and coordinate assertions do not require completeness of `G`, and
the zero space is permitted.
-/

@[expose] public section

noncomputable section

namespace lp

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {G : Type v} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [hG : CompleteSpace G]

/-! ## Reindexing of square-summable sequences -/

/-- **Reindexed square-summable sequence.** Let `G` be a normed additive commutative group, `e
: ℤ ≃ ℤ` and `x ∈ lp (fun _ : ℤ => G) 2`. The function `bilateralReindexSeq e x` has value
`x(e(n))` at `n : ℤ`; no scalar field or completeness is required for these coordinates. -/
def bilateralReindexSeq (e : ℤ ≃ ℤ)
    (x : lp (fun _ : ℤ ↦ G) 2) : ℤ → G :=
  fun n ↦ x (e n)

omit hG in
theorem bilateralReindexSeq_mem (e : ℤ ≃ ℤ)
    (x : lp (fun _ : ℤ ↦ G) 2) :
    Memℓp (bilateralReindexSeq e x) 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hx : Summable (fun n : ℤ ↦ ‖x n‖ ^ (2 : ENNReal).toReal) :=
    (memℓp_gen_iff hp).mp (lp.memℓp x)
  have hreindex :
      Summable (fun n : ℤ ↦ ‖x (e n)‖ ^ (2 : ENNReal).toReal) :=
    e.summable_iff.mpr hx
  exact memℓp_gen hreindex

omit hG in
/-- **Norm preserved by integer-coordinate reindexing.** Let `G` be a normed additive
commutative group and `e : ℤ ≃ ℤ`. For every `x ∈ ℓ²(ℤ,G)`, the reindexed square-summable
sequence `n ↦ x(e(n))` has norm `‖x‖₂`. -/
theorem bilateralReindexSeq_norm (e : ℤ ≃ ℤ)
    (x : lp (fun _ : ℤ ↦ G) 2) :
    ‖(⟨bilateralReindexSeq e x, bilateralReindexSeq_mem e x⟩ :
        lp (fun _ : ℤ ↦ G) 2)‖ = ‖x‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hsum :
      (∑' n : ℤ, ‖bilateralReindexSeq e x n‖ ^ (2 : ENNReal).toReal) =
        ∑' n : ℤ, ‖x n‖ ^ (2 : ENNReal).toReal := by
    change (∑' n : ℤ, ‖x (e n)‖ ^ (2 : ENNReal).toReal) = _
    exact e.tsum_eq (fun n : ℤ ↦ ‖x n‖ ^ (2 : ENNReal).toReal)
  have hnormReindex :
      ‖(⟨bilateralReindexSeq e x, bilateralReindexSeq_mem e x⟩ :
          lp (fun _ : ℤ ↦ G) 2)‖ =
        ((∑' n : ℤ,
            ‖bilateralReindexSeq e x n‖ ^ (2 : ENNReal).toReal) ^
          ((1 : ℝ) / (2 : ENNReal).toReal)) := by
    rw [lp.norm_eq_tsum_rpow hp]
  have hnormInput :
      ‖x‖ = ((∑' n : ℤ, ‖x n‖ ^ (2 : ENNReal).toReal) ^
        ((1 : ℝ) / (2 : ENNReal).toReal)) := by
    rw [lp.norm_eq_tsum_rpow hp]
  rw [hnormReindex, hnormInput, hsum]

/-- **Linear integer-coordinate reindexing.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. Write `L=lp (fun _ : ℤ => G) 2` and `Sx(n)=x(n-1)` for the right
bilateral shift. for `e : ℤ ≃ ℤ`, `bilateralReindexLinear e : L →ₗ[𝕜] L` acts by `x(n) ↦
x(e(n))`. -/
def bilateralReindexLinear (e : ℤ ≃ ℤ) :
    lp (fun _ : ℤ ↦ G) 2 →ₗ[𝕜] lp (fun _ : ℤ ↦ G) 2 where
  toFun x := ⟨bilateralReindexSeq e x, bilateralReindexSeq_mem e x⟩
  map_add' x y := by
    apply lp.ext
    funext n
    simp only [bilateralReindexSeq, lp.coeFn_add, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext n
    simp only [bilateralReindexSeq, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]

omit hG in
theorem bilateralReindexLinear_norm (e : ℤ ≃ ℤ)
    (x : lp (fun _ : ℤ ↦ G) 2) :
    ‖bilateralReindexLinear (𝕜 := 𝕜) e x‖ = ‖x‖ :=
  bilateralReindexSeq_norm e x

/-! ## Forward and inverse translations -/

/-- **Linear right bilateral translation.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. Write `L=lp (fun _ : ℤ => G) 2` and `Sx(n)=x(n-1)` for the right
bilateral shift. `bilateralShiftLinear : L →ₗ[𝕜] L` is `S`, with `(Sx)(n)=x(n-1)`. -/
def bilateralShiftLinear :
    lp (fun _ : ℤ ↦ G) 2 →ₗ[𝕜] lp (fun _ : ℤ ↦ G) 2 :=
  bilateralReindexLinear (Equiv.subRight (1 : ℤ))

/-- **Linear left bilateral translation.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. Write `L=lp (fun _ : ℤ => G) 2` and `Sx(n)=x(n-1)` for the right
bilateral shift. `bilateralShiftInverseLinear : L →ₗ[𝕜] L` is the inverse shift, with
value `x(n+1)` at `n`. -/
def bilateralShiftInverseLinear :
    lp (fun _ : ℤ ↦ G) 2 →ₗ[𝕜] lp (fun _ : ℤ ↦ G) 2 :=
  bilateralReindexLinear (Equiv.addRight (1 : ℤ))

omit hG in
@[simp]
private theorem bilateralShiftLinear_apply
    (x : lp (fun _ : ℤ ↦ G) 2) (n : ℤ) :
    bilateralShiftLinear (𝕜 := 𝕜) x n = x (n - 1) :=
  rfl

omit hG in
@[simp]
private theorem bilateralShiftInverseLinear_apply
    (x : lp (fun _ : ℤ ↦ G) 2) (n : ℤ) :
    bilateralShiftInverseLinear (𝕜 := 𝕜) x n = x (n + 1) :=
  rfl

omit hG in
theorem bilateralShiftLinear_norm
    (x : lp (fun _ : ℤ ↦ G) 2) :
    ‖bilateralShiftLinear (𝕜 := 𝕜) x‖ = ‖x‖ :=
  bilateralReindexLinear_norm (Equiv.subRight (1 : ℤ)) x

omit hG in
private theorem bilateralShiftLinear_comp_inverse :
    (bilateralShiftLinear (𝕜 := 𝕜) (G := G)).comp
        bilateralShiftInverseLinear = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply lp.ext
  funext n
  change x ((n - 1) + 1) = x n
  rw [sub_add_cancel]

omit hG in
private theorem bilateralShiftInverse_comp_linear :
    (bilateralShiftInverseLinear (𝕜 := 𝕜) (G := G)).comp
        bilateralShiftLinear = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply lp.ext
  funext n
  change x ((n + 1) - 1) = x n
  rw [add_sub_cancel_right]

private def bilateralShiftLinearIsometry :
    lp (fun _ : ℤ ↦ G) 2 →ₗᵢ[𝕜] lp (fun _ : ℤ ↦ G) 2 where
  toLinearMap := bilateralShiftLinear
  norm_map' := bilateralShiftLinear_norm

/-- **Isometric equivalence of the right bilateral shift.** Let `𝕜` be real or complex and `G`
a normed inner-product `𝕜`-space. Write `L=lp (fun _ : ℤ => G) 2` and `Sx(n)=x(n-1)` for
the right bilateral shift. the linear isometric equivalence `bilateralShiftEquiv : L
≃ₗᵢ[𝕜] L` has forward value `x(n-1)` and inverse value `x(n+1)`. -/
private noncomputable def bilateralShiftEquiv :
    lp (fun _ : ℤ ↦ G) 2 ≃ₗᵢ[𝕜] lp (fun _ : ℤ ↦ G) 2 :=
  LinearIsometryEquiv.ofLinearIsometry
    bilateralShiftLinearIsometry bilateralShiftInverseLinear
    bilateralShiftLinear_comp_inverse bilateralShiftInverse_comp_linear

/-! ## Bilateral shift and its adjoint -/

/-- **Bounded right bilateral shift.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. Write `L=lp (fun _ : ℤ => G) 2` and `Sx(n)=x(n-1)` for the right
bilateral shift. `bilateralShift : L →L[𝕜] L` is the bounded complex- or real-linear
operator `S`, preserving the ℓ² norm. Completeness is not needed for this bounded
operator. -/
noncomputable def bilateralShift :
    lp (fun _ : ℤ ↦ G) 2 →L[𝕜] lp (fun _ : ℤ ↦ G) 2 :=
  bilateralShiftLinear.mkContinuous 1 fun x ↦ by
    rw [bilateralShiftLinear_norm, one_mul]

omit hG in
/-- **Coordinates of the right bilateral shift.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. Write `L=lp (fun _ : ℤ => G) 2` and `Sx(n)=x(n-1)` for the right
bilateral shift. for `x ∈ L` and `n : ℤ`, `bilateralShift x n=x(n-1)`. -/
@[simp]
theorem bilateralShift_apply
    (x : lp (fun _ : ℤ ↦ G) 2) (n : ℤ) :
    bilateralShift (𝕜 := 𝕜) x n = x (n - 1) := by
  change bilateralShiftLinear (𝕜 := 𝕜) x n = x (n - 1)
  rfl

omit hG in
/-- **Right shift of an integer singleton.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. Write `L=lp (fun _ : ℤ => G) 2` and `Sx(n)=x(n-1)` for the right
bilateral shift. for `n : ℤ`, `g ∈ G`, `S(single_n g)=single_(n+1) g`. -/
@[simp]
theorem bilateralShift_single (n : ℤ) (g : G) :
    bilateralShift (𝕜 := 𝕜)
        (lp.single (E := fun _ : ℤ ↦ G) 2 n g) =
      lp.single (E := fun _ : ℤ ↦ G) 2 (n + 1) g := by
  apply lp.ext
  funext j
  rw [bilateralShift_apply]
  by_cases h : j - 1 = n
  · have hj : j = n + 1 := by linarith
    rw [h, hj]
    rw [lp.single_apply_self]
    rw [lp.single_apply_self]
  · have hj : j ≠ n + 1 := by
      intro hj
      apply h
      linarith
    rw [lp.single_apply_ne (E := fun _ : ℤ ↦ G) 2 n g h]
    rw [lp.single_apply_ne (E := fun _ : ℤ ↦ G) 2 (n + 1) g hj]

omit hG in
/-- **Square-summable norm preserved by the bilateral shift.** Let `𝕜` be real or complex and
`G` a normed inner-product `𝕜`-space. Write `L=lp (fun _ : ℤ => G) 2` and `Sx(n)=x(n-1)`
for the right bilateral shift. for every `x ∈ L`, `‖Sx‖₂=‖x‖₂`, including the zero-space
case. -/
theorem bilateralShift_norm (x : lp (fun _ : ℤ ↦ G) 2) :
    ‖bilateralShift (𝕜 := 𝕜) x‖ = ‖x‖ := by
  change ‖bilateralShiftLinear (𝕜 := 𝕜) x‖ = ‖x‖
  exact bilateralShiftLinear_norm x

omit hG in
/-- **Metric isometry of the right bilateral shift.** Let `𝕜` be real or complex and `G` a
normed inner-product `𝕜`-space. Write `L=lp (fun _ : ℤ => G) 2` and `Sx(n)=x(n-1)` for the
right bilateral shift. `S : L → L` is an isometry for the ℓ² norm-induced metric. -/
theorem bilateralShift_isometry :
    Isometry (bilateralShift (𝕜 := 𝕜) (G := G)) :=
  (AddMonoidHomClass.isometry_iff_norm _).mpr bilateralShift_norm

private theorem adjoint_bilateralShift_eq_inverse :
    ContinuousLinearMap.adjoint (bilateralShift (𝕜 := 𝕜) (G := G)) =
      ((bilateralShiftEquiv (𝕜 := 𝕜) (G := G)).symm :
        lp (fun _ : ℤ ↦ G) 2 →L[𝕜] lp (fun _ : ℤ ↦ G) 2) := by
  have hshift : bilateralShift (𝕜 := 𝕜) (G := G) =
      (bilateralShiftEquiv (𝕜 := 𝕜) (G := G) :
        lp (fun _ : ℤ ↦ G) 2 →L[𝕜] lp (fun _ : ℤ ↦ G) 2) := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  rw [hshift]
  exact (bilateralShiftEquiv (𝕜 := 𝕜) (G := G)).adjoint_eq_symm

/-- **Coordinate action of the bilateral-shift adjoint.** Let `𝕜` be real or complex and `G` a
normed inner-product `𝕜`-space. Write `L=lp (fun _ : ℤ => G) 2` and `Sx(n)=x(n-1)` for the
right bilateral shift. Assume `G` is complete, so the Hilbert adjoint on `L` is defined.
for `x ∈ L` and `n : ℤ`, `(S*x)(n)=x(n+1)`. -/
@[simp]
theorem adjoint_bilateralShift_apply
    (x : lp (fun _ : ℤ ↦ G) 2) (n : ℤ) :
    star (bilateralShift (𝕜 := 𝕜) (G := G)) x n = x (n + 1) := by
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_bilateralShift_eq_inverse]
  change bilateralShiftInverseLinear (𝕜 := 𝕜) x n = x (n + 1)
  rfl

/-- **Left singleton shift under the bilateral adjoint.** Let `𝕜` be real or complex and `G` a
normed inner-product `𝕜`-space. Write `L=lp (fun _ : ℤ => G) 2` and `Sx(n)=x(n-1)` for the
right bilateral shift. Assume `G` is complete, so the Hilbert adjoint on `L` is defined.
for `n : ℤ`, `g ∈ G`, `S*(single_n g)=single_(n-1) g`. -/
@[simp]
theorem adjoint_bilateralShift_single (n : ℤ) (g : G) :
    star (bilateralShift (𝕜 := 𝕜) (G := G))
        (lp.single (E := fun _ : ℤ ↦ G) 2 n g) =
      lp.single (E := fun _ : ℤ ↦ G) 2 (n - 1) g := by
  apply lp.ext
  funext j
  rw [adjoint_bilateralShift_apply]
  by_cases h : j + 1 = n
  · have hj : j = n - 1 := by linarith
    rw [h, hj]
    rw [lp.single_apply_self]
    rw [lp.single_apply_self]
  · have hj : j ≠ n - 1 := by
      intro hj
      apply h
      linarith
    rw [lp.single_apply_ne (E := fun _ : ℤ ↦ G) 2 n g h]
    rw [lp.single_apply_ne (E := fun _ : ℤ ↦ G) 2 (n - 1) g hj]

/-- **Bilateral-shift adjoint is a left inverse.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. Write `L=lp (fun _ : ℤ => G) 2` and `Sx(n)=x(n-1)` for the right
bilateral shift. Assume `G` is complete, so the Hilbert adjoint on `L` is defined.
`S*∘S=I_L`. -/
@[simp]
theorem adjoint_bilateralShift_comp_bilateralShift :
    star (bilateralShift (𝕜 := 𝕜) (G := G)) ∘L
        bilateralShift (𝕜 := 𝕜) (G := G) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  change (star (bilateralShift (𝕜 := 𝕜) (G := G))
      (bilateralShift (𝕜 := 𝕜) x)) n = x n
  rw [adjoint_bilateralShift_apply, bilateralShift_apply]
  rw [add_sub_cancel_right]

/-- **Bilateral-shift adjoint is a right inverse.** Let `𝕜` be real or complex and `G` a
normed inner-product `𝕜`-space. Write `L=lp (fun _ : ℤ => G) 2` and `Sx(n)=x(n-1)` for the
right bilateral shift. Assume `G` is complete, so the Hilbert adjoint on `L` is defined.
`S∘S*=I_L`. -/
@[simp]
theorem bilateralShift_comp_adjoint_bilateralShift :
    bilateralShift (𝕜 := 𝕜) (G := G) ∘L
        star (bilateralShift (𝕜 := 𝕜) (G := G)) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  change (bilateralShift (𝕜 := 𝕜)
      (star (bilateralShift (𝕜 := 𝕜) (G := G)) x)) n = x n
  rw [bilateralShift_apply, adjoint_bilateralShift_apply]
  rw [sub_add_cancel]

/-- **Unitarity of the vector-valued bilateral shift.** Let `𝕜` be real or complex and `G` a
normed inner-product `𝕜`-space. Write `L=lp (fun _ : ℤ => G) 2` and `Sx(n)=x(n-1)` for the
right bilateral shift. Assume `G` is complete, so the Hilbert adjoint on `L` is defined.
the bounded operator `S` lies in the unitary group of `B(L)`, with `S*S=SS*=I_L`. -/
theorem bilateralShift_mem_unitary :
    bilateralShift (𝕜 := 𝕜) (G := G) ∈
      unitary (lp (fun _ : ℤ ↦ G) 2 →L[𝕜]
        lp (fun _ : ℤ ↦ G) 2) := by
  rw [Unitary.mem_iff]
  constructor
  · rw [ContinuousLinearMap.mul_def]
    exact adjoint_bilateralShift_comp_bilateralShift
  · rw [ContinuousLinearMap.mul_def]
    exact bilateralShift_comp_adjoint_bilateralShift

end lp
