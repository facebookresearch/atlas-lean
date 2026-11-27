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

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.LinearAlgebra.Pi

/-!
# Diagonal partial operators on maximal weighted-coefficient domains

For a real or complex Hilbert basis `e_i` and any scalar family `α_i`, the diagonal domain is
`D_α={x : Σ_i ‖α_i⟨e_i,x⟩‖²<∞}`. The partial linear operator is `D_α → H`, `x ↦ Σ_i α_i⟨e_i,x⟩
e_i`, with norm-convergent Hilbert series on this domain.

Its weighted coordinate vector is `α_i (e.repr x)_i`. No bound, reality or positivity of the
weights is assumed, and indices may be empty. Zero weights give domain all of `H` and the zero
operator.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal InnerProductSpace

namespace HilbertBasis

universe uI uK uH

variable {ι : Type uI} {𝕜 : Type uK} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable (e : HilbertBasis ι 𝕜 H) (α : ι → 𝕜)

/-- **Linear weighted coordinates of a Hilbert-basis vector.** Let `𝕜` be real or complex, `H`
a normed inner-product `𝕜`-space, `e : HilbertBasis ι 𝕜 H` and `α : ι → 𝕜` any scalar
family. Write `D_α={x ∈ H : Σ_i ‖α_i⟨e_i,x⟩‖² < ∞}`. `diagonalCoordinateLinearMap e α : H
→ₗ[𝕜] (ι → 𝕜)` has coordinate `α_i (e.repr x)_i`, without a summability restriction on its
output. -/
def diagonalCoordinateLinearMap : H →ₗ[𝕜] (ι → 𝕜) :=
  LinearMap.pi fun i =>
    α i • ((lp.evalₗ (𝕜 := 𝕜) (fun _ : ι => 𝕜) 2 i).comp e.repr.toLinearMap)

/-- **Value of a weighted basis coordinate.** Let `𝕜` be real or complex, `H` a normed
inner-product `𝕜`-space, `e : HilbertBasis ι 𝕜 H` and `α : ι → 𝕜` any scalar family. Write
`D_α={x ∈ H : Σ_i ‖α_i⟨e_i,x⟩‖² < ∞}`. for `x ∈ H` and `i ∈ ι`,
`diagonalCoordinateLinearMap e α x i=α_i (e.repr x)_i`. -/
@[simp]
theorem diagonalCoordinateLinearMap_apply (h : H) (i : ι) :
    diagonalCoordinateLinearMap e α h i = α i * e.repr h i := rfl

/-- **Maximal square-summability domain of a diagonal operator.** Let `𝕜` be real or complex,
`H` a normed inner-product `𝕜`-space, `e : HilbertBasis ι 𝕜 H` and `α : ι → 𝕜` any scalar
family. Write `D_α={x ∈ H : Σ_i ‖α_i⟨e_i,x⟩‖² < ∞}`. `unboundedDiagonalDomain e α` is the
complex- or real-linear submodule `D_α` of vectors whose weighted coordinates belong to
`ℓ²(ι,𝕜)`. -/
def unboundedDiagonalDomain : Submodule 𝕜 H :=
  (lpSubmodule 𝕜 (fun _ : ι => 𝕜) 2).comap (diagonalCoordinateLinearMap e α)

/-- **Domain membership by summability of weighted coefficients.** Let `𝕜` be real or complex,
`H` a normed inner-product `𝕜`-space, `e : HilbertBasis ι 𝕜 H` and `α : ι → 𝕜` any scalar
family. Write `D_α={x ∈ H : Σ_i ‖α_i⟨e_i,x⟩‖² < ∞}`. for `x ∈ H`, `x∈D_α` exactly when the
nonnegative series `Σ_i ‖α_i⟨e_i,x⟩‖²` is summable. -/
theorem mem_unboundedDiagonalDomain_iff (h : H) :
    h ∈ unboundedDiagonalDomain e α ↔
      Summable fun i => ‖α i * ⟪e i, h⟫_𝕜‖ ^ 2 := by
  change Memℓp (fun i => α i * e.repr h i) (2 : ℝ≥0∞) ↔ _
  have htwo : 0 < (2 : ℝ≥0∞).toReal := by simp
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, HilbertBasis.repr_apply_apply] using
    (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (f := fun i => α i * e.repr h i) htwo)

/-- **Square-summable weighted-coordinate map on the diagonal domain.** Let `𝕜` be real or
complex, `H` a normed inner-product `𝕜`-space, `e : HilbertBasis ι 𝕜 H` and `α : ι → 𝕜`
any scalar family. Write `D_α={x ∈ H : Σ_i ‖α_i⟨e_i,x⟩‖² < ∞}`. `unboundedDiagonalLp e α :
D_α →ₗ[𝕜] ℓ²(ι,𝕜)` sends `x` to `(α_i (e.repr x)_i)_i`. -/
def unboundedDiagonalLp : unboundedDiagonalDomain e α →ₗ[𝕜] lp (fun _ : ι => 𝕜) 2 :=
  (diagonalCoordinateLinearMap e α).submoduleComap (lpSubmodule 𝕜 (fun _ : ι => 𝕜) 2)

/-- **Coordinate of the diagonal domain's weighted vector.** Let `𝕜` be real or complex, `H` a
normed inner-product `𝕜`-space, `e : HilbertBasis ι 𝕜 H` and `α : ι → 𝕜` any scalar
family. Write `D_α={x ∈ H : Σ_i ‖α_i⟨e_i,x⟩‖² < ∞}`. for `x ∈ D_α` and `i ∈ ι`,
`(unboundedDiagonalLp e α x)_i=α_i (e.repr x)_i`. -/
@[simp]
theorem unboundedDiagonalLp_apply (x : unboundedDiagonalDomain e α) (i : ι) :
    unboundedDiagonalLp e α x i = α i * e.repr (x : H) i := rfl

/-- **Diagonal partial linear operator on the full weighted domain.** Let `𝕜` be real or
complex, `H` a normed inner-product `𝕜`-space, `e : HilbertBasis ι 𝕜 H` and `α : ι → 𝕜`
any scalar family. Write `D_α={x ∈ H : Σ_i ‖α_i⟨e_i,x⟩‖² < ∞}`. `unboundedDiagonal e α : H
→ₗ.[𝕜] H` has domain `D_α` and value `e.repr⁻¹((α_i (e.repr x)_i)_i)`. -/
def unboundedDiagonal : H →ₗ.[𝕜] H :=
  LinearPMap.mk (unboundedDiagonalDomain e α)
    (e.repr.symm.toLinearMap.comp (unboundedDiagonalLp e α))

/-- **Domain of the diagonal partial map.** Let `𝕜` be real or complex, `H` a normed
inner-product `𝕜`-space, `e : HilbertBasis ι 𝕜 H` and `α : ι → 𝕜` any scalar family. Write
`D_α={x ∈ H : Σ_i ‖α_i⟨e_i,x⟩‖² < ∞}`. the domain of `unboundedDiagonal e α` is exactly
`unboundedDiagonalDomain e α=D_α`. -/
@[simp]
theorem unboundedDiagonal_domain :
    (unboundedDiagonal e α).domain = unboundedDiagonalDomain e α := rfl

/-- **Basis reconstruction of a diagonal partial-map value.** Let `𝕜` be real or complex, `H`
a normed inner-product `𝕜`-space, `e : HilbertBasis ι 𝕜 H` and `α : ι → 𝕜` any scalar
family. Write `D_α={x ∈ H : Σ_i ‖α_i⟨e_i,x⟩‖² < ∞}`. for `x ∈ D_α`, `unboundedDiagonal e α
x=e.repr.symm(unboundedDiagonalLp e α x)`. -/
@[simp]
theorem unboundedDiagonal_apply (x : unboundedDiagonalDomain e α) :
    unboundedDiagonal e α x = e.repr.symm (unboundedDiagonalLp e α x) := rfl

/-- **Weighted basis coefficient of the diagonal output.** Let `𝕜` be real or complex, `H` a
normed inner-product `𝕜`-space, `e : HilbertBasis ι 𝕜 H` and `α : ι → 𝕜` any scalar
family. Write `D_α={x ∈ H : Σ_i ‖α_i⟨e_i,x⟩‖² < ∞}`. for `x ∈ D_α` and `i ∈ ι`,
`(e.repr(unboundedDiagonal e α x))_i=α_i (e.repr x)_i`. -/
theorem unboundedDiagonal_repr_apply (x : unboundedDiagonalDomain e α) (i : ι) :
    e.repr (unboundedDiagonal e α x) i = α i * e.repr (x : H) i := by
  rw [unboundedDiagonal_apply, e.repr.apply_symm_apply]
  exact unboundedDiagonalLp_apply e α x i

/-- **Norm-convergent Hilbert series of the diagonal operator.** Let `𝕜` be real or complex,
`H` a normed inner-product `𝕜`-space, `e : HilbertBasis ι 𝕜 H` and `α : ι → 𝕜` any scalar
family. Write `D_α={x ∈ H : Σ_i ‖α_i⟨e_i,x⟩‖² < ∞}`. for `x ∈ D_α`, the vector series `Σ_i
(α_i⟨e_i,x⟩) • e_i` has sum `unboundedDiagonal e α x` in the norm of `H`. -/
theorem unboundedDiagonal_hasSum (x : unboundedDiagonalDomain e α) :
    HasSum (fun i => (α i * ⟪e i, (x : H)⟫_𝕜) • e i) (unboundedDiagonal e α x) := by
  simpa only [unboundedDiagonal_apply, unboundedDiagonalLp_apply,
    HilbertBasis.repr_apply_apply] using e.hasSum_repr_symm (unboundedDiagonalLp e α x)

/-- **Series formula for a diagonal partial operator.** Let `𝕜` be real or complex, `H` a
normed inner-product `𝕜`-space, `e : HilbertBasis ι 𝕜 H` and `α : ι → 𝕜` any scalar
family. Write `D_α={x ∈ H : Σ_i ‖α_i⟨e_i,x⟩‖² < ∞}`. for `x ∈ D_α`, `unboundedDiagonal e α
x=Σ' i, (α_i⟨e_i,x⟩) • e_i`. -/
theorem unboundedDiagonal_eq_tsum (x : unboundedDiagonalDomain e α) :
    unboundedDiagonal e α x = ∑' i, (α i * ⟪e i, (x : H)⟫_𝕜) • e i :=
  (unboundedDiagonal_hasSum e α x).tsum_eq.symm

/-- **Zero diagonal weights give the whole domain.** Let `𝕜` be real or complex, `H` a normed
inner-product `𝕜`-space, `e : HilbertBasis ι 𝕜 H` and `α : ι → 𝕜` any scalar family. Write
`D_α={x ∈ H : Σ_i ‖α_i⟨e_i,x⟩‖² < ∞}`. when every weight is zero, `unboundedDiagonalDomain
e 0=H`. -/
@[simp]
theorem unboundedDiagonalDomain_zero : unboundedDiagonalDomain e (0 : ι → 𝕜) = ⊤ := by
  ext h
  simp [mem_unboundedDiagonalDomain_iff]

/-- **Zero diagonal weights give zero output.** Let `𝕜` be real or complex, `H` a normed
inner-product `𝕜`-space, `e : HilbertBasis ι 𝕜 H` and `α : ι → 𝕜` any scalar family. Write
`D_α={x ∈ H : Σ_i ‖α_i⟨e_i,x⟩‖² < ∞}`. for zero weights and every vector in the resulting
whole-space domain, `unboundedDiagonal e 0 x=0`. -/
theorem unboundedDiagonal_zero_apply (x : unboundedDiagonalDomain e (0 : ι → 𝕜)) :
    unboundedDiagonal e (0 : ι → 𝕜) x = 0 := by
  apply e.repr.injective
  apply lp.ext
  funext i
  simp

end HilbertBasis

end
