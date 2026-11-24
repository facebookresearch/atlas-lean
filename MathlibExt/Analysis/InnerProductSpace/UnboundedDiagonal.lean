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
# Unbounded diagonal operators for a supplied Hilbert basis

Arbitrary scalar weights define a partial linear operator on precisely those
vectors whose weighted basis coefficients belong to `ℓ²`. Its value is the
inverse basis representation of that actual `ℓ²` vector. No bound on the
weights or nonempty-index hypothesis is imposed.
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

/-- The unrestricted weighted basis coordinates as a linear map into all scalar families. -/
def diagonalCoordinateLinearMap : H →ₗ[𝕜] (ι → 𝕜) :=
  LinearMap.pi fun i =>
    α i • ((lp.evalₗ (𝕜 := 𝕜) (fun _ : ι => 𝕜) 2 i).comp e.repr.toLinearMap)

/-- Every raw coordinate is the original scalar weight times the supplied basis coefficient. -/
@[simp]
theorem diagonalCoordinateLinearMap_apply (h : H) (i : ι) :
    diagonalCoordinateLinearMap e α h i = α i * e.repr h i := rfl

/-- The maximal domain on which the weighted basis coefficients are square summable. -/
def unboundedDiagonalDomain : Submodule 𝕜 H :=
  (lpSubmodule 𝕜 (fun _ : ι => 𝕜) 2).comap (diagonalCoordinateLinearMap e α)

/-- Membership in the domain is exactly square summability of the weighted coordinates. -/
theorem mem_unboundedDiagonalDomain_iff (h : H) :
    h ∈ unboundedDiagonalDomain e α ↔
      Summable fun i => ‖α i * ⟪e i, h⟫_𝕜‖ ^ 2 := by
  change Memℓp (fun i => α i * e.repr h i) (2 : ℝ≥0∞) ↔ _
  have htwo : 0 < (2 : ℝ≥0∞).toReal := by simp
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, HilbertBasis.repr_apply_apply] using
    (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (f := fun i => α i * e.repr h i) htwo)

/-- The actual square-summable weighted coordinate vector, as a linear map on the domain. -/
def unboundedDiagonalLp : unboundedDiagonalDomain e α →ₗ[𝕜] lp (fun _ : ι => 𝕜) 2 :=
  (diagonalCoordinateLinearMap e α).submoduleComap (lpSubmodule 𝕜 (fun _ : ι => 𝕜) 2)

/-- The coordinate vector retains the original weight and supplied basis coefficient. -/
@[simp]
theorem unboundedDiagonalLp_apply (x : unboundedDiagonalDomain e α) (i : ι) :
    unboundedDiagonalLp e α x i = α i * e.repr (x : H) i := rfl

/-- The diagonal partial linear map on its full square-summability domain. -/
def unboundedDiagonal : H →ₗ.[𝕜] H :=
  LinearPMap.mk (unboundedDiagonalDomain e α)
    (e.repr.symm.toLinearMap.comp (unboundedDiagonalLp e α))

/-- The partial map has precisely the maximal weighted-coordinate domain. -/
@[simp]
theorem unboundedDiagonal_domain :
    (unboundedDiagonal e α).domain = unboundedDiagonalDomain e α := rfl

/-- The value is the supplied basis reconstruction of the actual weighted coordinate vector. -/
@[simp]
theorem unboundedDiagonal_apply (x : unboundedDiagonalDomain e α) :
    unboundedDiagonal e α x = e.repr.symm (unboundedDiagonalLp e α x) := rfl

/-- Every basis coordinate is multiplied by its original scalar weight. -/
theorem unboundedDiagonal_repr_apply (x : unboundedDiagonalDomain e α) (i : ι) :
    e.repr (unboundedDiagonal e α x) i = α i * e.repr (x : H) i := by
  rw [unboundedDiagonal_apply, e.repr.apply_symm_apply]
  exact unboundedDiagonalLp_apply e α x i

/-- The defining Hilbert series converges to the actual partial-map value. -/
theorem unboundedDiagonal_hasSum (x : unboundedDiagonalDomain e α) :
    HasSum (fun i => (α i * ⟪e i, (x : H)⟫_𝕜) • e i) (unboundedDiagonal e α x) := by
  simpa only [unboundedDiagonal_apply, unboundedDiagonalLp_apply,
    HilbertBasis.repr_apply_apply] using e.hasSum_repr_symm (unboundedDiagonalLp e α x)

/-- The convergent defining series evaluates to the diagonal operator. -/
theorem unboundedDiagonal_eq_tsum (x : unboundedDiagonalDomain e α) :
    unboundedDiagonal e α x = ∑' i, (α i * ⟪e i, (x : H)⟫_𝕜) • e i :=
  (unboundedDiagonal_hasSum e α x).tsum_eq.symm

/-- Zero weights give the entire original space as the domain. -/
@[simp]
theorem unboundedDiagonalDomain_zero : unboundedDiagonalDomain e (0 : ι → 𝕜) = ⊤ := by
  ext h
  simp [mem_unboundedDiagonalDomain_iff]

/-- Zero weights give the zero vector at every point of the actual domain. -/
theorem unboundedDiagonal_zero_apply (x : unboundedDiagonalDomain e (0 : ι → 𝕜)) :
    unboundedDiagonal e (0 : ι → 𝕜) x = 0 := by
  apply e.repr.injective
  apply lp.ext
  funext i
  simp

end HilbertBasis

end
