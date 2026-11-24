/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.ExteriorPower.ContractionWedge
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Exactness of exterior multiplication by a nonzero vector

Dual separation earns a normalized contraction internally over any field.
Cartan's identity then proves the entire positive-degree kernel of left
wedge is its previous-degree image. The zero-degree map is injective.
No finite dimension, chosen basis, splitting or source residue certificate
is assumed.
-/

public section
noncomputable section
namespace exteriorPower

universe u v
variable {K : Type u} [Field K] {M : Type v} [AddCommGroup M] [Module K M]

private theorem wedge_twice_zero (w : M) (n : ℕ) (x : ⋀[K]^n M) :
    wedgeLeft K M w (n + 1) (wedgeLeft K M w n x) = 0 := by
  apply Subtype.ext
  change (wedgeLeft K M w (n + 1) (wedgeLeft K M w n x) : ExteriorAlgebra K M) = 0
  rw [wedgeLeft_apply_coe, wedgeLeft_apply_coe, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- A normalized actual contraction recovers every vector killed by the next wedge map. -/
theorem wedge_kernel_eq_wedge_contraction (w : M) (φ : Module.Dual K M) (hφ : φ w = 1)
    (n : ℕ) (x : ⋀[K]^(n + 1) M) (hx : wedgeLeft K M w (n + 1) x = 0) :
    wedgeLeft K M w n (contractLeft K M φ n x) = x := by
  have h := LinearMap.congr_fun
    (contractLeft_comp_wedgeLeft_add_wedgeLeft_comp_contractLeft K M φ w n) x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, hx, map_zero, zero_add,
    LinearMap.smul_apply, LinearMap.id_apply, hφ, one_smul] using h

/-- The entire positive-degree kernel of actual left wedge is exactly the preceding wedge image. -/
theorem ker_wedgeLeft_eq_range_of_ne_zero (w : M) (hw : w ≠ 0) (n : ℕ) :
    LinearMap.ker (wedgeLeft K M w (n + 1)) = LinearMap.range (wedgeLeft K M w n) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hw
  apply le_antisymm
  · intro x hx
    exact ⟨contractLeft K M φ n x, wedge_kernel_eq_wedge_contraction w φ hφ n x hx⟩
  · rintro x ⟨y, rfl⟩
    exact wedge_twice_zero w n y

/-- The left-wedge sequence is exact in every positive degree, including infinite-dimensional modules. -/
theorem wedgeLeft_exact_of_ne_zero (w : M) (hw : w ≠ 0) (n : ℕ) :
    Function.Exact (wedgeLeft K M w n) (wedgeLeft K M w (n + 1)) := by
  rw [LinearMap.exact_iff]
  exact ker_wedgeLeft_eq_range_of_ne_zero w hw n

/-- The zero-degree exterior multiplication by a nonzero vector is injective. -/
theorem wedgeLeft_zero_injective_of_ne_zero (w : M) (hw : w ≠ 0) :
    Function.Injective (wedgeLeft K M w 0) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hw
  have h := contractLeft_comp_wedgeLeft_zero K M φ w
  rw [hφ, one_smul] at h
  apply Function.LeftInverse.injective (f := wedgeLeft K M w 0) (g := contractLeft K M φ 0)
  intro x
  exact LinearMap.congr_fun h x

/-- In positive degree, actual next-wedge vanishing is precisely a preceding-wedge representation. -/
theorem wedgeLeft_eq_zero_iff_mem_range (w : M) (hw : w ≠ 0) (n : ℕ) (x : ⋀[K]^(n + 1) M) :
    wedgeLeft K M w (n + 1) x = 0 ↔ ∃ y : ⋀[K]^n M, wedgeLeft K M w n y = x := by
  change x ∈ LinearMap.ker (wedgeLeft K M w (n + 1)) ↔ _
  rw [ker_wedgeLeft_eq_range_of_ne_zero w hw n]
  rfl

/-- An actual linear map killing a nonzero vector kills every exterior form annihilated by wedge with that vector. -/
theorem map_eq_zero_of_wedgeLeft_eq_zero
    {N : Type*} [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (w : M) (hw : w ≠ 0) (hfw : f w = 0)
    (n : ℕ) (x : ⋀[K]^n M) (hx : wedgeLeft K M w n x = 0) :
    map n f x = 0 := by
  cases n with
  | zero =>
    have hx0 : x = 0 := (wedgeLeft_zero_injective_of_ne_zero w hw) (hx.trans (map_zero _).symm)
    rw [hx0, map_zero]
  | succ n =>
    obtain ⟨y, hy⟩ := (wedgeLeft_eq_zero_iff_mem_range w hw n x).mp hx
    rw [← hy]
    have h := LinearMap.congr_fun (map_comp_wedgeLeft K M f w n) y
    change map (n + 1) f (wedgeLeft K M w n y) = wedgeLeft K N (f w) n (map n f y) at h
    rw [h, hfw]
    apply Subtype.ext
    change (wedgeLeft K N 0 n (map n f y) : ExteriorAlgebra K N) = 0
    rw [wedgeLeft_apply_coe, map_zero, zero_mul]

end exteriorPower
