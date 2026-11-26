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
# Exactness of wedge multiplication over a field

For a vector space `M` over a field `K` and a nonzero vector `w`, the sequence `Λ^n_K M —w∧→
Λ^(n+1)_K M —w∧→ Λ^(n+2)_K M` is exact for every `n : ℕ`. The degree-zero map `Λ^0_K M → Λ^1_K
M` is injective.

A functional `φ` with `φ(w)=1` gives the contraction formula `w ∧ ι_φ(x)=x` whenever `w ∧ x=0`
in positive degree. This also implies that a linear map killing `w` kills any exterior form
annihilated by wedging with `w`.

Reference: Bourbaki, *Algebra*, Chapter III.
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

/-- Let `K` be a field and `M` a `K`-vector space. Let `w : M`, `φ : Dual K M` with `φ w=1`, `n :
ℕ`, and `x ∈ Λ^(n+1)_K M` with `w ∧ x=0`. Then `wedgeLeft w n (contractLeft φ n x)=x`. -/
theorem wedge_kernel_eq_wedge_contraction (w : M) (φ : Module.Dual K M) (hφ : φ w = 1)
    (n : ℕ) (x : ⋀[K]^(n + 1) M) (hx : wedgeLeft K M w (n + 1) x = 0) :
    wedgeLeft K M w n (contractLeft K M φ n x) = x := by
  have h := LinearMap.congr_fun
    (contractLeft_comp_wedgeLeft_add_wedgeLeft_comp_contractLeft K M φ w n) x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, hx, map_zero, zero_add,
    LinearMap.smul_apply, LinearMap.id_apply, hφ, one_smul] using h

/-- Let `K` be a field and `M` a `K`-vector space. For `w≠0` and `n : ℕ`, `ker(wedgeLeft K M w
(n+1)) = range(wedgeLeft K M w n)`, as subspaces of `Λ^(n+1)_K M`. -/
theorem ker_wedgeLeft_eq_range_of_ne_zero (w : M) (hw : w ≠ 0) (n : ℕ) :
    LinearMap.ker (wedgeLeft K M w (n + 1)) = LinearMap.range (wedgeLeft K M w n) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hw
  apply le_antisymm
  · intro x hx
    exact ⟨contractLeft K M φ n x, wedge_kernel_eq_wedge_contraction w φ hφ n x hx⟩
  · rintro x ⟨y, rfl⟩
    exact wedge_twice_zero w n y

/-- Let `K` be a field and `M` a `K`-vector space. For `w≠0` and `n : ℕ`, the maps `Λ^n_K M —w∧→
Λ^(n+1)_K M —w∧→ Λ^(n+2)_K M` satisfy `Function.Exact`. -/
theorem wedgeLeft_exact_of_ne_zero (w : M) (hw : w ≠ 0) (n : ℕ) :
    Function.Exact (wedgeLeft K M w n) (wedgeLeft K M w (n + 1)) := by
  rw [LinearMap.exact_iff]
  exact ker_wedgeLeft_eq_range_of_ne_zero w hw n

/-- Let `K` be a field and `M` a `K`-vector space. For `w : M` with `w≠0`, `wedgeLeft K M w 0 :
Λ^0_K M → Λ^1_K M` is injective. -/
theorem wedgeLeft_zero_injective_of_ne_zero (w : M) (hw : w ≠ 0) :
    Function.Injective (wedgeLeft K M w 0) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hw
  have h := contractLeft_comp_wedgeLeft_zero K M φ w
  rw [hφ, one_smul] at h
  apply Function.LeftInverse.injective (f := wedgeLeft K M w 0) (g := contractLeft K M φ 0)
  intro x
  exact LinearMap.congr_fun h x

/-- Let `K` be a field and `M` a `K`-vector space. For `w≠0`, `n : ℕ`, and `x ∈ Λ^(n+1)_K M`, `w ∧
x=0` if and only if there exists `y ∈ Λ^n_K M` with `w ∧ y=x`. -/
theorem wedgeLeft_eq_zero_iff_mem_range (w : M) (hw : w ≠ 0) (n : ℕ) (x : ⋀[K]^(n + 1) M) :
    wedgeLeft K M w (n + 1) x = 0 ↔ ∃ y : ⋀[K]^n M, wedgeLeft K M w n y = x := by
  change x ∈ LinearMap.ker (wedgeLeft K M w (n + 1)) ↔ _
  rw [ker_wedgeLeft_eq_range_of_ne_zero w hw n]
  rfl

/-- Let `K` be a field and `M` a `K`-vector space. Let `N` be a `K`-vector space and `f : M →ₗ[K]
N`. For `w≠0` with `f w=0`, `n : ℕ`, and `x ∈ Λ^n_K M` satisfying `w ∧ x=0`, the induced
exterior map satisfies `exteriorPower.map n f x=0`. -/
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
