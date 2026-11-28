/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Canonical exterior-degree projections

The grading of the exterior algebra decomposes it into the direct sum of
its homogeneous exterior powers. Evaluating one component defines the
degree projection. Its restriction is the identity in that degree and
zero in every other degree, and it commutes with exterior maps induced by
linear maps of modules over a commutative ring.
-/

@[expose] public section

noncomputable section

universe u v w

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- For a module `M` over a commutative ring `R`, the linear map
`ExteriorAlgebra R M →ₗ[R] ⋀[R]^n M` obtained by taking the degree-`n`
component of the canonical direct-sum decomposition of the exterior algebra. -/
def projection (n : ℕ) : ExteriorAlgebra R M →ₗ[R] (⋀[R]^n M) :=
  (DFinsupp.lapply n).comp
    (DirectSum.decomposeLinearEquiv (fun k : ℕ => ⋀[R]^k M)).toLinearMap

@[simp]
theorem projection_ιMulti_self (n : ℕ) (v : Fin n → M) :
    projection R M n (ExteriorAlgebra.ιMulti R n v) = ιMulti R n v := by
  apply Subtype.ext
  change (DirectSum.decompose (fun k : ℕ => ⋀[R]^k M)
    (ExteriorAlgebra.ιMulti R n v) n : ExteriorAlgebra R M) = ExteriorAlgebra.ιMulti R n v
  exact DirectSum.decompose_of_mem_same (fun k : ℕ => ⋀[R]^k M)
    (ExteriorAlgebra.ιMulti_range R n ⟨v, rfl⟩)

theorem projection_ιMulti_ne (n k : ℕ) (h : k ≠ n) (v : Fin k → M) :
    projection R M n (ExteriorAlgebra.ιMulti R k v) = 0 := by
  apply Subtype.ext
  change (DirectSum.decompose (fun k : ℕ => ⋀[R]^k M)
    (ExteriorAlgebra.ιMulti R k v) n : ExteriorAlgebra R M) = 0
  exact DirectSum.decompose_of_mem_ne (fun k : ℕ => ⋀[R]^k M)
    (ExteriorAlgebra.ιMulti_range R k ⟨v, rfl⟩) h

/-- The degree-`n` projection retracts the inclusion of the homogeneous exterior
power: `projection R M n ∘ (⋀[R]^n M).subtype = id` as `R`-linear maps.
This holds for any module over a commutative ring, without freeness assumptions. -/
theorem projection_comp_subtype (n : ℕ) :
    (projection R M n).comp (⋀[R]^n M).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change (DirectSum.decompose (fun k : ℕ => ⋀[R]^k M)
    (a : ExteriorAlgebra R M) n : ExteriorAlgebra R M) = a
  exact DirectSum.decompose_of_mem_same (fun k : ℕ => ⋀[R]^k M) a.property

@[simp]
theorem projection_subtype_apply (n : ℕ) (a : ⋀[R]^n M) :
    projection R M n (a : ExteriorAlgebra R M) = a :=
  LinearMap.congr_fun (projection_comp_subtype R M n) a

/-- If `k ≠ n`, the degree-`n` projection vanishes on the homogeneous exterior
power of degree `k`: `projection R M n ∘ (⋀[R]^k M).subtype = 0`.
The exterior algebra is formed over an arbitrary commutative ring `R`. -/
theorem projection_comp_subtype_ne (n k : ℕ) (h : k ≠ n) :
    (projection R M n).comp (⋀[R]^k M).subtype = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change (DirectSum.decompose (fun k : ℕ => ⋀[R]^k M)
    (a : ExteriorAlgebra R M) n : ExteriorAlgebra R M) = 0
  exact DirectSum.decompose_of_mem_ne (fun k : ℕ => ⋀[R]^k M) a.property h

theorem projection_eq_zero_of_mem (n k : ℕ) (h : k ≠ n)
    (a : ExteriorAlgebra R M) (ha : a ∈ ⋀[R]^k M) : projection R M n a = 0 :=
  LinearMap.congr_fun (projection_comp_subtype_ne R M n k h) ⟨a, ha⟩

/-- For a word of `n` vectors in a module over a commutative ring `R`, the
grade involution acts on their exterior product by scalar multiplication with
`(-1 : R)^n`. The order of the vectors is unchanged. -/
theorem involute_ιMulti (n : ℕ) (v : Fin n → M) :
    CliffordAlgebra.involute (ExteriorAlgebra.ιMulti R n v) =
      (-1 : R) ^ n • ExteriorAlgebra.ιMulti R n v := by
  induction n with
  | zero =>
      simp only [ExteriorAlgebra.ιMulti_zero_apply, map_one, pow_zero, one_smul]
  | succ n ih =>
      simp only [ExteriorAlgebra.ιMulti_succ_apply, map_mul,
        CliffordAlgebra.involute_ι, ih]
      rw [mul_smul_comm, neg_mul, pow_succ, ← smul_smul, neg_one_smul]

/-- For any element `a` of the exterior algebra of an `R`-module, the degree-`n`
component of its grade involution is `(-1 : R)^n` times its degree-`n`
component. The element `a` need not itself be homogeneous. -/
theorem projection_involute (n : ℕ) (a : ExteriorAlgebra R M) :
    projection R M n (CliffordAlgebra.involute a) = (-1 : R) ^ n • projection R M n a := by
  have h : (projection R M n).comp
      (CliffordAlgebra.involute : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M).toLinearMap =
      (-1 : R) ^ n • projection R M n := by
    apply ExteriorAlgebra.lhom_ext
    intro k
    apply AlternatingMap.ext
    intro v
    by_cases hk : k = n
    · subst k
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, involute_ιMulti, map_smul,
        projection_ιMulti_self, LinearMap.smul_apply]
    · simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, involute_ιMulti, map_smul,
        projection_ιMulti_ne R M n k hk, smul_zero, LinearMap.smul_apply]
  exact LinearMap.congr_fun h a

section Naturality

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- For an `R`-linear map `f : M →ₗ[R] N`, degree-`n` projections satisfy
`projection R N n ∘ ExteriorAlgebra.map f = exteriorPower.map n f ∘ projection R M n`.
The modules `M` and `N` may belong to independent universes; no injectivity,
surjectivity or freeness hypothesis is imposed on `f` or the modules. -/
theorem projection_naturality (n : ℕ) (f : M →ₗ[R] N) :
    (projection R N n).comp (ExteriorAlgebra.map f).toLinearMap =
      (map n f).comp (projection R M n) := by
  have hmap (k : ℕ) (v : Fin k → M) :
      ExteriorAlgebra.map f (ExteriorAlgebra.ιMulti R k v) =
        ExteriorAlgebra.ιMulti R k (f ∘ v) := by
    simpa only [coe_map, ιMulti_apply_coe] using
      congrArg Subtype.val (map_apply_ιMulti f v)
  apply ExteriorAlgebra.lhom_ext
  intro k
  apply AlternatingMap.ext
  intro v
  by_cases hk : k = n
  · subst k
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, hmap, projection_ιMulti_self, map_apply_ιMulti]
  · simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, hmap, projection_ιMulti_ne R N n k hk,
      projection_ιMulti_ne R M n k hk, map_zero]

end Naturality

end exteriorPower

namespace ExteriorAlgebra

/-- If `x ∈ ⋀[A]^n M` is a homogeneous element of the exterior algebra of a
module over a commutative ring `A`, its grade involution is `(-1 : A)^n • x`.
This identifies the involution on every homogeneous component without choosing
a basis of `M`. -/
theorem involute_of_mem_exteriorPower
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {n : ℕ} {x : ExteriorAlgebra A M} (hx : x ∈ ⋀[A]^n M) :
    CliffordAlgebra.involute x = (-1 : A) ^ n • x := by
  have h :
      (CliffordAlgebra.involute : ExteriorAlgebra A M →ₐ[A] ExteriorAlgebra A M).toLinearMap.comp
          (⋀[A]^n M).subtype = (-1 : A) ^ n • (⋀[A]^n M).subtype := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    exact exteriorPower.involute_ιMulti A M n v
  exact LinearMap.congr_fun h ⟨x, hx⟩

end ExteriorAlgebra
