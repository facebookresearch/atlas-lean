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

public import MathlibExt.LinearAlgebra.ExteriorPower.Contraction

/-!
# Contraction and left exterior multiplication

Left exterior multiplication raises homogeneous degree by one. Restricted
contraction and left multiplication satisfy Cartan's contraction identity,
as a direct homogeneous consequence of Mathlib's
`CliffordAlgebra.contractLeft_ι_mul`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- **Left exterior multiplication over a commutative ring.** Let R be a commutative
ring, M an R-module whose addition is an abelian group, m∈M, and n∈ℕ.
The R-linear map wedgeLeft R M m n sends x∈⋀^n M to m∧x∈⋀^(n+1) M. -/
def wedgeLeft (m : M) (n : ℕ) :
    (⋀[R]^n M) →ₗ[R] (⋀[R]^(n + 1) M) :=
  alternatingMapLinearEquiv ((ιMulti R (n + 1)).curryLeft m)

/-- **Wedge prepends a vector to a pure exterior product.** Let R be a commutative
ring, M an R-module with abelian-group addition, m∈M, n∈ℕ, and a : Fin n→M.
Left multiplication sends the pure exterior word a to the word with m prepended. -/
@[simp]
theorem wedgeLeft_apply_ιMulti (m : M) (n : ℕ) (a : Fin n → M) :
    wedgeLeft R M m n (ιMulti R n a) =
      ιMulti R (n + 1) (Matrix.vecCons m a) := by
  simp [wedgeLeft]

/-- **Left wedge agrees with multiplication in the exterior algebra.** Let R be a
commutative ring, M an R-module with abelian-group addition, m∈M, n∈ℕ, and
x∈⋀^n M. In ExteriorAlgebra R M, the image of wedgeLeft R M m n x is ι(m)*x. -/
theorem wedgeLeft_apply_coe (m : M) (n : ℕ) (a : ⋀[R]^n M) :
    (wedgeLeft R M m n a : ExteriorAlgebra R M) =
      ExteriorAlgebra.ι R m * (a : ExteriorAlgebra R M) := by
  let lhs : (⋀[R]^n M) →ₗ[R] ExteriorAlgebra R M :=
    (⋀[R]^(n + 1) M).subtype.comp (wedgeLeft R M m n)
  let rhs : (⋀[R]^n M) →ₗ[R] ExteriorAlgebra R M :=
    ((Algebra.lmul R (ExteriorAlgebra R M)) (ExteriorAlgebra.ι R m)).comp
      (⋀[R]^n M).subtype
  have h : lhs = rhs := by
    apply exteriorPower.linearMap_ext
      (R := R) (n := n) (M := M) (N := ExteriorAlgebra R M)
    apply AlternatingMap.ext
    intro v
    change (wedgeLeft R M m n (ιMulti R n v) : ExteriorAlgebra R M) =
      ExteriorAlgebra.ι R m * (ιMulti R n v : ExteriorAlgebra R M)
    rw [wedgeLeft_apply_ιMulti, ιMulti_apply_coe, ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_succ_apply]
    simp only [Matrix.cons_val_zero]
    congr 1
  exact LinearMap.congr_fun h a

/-- **Naturality of left exterior multiplication.** Let R be a commutative ring,
M and N R-modules with abelian-group addition, f : M→ₗ[R] N, m∈M, and n∈ℕ.
The induced exterior maps satisfy (⋀^(n+1) f)(m∧x)=f(m)∧(⋀^n f)(x). -/
theorem map_comp_wedgeLeft
    {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (m : M) (n : ℕ) :
    (map (n + 1) f).comp (wedgeLeft R M m n) =
      (wedgeLeft R N (f m) n).comp (map n f) := by
  apply exteriorPower.linearMap_ext
    (R := R) (n := n) (M := M) (N := ⋀[R]^(n + 1) N)
  apply AlternatingMap.ext
  intro a
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    wedgeLeft_apply_ιMulti, map_apply_ιMulti]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · rfl

/-- **Cartan contraction identity over a commutative ring.** Let R be a commutative
ring, M an R-module with abelian-group addition, φ : M→ₗ[R] R, m∈M, and n∈ℕ.
On ⋀^(n+1) M, left contraction and exterior multiplication satisfy
ι_φ∘(m∧·)+(m∧·)∘ι_φ=φ(m)•id. No normalization of φ or nonzero condition on m is assumed. -/
theorem contractLeft_comp_wedgeLeft_add_wedgeLeft_comp_contractLeft
    (x : Module.Dual R M) (m : M) (n : ℕ) :
    (contractLeft R M x (n + 1)).comp (wedgeLeft R M m (n + 1)) +
        (wedgeLeft R M m n).comp (contractLeft R M x n) =
      x m • LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change (contractLeft R M x (n + 1) (wedgeLeft R M m (n + 1) a) :
        ExteriorAlgebra R M) +
      (wedgeLeft R M m n (contractLeft R M x n a) : ExteriorAlgebra R M) =
        x m • (a : ExteriorAlgebra R M)
  rw [contractLeft_apply_coe, wedgeLeft_apply_coe, wedgeLeft_apply_coe,
    contractLeft_apply_coe, CliffordAlgebra.contractLeft_ι_mul]
  exact sub_add_cancel _ _

/-- **Degree-zero contraction and wedge identity.** Let R be a commutative ring,
M an R-module with abelian-group addition, φ : M→ₗ[R] R, and m∈M.
On ⋀^0 M, contracting after left exterior multiplication by m equals φ(m)•id. -/
theorem contractLeft_comp_wedgeLeft_zero
    (x : Module.Dual R M) (m : M) :
    (contractLeft R M x 0).comp (wedgeLeft R M m 0) =
      x m • LinearMap.id := by
  apply exteriorPower.linearMap_ext
    (R := R) (n := 0) (M := M) (N := ⋀[R]^0 M)
  apply AlternatingMap.ext
  intro a
  simp [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    wedgeLeft_apply_ιMulti, contractLeft_apply_ιMulti]
  congr 1

end exteriorPower
