/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Combinatorics.Perm.CyclicHeadFixing
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Signed cyclic norms and fixed-head group-ring maps

For a commutative ring `R` and `N=n+1`, the signed cyclic norm is `N_n=∑_(r=0)^(N-1) sign(ρ^r)
[ρ^r]` in `R[S_N]`, where `ρ=finRotate N`. Summing the inverse rotation powers with their
signs gives the same element.

The fixed-head permutation map `H_n : S_n → S_N` extends to an `R`-algebra homomorphism
`R[S_n] → R[S_N]`, preserving coefficients on each permutation basis element.

Reference: Loday, *Cyclic Homology*, Sections 1.1 and 4.5.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

universe u

namespace Equiv.Perm

variable (R : Type u) [CommRing R]

/-- Let `R` be a commutative ring, `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. In `R[S_N]`, put `N_n =
∑ r : Fin N, sign(ρ^r.val) [ρ^r.val]`, with signs cast from `ℤ` to `R`.
`signedCyclicNormElement R n` is this sum over one full rotation cycle. -/
def signedCyclicNormElement (n : ℕ) : MonoidAlgebra R (Perm (Fin (n + 1))) :=
  ∑ r : Fin (n + 1), MonoidAlgebra.single (finRotate (n + 1) ^ r.val)
    ((((finRotate (n + 1) ^ r.val).sign : ℤ) : R))

/-- Let `R` be a commutative ring, `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. In `R[S_N]`, put `N_n =
∑ r : Fin N, sign(ρ^r.val) [ρ^r.val]`, with signs cast from `ℤ` to `R`. The inverse-power sum
satisfies `∑ r : Fin N, sign((ρ^r.val)⁻¹) [(ρ^r.val)⁻¹] = signedCyclicNormElement R n`. -/
theorem signedCyclicNormElement_inverse (n : ℕ) :
    (∑ r : Fin (n + 1), MonoidAlgebra.single (finRotate (n + 1) ^ r.val)⁻¹
      (((((finRotate (n + 1) ^ r.val)⁻¹).sign : ℤ) : R))) =
        signedCyclicNormElement R n := by
  classical
  simp_rw [rotationPower_inverse]
  exact Fintype.sum_equiv (Equiv.neg (Fin (n + 1)))
    (fun r : Fin (n + 1) => MonoidAlgebra.single (finRotate (n + 1) ^ (-r).val)
      ((((finRotate (n + 1) ^ (-r).val).sign : ℤ) : R)))
    (fun r : Fin (n + 1) => MonoidAlgebra.single (finRotate (n + 1) ^ r.val)
      ((((finRotate (n + 1) ^ r.val).sign : ℤ) : R)))
    (fun _ => rfl)

/-- For a commutative ring `R` and `n : ℕ`, `headFixingGroupRingMap R n : R[S_n] →ₐ[R] R[S_(n+1)]`
sends `[π]` to `[headFixingHom n π]`. The permutation image fixes zero and permutes the tail. -/
def headFixingGroupRingMap (n : ℕ) :
    MonoidAlgebra R (Perm (Fin n)) →ₐ[R] MonoidAlgebra R (Perm (Fin (n + 1))) :=
  MonoidAlgebra.mapDomainAlgHom R R (headFixingHom n)

/-- For a commutative ring `R`, `n : ℕ`, `σ ∈ S_n`, and `c : R`, `headFixingGroupRingMap R n
(MonoidAlgebra.single σ c) = MonoidAlgebra.single (headFixingHom n σ) c`. -/
theorem headFixingGroupRingMap_single (n : ℕ) (σ : Perm (Fin n)) (r : R) :
    headFixingGroupRingMap R n (MonoidAlgebra.single σ r) =
      MonoidAlgebra.single (headFixingHom n σ) r := by
  simp [headFixingGroupRingMap, MonoidAlgebra.mapDomainAlgHom]

end Equiv.Perm
