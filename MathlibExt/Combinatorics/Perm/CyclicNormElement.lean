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
# Actual signed cyclic norm elements

The signed norm is the sum of every actual finite rotation with its integer
permutation sign. Reindexing through the actual negative rotation coordinate
gives the same element for inverse rotations. The head-fixing group-ring
map is the native monoid-algebra map of the actual permutation embedding.
No rational scalar or norm/composition certificate is used.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

universe u

namespace Equiv.Perm

variable (R : Type u) [CommRing R]

/-- The original signed sum of all actual rotations of `n+1` letters. -/
def signedCyclicNormElement (n : ℕ) : MonoidAlgebra R (Perm (Fin (n + 1))) :=
  ∑ r : Fin (n + 1), MonoidAlgebra.single (finRotate (n + 1) ^ r.val)
    ((((finRotate (n + 1) ^ r.val).sign : ℤ) : R))

/-- Inverse rotations give exactly the same original signed norm. -/
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

/-- The actual native group-ring embedding fixes the original first coefficient position. -/
def headFixingGroupRingMap (n : ℕ) :
    MonoidAlgebra R (Perm (Fin n)) →ₐ[R] MonoidAlgebra R (Perm (Fin (n + 1))) :=
  MonoidAlgebra.mapDomainAlgHom R R (headFixingHom n)

/-- Every actual head-fixing group-ring generator keeps the original coefficient. -/
theorem headFixingGroupRingMap_single (n : ℕ) (σ : Perm (Fin n)) (r : R) :
    headFixingGroupRingMap R n (MonoidAlgebra.single σ r) =
      MonoidAlgebra.single (headFixingHom n σ) r := by
  simp [headFixingGroupRingMap, MonoidAlgebra.mapDomainAlgHom]

end Equiv.Perm
