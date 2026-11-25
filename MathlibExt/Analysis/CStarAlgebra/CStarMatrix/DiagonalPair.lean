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

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Literal diagonal pairs of star homomorphisms

Two actual homomorphisms form the two diagonal entries of a homomorphism
into the existing matrix type copy. Multiplication is genuine matrix
multiplication; no norm, commutativity, stable fold or class-sum law is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra Matrix

universe uC uP uQ uA


namespace NonUnitalStarAlgHom

variable {C : Type uC} {Q : Type uQ}
variable [NonUnitalNonAssocSemiring C] [DistribMulAction ℂ C] [Star C]
variable [Semiring Q] [StarRing Q] [Algebra ℂ Q]

/-- Let `C` be a possibly nonunital, nonassociative semiring. Let `Q` be a semiring. `ℂ` acts on `C`
preserving addition and zero. `C` has a star operation. The star on `Q` is an additive involution
reversing products. `Q` has a complex algebra structure. For `phi` and `psi : C →⋆ₙₐ[ℂ] Q`. Literal
two-entry diagonal pairing into the `CStarMatrix` representation. The source need not be unital and
the target need not be commutative or normed.
-/
noncomputable def diagonalPair (phi psi : C →⋆ₙₐ[ℂ] Q) :
    C →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) Q := by
  let family : Fin 2 → (C →⋆ₙₐ[ℂ] Q) := fun i => if i = 0 then phi else psi
  let piHom : C →⋆ₙₐ[ℂ] (Fin 2 → Q) :=
    { toFun a i := family i a
      map_zero' := funext (fun i => map_zero (family i))
      map_add' a b := funext (fun i => map_add (family i) a b)
      map_smul' c a := funext (fun i => map_smul (family i) c a)
      map_mul' a b := funext (fun i => map_mul (family i) a b)
      map_star' a := funext (fun i => map_star (family i) a) }
  let delta : (Fin 2 → Q) →⋆ₐ[ℂ] Matrix (Fin 2) (Fin 2) Q :=
    { toAlgHom := Matrix.diagonalAlgHom (n := Fin 2) (α := Q) ℂ
      map_star' v := by
        change Matrix.diagonal (star v) = (Matrix.diagonal v)ᴴ
        exact (Matrix.diagonal_conjTranspose v).symm }
  let diagonalCopy : (Fin 2 → Q) →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) Q :=
    (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin 2) (A := Q)).toStarAlgHom.comp delta
  exact diagonalCopy.toNonUnitalStarAlgHom.comp piHom

/-- Let `C` be a possibly nonunital, nonassociative semiring. Let `Q` be a semiring. `ℂ` acts on `C`
preserving addition and zero. `C` has a star operation. The star on `Q` is an additive involution
reversing products. `Q` has a complex algebra structure. For `phi` and `psi : C →⋆ₙₐ[ℂ] Q`, `a : C`
and `i` and `j : Fin 2`. Exact entries of the diagonal pairing, including both off-diagonal zeros.
-/
theorem diagonalPair_apply (phi psi : C →⋆ₙₐ[ℂ] Q) (a : C) (i j : Fin 2) :
    diagonalPair phi psi a i j =
      if i = j then (if i = 0 then phi a else psi a) else 0 := by
  dsimp only [diagonalPair]
  change Matrix.diagonal
      (fun k : Fin 2 => (if k = 0 then phi else psi) a) i j = _
  rw [Matrix.diagonal_apply]
  split_ifs <;> rfl

end NonUnitalStarAlgHom
