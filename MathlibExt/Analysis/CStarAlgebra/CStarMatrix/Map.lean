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
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Unital entrywise star-algebra maps on C-star matrices

The existing nonunital entrywise map is upgraded using its actual matrix
identity value. Every coefficient has its original mapped value; no norm,
injectivity, equivalence or nontriviality premise is introduced.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarMatrix
universe uR uI
variable {R : Type uR} {ι : Type uI}
variable [Semiring R] [StarRing R] [Fintype ι] [DecidableEq ι]

section UnitalMap

universe uS uT
variable {S : Type uS} [CommSemiring S] {T : Type uT}
variable [Semiring T] [StarRing T] [Algebra S R] [Algebra S T]

/-- Let `R` be a semiring. Let `ι` be a finite index type with decidable equality. Let `S` be a
commutative semiring. Let `T` be a semiring. The star on `R` is an additive involution reversing
products. The star on `T` is an additive involution reversing products. `R` is an algebra over `S`.
`T` is an algebra over `S`. For `f : R →⋆ₐ[S] T`. The construction upgrades the stock entrywise
nonunital star hom using its matrix identity value.
-/
public def mapStarAlgHom (f : R →⋆ₐ[S] T) :
    CStarMatrix ι ι R →⋆ₐ[S] CStarMatrix ι ι T := by
  let g : CStarMatrix ι ι R →⋆ₙₐ[S] CStarMatrix ι ι T :=
    CStarMatrix.mapₙₐ (n := ι) f.toNonUnitalStarAlgHom
  have hOne : g 1 = 1 := by
    apply CStarMatrix.ext
    intro i j
    change f (if i = j then 1 else 0) = if i = j then 1 else 0
    by_cases hij : i = j <;> simp only [hij, ↓reduceIte, map_one, map_zero]
  exact
    { toFun := g
      map_zero' := map_zero g
      map_add' := map_add g
      map_mul' := map_mul g
      map_one' := hOne
      commutes' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, hOne]
      map_star' := map_star g }

/-- Let `R` be a semiring. Let `ι` be a finite index type with decidable equality. Let `S` be a
commutative semiring. Let `T` be a semiring. The star on `R` is an additive involution reversing
products. The star on `T` is an additive involution reversing products. `R` is an algebra over `S`.
`T` is an algebra over `S`. For `f : R →⋆ₐ[S] T`, `X : CStarMatrix ι ι R` and `i` and `j : ι`. Every
unital matrix-hom value is the entrywise coefficient map.
-/
public theorem mapStarAlgHom_apply (f : R →⋆ₐ[S] T) (X : CStarMatrix ι ι R) (i j : ι) :
    mapStarAlgHom f X i j = f (X i j) := by
  change (X.map f) i j = f (X i j)
  exact CStarMatrix.map_apply

end UnitalMap

end CStarMatrix
