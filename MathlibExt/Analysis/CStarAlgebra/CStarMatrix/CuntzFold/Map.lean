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

public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.CuntzFold
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Actual coefficient-map naturality of finite Cuntz folds

The two supplied families are genuine algebraic families and the second is
exactly the coefficient image of the first. The literal matrix fold and its
inverse commute with that actual coefficient map. These characteristics are
needed to build the all-positive-size stabilized quotient and unitary maps.
No matrix equivalence, norm, quotient kernel or outcome model is an input.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Matrix

namespace CuntzFamily

universe uS uR uT uI
variable {S : Type uS} [CommSemiring S]
variable {R : Type uR} {T : Type uT} {ι : Type uI}
variable [Semiring R] [StarRing R] [Algebra S R]
variable [Semiring T] [StarRing T] [Algebra S T]
variable [Fintype ι] [DecidableEq ι]

/-- Let `S` be a commutative semiring and let `R`, `T` be star semirings with `S`-algebra structures.
Let `ι` be finite with decidable equality and let `f : R →⋆ₐ[S] T`. Suppose `v : ι → R` and `w : ι →
T` satisfy the Cuntz relations `star (v i) * v j = δij`, `∑ i, v i * star (v i) = 1`, and the
corresponding two relations for `w`. If `w i = f (v i)` for every `i`, applying `f` to the fold of
any matrix agrees with folding the entrywise image using `w`. The symbol `δij` is one on equal
indices and zero otherwise.
-/
public theorem fold_map (f : R →⋆ₐ[S] T) (v : ι → R) (w : ι → T)
    (hVOrth : ∀ i j : ι, star (v i) * v j = if i = j then 1 else 0)
    (hVPartition : (∑ i : ι, v i * star (v i)) = 1)
    (hWOrth : ∀ i j : ι, star (w i) * w j = if i = j then 1 else 0)
    (hWPartition : (∑ i : ι, w i * star (w i)) = 1)
    (hw : ∀ i : ι, w i = f (v i)) (X : CStarMatrix ι ι R) :
    fold S w hWOrth hWPartition (X.map f) = f (fold S v hVOrth hVPartition X) := by
  simp only [fold_apply, CStarMatrix.map_apply, map_sum, map_mul, map_star, hw]

/-- Let `S` be a commutative semiring. Let `R` be a semiring. Let `T` be a semiring. Let `ι` be a finite
index type with decidable equality. The star on `R` is an additive involution reversing products.
`R` is an algebra over `S`. The star on `T` is an additive involution reversing products. `T` is an
algebra over `S`. For `f : R →⋆ₐ[S] T`, `v : ι → R`, `w : ι → T` and `z : R`. Assume `∀ i j : ι,
star (v i) * v j = if i = j then 1 else 0`, `(∑ i : ι, v i * star (v i)) = 1`, `∀ i j : ι, star (w
i) * w j = if i = j then 1 else 0`, `(∑ i : ι, w i * star (w i)) = 1` and `∀ i : ι, w i = f (v i)`.
Every inverse matrix entry is the coefficient image of the source sandwich entry.
-/
public theorem fold_symm_map (f : R →⋆ₐ[S] T) (v : ι → R) (w : ι → T)
    (hVOrth : ∀ i j : ι, star (v i) * v j = if i = j then 1 else 0)
    (hVPartition : (∑ i : ι, v i * star (v i)) = 1)
    (hWOrth : ∀ i j : ι, star (w i) * w j = if i = j then 1 else 0)
    (hWPartition : (∑ i : ι, w i * star (w i)) = 1)
    (hw : ∀ i : ι, w i = f (v i)) (z : R) :
    (fold S w hWOrth hWPartition).symm (f z) =
      ((fold S v hVOrth hVPartition).symm z).map f := by
  apply CStarMatrix.ext
  intro i j
  simp only [fold_symm_apply_entry, CStarMatrix.map_apply, map_mul, map_star, hw]

end CuntzFamily
