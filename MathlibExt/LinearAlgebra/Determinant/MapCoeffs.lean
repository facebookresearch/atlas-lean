/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Determinants after transporting scalar coefficients

Let `e : R ≃+* S`, and let the same additive group `M` carry compatible
`R`- and `S`-module structures.  Compatibility means

```text
e c • x = c • x.
```

Suppose `fR : M →ₗ[R] M` and `fS : M →ₗ[S] M` have the same underlying
function.  Given a finite `R`-basis of `M`, this file proves

```text
e fR.det = fS.det.
```

## Informal proof

Let `b : Basis ι R M`, and use `b.mapCoeffs e h` as the corresponding
`S`-basis.  The transported basis has the same vectors as `b`.  Moreover,
`Module.Basis.mapCoeffs_repr` identifies the entire representation
equivalence. In particular, the `i`-th coordinate of any
vector in the transported basis is obtained by applying `e` to its `i`-th
coordinate in `b`.

Consequently, for every pair of basis indices `i,j`,

```text
toMatrix (b.mapCoeffs e h) (b.mapCoeffs e h) fS i j
  = e (toMatrix b b fR i j).
```

Indeed, both entries are the corresponding coordinate of the common value
`fS (b j) = fR (b j)`.  Matrix extensionality therefore identifies the
`S`-matrix with `Matrix.map e` of the `R`-matrix.

Now rewrite both linear-map determinants using `LinearMap.det_toMatrix`.
The matrix equality and `RingEquiv.map_det` give

```text
e (det (toMatrix b b fR))
  = det (toMatrix (b.mapCoeffs e h) (b.mapCoeffs e h) fS),
```

which is the desired equality.

The argument uses only commutative rings.  Empty finite bases are included:
both matrix determinants are the empty determinant `1`, and the same proof
applies unchanged.

## API novelty

The closest standard result is `Algebra.norm_eq_of_ringEquiv`, but that
compares determinants only for multiplication endomorphisms in algebra
norms.  It does not apply to arbitrary linear endomorphisms.  The ingredients
used here—`Basis.mapCoeffs_repr`, `RingEquiv.map_det`, and
`LinearMap.det_toMatrix`—do not already package this general transport law.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Module

universe uR uS uM uι

namespace LinearMap

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
variable {M : Type uM} [AddCommGroup M] [Module R M] [Module S M]
variable {ι : Type uι} [Finite ι]

/-- Determinants commute with transport along a scalar-ring equivalence when
the scalar actions and the underlying endomorphism agree. -/
theorem det_mapCoeffs (e : R ≃+* S)
    (h : ∀ (c : R) (x : M), e c • x = c • x)
    (b : Basis ι R M) (fR : M →ₗ[R] M) (fS : M →ₗ[S] M)
    (hf : ∀ x, fS x = fR x) :
    e fR.det = fS.det := by
  let _ : Fintype ι := Fintype.ofFinite ι
  classical
  have hmatrix :
      LinearMap.toMatrix (b.mapCoeffs e h) (b.mapCoeffs e h) fS =
        (LinearMap.toMatrix b b fR).map e := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply,
      Basis.mapCoeffs_apply, Basis.mapCoeffs_repr,
      LinearMap.toMatrix_apply]
    change e (b.repr (fS (b j)) i) = e (b.repr (fR (b j)) i)
    rw [hf]
  calc
    e fR.det = e (LinearMap.toMatrix b b fR).det := by
      rw [LinearMap.det_toMatrix]
    _ = ((LinearMap.toMatrix b b fR).map e).det := e.map_det _
    _ = (LinearMap.toMatrix (b.mapCoeffs e h)
        (b.mapCoeffs e h) fS).det := by rw [hmatrix]
    _ = fS.det := LinearMap.det_toMatrix _ _

end LinearMap

end
