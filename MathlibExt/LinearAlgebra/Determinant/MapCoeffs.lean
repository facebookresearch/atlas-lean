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
# Determinant under a scalar-ring equivalence

Let R,S be commutative rings, e:R≃+*S and M have R,S actions with e(c)•x=c•x. For a finite
R-basis b and endomorphisms f_R,f_S with identical functions, e(det_R f_R)=det_S f_S.
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

/-- **Scalar coefficient transport of a determinant.**

Let R,S be commutative rings, e:R≃+*S, and M an R- and S-module with compatible e-scalars. If
M has a finite R-basis and f_R:M→ₗ[R]M,f_S:M→ₗ[S]M agree on every x, then e(f_R.det)=f_S.det.
-/
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
