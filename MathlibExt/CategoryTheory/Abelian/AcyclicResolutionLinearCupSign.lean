/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.AcyclicResolutionBilinearCupSign

/-!
# Cross-degree sign for a ring-linear cup pairing

For modules over a commutative ring `R`, an `R`-bilinear pairing
is also integer-bilinear on the underlying groups. The triangular
normalization scalars therefore yield the cross-degree factor `(-1)^(pq)`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe r a b c
open CategoryTheory.ProjectiveResolution

namespace CategoryTheory

/- Proof implementation note.
The additive pairing of an arbitrary-ring linear cup has the same
forced cross-degree sign. Its integer linearization is built from the
literal additive functions, without replacing the original coefficient modules.
-/

/-- Let `R` be a commutative ring, `A,B,C` be `R`-modules, and
`cup : A →ₗ[R] B →ₗ[R] C`. For `p,q ∈ ℕ`, if
`σ_(p+q) • z = cup(σ_p • x, σ_q • y)`, with integer
`σ_n = (-1)^(n(n+1)/2)`, then `z = (-1)^(pq) • cup(x,y)`. -/
theorem linearCup_normalization_sign
    {R : Type r} [CommRing R]
    {A : Type a} {B : Type b} {C : Type c}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (cup : A →ₗ[R] B →ₗ[R] C) (p q : ℕ) (x : A) (y : B) (z : C)
    (h : acyclicResolutionNormalizationSign (p + q) • z =
      cup (acyclicResolutionNormalizationSign p • x)
        (acyclicResolutionNormalizationSign q • y)) :
    z = (-1 : ℤ) ^ (p * q) • cup x y := by
  let cupZ : A →ₗ[ℤ] B →ₗ[ℤ] C :=
    { toFun := fun a => (cup a).toAddMonoidHom.toIntLinearMap
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro y
        exact DFunLike.congr_fun (map_add cup a b) y
      map_smul' := by
        intro n a
        apply LinearMap.ext
        intro y
        change cup (n • a) y = n • cup a y
        simpa only [LinearMap.smul_apply] using DFunLike.congr_fun (map_zsmul cup n a) y }
  have hz : acyclicResolutionNormalizationSign (p + q) • z =
      cupZ (acyclicResolutionNormalizationSign p • x)
        (acyclicResolutionNormalizationSign q • y) := h
  exact bilinearCup_normalization_sign cupZ p q x y z hz

end CategoryTheory
