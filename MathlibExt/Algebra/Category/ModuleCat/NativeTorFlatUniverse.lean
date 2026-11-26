/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.TorBalancedUniverse

/-!
# Positive-degree Tor vanishing for flat coefficients

Let R be a commutative ring in universe u and M,N R-modules in W=max(u,v). If M is flat,
tensoring a projective resolution of N with M preserves its exactness in positive degrees, so
Tor_{q+1}^R(M,N)=0 for every q∈ℕ.

The canonical Tor symmetry gives the same vanishing when N is flat and M is arbitrary. The
coefficient lift height v is independent of the ring universe, and neither statement requires
projectivity of the other module.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ModuleCat.UniverseTensor

namespace ModuleCat.UniverseTensor
universe u v

variable (R : Type u) [CommRing R]

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. For R-modules M,N in W and q∈ℕ, assume M is flat over R. Then
Tor_{q+1}^R(M,N) is zero. The tensor functor M⊗_R(-) preserves exactness of a projective
resolution of N in all positive degrees. -/
theorem nativeTor_isZero_succ_of_flat_left
    (M N : ModuleCat.{max u v} R) [Module.Flat R M] (q : ℕ) :
    IsZero (((Tor (ModuleCat.{max u v} R) (q + 1)).obj M).obj N) := by
  let F := (tensoringLeft (ModuleCat.{max u v} R)).obj M
  let Q := projectiveResolution N
  change IsZero ((F.leftDerived (q + 1)).obj N)
  refine IsZero.of_iso ?_ (Q.isoLeftDerivedObj F (q + 1))
  change IsZero
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex).homology
      (q + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  apply (HomologicalComplex.exactAt_iff'
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)
      (q + 2) (q + 1) q
      (by simp only [ChainComplex.prev]; rfl) (by simp)).2
  change ((ShortComplex.mk _ _ (Q.complex.d_comp_d (q + 2) (q + 1) q)).map
    (tensorLeft M)).Exact
  have hQ := Q.exact_succ q
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hQ ⊢
  exact Module.Flat.lTensor_exact M hQ

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. For R-modules M,N in W and q∈ℕ, assume N is flat over R. Then
Tor_{q+1}^R(M,N) is zero, by the canonical symmetry with Tor_{q+1}^R(N,M) and
flat-first-coefficient vanishing. -/
theorem nativeTor_isZero_succ_of_flat_right
    (M N : ModuleCat.{max u v} R) [Module.Flat R N] (q : ℕ) :
    IsZero (((Tor (ModuleCat.{max u v} R) (q + 1)).obj M).obj N) :=
  IsZero.of_iso (nativeTor_isZero_succ_of_flat_left R N M q)
    (nativeTorSymmetry R M N (q + 1))

end ModuleCat.UniverseTensor
