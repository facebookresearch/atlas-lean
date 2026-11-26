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


public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# A flat first factor makes positive Tor vanish

Let R be a commutative ring and A,D R-modules in ModuleCat^u(R).
Here Tor_n(A,D) is the nth left derived object of the functor
A ⊗[R] − evaluated at D, so derivation is in the second factor.

If A is flat over R, tensoring a projective resolution of D by A
preserves its exact positive-degree stages. Therefore Tor_(p+1)(A,D)
is a zero object for every p ≥ 0, with no condition on D beyond its
R-module structure.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

universe u

namespace CategoryTheory

/-- For a commutative ring R and modules A,D in
ModuleCat^u(R), if A is flat over R, then Tor_(p+1)(A,D) is
a zero object for every p ≥ 0.
The Tor convention is derivation of A ⊗[R] − in its second factor D. -/
theorem isZero_Tor_succ_of_flat_left
    {R : Type u} [CommRing R]
    (A D : ModuleCat.{u} R) [Module.Flat R A] (p : ℕ) :
    IsZero
      (((CategoryTheory.Tor (ModuleCat.{u} R) (p + 1)).obj A).obj D) := by
  let F := (tensoringLeft (ModuleCat.{u} R)).obj A
  let Q := projectiveResolution D
  change IsZero ((F.leftDerived (p + 1)).obj D)
  refine IsZero.of_iso ?_ (Q.isoLeftDerivedObj F (p + 1))
  change IsZero
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex).homology
      (p + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  apply (HomologicalComplex.exactAt_iff'
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)
      (p + 2) (p + 1) p
      (by simp only [ChainComplex.prev]; rfl) (by simp)).2
  change
    ((ShortComplex.mk _ _
      (Q.complex.d_comp_d (p + 2) (p + 1) p)).map (tensorLeft A)).Exact
  exact Module.Flat.lTensor_shortComplex_exact A _ (Q.exact_succ p)

end CategoryTheory

end
