/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.RowHomologyPositive
public import MathlibExt.Algebra.Homology.CartanEilenberg.RowHomologyZeroAugmentation

/-!
# Uniform vertical-homology projective resolutions

Let P be Cartan–Eilenberg data for a nonnegative complex L in an abelian category. For every
original degree q, its resolution-direction vertical homology is equipped as a projective
resolution of H_q(L).

In degree zero the augmentation is the canonical column-zero homology augmentation. In positive
degree it is transported from the stored homology resolution. The underlying complex remains the
full vertical- homology complex in every degree.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex.CartanEilenbergResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L : ChainComplex C ℕ} (P : CartanEilenbergResolution L)

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. For
every q ∈ ℕ, P.bicomplex.verticalHomologyComplex(q) is equipped as a projective resolution of
H_q(L). Degree zero uses the canonical row-homology augmentation and positive degrees use the
stored homology-resolution comparison. -/
noncomputable def cartanEilenbergVerticalHomologyResolution (q : ℕ) :
    ProjectiveResolution (L.homology q) where
  complex := P.bicomplex.verticalHomologyComplex q
  projective a := by
    cases q with
    | zero =>
        apply Projective.of_iso (P.rowHomologyZeroIso a).symm
        infer_instance
    | succ q =>
        exact
          (P.cartanEilenbergVerticalHomologySuccResolution q).projective a
  π := by
    cases q with
    | zero =>
        exact P.rowHomologyAugmentation 0
    | succ q =>
        exact (P.cartanEilenbergVerticalHomologySuccResolution q).π
  quasiIso := by
    cases q with
    | zero =>
        exact P.rowHomologyZeroAugmentation_quasiIso
    | succ q =>
        exact (P.cartanEilenbergVerticalHomologySuccResolution q).quasiIso

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. For
each q ∈ ℕ, the complex underlying the uniform projective resolution of H_q(L) is exactly
P.bicomplex.verticalHomologyComplex(q). -/
@[simp]
theorem cartanEilenbergVerticalHomologyResolution_complex (q : ℕ) :
    (P.cartanEilenbergVerticalHomologyResolution q).complex =
      P.bicomplex.verticalHomologyComplex q :=
  rfl

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. At
original degree zero, the uniform resolution's augmentation is the canonical
rowHomologyAugmentation(0) to H₀(L)[0], induced by the term-resolution column augmentation. -/
@[simp]
theorem cartanEilenbergVerticalHomologyResolution_π_zero :
    (P.cartanEilenbergVerticalHomologyResolution 0).π =
      P.rowHomologyAugmentation 0 :=
  rfl

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. At
original degree q+1, the uniform resolution uses precisely the augmentation of the positive-row
resolution transported from PH_{q+1}. -/
@[simp]
theorem cartanEilenbergVerticalHomologyResolution_π_succ (q : ℕ) :
    (P.cartanEilenbergVerticalHomologyResolution (q + 1)).π =
      (P.cartanEilenbergVerticalHomologySuccResolution q).π :=
  rfl

end HomologicalComplex.CartanEilenbergResolution

end
