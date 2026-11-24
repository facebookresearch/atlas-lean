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
# Uniform row-homology resolutions of a Cartan--Eilenberg resolution

The vertical-homology complex in every original degree is equipped as a projective resolution of
the corresponding homology object.  Degree zero uses the canonical strict augmentation, while
positive degrees use the transported stored homology-resolution augmentation.
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

/--
The vertical row-homology complex, uniformly equipped as a projective resolution of the
corresponding homology object.
-/
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

/-- The uniform resolution has the vertical-homology complex definitionally. -/
@[simp]
theorem cartanEilenbergVerticalHomologyResolution_complex (q : ℕ) :
    (P.cartanEilenbergVerticalHomologyResolution q).complex =
      P.bicomplex.verticalHomologyComplex q :=
  rfl

/-- In degree zero, the uniform resolution uses the canonical strict
row-homology augmentation. -/
@[simp]
theorem cartanEilenbergVerticalHomologyResolution_π_zero :
    (P.cartanEilenbergVerticalHomologyResolution 0).π =
      P.rowHomologyAugmentation 0 :=
  rfl

/-- In positive degree, the uniform resolution reuses the transported
positive-row augmentation. -/
@[simp]
theorem cartanEilenbergVerticalHomologyResolution_π_succ (q : ℕ) :
    (P.cartanEilenbergVerticalHomologyResolution (q + 1)).π =
      (P.cartanEilenbergVerticalHomologySuccResolution q).π :=
  rfl

end HomologicalComplex.CartanEilenbergResolution

end
