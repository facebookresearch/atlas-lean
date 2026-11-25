/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Actual augmentation-ideal cotangents at a group-scheme identity

The coefficient algebra is the original global section ring of the
group scheme over Spec R. Its augmentation is induced by the actual
identity section through the native Gamma--Spec coefficient isomorphism.
For an affine group the invariant cotangent is the actual augmentation
ideal modulo its square; morphisms use the original algebra maps on
both ideals. Affineness is required at that geometric identification.

For finite p-power group schemes this cotangent lives over the original
integral base. Formal p-divisible Lie is a separate representation of
the complete tower, rather than differentiation after inverting p.

References: Messing, *The crystals associated to Barsotti--Tate groups*,
Chapter II; Scholze--Weinstein, arXiv:1211.6357v2, Sections 1 and 3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GroupZeroCotangentModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (R : Type) [CommRing R]

/-- An actual augmented coefficient algebra over the original base ring. -/
structure AugmentedAlgebra where
  ring : CommAlgCat.{0} R
  augmentation : ring →ₐ[R] R

/-- The original augmentation kernel, retaining its entire nilpotent structure. -/
def AugmentedAlgebra.ideal (A : AugmentedAlgebra R) : Ideal A.ring :=
  RingHom.ker A.augmentation.toRingHom

/-- The genuine zero-section cotangent I/I². -/
abbrev AugmentedAlgebra.cotangent (A : AugmentedAlgebra R) := (A.ideal R).Cotangent

/-- An algebra map preserving the actual zero section. -/
structure AugmentedMap (A B : AugmentedAlgebra R) where
  map : A.ring →ₐ[R] B.ring
  augmentation : B.augmentation.comp map = A.augmentation

/-- The map of actual augmentation ideals. -/
theorem AugmentedMap.ideal_compatible {A B : AugmentedAlgebra R}
    (f : AugmentedMap R A B) : A.ideal R ≤ (B.ideal R).comap f.map.toRingHom := by
  intro x hx
  change B.augmentation (f.map x) = 0
  rw [← AlgHom.comp_apply, f.augmentation]
  exact hx

/-- The native quotient-induced cotangent map of this original algebra map. -/
def AugmentedMap.cotangent {A B : AugmentedAlgebra R} (f : AugmentedMap R A B) :
    A.cotangent R →ₗ[R] B.cotangent R :=
  Ideal.mapCotangent (A.ideal R) (B.ideal R) f.map (f.ideal_compatible R)

variable (G : Over (Spec (.of R))) [GrpObj G]

/-- The original global section ring of the group scheme. -/
abbrev GroupRing := Γ(G.left, ⊤)

/-- Original R scalars through the actual structure morphism. -/
def groupScalars : R →+* GroupRing R G :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ G.hom.appTop).hom

/-- The actual identity section induces this augmentation. -/
def groupAugmentation : GroupRing R G →+* R :=
  ((η[G]).left.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom).hom

/-- Its coefficient identity is the original group identity-section square. -/
theorem groupAugmentation_scalars :
    (groupAugmentation R G).comp (groupScalars R G) = RingHom.id R := by
  have hw : (η[G]).left ≫ G.hom = 𝟙 (Spec (.of R)) := by
    exact Over.w (η[G])
  have h : G.hom.appTop ≫ (η[G]).left.appTop = 𝟙 Γ(Spec (.of R), ⊤) := by
    rw [← Scheme.Hom.comp_appTop, hw, Scheme.Hom.id_appTop]
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ G.hom.appTop ≫
    (η[G]).left.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom).hom = RingHom.id R
  rw [← Category.assoc G.hom.appTop, h, Category.id_comp, Iso.inv_hom_id]
  rfl

/-- The original group scheme's coordinate algebra with its actual augmentation. -/
def groupAlgebra : AugmentedAlgebra R := by
  letI := (groupScalars R G).toAlgebra
  exact
    { ring := CommAlgCat.of R (GroupRing R G)
      augmentation :=
        { __ := groupAugmentation R G
          commutes' := fun a ↦ DFunLike.congr_fun (groupAugmentation_scalars R G) a } }

/-- The invariant zero-section cotangent of the actual affine group scheme. -/
abbrev GroupCotangent [IsAffine G.left] := (groupAlgebra R G).cotangent R

end MathlibExt.AlgebraicGeometry.GroupZeroCotangentModels
