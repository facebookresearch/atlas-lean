/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.WittLoopGroups
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.Algebra.Group.ULift

/-!
# Witt Grassmannian and convolution as actual quotient sheaves

The Grassmannian is the fpqc sheafification of LG/L+G. The twofold
convolution quotient is the sheafification of (LG times LG)/(L+G times L+G),
with action (g,k).(h,j) = (g h, h^{-1} k j). Its multiplication map is
induced by actual group multiplication. Neither quotient carries a freely
chosen multiplication, geometric space or monoidal sheaf category.

Reference: Zhu, arXiv:1407.8519v3, Sections1.1 and1.4. The quotient and
sheafification are completed native category constructions. Ind-perfect
geometry, equivariant perverse coefficients and Satake are separate inputs
and conclusions, not consequences claimed here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.WittLoopCorrespondences

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open WittLoopGroups WittLatticeFamilies

variable (p : ℕ) [Fact p.Prime]
  (G : Over (Spec (.of ℤ_[p]))) [GrpObj G]

abbrev AffinePresheaf := PerfectAlgebra p ⥤ Type 1

/-- Only lift the actual geometric point sets to the site's sheaf universe. -/
def loopSets : AffinePresheaf p :=
  loops p G ⋙ forget GrpCat ⋙ uliftFunctor.{1, 0}

/-- The actual positive-loop point sets, in the same universe. -/
def positiveSets : AffinePresheaf p :=
  positiveLoops p G ⋙ forget GrpCat ⋙ uliftFunctor.{1, 0}

instance loopSetsGroup (R : PerfectAlgebra p) :
    Group ((loopSets p G).obj R) :=
  inferInstanceAs (Group (ULift.{1} ((loops p G).obj R)))

instance positiveSetsGroup (R : PerfectAlgebra p) :
    Group ((positiveSets p G).obj R) :=
  inferInstanceAs (Group (ULift.{1} ((positiveLoops p G).obj R)))

/-- The prescribed inclusion of the actual positive-loop point sets. -/
def inclusion : positiveSets p G ⟶ loopSets p G :=
  Functor.whiskerRight (positiveToLoop p G)
    (forget GrpCat ⋙ uliftFunctor.{1, 0})

/-- Product of actual presheaves, with the actual pointwise maps. -/
def pairs (A B : AffinePresheaf p) : AffinePresheaf p where
  obj R := A.obj R × B.obj R
  map f := TypeCat.ofHom fun x ↦ (A.map f x.1, B.map f x.2)
  map_id R := by ext x <;> simp
  map_comp f g := by ext x <;> simp

/-- The actual right action used to define the Grassmannian. -/
def rightAction : pairs p (loopSets p G) (positiveSets p G) ⟶ loopSets p G where
  app R := TypeCat.ofHom fun x ↦ x.1 * (inclusion p G).app R x.2
  naturality {R S} f := by
    ext x
    symm
    change ULift.up ((loops p G).map f
      (x.1.down * (positiveToLoop p G).app R x.2.down)) = _
    rw [map_mul]
    exact congrArg ULift.up (congrArg (fun y ↦ (loops p G).map f x.1.down * y)
      (congrArg (fun h ↦ h x.2.down) ((positiveToLoop p G).naturality f).symm))

/-- Forget the positive-loop factor in the actual action domain. -/
def rightProjection : pairs p (loopSets p G) (positiveSets p G) ⟶ loopSets p G where
  app R := TypeCat.ofHom Prod.fst

/-- The literal right-action quotient, prior to fpqc sheafification. -/
def grassmannianPresheaf : AffinePresheaf p :=
  coequalizer (rightAction p G) (rightProjection p G)

/-- The fixed quotient map on the actual loop points. -/
def quotient : loopSets p G ⟶ grassmannianPresheaf p G :=
  coequalizer.π (rightAction p G) (rightProjection p G)

/-- Every actual positive-loop translate represents the same quotient point. -/
theorem quotient_translate (R : PerfectAlgebra p) (g : (loopSets p G).obj R)
    (h : (positiveSets p G).obj R) :
    (quotient p G).app R (g * (inclusion p G).app R h) =
      (quotient p G).app R g := by
  exact congrArg (fun t ↦ t.app R (g, h))
    (coequalizer.condition (rightAction p G) (rightProjection p G))

/-- The actual convolution action domain. -/
def convolutionActionDomain : AffinePresheaf p :=
  pairs p (pairs p (loopSets p G) (loopSets p G))
    (pairs p (positiveSets p G) (positiveSets p G))

/-- The middle and right positive-loop changes of trivialization. -/
def convolutionAction : convolutionActionDomain p G ⟶
    pairs p (loopSets p G) (loopSets p G) where
  app R := TypeCat.ofHom fun x ↦
    (x.1.1 * (inclusion p G).app R x.2.1,
      ((inclusion p G).app R x.2.1)⁻¹ * x.1.2 * (inclusion p G).app R x.2.2)
  naturality {R S} f := by
    ext x
    symm
    have h₁ := congrArg (fun h ↦ h x.2.1.down)
      ((positiveToLoop p G).naturality f).symm
    have h₂ := congrArg (fun h ↦ h x.2.2.down)
      ((positiveToLoop p G).naturality f).symm
    change (loops p G).map f ((positiveToLoop p G).app R x.2.1.down) =
      (positiveToLoop p G).app S ((positiveLoops p G).map f x.2.1.down) at h₁
    change (loops p G).map f ((positiveToLoop p G).app R x.2.2.down) =
      (positiveToLoop p G).app S ((positiveLoops p G).map f x.2.2.down) at h₂
    change (ULift.up ((loops p G).map f
        (x.1.1.down * (positiveToLoop p G).app R x.2.1.down)),
      ULift.up ((loops p G).map f
        (((positiveToLoop p G).app R x.2.1.down)⁻¹ * x.1.2.down *
          (positiveToLoop p G).app R x.2.2.down))) =
      (ULift.up ((loops p G).map f x.1.1.down *
        (positiveToLoop p G).app S ((positiveLoops p G).map f x.2.1.down)),
      ULift.up (((positiveToLoop p G).app S
        ((positiveLoops p G).map f x.2.1.down))⁻¹ *
          (loops p G).map f x.1.2.down * (positiveToLoop p G).app S
            ((positiveLoops p G).map f x.2.2.down)))
    simp only [map_mul, map_inv, h₁, h₂]

/-- Forget the actual changes of trivialization. -/
def convolutionProjection : convolutionActionDomain p G ⟶
    pairs p (loopSets p G) (loopSets p G) where
  app R := TypeCat.ofHom Prod.fst

/-- The actual twofold twisted quotient before sheafification. -/
def convolutionPresheaf : AffinePresheaf p :=
  coequalizer (convolutionAction p G) (convolutionProjection p G)

/-- Actual multiplication of loop points, followed by the fixed quotient. -/
def productToGrassmannian : pairs p (loopSets p G) (loopSets p G) ⟶
    grassmannianPresheaf p G where
  app R := TypeCat.ofHom fun x ↦ (quotient p G).app R (x.1 * x.2)
  naturality {R S} f := by
    ext x
    have h := congrArg (fun t ↦ t (x.1 * x.2)) ((quotient p G).naturality f)
    change (quotient p G).app S
      ((loopSets p G).map f x.1 * (loopSets p G).map f x.2) =
          (grassmannianPresheaf p G).map f ((quotient p G).app R (x.1 * x.2))
    have hm : (loopSets p G).map f (x.1 * x.2) =
        (loopSets p G).map f x.1 * (loopSets p G).map f x.2 := by
      apply ULift.ext
      exact map_mul ((loops p G).map f).hom _ _
    rw [← hm]
    exact h

/-- Multiplication is invariant under both actual changes of trivialization. -/
theorem multiplication_invariant :
    convolutionAction p G ≫ productToGrassmannian p G =
      convolutionProjection p G ≫ productToGrassmannian p G := by
  ext R x
  change (quotient p G).app R
    ((x.1.1 * (inclusion p G).app R x.2.1) *
      (((inclusion p G).app R x.2.1)⁻¹ * x.1.2 *
        (inclusion p G).app R x.2.2)) =
          (quotient p G).app R (x.1.1 * x.1.2)
  have h : (x.1.1 * (inclusion p G).app R x.2.1) *
      (((inclusion p G).app R x.2.1)⁻¹ * x.1.2 *
        (inclusion p G).app R x.2.2) =
          (x.1.1 * x.1.2) * (inclusion p G).app R x.2.2 := by
    simp only [_root_.mul_assoc, mul_inv_cancel_left]
  rw [h]
  exact quotient_translate p G R (x.1.1 * x.1.2) x.2.2

/-- The convolution morphism is the actual coequalizer-descended product. -/
def multiplication : convolutionPresheaf p G ⟶ grassmannianPresheaf p G :=
  coequalizer.desc (productToGrassmannian p G) (multiplication_invariant p G)

/-- The actual fpqc Grassmannian sheaf, independent of a representing model. -/
def grassmannian : Sheaf (fpqcTopology p) (Type 1) :=
  (presheafToSheaf (fpqcTopology p) (Type 1)).obj
    ((opOpEquivalence (PerfectAlgebra p)).functor ⋙ grassmannianPresheaf p G)

/-- The actual fpqc convolution sheaf. -/
def convolution : Sheaf (fpqcTopology p) (Type 1) :=
  (presheafToSheaf (fpqcTopology p) (Type 1)).obj
    ((opOpEquivalence (PerfectAlgebra p)).functor ⋙ convolutionPresheaf p G)

/-- Its fixed multiplication map, induced by the same sheafification functor. -/
def convolutionMap : convolution p G ⟶ grassmannian p G :=
  (presheafToSheaf (fpqcTopology p) (Type 1)).map
    (Functor.whiskerLeft (opOpEquivalence (PerfectAlgebra p)).functor
      (multiplication p G))

end MathlibExt.AlgebraicGeometry.WittLoopCorrespondences
